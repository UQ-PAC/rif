module Cvc = struct
    open LibASL
    open Cvc5

    type errnode =
      | Slice of Asl_ast.slice
      | LExpr of Asl_ast.lexpr
      | Expr of Asl_ast.expr
      | Addr of Asl_ast.expr
      | Stmt of Asl_ast.stmt
      | Fun of string

    let unexpected (node : errnode) =
      match node with
      | Slice n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected slice %s"
               (Utils.to_string @@ Asl_utils.PP.pp_slice n))
      | LExpr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected lexpr %s"
               (Asl_utils.pp_lexpr n))
      | Expr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected expr %s"
               (Asl_utils.pp_expr n))
      | Addr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected address expr %s"
               (Asl_utils.pp_expr n))
      | Stmt n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected stmt %s"
               (Asl_utils.pp_stmt n))
      | Fun n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected function %s" n)

    class translator =
      object (this)
        val mutable ivars = Util.Cvc.TermMap.empty
        val mutable updated : string list = []

        method was_updated s =
          Option.is_some (List.find_opt (String.equal s) updated)

        method cvc_of_stmtlist (tm : TermManager.tm) (fromv : Util.Cvc.terms)
            (tov : Util.Cvc.terms) (stmts : Asl_ast.stmt list) =
          let cvc_of_slice (s : Asl_ast.slice) : Op.op =
            match s with
            | Slice_LoWd (Expr_LitInt l, Expr_LitInt h) ->
                Op.mk_op tm Kind.Bitvector_extract
                  (Array.of_list [ int_of_string h - 1; int_of_string l ])
            | _ -> unexpected @@ Slice s
          in

          let cvc_of_lexpr (e : Asl_ast.lexpr) : Term.term =
            match e with
            | LExpr_Var (Ident "SP_EL0") ->
                updated <- "SP" :: updated;
                Util.Cvc.find_sp tov
            | LExpr_Var (Ident "_PC") ->
                updated <- "PC" :: updated;
                Util.Cvc.find_pc tov
            | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
                updated <- ("R" ^ i) :: updated;
                Util.Cvc.find_reg tov i
            | _ -> unexpected @@ LExpr e
          in

          let cvc_of_function (s : string) : Kind.t =
            match s with
            (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
            | _ when String.equal s "ZeroExtend" -> Kind.Null_term
            | _ when String.equal s "add_bits" -> Kind.Add
            | _ -> unexpected @@ Fun s
          in

          let cvc_of_addr (write : bool) (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                if write then updated <- ("MR" ^ i) :: updated;
                Util.Cvc.find_mem_reg (if write then tov else fromv) i
            | Expr_TApply
                ( FIdent ("add_bits", _),
                  _,
                  [
                    Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i);
                    Expr_LitBits _;
                  ] ) ->
                (* Collapse mem[R1 + X] into mem[R0] *)
                if write then updated <- ("MR" ^ i) :: updated;
                Util.Cvc.find_mem_reg (if write then tov else fromv) i
            | _ -> unexpected @@ Addr e
          in

          let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                Util.Cvc.find_reg fromv i
            | Expr_Var (Ident n) -> Util.Cvc.TermMap.find n ivars
            | Expr_TApply (FIdent ("Mem.set", _), _, es) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Term.mk_term tm Kind.Equal
                  (Array.of_list [ cvc_of_addr true addr; cvc_of_expr value ])
            | Expr_TApply (FIdent ("Mem.read", _), _, es) ->
                cvc_of_addr false (List.hd es)
            | Expr_TApply (FIdent (f, _), _, es) -> (
                match cvc_of_function f with
                | Kind.Null_term -> cvc_of_expr (List.hd es)
                | k ->
                    Term.mk_term tm k (Array.of_list (List.map cvc_of_expr es)))
            | Expr_Slices (e, slices) ->
                (* Pretend slices aren't real *)
                ignore (List.map cvc_of_slice slices);
                cvc_of_expr e
                (* let sliced =
                  List.fold_left
                    (fun acc s ->
                      Term.mk_term_op tm (cvc_of_slice s)
                        (Array.of_list [ acc ]))
                    (cvc_of_expr e) slices *)
            | Expr_Field _ -> Term.mk_true tm
            | Expr_LitInt s -> Term.mk_int tm @@ int_of_string s
            | Expr_LitBits s ->
                Term.mk_int tm @@ Int64.to_int @@ Int64.of_string @@ "0b" ^ s
            | _ -> unexpected @@ Expr e
          in

          let cvc_of_stmt (s : Asl_ast.stmt) =
            match s with
            | Stmt_Assign (l, r, _) ->
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list [ cvc_of_lexpr l; cvc_of_expr r ]))
            | Stmt_ConstDecl (_, Ident n, exp, _) ->
                ivars <- Util.Cvc.TermMap.add n (cvc_of_expr exp) ivars;
                None
            | Stmt_VarDecl _ -> None
            | Stmt_VarDeclsNoInit _ -> None
            | Stmt_Assert _ -> None
            | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list
                        [ cvc_of_addr true addr; cvc_of_expr value ]))
            | Stmt_TCall (FIdent (_f, _), _, _es, _) -> None
            | Stmt_If _ -> None
            | Stmt_Throw _ -> None
            | _ -> unexpected @@ Stmt s
          in

          let updates = List.filter_map cvc_of_stmt stmts in
          let no_updates =
            Util.Cvc.TermMap.fold
              (fun key term acc ->
                if this#was_updated key then acc
                else
                  Term.mk_term tm Kind.Equal
                    (Array.of_list [ term; Util.Cvc.TermMap.find key tov ])
                  :: acc)
              fromv []
          in
          updates @ no_updates
      end
  end

  let semantics_to_cvc tm fromv tov stmts =
    (new Cvc.translator)#cvc_of_stmtlist tm fromv tov stmts

  let cvc_of_inst tm fromv tov (i : instruction) =
    semantics_to_cvc tm fromv tov i.semantics

