open Cvc5
open Lifter
open Util

module Solver = struct
  module Cvc_util = struct
    module Variables = Map.Make (String)

    let make_term tm srt name = Term.mk_var_s tm srt name

    let make_global_state tm srt (i1, i2) : Term.term Variables.t =
      let extract_names (i : Lifter.instruction_summary) =
        List.map Lifter.varSym (i.read @ i.write)
        @ List.map (fun v -> "M" ^ Lifter.varSym v) (i.load @ i.store)
      in

      List.fold_left
        (fun map name -> Variables.add name (make_term tm srt name) map)
        Variables.empty
        (extract_names i1 @ extract_names i2)

    (* adds a level of "prime" to all variables in this map
       keeps names the same for lookup purposes *)
    let promote_variables ?(ext = "'") tm srt map : Term.term Variables.t =
      Variables.fold
        (fun name _ acc ->
          let prime = name ^ ext in
          Variables.add name (make_term tm srt prime) acc)
        map Variables.empty

    let middlestate_functions solver tm srt map inputs : Term.term Variables.t =
      Variables.fold
        (fun name _ acc ->
          let f = "f" ^ name in
          Variables.add name
            (Solver.synth_fun solver tm f (Array.of_list inputs)
               srt None)
            acc)
        map Variables.empty

    let find_sp map = Variables.find "SP" map
    let find_pc map = Variables.find "PC" map
    let find_reg map i = Variables.find ("R" ^ i) map
    let find_mem_reg map i = Variables.find ("MR" ^ i) map
  end

  module Asl_util = struct
    open LibASL

    type vmap = Term.term Cvc_util.Variables.t

    type node =
      | Slice of Asl_ast.slice
      | LExpr of Asl_ast.lexpr
      | Expr of Asl_ast.expr
      | Addr of Asl_ast.expr
      | Stmt of Asl_ast.stmt
      | Fun of string

    let unexpected (node : node) =
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
        val mutable ivars = Cvc_util.Variables.empty
        val mutable updated : string list = []

        method was_updated s =
          Option.is_some (List.find_opt (String.equal s) updated)

        method cvc_of_stmtlist (tm : TermManager.tm) (fromv : vmap) (tov : vmap)
            (stmts : Asl_ast.stmt list) =
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
                Cvc_util.find_sp tov
            | LExpr_Var (Ident "_PC") ->
                updated <- "PC" :: updated;
                Cvc_util.find_pc tov
            | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
                updated <- ("R" ^ i) :: updated;
                Cvc_util.find_reg tov i
            | _ -> unexpected @@ LExpr e
          in

          let cvc_of_function (s : string) : Kind.t =
            match s with
            (* for simplicity, everything is 64bv, so ZeroExtending can be treated as a noop *)
            | _ when String.equal s "ZeroExtend" -> Kind.Null_term
            | _ -> unexpected @@ Fun s
          in

          let cvc_of_addr (write : bool) (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                if write then updated <- ("MR" ^ i) :: updated;
                Cvc_util.find_mem_reg (if write then tov else fromv) i
            | _ -> unexpected @@ Addr e
          in

          let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                Cvc_util.find_reg fromv i
            | Expr_Var (Ident n) -> Cvc_util.Variables.find n ivars
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
                ignore (List.map cvc_of_slice slices);
                cvc_of_expr e
                (* let sliced =
                  List.fold_left
                    (fun acc s ->
                      Term.mk_term_op tm (cvc_of_slice s)
                        (Array.of_list [ acc ]))
                    (cvc_of_expr e) slices *)
            | Expr_Field _ -> Term.mk_true tm
            | Expr_LitInt _ -> Term.mk_true tm
            | Expr_LitBits _ -> Term.mk_true tm
            | _ -> unexpected @@ Expr e
          in

          let cvc_of_stmt (s : Asl_ast.stmt) =
            match s with
            | Stmt_Assign (l, r, _) ->
                Term.mk_term tm Kind.Equal
                  (Array.of_list [ cvc_of_lexpr l; cvc_of_expr r ])
            | Stmt_ConstDecl (_, Ident n, exp, _) ->
                ivars <- Cvc_util.Variables.add n (cvc_of_expr exp) ivars;
                Term.mk_true tm
            | Stmt_VarDecl _ -> Term.mk_true tm
            | Stmt_VarDeclsNoInit _ -> Term.mk_true tm
            | Stmt_Assert _ -> Term.mk_true tm
            | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Term.mk_term tm Kind.Equal
                  (Array.of_list [ cvc_of_addr true addr; cvc_of_expr value ])
            | Stmt_TCall (FIdent (_f, _), _, es, _) ->
                ignore es;
                Term.mk_true tm
            | Stmt_If _ -> Term.mk_true tm
            | Stmt_Throw _ -> Term.mk_true tm
            | _ -> unexpected @@ Stmt s
          in

          let updates =
            List.filter_map
              (fun s ->
                let x = cvc_of_stmt s in
                if Term.equal x (Term.mk_true tm) then None else Some x)
              stmts
          in
          let no_updates =
            Cvc_util.Variables.fold
              (fun key term acc ->
                if this#was_updated key then acc
                else
                  Term.mk_term tm Kind.Equal
                    (Array.of_list [ term; Cvc_util.Variables.find key tov ])
                  :: acc)
              fromv []
          in
          updates @ no_updates
      end

    let cvc_of_stmtlist tm fromv tov stmts =
      (new translator)#cvc_of_stmtlist tm fromv tov stmts
  end

  let unpack_sem (blocks : Lifter.blockdata Lifter.Blocks.t) ((b1, i1), (b2, i2))
      =
    ( (match access_index i1 (Lifter.Blocks.find b1 blocks).block_semantics with
      | _, r -> r),
      match access_index i2 (Lifter.Blocks.find b2 blocks).block_semantics with
      | _, r -> r )

  let unpack_sum (blocks : Lifter.blockdata Lifter.Blocks.t) ((b1, i1), (b2, i2))
      =
    ( (match access_index i1 (Lifter.Blocks.find b1 blocks).block_summary with
      | _, r -> r),
      match access_index i2 (Lifter.Blocks.find b2 blocks).block_summary with
      | _, r -> r )

  let solve ~verb block_semantics pair : bool =
    let tm = TermManager.mk_tm () in
    let solver = Solver.mk_solver ~logic:"QF_BV" tm in
    Solver.set_option solver "sygus" "true";
    Solver.set_option solver "full-sygus-verify" "true";
    Solver.set_option solver "sygus-enum" "fast";
    Solver.set_option solver "sygus-si" "all";

    if verb then (
      Solver.set_option solver "output" "sygus";
    );

    Solver.set_option solver "incremental" "true";
    let bv64 = Sort.mk_int_sort tm in

    let instruction_one, instruction_two = unpack_sem block_semantics pair in

    let vars =
      Cvc_util.make_global_state tm bv64 (unpack_sum block_semantics pair)
    in
    let vars_p = Cvc_util.promote_variables ~ext:"'" tm bv64 vars in
    let vars_pp = Cvc_util.promote_variables ~ext:"\"" tm bv64 vars in

    let state_terms =
      List.map second (Cvc_util.Variables.bindings vars)
      @ List.map second (Cvc_util.Variables.bindings vars_pp)
    in
    let state_funcs =
      Cvc_util.middlestate_functions solver tm bv64 vars state_terms
    in

    let sygus_vars =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) bv64)
        vars
    in
    let sygus_vars_p =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) bv64)
        vars_p
    in
    let sygus_vars_pp =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) bv64)
        vars_pp
    in

    let sygus_terms =
      List.map second (Cvc_util.Variables.bindings sygus_vars)
      @ List.map second (Cvc_util.Variables.bindings sygus_vars_pp)
    in
    let sygus_funcs =
      Cvc_util.Variables.map
        (fun t ->
          Term.mk_term tm Kind.Apply_uf (Array.of_list (t :: sygus_terms)))
        state_funcs
    in

    let assume_terms =
      (Asl_util.cvc_of_stmtlist tm sygus_vars sygus_vars_p instruction_one) @
      (Asl_util.cvc_of_stmtlist tm sygus_vars_p sygus_vars_pp instruction_two) in
    List.iter (Solver.add_sygus_assume solver) assume_terms;

    let constraint_terms =
      (Asl_util.cvc_of_stmtlist tm sygus_vars sygus_funcs instruction_two) @
      (Asl_util.cvc_of_stmtlist tm sygus_funcs sygus_vars_pp instruction_one) in
    List.iter (Solver.add_sygus_constraint solver) constraint_terms;

    let result = Solver.check_synth solver in
    print_endline
      (Printf.sprintf "[!] Solver found middlestate... %s"
         (SynthResult.to_string result));

    SynthResult.has_solution result
end
