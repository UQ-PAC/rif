open Cvc5
open Lifter
open Util

module Solver = struct
  type style = Integers | BitVectors

  module Cvc_util = struct
    module Variables = Map.Make (String)
    module Globals = Map.Make (String)

    let make_term tm srt name = Term.mk_var_s tm srt name

    let make_register_vars tm srt (i1, i2) : Term.term Variables.t =
      let extract_names (i : Lifter.instruction_summary) =
        List.map Lifter.varSym (i.read @ i.write)
        @ List.map (fun v -> "M" ^ Lifter.varSym v) (i.load @ i.store)
      in

      List.fold_left
        (fun map name -> Variables.add name (make_term tm srt name) map)
        Variables.empty
        (extract_names i1 @ extract_names i2)

    let make_spec_vars tm srt gs : Term.term Globals.t =
      List.fold_left
        (fun map name -> Globals.add name (make_term tm srt name) map)
        Globals.empty gs

    (* adds a level of "prime" to all variables in this map
       keeps keys the same for lookup purposes *)
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
            (Solver.synth_fun solver tm f (Array.of_list inputs) srt None)
            acc)
        map Variables.empty

    let find_sp map = Variables.find "SP" map
    let find_pc map = Variables.find "PC" map
    let find_reg map i = Variables.find ("R" ^ i) map
    let find_mem_reg map i = Variables.find ("MR" ^ i) map
    let find_glob map n = Globals.find n map
  end

  module Asl_util = struct
    open LibASL

    type vmap = Term.term Cvc_util.Variables.t

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
            (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
            | _ when String.equal s "ZeroExtend" -> Kind.Null_term
            | _ when String.equal s "add_bits" -> Kind.Add
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

  module Spec = struct
    type speclang =
      | Term of Kind.t * speclang list
      | Const of int
      | Bool of bool
      | Pre of string
      | Post of string

    let rec collect_globs s =
      match s with
      | Post n -> [ n ]
      | Pre n -> [ n ]
      | Term (_, ss) -> List.flatten @@ List.map collect_globs ss
      | _ -> []

    let rec sanity_guar_uses_posts s =
      match s with
      | Post _ -> failwith "Sanity check: guarantee includes a post-state?"
      | Term (_, ss) -> List.iter sanity_guar_uses_posts ss
      | _ -> ()

    let input (r : string) (g : string) : speclang * speclang =
      let parse s =
        ignore s;
        Bool true
      in
      let guar = parse g in

      sanity_guar_uses_posts guar;
      (parse r, guar)

    let rec cvc_of_spec tm fromv tov spec =
      let subcall = cvc_of_spec tm fromv tov in

      match spec with
      | Term (k, ts) -> Term.mk_term tm k (Array.of_list @@ List.map subcall ts)
      | Const i -> Term.mk_int tm i
      | Bool b -> Term.mk_bool tm b
      | Pre s -> Cvc_util.find_glob fromv s
      | Post s -> Cvc_util.find_glob tov s
  end

  let subset_only_mem vars : string list =
    Cvc_util.Variables.fold
      (fun k _ (l : string list) : string list ->
        if Char.equal k.[0] 'M' then k :: l else l)
      vars []

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

  let solve ~verb block_semantics (style : style) spec pair : bool =
    let tm = TermManager.mk_tm () in
    let solver = Solver.mk_solver ~logic:"ALL" tm in
    Solver.set_option solver "sygus" "true";
    Solver.set_option solver "full-sygus-verify" "true";
    Solver.set_option solver "sygus-enum" "fast";
    Solver.set_option solver "sygus-si" "all";

    if verb then Solver.set_option solver "output" "sygus";

    Solver.set_option solver "incremental" "true";
    let var_sort =
      match style with
      | Integers -> Sort.mk_int_sort tm
      | BitVectors -> Sort.mk_bv_sort tm 64
    in

    let instruction_one, instruction_two = unpack_sem block_semantics pair in
    let rely, guarantee = spec in

    let inst_vars =
      Cvc_util.make_register_vars tm var_sort (unpack_sum block_semantics pair)
    in
    let spec_globs =
      Cvc_util.make_spec_vars tm var_sort
        (Spec.collect_globs rely @ Spec.collect_globs guarantee)
    in

    let mems = subset_only_mem inst_vars in

    (*
      inst_vars  (string->term map) -> all registers & referenced memory-locations
      mems       (string list)      -> all referenced memory-location names
      spec_globs (string->term map) -> all x,y program variables
    *)
    let inst_vars_p =
      Cvc_util.promote_variables ~ext:"'" tm var_sort inst_vars
    in
    let inst_vars_pp =
      Cvc_util.promote_variables ~ext:"\"" tm var_sort inst_vars
    in

    let state_terms =
      List.map second (Cvc_util.Variables.bindings inst_vars)
      @ List.map second (Cvc_util.Variables.bindings inst_vars_p)
      @ List.map second (Cvc_util.Variables.bindings inst_vars_pp)
    in
    let state_funcs =
      Cvc_util.middlestate_functions solver tm var_sort inst_vars state_terms
    in

    let sygus_inst_vars =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) var_sort)
        inst_vars
    in
    let sygus_inst_vars_p =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) var_sort)
        inst_vars_p
    in
    let sygus_inst_vars_pp =
      Cvc_util.Variables.map
        (fun t -> Solver.declare_sygus_var solver (Term.to_string t) var_sort)
        inst_vars_pp
    in

    let sygus_terms =
      List.map second (Cvc_util.Variables.bindings sygus_inst_vars)
      @ List.map second (Cvc_util.Variables.bindings sygus_inst_vars_p)
      @ List.map second (Cvc_util.Variables.bindings sygus_inst_vars_pp)
    in
    let sygus_funcs =
      Cvc_util.Variables.map
        (fun t ->
          Term.mk_term tm Kind.Apply_uf (Array.of_list (t :: sygus_terms)))
        state_funcs
    in

    let assume_terms =
      Asl_util.cvc_of_stmtlist tm sygus_inst_vars sygus_inst_vars_p
        instruction_one
      @ Asl_util.cvc_of_stmtlist tm sygus_inst_vars_p sygus_inst_vars_pp
          instruction_two
    in
    List.iter (Solver.add_sygus_assume solver) assume_terms;

    let constraint_terms =
      Asl_util.cvc_of_stmtlist tm sygus_inst_vars sygus_funcs instruction_two
      @ Asl_util.cvc_of_stmtlist tm sygus_funcs sygus_inst_vars_pp
          instruction_one
    in
    List.iter (Solver.add_sygus_constraint solver) constraint_terms;

    let result = Solver.check_synth solver in
    print_endline
      (Printf.sprintf "[!] Solver found middlestate... %s"
         (SynthResult.to_string result));

    SynthResult.has_solution result
end
