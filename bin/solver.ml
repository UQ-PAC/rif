open Cvc5
open Lifter
open Util

module Solver = struct
  module Cvc_util = struct
    module Variables = Map.Make (String)

    let make_term tm name = Term.mk_var_s tm (Sort.mk_bv_sort tm 64) name

    let make_global_state tm (i1, i2) : Term.term Variables.t =
      let extract_names (i : Lifter.instruction_summary) =
        List.map Lifter.varSym (i.read @ i.write)
        @ List.map (fun v -> "M" ^ Lifter.varSym v) (i.load @ i.store)
      in

      List.fold_left
        (fun map name -> Variables.add name (make_term tm name) map)
        Variables.empty
        (extract_names i1 @ extract_names i2)

    (* adds a level of "prime" to all variables in this map
       keeps names the same for lookup purposes *)
    let promote_variables tm map : Term.term Variables.t =
      Variables.fold (fun name _ acc ->
        let prime = name ^ "'" in
        Variables.add name (make_term tm prime) acc)
      map Variables.empty

    let find_sp map = Variables.find "SP" map
    let find_pc map = Variables.find "PC" map
    let find_reg map i = Variables.find ("R" ^ i) map
    let find_mem_reg map i = Variables.find ("MR" ^ i) map
  end

  module Asl_util = struct
    open LibASL

    type vmap = Term.term Cvc_util.Variables.t

    type node = Slice of Asl_ast.slice | LExpr of Asl_ast.lexpr | Expr of Asl_ast.expr | Addr of Asl_ast.expr | Stmt of Asl_ast.stmt | Fun of string

    let unexpected (node : node) =
      match node with
      | Slice n -> failwith (Printf.sprintf "Internal: converting unexpected slice %s" (Utils.to_string @@ Asl_utils.PP.pp_slice n))
      | LExpr n -> failwith (Printf.sprintf "Internal: converting unexpected lexpr %s" (Asl_utils.pp_lexpr n))
      | Expr n -> failwith (Printf.sprintf "Internal: converting unexpected expr %s" (Asl_utils.pp_expr n))
      | Addr n -> failwith (Printf.sprintf "Internal: converting unexpected address expr %s" (Asl_utils.pp_expr n))
      | Stmt n -> failwith (Printf.sprintf "Internal: converting unexpected stmt %s" (Asl_utils.pp_stmt n))
      | Fun n -> failwith (Printf.sprintf "Internal: converting unexpected function %s" n)

    let cvc_of_stmtlist (tm : TermManager.tm) (fromv : vmap) (tov : vmap) =
      let memop s = String.equal "Mem.set" s || String.equal "Mem.read" s in

      let cvc_of_slice (s : Asl_ast.slice) : Op.op =
        match s with
        | Slice_LoWd (Expr_LitInt l, Expr_LitInt h) ->
            Op.mk_op tm Kind.Bitvector_extract
              (Array.of_list [ int_of_string h; int_of_string l ])
        | _ -> unexpected @@ Slice s
      in

      let cvc_of_lexpr (e : Asl_ast.lexpr) : Term.term =
        match e with
        | LExpr_Var (Ident "SP_EL0") ->
            Cvc_util.find_sp tov
        | LExpr_Var (Ident "_PC") ->
            Cvc_util.find_pc tov
        | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
            Cvc_util.find_reg tov i
        | _ -> unexpected @@ LExpr e
      in

      let cvc_of_function (s : string) : Kind.t =
        match s with
        | _ when String.equal s "" -> Kind.Null_term
        | _ -> unexpected @@ Fun s
      in

      let cvc_of_addr vs (e : Asl_ast.expr) : Term.term =
        match e with
        | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
          Cvc_util.find_mem_reg vs i
        | _ -> unexpected @@ Addr e
      in

      let rec cvc_of_expr ?(vs = fromv) (e : Asl_ast.expr) : Term.term =
        match e with
        | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
          Cvc_util.find_reg vs i
        | Expr_Var _ -> Term.mk_true tm
        | Expr_TApply (FIdent (f, _), _, es) when memop f ->
          let addr = List.hd es in
          let value = List.hd (List.rev es) in
          Term.mk_term tm Kind.Equal (Array.of_list [cvc_of_addr vs addr; cvc_of_expr value])
        | Expr_TApply (FIdent (f, _), _, es) ->
            Term.mk_term tm (cvc_of_function f)
              (Array.of_list (List.map cvc_of_expr es))
        | Expr_Slices (e, slices) ->
            List.fold_left
              (fun acc s ->
                Term.mk_term_op tm (cvc_of_slice s) (Array.of_list [ acc ]))
              (cvc_of_expr e) slices
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
        | Stmt_ConstDecl _ -> Term.mk_true tm
        | Stmt_VarDecl _ -> Term.mk_true tm
        | Stmt_VarDeclsNoInit _ -> Term.mk_true tm
        | Stmt_Assert _ -> Term.mk_true tm
        | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
          let addr = List.hd es in
          let value = List.hd (List.rev es) in
          Term.mk_term tm Kind.Equal (Array.of_list [cvc_of_addr tov addr; cvc_of_expr value])
        | Stmt_TCall (FIdent (_f, _), _, es, _) ->
            ignore es;
            Term.mk_true tm
        | Stmt_If _ -> Term.mk_true tm
        | Stmt_Throw _ -> Term.mk_true tm
        | _ -> unexpected @@ Stmt s
      in

      List.map cvc_of_stmt
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

  let _demo_prove tm solver =
    let integer = Sort.mk_int_sort tm in
    let boolean = Sort.mk_bool_sort tm in

    let x = Term.mk_var_s tm integer "x" in
    let y = Term.mk_var_s tm integer "y" in

    let start = Term.mk_var_s tm integer "Start" in
    let start_bool = Term.mk_var_s tm boolean "StartBool" in

    let zero = Term.mk_int tm 0 in
    let one = Term.mk_int tm 1 in

    let plus = Term.mk_term_2 tm Kind.Add start start in
    let minus = Term.mk_term_2 tm Kind.Sub start start in
    let ite = Term.mk_term_3 tm Kind.Ite start_bool start start in

    let and' = Term.mk_term_2 tm Kind.And start_bool start_bool in
    let not' = Term.mk_term_1 tm Kind.Not start_bool in
    let leq = Term.mk_term_2 tm Kind.Leq start start in

    let g =
      Solver.mk_grammar solver
        (Array.of_list [ x; y ])
        (Array.of_list [ start; start_bool ])
    in

    Grammar.add_rules g start
      (Array.of_list [ zero; one; x; y; plus; minus; ite ]);
    Grammar.add_rules g start_bool (Array.of_list [ and'; not'; leq ]);

    let max =
      Solver.synth_fun solver tm "max" (Array.of_list [ x; y ]) integer (Some g)
    in
    let min =
      Solver.synth_fun solver tm "min" (Array.of_list [ x; y ]) integer None
    in

    let varX = Solver.declare_sygus_var solver "x" integer in
    let varY = Solver.declare_sygus_var solver "y" integer in

    let max_x_y = Term.mk_term_3 tm Kind.Apply_uf max varX varY in
    let min_x_y = Term.mk_term_3 tm Kind.Apply_uf min varX varY in

    Solver.add_sygus_constraint solver (Term.mk_term_2 tm Kind.Geq max_x_y varX);
    Solver.add_sygus_constraint solver (Term.mk_term_2 tm Kind.Geq max_x_y varY);
    Solver.add_sygus_constraint solver
      (Term.mk_term_2 tm Kind.Or
         (Term.mk_term_2 tm Kind.Equal max_x_y varX)
         (Term.mk_term_2 tm Kind.Equal max_x_y varY));
    Solver.add_sygus_constraint solver
      (Term.mk_term_2 tm Kind.Equal
         (Term.mk_term_2 tm Kind.Add max_x_y min_x_y)
         (Term.mk_term_2 tm Kind.Add varX varY));

    let result = Solver.check_synth solver in
    print_endline (SynthResult.to_string result);

    tm (* return tm to ensure it outlives its terms *)

  let solve block_semantics pair : bool =
    let tm = TermManager.mk_tm () in
    let solver = Solver.mk_solver ~logic:"LIA" tm in
    Solver.set_option solver "sygus" "true";
    Solver.set_option solver "incremental" "false";

    let instruction_one, instruction_two = unpack_sem block_semantics pair in

    let vars = Cvc_util.make_global_state tm (unpack_sum block_semantics pair) in
    let vars_p = Cvc_util.promote_variables tm vars in
    let vars_pp = Cvc_util.promote_variables tm vars_p in

    Cvc_util.Variables.iter (fun n _ -> print_endline n) vars;

    let terms_one =
      Asl_util.cvc_of_stmtlist tm vars vars_p instruction_one
    in
    let terms_two =
      Asl_util.cvc_of_stmtlist tm vars_p vars_pp instruction_two
    in

    List.iter
      (fun t -> print_endline @@ Term.to_string t)
      (terms_one @ terms_two);
    true
end
