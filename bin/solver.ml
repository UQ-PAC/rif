open Cvc5
open Lifter
open Util

module Solver = struct
  module Cvc_util = struct
    module Variables = Map.Make (String)

    let make_global_state tm (i1, i2) : Term.term Variables.t =
      let make_term name = Term.mk_var_s tm (Sort.mk_bv_sort tm 64) name in

      let extract_all (i : Lifter.instruction_summary) =
        List.map Lifter.varSym (i.read @ i.write)
        @ List.map (fun v -> "M" ^ Lifter.varSym v) (i.load @ i.store)
      in

      List.fold_left
        (fun map name -> Variables.add name (make_term name) map)
        Variables.empty
        (extract_all i1 @ extract_all i2)
  end

  module Asl_lib = struct
    open LibASL

    type vmap = Term.term Cvc_util.Variables.t

    let regSym i = "R" ^ i

    let cvc_of_stmtlist (tm : TermManager.tm) (vs : vmap) =
      let cvc_of_slice (s : Asl_ast.slice) : Op.op =
        match s with
        | Slice_LoWd (Expr_LitInt l, Expr_LitInt h) ->
            Op.mk_op tm Kind.Bitvector_extract
              (Array.of_list [ int_of_string h; int_of_string l ])
        | _ -> failwith "Internal: converting unexpected ASL slice"
      in

      let cvc_of_lexpr (e : Asl_ast.lexpr) : Term.term =
        match e with
        | LExpr_Var (Ident n) when String.equal n "SP_EL0" ->
            Cvc_util.Variables.find "SP" vs
        | LExpr_Var (Ident n) when String.equal n "_PC" ->
            Cvc_util.Variables.find "PC" vs
        | LExpr_Array (LExpr_Var (Ident n), Expr_LitInt i)
          when String.equal n "_R" ->
            Cvc_util.Variables.find (regSym i) vs
        | _ -> failwith "Internal: converting unexpected ASL lexpr"
      in

      let cvc_of_function (s : string) : Kind.t =
        match s with
        | _ when String.equal s "" -> Kind.Null_term
        | _ -> failwith "Internal: converting unexpected ASL function"
      in

      let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
        match e with
        | Expr_Var _ -> Term.mk_true tm
        | Expr_TApply (FIdent (f, _), e1s, e2s) ->
            Term.mk_term tm (cvc_of_function f)
              (Array.of_list (List.map cvc_of_expr (e1s @ e2s)))
        | Expr_Slices (e, slices) ->
            List.fold_left
              (fun acc s ->
                Term.mk_term_op tm (cvc_of_slice s) (Array.of_list [ acc ]))
              (cvc_of_expr e) slices
        | Expr_Field _ -> Term.mk_true tm
        | Expr_Array _ -> Term.mk_true tm
        | Expr_LitInt _ -> Term.mk_true tm
        | Expr_LitBits _ -> Term.mk_true tm
        | _ -> failwith "Internal: converting unexpected ASL expr"
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
        | Stmt_TCall (FIdent (_f, _), e1s, e2s, _) ->
            ignore e1s;
            ignore e2s;
            Term.mk_true tm
        | Stmt_If _ -> Term.mk_true tm
        | Stmt_Throw _ -> Term.mk_true tm
        | _ -> failwith "Internal: converting unexpected ASL stmt"
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

    let necessary_state =
      Cvc_util.make_global_state tm (unpack_sum block_semantics pair)
    in

    let terms_one =
      Asl_lib.cvc_of_stmtlist tm necessary_state instruction_one
    in
    let terms_two =
      Asl_lib.cvc_of_stmtlist tm necessary_state instruction_two
    in

    List.iter
      (fun t -> print_endline @@ Term.to_string t)
      (terms_one @ terms_two);
    true
end
