open Cvc5
open Lifter
open Util

module Solver = struct
  module Asl_lib = struct
    open LibASL

    let cvc_of_slice (s : Asl_ast.slice) =
      match s with
      | Slice_LoWd _ -> ()
      | Slice_HiLo _ -> ()
      | _ -> failwith "Internal: converting unexpected ASL slice"

    let cvc_of_lexpr (e : Asl_ast.lexpr) =
      match e with
      | LExpr_Var _ -> ()
      | LExpr_Field _ -> ()
      | LExpr_Array _ -> ()
      | _ -> failwith "Internal: converting unexpected ASL lexpr"

    let cvc_of_expr (e : Asl_ast.expr) =
      match e with
      | Expr_Var _ -> ()
      | Expr_TApply _ -> ()
      | Expr_Slices _ -> ()
      | Expr_Field _ -> ()
      | Expr_Array _ -> ()
      | Expr_LitInt _ -> ()
      | Expr_LitBits _ -> ()
      | _ -> failwith "Internal: converting unexpected ASL expr"

    let cvc_of_stmt (s : Asl_ast.stmt) =
      match s with
      | Stmt_Assign _ -> ()
      | Stmt_ConstDecl _ -> ()
      | Stmt_VarDecl _ -> ()
      | Stmt_VarDeclsNoInit _ -> ()
      | Stmt_Assert _ -> ()
      | Stmt_TCall _ -> ()
      | Stmt_If _ -> ()
      | Stmt_Throw _ -> ()
      | _ -> failwith "Internal: converting unexpected ASL stmt"

    let cvc_of_stmtlist = List.map cvc_of_stmt
  end

  module Cvc_helpers = struct
    module Variables = Map.Make (String)

    let make_global_state vs tm : Term.term Variables.t =
      let make_term v =
        Term.mk_var_s tm (Sort.mk_bv_sort tm 64) (Lifter.varSym v)
      in
      List.fold_left
        (fun map var -> Variables.add (Lifter.varSym var) (make_term var) map)
        Variables.empty vs
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

  let _demo_prove : TermManager.tm =
    let tm = TermManager.mk_tm () in
    let solver = Solver.mk_solver ~logic:"LIA" tm in

    Solver.set_option solver "sygus" "true";
    Solver.set_option solver "incremental" "false";

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
    let instruction_one, instruction_two = unpack_sem block_semantics pair in
    let necessary_state =
      Lifter.all_variables (unpack_sum block_semantics pair)
    in

    ignore _demo_prove;

    ignore necessary_state;
    ignore (Asl_lib.cvc_of_stmtlist instruction_one);
    ignore (Asl_lib.cvc_of_stmtlist instruction_two);
    true
end
