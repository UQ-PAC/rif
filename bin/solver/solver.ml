open Cvc5
open Lifter
open Spec
open Solver_utils
open Solver_state
open Solver_instruction
open Solver_spec

module type Solver = sig
  module Utils : SolverUtils

  type failure = {
    i1 : Lifter.IR.instruction;
    i2 : Lifter.IR.instruction;
    aliasing : (string * string) list;
    precondition : (string * string * bool) list;
  }

  val failure_eq : failure -> failure -> bool

  val solve_all :
    verb:bool ->
    mode:Utils.mode ->
    Spec.Lang.spec * Spec.Lang.spec ->
    (Lifter.IR.instruction * Lifter.IR.instruction) list ->
    failure list
end

module Solver : Solver = struct
  module Utils = SolverUtils

  type failure = {
    i1 : Lifter.IR.instruction;
    i2 : Lifter.IR.instruction;
    aliasing : (string * string) list;
    precondition : (string * string * bool) list;
  }

  let failure_eq f1 f2 =
    Lifter.IR.instruction_eq f1.i1 f2.i1 &&
    Lifter.IR.instruction_eq f1.i2 f2.i2 &&
    List.equal (fun (a,b) (c,d) -> String.equal a c && String.equal b d) f1.aliasing f2.aliasing &&
    List.equal (fun (a,b,c) (d,e,f) -> String.equal a d && String.equal b e && (c == f)) f1.precondition f2.precondition

  type sp = Spec.Lang.spec * Spec.Lang.spec
  type ip = Lifter.IR.instruction * Lifter.IR.instruction
  type ctx = ip * sp * string list * string list

  let solve_in_order tm srt (((i1, i2), (r, g), syms, ssyms) : ctx) (als, pre) =
    let slv = SolverUtils.mk_solver tm in
    let initial =
      SolverState.initialise slv srt syms
      |> SolverState.link_aliases slv srt als ssyms
      |> SolverState.add_preconditions tm slv srt pre
    in

    let rely =
      SolverSpec.translate_fn tm r |> SolverState.apply_pred tm slv srt
    in
    let assert_guar_over =
      SolverSpec.translate_cn tm g |> SolverState.assert_over tm slv srt
    in
    let i1 = SolverInst.translate tm i1 in
    let i2 = SolverInst.translate tm i2 in

    let _final =
      initial |> rely |> assert_guar_over i1 |> rely |> assert_guar_over i2
    in

    SolverUtils.trivial_sygus tm srt slv;
    let result = Solver.check_synth slv in
    SynthResult.has_solution result

  let solve_out_order tm srt (((i1, i2), (r, g), syms, ssyms) : ctx) (als, pre)
      =
    let slv = SolverUtils.mk_solver tm in
    let initial =
      SolverState.initialise slv srt syms
      |> SolverState.link_aliases slv srt als ssyms
      |> SolverState.add_preconditions tm slv srt pre
    in

    let exists1 = SolverState.reinitialise ~prime:"'" tm slv srt initial in
    let exists2 = SolverState.reinitialise ~prime:"\"" tm slv srt initial in

    let rely =
      SolverSpec.translate_fn tm r |> SolverState.apply_pred tm slv srt
    in
    let assert_guar_over =
      SolverSpec.translate_cn tm g |> SolverState.assert_over tm slv srt
    in
    let i1 = SolverInst.translate tm i1 in
    let i2 = SolverInst.translate tm i2 in

    let final =
      initial |> rely |> assert_guar_over i2 |> rely |> assert_guar_over i1
      |> rely
    in

    let just_execute = SolverState.apply_inst tm slv srt in

    initial |> rely |> SolverState.constrain_eq tm slv srt exists1;
    exists1 |> just_execute i1 |> rely
    |> SolverState.constrain_eq tm slv srt exists2;
    exists2 |> just_execute i2 |> rely
    |> SolverState.constrain_eq tm slv srt final;

    let result = Solver.check_synth slv in
    SynthResult.has_solution result

  let solve_pair tm srt (spec : sp) idx (pair : ip) : failure list =
    print_endline @@ Printf.sprintf "[!] Solving pair %i" (idx + 1);
    let inst_vars = Lifter.IR.pair_syms pair in
    let spec_vars = Spec.Analysis.spec_syms spec in
    let context = (pair, spec, inst_vars, spec_vars) in

    let aliases = SolverUtils.make_aliases inst_vars spec_vars in
    let preconditions = SolverSpec.generate_stage1_pres spec in
    (* TODO(nice; config): manual specification of combinations *)
    let combinations =
      SolverUtils.cross_product aliases preconditions
      |> SolverUtils.generate_stage2_pres inst_vars
    in
    (* TODO(nice): base output on --verbose flag *)
    print_endline
    @@ Printf.sprintf "    [!] Have %i possible pre-states"
    @@ List.length combinations;

    let valid_in_order =
      List.filter (solve_in_order tm srt context) combinations
    in
    print_endline
    @@ Printf.sprintf "    [!] Have %i valid pre-states"
    @@ List.length valid_in_order;

    if 0 == List.length valid_in_order then
      failwith "[ERROR] No pre-states are valid in-order. Check your spec!";

    let failing_out_order =
      List.filter
        (fun c -> solve_out_order tm srt context c |> not)
        valid_in_order
    in
    print_endline
    @@ Printf.sprintf "    [!] Have %i successful pre-states"
    @@ (List.length valid_in_order - List.length failing_out_order);

    List.map
      (fun (a, p) ->
        { i1 = fst pair; i2 = snd pair; aliasing = a; precondition = p })
      failing_out_order

  let solve_all ~verb ~mode (spec : sp) (pairs : ip list) : failure list =
    let tm = TermManager.mk_tm () in
    let srt = Sort.mk_int_sort tm in

    List.mapi (solve_pair tm srt spec) pairs |> List.flatten
end
