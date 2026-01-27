open Cvc5
open Lifter
open Spec
open Solver_utils
open Solver_state
open Solver_instruction
open Solver_spec

module type Solver = sig
  module Utils : SolverUtils

  val solve_all :
    verb:bool ->
    mode:Utils.mode ->
    Spec.Lang.spec * Spec.Lang.spec ->
    (Lifter.IR.instruction * Lifter.IR.instruction) list ->
    (Lifter.IR.instruction * Lifter.IR.instruction) list
end

module Solver : Solver = struct
  module Utils = SolverUtils

  type sp = Spec.Lang.spec * Spec.Lang.spec
  type ip = Lifter.IR.instruction * Lifter.IR.instruction

  let solve_in_order tm srt (i1, i2) (r, g) =
    let slv = SolverUtils.mk_solver tm in

    let rely =
      SolverSpec.translate tm r |> SolverState.apply ~rely:true slv srt
    in
    let guar =
      SolverSpec.translate tm g |> SolverState.assert_over tm slv srt
    in
    let i1 = SolverInst.translate tm i1 in
    let i2 = SolverInst.translate tm i2 in

    ignore
      (SolverState.initialise slv srt [] |> rely |> guar i1 |> rely |> guar i2);

    SolverUtils.trivial_sygus tm srt slv;
    let result = Solver.check_synth slv in
    SynthResult.has_solution result

  let solve_out_order tm srt (i1, i2) (r, g) =
    let slv = SolverUtils.mk_solver tm in

    let rely =
      SolverSpec.translate tm r |> SolverState.apply ~rely:true slv srt
    in
    let guar =
      SolverSpec.translate tm g |> SolverState.assert_over tm slv srt
    in
    let i1 = SolverInst.translate tm i1 in
    let i2 = SolverInst.translate tm i2 in

    let initial_state = SolverState.initialise slv srt [] in

    let final_state =
      rely initial_state |> guar i2 |> rely |> guar i1 |> rely
    in

    ignore (final_state, g);
    true

  let solve_pair tm srt (spec : sp) (pair : ip) =
    let inst_vars = Lifter.IR.pair_syms pair in
    let spec_vars = Spec.Analysis.spec_syms spec in

    let aliases = [] in
    let preconditions = [] in

    solve_in_order tm srt pair spec

  let solve_all ~verb ~mode (spec : sp) (pairs : ip list) : ip list =
    let tm = TermManager.mk_tm () in
    let srt = Sort.mk_int_sort tm in

    List.filter (solve_pair tm srt spec) pairs
end
