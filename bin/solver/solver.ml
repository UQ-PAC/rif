open Cvc5
open Lifter
open Spec
open Solver_utils
open Solver_state
open Solver_instruction
open Solver_spec

module Solver = struct
  let solve tm (i1, i2) (r, g) =
    let i1 = SolverInst.translate tm i1 in
    let i2 = SolverInst.translate tm i2 in
    let r = SolverSpec.translate tm r in
    let g = SolverSpec.translate tm g in

    ignore (i1, i2, r, g);
    true
end
