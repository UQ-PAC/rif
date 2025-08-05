module DL = Datalog_caml_interface
open Lifter

module Datalog = struct
  type instruction = { identifier : int; semantics : string list }
  type pairs = (instruction * instruction) list

  let backend = DL.Logic.DB.create

  let compute_reorderable_pairs
      (block_semantics : Lifter.blockdata Lifter.Blocks.t) (verb : bool) : pairs
      =
    ignore block_semantics;
    ignore verb;
    []
end
