module DL = Datalog_caml_interface
open Lifter

type instruction = { identifier : int; semantics : string list }
type pairs = (instruction * instruction) list

let rules =
  "\n\
  \    execution_order(A,B) :- instruction_in_block(A,C), \
   instruction_in_block(C,D), block_order(C,D).\n\
  \    execution_order(A,B) :- instruction_order(A,B).\n\n\
  \    instruction_order(0,1).\n\
  \  "

let backend = DL.Logic.DB.create ()

let compute_reorderable_pairs (block_semantics : blockdata Blocks.t)
    (verb : bool) : pairs =
  if not (DL.Parse.load_string backend rules) then
    failwith "Internal error: failed to initialise datalog";

  ignore block_semantics;
  ignore verb;
  []
