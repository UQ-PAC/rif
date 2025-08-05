(*
  Map from block UUIDs to blocks. Represents a CFG.
*)
module Blocks : Map.S with type key = bytes

(*
  Edges we care about are
  - linear (instruction -> instruction)
  - call (instruction -> instruction, but with a call acting as a guard and preventing reordering)
  - entry (edge from nowhere into the function, marking the entrypoint)
*)
type edgetype = Linear | Call | Entry

(*
  An outgoing CFG edge from this block to another block UUID, of a particular type
*)
type outgoing_edge = bytes * edgetype

(*
  The semantics provided for an instruction -- a list of ASL statements.
*)
type instruction_semantics = string list

(*
  Every block in the function is a blockdata, with
  - outgoing edges to other blocks
  - a list of instructions (with their semantics)
  - and an offset (inside the parent ByteInterval) that this block lives at (to calculate instruction addresses)
*)
type blockdata = {
  outgoing_edges : outgoing_edge list;
  block_semantics : instruction_semantics list;
  offset : int;
}

(*
  Takes a protobuf from the protoc plugin, a function name, and a boolean (verbosity).
  Generates a big map containing all blocks (identified by UUID) and containing all block data as described.
*)
val parse : Rif.IR.Gtirb.Proto.IR.t -> string -> bool -> blockdata Blocks.t
