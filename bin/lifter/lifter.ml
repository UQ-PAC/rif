open Rif

open Lifter_ir
open Lifter_elf
open Lifter_disassembly

(****************************************************************************************
  Wrapper around GTIRB serialised data, ASLp parsing, etc. Basically all the binary stuff.
*)
module type Lifter = sig
  module Blocks : Map.S with type key = string
  module Instructions : Map.S with type key = int

  val parse : string -> string -> bool -> IR.blocks
end

module Lifter : Lifter = struct
  module IR = LifterIR
  module Disasm = LifterDisassembly
  module Elf = LifterElf

  let parse (filename : string) (component : string) (verb : bool) =
    print_endline "[!] Parsing GTIRB IR...";

    let relevant_binary = Elf.parse filename component verb in
    Disasm.lift relevant_binary
end
