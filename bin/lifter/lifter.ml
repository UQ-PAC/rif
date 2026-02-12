open Rif
open Lifter_ir
open Lifter_elf
open Lifter_disassembly

(****************************************************************************************
  Wrapper around GTIRB serialised data, ASLp parsing, etc. Basically all the binary stuff.
*)
module type Lifter = sig
  module IR : LifterIR

  val parse : string -> string -> bool -> IR.blocks

  val resolve_ids :
    IR.blocks ->
    bool ->
    ((string * int) * (string * int)) list ->
    (IR.instruction * IR.instruction) list
end

module Lifter : Lifter = struct
  module IR = LifterIR
  module Disasm = LifterDisassembly
  module Elf = LifterElf

  let parse (filename : string) (component : string) (verb : bool) =
    print_endline "[!] Parsing GTIRB IR...";

    let result =
      Elf.parse filename component verb
      |> Option.get_or "Unknown failure parsing elf"
      |> Disasm.lift_all verb
    in

    let bcount = IR.B.cardinal result in
    let icount =
      IR.B.fold
        (fun _ (b : IR.block) s ->
          s + (IR.I.bindings b.instructions |> List.length))
        result 0
    in

    print_endline
      (Printf.sprintf
         "[!] Extracted %i basic block%s (%i instructions) from '%s()'..."
         bcount
         (if bcount == 1 then "" else "s")
         icount component);

    result

  let resolve_ids (blocks : IR.blocks) verb =
    List.map (fun ((i1b, i1i), (i2b, i2i)) ->
        let b1 = IR.B.find i1b blocks in
        let b2 = IR.B.find i2b blocks in

        if verb then
          print_endline
            (Printf.sprintf "    [!] Could reorder instructions %x <-> %x" i1i i2i);

        (IR.I.find i1i b1.instructions, IR.I.find i2i b2.instructions))
end
