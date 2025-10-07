open Ocaml_protoc_plugin
open Rif.IR.Gtirb.Proto
open Lifter
open Datalog
open Solver
open Rgspec
open Util

(* Argument parsing *)
let component = ref "main"
let style = ref "integers"
let verb = ref false
let input_gtirb = ref ""
let rely = ref "true"
let guar = ref "true"

let speclist =
  [
    ("--function", Arg.Set_string component, "the function to be RIF-checked");
    ( "--solver-type",
      Arg.Set_string style,
      "the primary 'sort' to be used by the cvc5 solver" );
    ( "--rely",
      Arg.Set_string rely,
      "the rely-condition describing all other concurrent components" );
    ( "--guar",
      Arg.Set_string guar,
      "the guarantee(s) this component must uphold" );
    ("--verbose", Arg.Set verb, "verbose-mode output");
  ]

let usage = Printf.sprintf "Usage: %s [options] input.gtirb\n" Sys.argv.(0)
let argc = ref 0

let args arg =
  argc := 1 + !argc;
  match !argc with 1 -> input_gtirb := arg | _ -> ()

let cvcstyle : Solver.style =
  match !style with
  | "integers" -> Solver.Integers
  | "bitvectors" -> Solver.BitVectors
  | _ -> failwith "Bad solver type :("

(* From UQ-PAC/gtirb_semantics *)
let read_gtirb filename =
  let bytes_in =
    let gtirb = open_in_bin filename in
    let len = in_channel_length gtirb in
    let magic = really_input_string gtirb 8 in
    let rest = really_input_string gtirb (len - 8) in
    let res =
      if String.starts_with ~prefix:"GTIRB" magic then rest else magic ^ rest
    in
    close_in gtirb;
    res
  in
  let gtirb = IR.from_proto (Reader.create bytes_in) in
  match gtirb with
  | Ok a -> a
  | Error e ->
      failwith
        (Printf.sprintf "Bad IR: could not reply request: %s"
           (Ocaml_protoc_plugin.Result.show_error e))

(* MAIN *)
let () =
  (* Memtrace.trace_if_requested ~context:"UQ-PAC/rif" (); *)
  Arg.parse speclist args usage;
  if !argc <> 1 then (
    output_string stderr usage;
    exit 1);

  let ir = read_gtirb !input_gtirb in
  let (all_block_semantics : Lifter.blockdata Lifter.Blocks.t) =
    Lifter.parse ir !component !verb
  in

  let specification = RGSpec.input !rely !guar in

  let bcount = Lifter.Blocks.cardinal all_block_semantics in
  let icount =
    Lifter.Blocks.fold
      (fun _ (b : Lifter.blockdata) s -> s + List.length b.block_semantics)
      all_block_semantics 0
  in
  print_endline
    (Printf.sprintf
       "[!] Extracted %i basic block%s (%i instructions) from '%s()'..." bcount
       (if bcount == 1 then "" else "s")
       icount !component);

  let reorderable_pairs =
    Datalog.compute_reorderable_pairs all_block_semantics !verb
  in

  let get_actual_instructions (r : (int * int) list * (bytes * int) list) :
      ((bytes * int) * (bytes * int)) list =
    let pairs, map = r in
    let find ins =
      match List.find (fun (_, i) -> i == ins) map with b, _ -> b
    in
    let unaddress (uuid, ins) =
      ( uuid,
        (ins - (Lifter.Blocks.find uuid all_block_semantics).offset)
        / Lifter.opcode_length )
    in

    List.map
      (fun (i1, i2) -> (unaddress (find i1, i1), unaddress (find i2, i2)))
      pairs
  in

  let identifiable = get_actual_instructions reorderable_pairs in
  if !verb then
    List.iter
      (fun ((b1, i1), (b2, i2)) ->
        print_endline
          (Printf.sprintf "    [!] Could reorder %s.%i <-> %s.%i" (b64_bytes b1)
             i1 (b64_bytes b2) i2))
      identifiable;

  let failed =
    List.filteri
      (Solver.solve ~verb:!verb all_block_semantics cvcstyle specification)
      identifiable
  in

  if List.length failed == 0 then
    print_endline
      "[!] SUCCESS: All reorderable instructions will uphold the R/G spec."
  else
    print_endline
      "[!] FAILED: At least one reorderable pair did not uphold the R/G spec."
