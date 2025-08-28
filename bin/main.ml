open Ocaml_protoc_plugin
open Rif.IR.Gtirb.Proto
open Lifter
open Datalog
open Util
open Solver

(* Argument parsing *)
let component = ref "main"
let verb = ref false
let input_gts = ref ""

let speclist =
  [
    ("--function", Arg.Set_string component, "the function to be RIF-checked");
    ("--verbose", Arg.Set verb, "verbose-mode output");
  ]

let usage = Printf.sprintf "Usage: %s [options] input.gts\n" Sys.argv.(0)
let argc = ref 0

let args arg =
  argc := 1 + !argc;
  match !argc with 1 -> input_gts := arg | _ -> ()

(* From UQ-PAC/gtirb_semantics *)
let read_gts filename =
  let bytes_in =
    let gts = open_in_bin filename in
    let len = in_channel_length gts in
    let magic = really_input_string gts 8 in
    let rest = really_input_string gts (len - 8) in
    let res =
      if String.starts_with ~prefix:"GTIRB" magic then rest else magic ^ rest
    in
    close_in gts;
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

  let ir = read_gts !input_gts in
  let (all_block_semantics : Lifter.blockdata Lifter.Blocks.t) =
    Lifter.parse ir !component !verb
  in

  let count = Lifter.Blocks.cardinal all_block_semantics in
  print_endline
    (Printf.sprintf
       "[!] Extracted %i basic block%s (%i instructions) from %s..." count
       (if count == 1 then "" else "s")
       1 !component);

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
          (Printf.sprintf "    Could reorder %s.%i <-> %s.%i" (b64_bytes b1) i1
             (b64_bytes b2) i2))
      identifiable;

  ignore (List.map (Solver.solve all_block_semantics) identifiable)
