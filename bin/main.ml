open Ocaml_protoc_plugin
open Rif.IR.Gtirb.Proto
open Lifter
open Datalog

(* Argument parsing *)
let component = ref "main"
let verb = ref false
let input_gts = ref ""

let speclist =
  [
    ("--function", Arg.Set_string component, "the function to be RIF-checked");
    ("--verbose", Arg.Set verb, "verbose-mode output");
  ]

let usage = Printf.sprintf "Usage: %s [options] input.gts" Sys.argv.(0)
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
        (Printf.sprintf "Could not reply request: %s"
           (Ocaml_protoc_plugin.Result.show_error e))

(* MAIN *)
let () =
  Arg.parse speclist args usage;
  if !argc <> 1 then (
    output_string stderr usage;
    exit 1);

  let ir = read_gts !input_gts in
  let block_semantics = Lifter.parse ir !component !verb in

  Datalog.pairs;
  ignore block_semantics
