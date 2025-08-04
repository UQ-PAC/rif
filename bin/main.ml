open Ocaml_protoc_plugin
open Rif.IR.Gtirb.Proto
open Lifter

(* Argument parsing *)
let component = ref "main"
let input_gts = ref ""

let speclist =
  [ ("--function", Arg.Set_string component, "the function to be RIF-checked") ]

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
  let cfg, symbols, blocks, aux = Lifter.parse ir in
  print_endline
    (Printf.sprintf "[!] Successfully read %s intermediate representation..."
       !input_gts);

  let symbol = Lifter.symbol_by_name symbols !component in
  let uuid = Lifter.expect_referent_uuid symbol in
  print_endline
    (Printf.sprintf "[!] Located the entry-point block of function %s..."
       !component);

  let code =
    [ Lifter.codeblock_by_uuid blocks uuid ]
    @ Lifter.all_func_codeblocks blocks cfg uuid
  in
  let code_uuids = List.map (fun (c : Lifter.p_code) -> c.uuid) code in
  print_endline
    (Printf.sprintf "[!] Found %i codeblock%s associated with function..."
       (List.length code)
       (if List.length code == 1 then "" else "s"));

  let json_semantics = Lifter.parse_semantics aux in
  let block_semantics = Lifter.find_for_blocks code_uuids json_semantics in
  let instruction_count =
    Lifter.SemanticsMap.fold (fun _ l c -> c + List.length l) block_semantics 0
  in
  print_endline
    (Printf.sprintf "[!] Found semantic information for %i instructions..."
       instruction_count);

  

  ignore block_semantics
