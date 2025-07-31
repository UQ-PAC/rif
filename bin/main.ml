open Ocaml_protoc_plugin
open Rif.IR.Gtirb.Proto

let component = ref ""
let input_gts = ref ""
let input_relf = ref ""
let speclist = [( "--function", Arg.Set_string component, "the function to be RIF-checked")]
let usage = Printf.sprintf "Usage: %s [options] input.gts input.relf" Sys.argv.(0)

let argc = ref 0
let args arg =
  argc := 1 + !argc;
  match !argc with
  | 1 -> input_gts := arg
  | 2 -> input_relf := arg
  | _ -> ()


let read_ir filename =
  let bytes =
    let gts = open_in_bin filename in
    let len = in_channel_length gts in
    let magic = really_input_string gts 8 in
    let rest = really_input_string gts (len - 8) in
    let res = if String.starts_with ~prefix:"GTIRB" magic then rest else magic ^ rest in
    close_in gts;
    res
  in

  let gtirb = IR.from_proto (Reader.create bytes) in

  let ir =
    match gtirb with
    | Ok a -> a
    | Error e -> failwith (Printf.sprintf "%s%s" "Could not reply request: "
                           (Ocaml_protoc_plugin.Result.show_error e))
  in
  ir

(* MAIN *)
let () =
  Arg.parse speclist args usage;
  if !argc <> 2 then (output_string stderr usage; exit 1);

  let ir = read_ir !input_gts in ()
