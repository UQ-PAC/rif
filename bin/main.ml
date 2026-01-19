open Lifter
open Datalog
open Solver
open Rgspec

(* Argument parsing *)
let component = ref "main"
let verb = ref false
let input_gtirb = ref ""
let rely = ref "true"
let guar = ref "true"

let concurrency = ref "easy"

let speclist =
  [
    ("--function", Arg.Set_string component, "the function to be RIF-checked");
    ( "--rely",
      Arg.Set_string rely,
      "the rely-condition describing all other concurrent components" );
    ( "--guar",
      Arg.Set_string guar,
      "the guarantee(s) this component must uphold" );
    ("--verbose", Arg.Set verb, "verbose-mode output");
    ("--concurrency", Arg.Set_string concurrency, "concurrency mode (safe / easy)");
  ]

let usage = Printf.sprintf "Usage: %s [options] input.gtirb\n" Sys.argv.(0)
let argc = ref 0

let args arg =
  argc := 1 + !argc;
  match !argc with 1 -> input_gtirb := arg | _ -> ()

(* From UQ-PAC/gtirb_semantics *)
(* MAIN *)
let () =
  (* Memtrace.trace_if_requested ~context:"UQ-PAC/rif" (); *)
  Arg.parse speclist args usage;
  if !argc <> 1 then (
    output_string stderr usage;
    exit 1);

  let mode = if String.equal !concurrency "safe" then
    Solver.Safe else
    Solver.Easy in

  (match mode with
  | Solver.Easy -> print_endline
      ("[!] Executing in easy-concurrency mode. This mode makes strong " ^
      "assumptions about memory that isn't covered by the specification. Be careful!\n")
  | Solver.Safe -> print_endline
      ("[!] Executing in safe-concurrency mode. This mode makes no assumptions " ^
      "about unspecified memory; you will have to write much larger specifications.\n"));

  let ir = read_gtirb !input_gtirb in
  let (lifter_result : Lifter.blockdata Lifter.Blocks.t) =
    Lifter.parse ir !component !verb
  in

  let specification = RGSpec.input !rely !guar in

  let bcount = Lifter.Blocks.cardinal lifter_result in
  let icount =
    Lifter.Blocks.fold
      (fun _ (b : Lifter.blockdata) s ->
        s + (Lifter.Instructions.bindings b.instructions |> List.length))
      lifter_result 0
  in
  print_endline
    (Printf.sprintf
       "[!] Extracted %i basic block%s (%i instructions) from '%s()'..." bcount
       (if bcount == 1 then "" else "s")
       icount !component);

  let pair_result = Datalog.compute_reorderable_pairs lifter_result !verb in

  let reorderable_pairs =
    List.map
      (fun ((i1b, i1i), (i2b, i2i)) ->
        let b1 = Lifter.Blocks.find i1b lifter_result in
        let b2 = Lifter.Blocks.find i2b lifter_result in

        if !verb then
          print_endline
            (Printf.sprintf "    [!] Could reorder %s.%i <-> %s.%i" b1.name i1i
               b2.name i2i);

        ( Lifter.Instructions.find i1i b1.instructions,
          Lifter.Instructions.find i2i b2.instructions ))
      pair_result
  in

  let failed = Solver.solve_all ~verb:!verb ~mode:mode reorderable_pairs specification in

  if List.length failed != 0 then
    print_endline
      "[!] SUCCESS: All reorderable instructions will uphold the R/G spec."
  else
    print_endline
      "[!] FAILED: At least one reorderable pair did not uphold the R/G spec."
