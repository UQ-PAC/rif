open Lifter
open Datalog
open Solver
open Spec

(* Argument parsing *)
let component = ref "main"
let verb = ref false
let input_gtirb = ref ""
let rely = ref ""
let guar = ref ""
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
    ( "--concurrency",
      Arg.Set_string concurrency,
      "concurrency mode (safe / easy)" );
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

  let mode =
    if String.equal !concurrency "safe" then Solver.Utils.Safe
    else Solver.Utils.Easy
  in

  (match mode with
  | Solver.Utils.Easy ->
      print_endline
        ("[!] Executing in easy-concurrency mode. This mode makes strong "
       ^ "assumptions about memory that isn't covered by the specification. Be \
          careful!\n")
  | Solver.Utils.Safe ->
      print_endline
        ("[!] Executing in safe-concurrency mode. This mode makes no \
          assumptions "
       ^ "about unspecified memory; you will have to write much larger \
          specifications.\n"));

  let basic_blocks = Lifter.parse !input_gtirb !component !verb in

  let specification = Spec.input !rely !guar in

  let pair_ids = Datalog.compute_reorderable_pairs basic_blocks !verb in

  let reorderable_pairs = Lifter.resolve_ids basic_blocks !verb pair_ids in

  let failed =
    Solver.solve_all ~verb:!verb ~mode specification reorderable_pairs
  in

  if List.length failed != 0 then
    print_endline
      "[!] SUCCESS: All reorderable instructions will uphold the R/G spec."
  else
    print_endline
      "[!] FAILED: At least one reorderable pair did not uphold the R/G spec."
