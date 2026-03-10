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
let concurrency = ref "safe"

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
(* TODO(nice): some sort of config-file argument instead of parameters *)

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

  if List.length failed == 0 then
    print_endline
      "[!] SUCCESS: All reorderable instructions will uphold the R/G spec."
  else
    print_endline
      "[!] FAILED: At least one reorderable pair did not uphold the R/G spec.";

  let generalise_failure others (f : Solver.failure) =
    let identical_except_for (f1 : Solver.failure) (f2 : Solver.failure)
        (pred, input) =
      Lifter.IR.instruction_eq f1.i1 f2.i1
      && Lifter.IR.instruction_eq f2.i2 f2.i2
      && List.equal
           (fun (a, b) (c, d) -> String.equal a c && String.equal b d)
           f1.aliasing f2.aliasing
      &&
      let f1pre =
        List.find_opt
          (fun (a, b, _) -> String.equal a pred && String.equal b input)
          f1.precondition
      in
      let f2pre =
        List.find_opt
          (fun (a, b, _) -> String.equal a pred && String.equal b input)
          f2.precondition
      in
      match (f1pre, f2pre) with
      | Some (_, _, false), Some (_, _, true) -> true
      | Some (_, _, true), Some (_, _, false) -> true
      | _ -> false
    in

    let distinct_pres =
      List.filter
        (fun (p, i, _) ->
          not @@ List.exists (fun o -> identical_except_for f o (p, i)) others)
        f.precondition
    in
    { f with precondition = distinct_pres }
  in

  let rec uniq_failures = function
    | [] -> []
    | x :: xs ->
        if List.exists (Solver.failure_eq x) xs then uniq_failures xs
        else x :: uniq_failures xs
  in

  List.map (generalise_failure failed) failed
  |> uniq_failures
  |> List.iteri (fun idx (f : Solver.failure) ->
      print_endline
      @@ Printf.sprintf
           "    [!] Failure %i:\n\
           \      Instruction [%x: %s] reordering with [%x: %s], when:"
           (idx + 1) f.i1.index f.i1.readable f.i2.index f.i2.readable;
      List.iter
        (fun (a, b) ->
          print_endline @@ Printf.sprintf "      %s refers to %s" b a)
        f.aliasing;
      List.iter
        (fun (a, b, c) ->
          print_endline @@ Printf.sprintf "      %s(%s) is %B" a b c)
        f.precondition;

      print_endline "")
