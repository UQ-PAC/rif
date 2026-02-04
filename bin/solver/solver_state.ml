open Cvc5
open Solver_utils

module type SolverState = sig
  type state
  type state_function = state -> string -> Term.term option

  val initialise : Cvc5.Solver.solver -> Sort.sort -> string list -> state

  val reinitialise :
    prime:string ->
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state ->
    state

  val link_aliases : (string * string) list -> state -> state
  val find_opt : state -> string -> Term.term option
  val dump : state -> unit

  val apply_pred :
    Cvc5.Solver.solver -> Sort.sort -> state_function -> state -> state

  val apply_inst :
    Cvc5.Solver.solver -> Sort.sort -> state_function -> state -> state

  val constrain_eq :
    TermManager.tm -> Cvc5.Solver.solver -> Sort.sort -> state -> state -> unit

  val assert_over :
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state_function ->
    state_function ->
    state ->
    state
end

module SolverState : SolverState = struct
  module S = Map.Make (String)

  type state = string S.t * Term.term S.t

  let dump (s : state) : unit =
    List.iter (fun (k, v) ->
        print_endline k;
        print_endline v)
    @@ S.bindings @@ fst s;

    fst s |> S.bindings
    |> List.map (fun (k, v) ->
           snd s |> S.find v |> Term.to_string
           |> Printf.sprintf "%s -> %s -> %s" k v)
    |> List.iter print_endline;

    snd s |> S.bindings
    |> List.map (fun (k, v) -> Term.to_string v |> Printf.sprintf "%s -> %s" k)
    |> List.iter print_endline

  let find_opt (s : state) (k : string) : Term.term option =
    match S.find_opt k (fst s) with
    | Some alias -> S.find_opt alias (snd s)
    | None -> S.find_opt k (snd s)

  type state_function = state -> string -> Term.term option

  let initialise slv srt (names : string list) : state =
    List.iter SolverUtils.Printing.pp_newterm names;
    ( S.empty,
      List.fold_left
        (fun acc n -> S.add n (Cvc5.Solver.declare_sygus_var slv n srt) acc)
        S.empty names )

  let reinitialise ~prime tm slv srt state : state =
    let names = snd state |> S.bindings |> List.map fst in

    let values = snd state |> S.bindings |> List.map snd |> Array.of_list in
    let var_inputs = List.map (Term.mk_var_s tm srt) names |> Array.of_list in

    let funcs =
      List.map
        (fun n -> (n, Cvc5.Solver.synth_fun slv tm n var_inputs srt None))
        names
    in

    let ufs =
      List.fold_left
        (fun acc (k, v) -> S.add k (Term.mk_term tm Kind.Apply_uf values) acc)
        S.empty funcs
    in

    (fst state, ufs)

  let link_aliases (pairs : (string * string) list) (state : state) =
    ( List.fold_left (fun acc (n1, n2) -> S.add n1 n2 acc) (fst state) pairs,
      snd state )

  let nondeterminism_counter = ref 0

  let fresh_nondeterminism slv srt =
    incr nondeterminism_counter;
    Cvc5.Solver.declare_sygus_var slv
      ("???_" ^ string_of_int !nondeterminism_counter)
      srt

  let apply_pred slv srt (func : state_function) (state : state) =
    let promote = function
      | None -> fresh_nondeterminism slv srt
      | Some v -> v
    in

    let updated =
      S.fold (fun k v acc -> (v, func state k) :: acc) (fst state) []
    in

    let map =
      List.fold_left
        (fun acc (k, v) -> S.add k (promote v) acc)
        (snd state) updated
    in

    (fst state, map)

  let apply_inst slv srt (func : state_function) (state : state) =
    let map = snd state |> S.mapi (fun k v -> func state k |> Option.get) in
    (fst state, map)

  type bhv = Constrain | Assert

  let eq_underlying ~bhv tm slv srt (s1 : state) (s2 : state) =
    let s1_contents = snd s1 |> S.bindings in

    let solver_function =
      match bhv with
      | Constrain -> Cvc5.Solver.add_sygus_constraint
      | Assert ->
          Cvc5.Solver.add_sygus_constraint (* Cvc5.Solver.assert_formula *)
    in
    let print =
      match bhv with
      | Constrain -> SolverUtils.Printing.pp_constrain ~human:true
      | Assert -> SolverUtils.Printing.pp_constrain ~human:true
    in

    List.iter
      (fun (k, v) ->
        find_opt s2 k |> Option.get |> SolverUtils.term_eq tm v |> fun t ->
        ignore @@ print t;
        solver_function slv t)
      s1_contents

  let constrain_eq = eq_underlying ~bhv:Constrain

  let assert_over tm slv srt (pred : state_function) (func : state_function)
      (state : state) =
    let results = apply_inst slv srt func state in
    let expected = apply_pred slv srt pred state in

    eq_underlying ~bhv:Assert tm slv srt results expected;

    (fst state, snd results)
end
