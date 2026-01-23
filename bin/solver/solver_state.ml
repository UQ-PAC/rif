open Cvc5

open Solver_utils

module type SolverState = sig
  type state
  type state_function = state -> string -> Term.term option

  val initialise : Cvc5.Solver.solver -> Sort.sort -> string list -> state
  val link_aliases : (string * string) list -> state -> state
  val find_opt : state -> string -> Term.term option

  val apply :
    ?rely:bool ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state_function ->
    state ->
    state
  val assert' :
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state_function ->
    state ->
    state
end

module SolverState : SolverState = struct
  module S = Map.Make (String)

  type state = string S.t * Term.term S.t

  let find_opt (s : state) (k : string) : Term.term option =
    match S.find_opt k (fst s) with
    | Some alias -> S.find_opt alias (snd s)
    | None -> S.find_opt k (snd s)

  type state_function = state -> string -> Term.term option

  let initialise slv srt (names : string list) : state =
    ( S.empty,
      List.fold_left
        (fun acc n -> S.add n (Cvc5.Solver.declare_sygus_var slv n srt) acc)
        S.empty names )

  let link_aliases (pairs : (string * string) list) (state : state) =
    ( List.fold_left (fun acc (n1, n2) -> S.add n1 n2 acc) (fst state) pairs,
      snd state )

  let nondeterminism_counter = ref 0

  let fresh_nondeterminism slv srt =
    incr nondeterminism_counter;
    Cvc5.Solver.declare_sygus_var slv
      ("???_" ^ string_of_int !nondeterminism_counter)
      srt

  let apply ?(rely = false) slv srt (func : state_function) (state : state) =
    let map =
      S.mapi
        (fun (k : string) (v : Term.term) ->
          if (not rely) && String.starts_with ~prefix:"R" k then v
          else
            match func state k with
            | None -> fresh_nondeterminism slv srt
            | Some next -> next)
        (snd state)
    in
    (fst state, map)

  let assert' tm slv srt (func : state_function) (state : state) =
    let results =
      S.mapi (fun k _ ->
        match func state k with
        | None -> fresh_nondeterminism slv srt
        | Some value -> value
      ) (snd state)
    in
    List.iter (fun (k,v) ->
      Cvc5.Solver.assert_formula slv (find_opt state k |> Option.get |> SolverUtils.term_eq tm v);
    ) (S.bindings results);
    state
end
