open Cvc5
open Solver_utils

module type SolverState = sig
  type state
  type state_function = state -> string -> Term.term option
  type state_constraints = state -> state -> Term.term list

  type spec_predicates

  val initialise : Cvc5.Solver.solver -> Sort.sort -> string list -> state

  val reinitialise :
    prime:string ->
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state ->
    state

  val link_aliases :
    Cvc5.Solver.solver ->
    Sort.sort ->
    (string * string) list ->
    string list ->
    state ->
    state

  val find_opt : state -> string -> Term.term option
  val find_predicate : spec_predicates -> string -> Term.term
  val dump : state -> unit

  val apply_preconditions :
    TermManager.tm -> Cvc5.Solver.solver -> Sort.sort -> state -> (string * string * bool) list -> spec_predicates

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
    state_constraints ->
    state_function ->
    state ->
    state
end

module SolverState : SolverState = struct
  module S = Map.Make (String)

  let nondeterminism_counter = ref 0

  let fresh_nondeterminism slv srt =
    incr nondeterminism_counter;
    Cvc5.Solver.declare_sygus_var slv
      ("???_" ^ string_of_int !nondeterminism_counter)
      srt

  type state = string S.t * Term.term S.t
  type spec_predicates = Term.term S.t

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

  let find_predicate p n = S.find n p

  type state_function = state -> string -> Term.term option
  type state_constraints = state -> state -> Term.term list

  let initialise slv srt (names : string list) : state =
    List.iter SolverUtils.Printing.pp_newterm names;
    ( S.empty,
      List.fold_left
        (fun acc n -> S.add n (Cvc5.Solver.declare_sygus_var slv n srt) acc)
        S.empty names )

  let reinitialise ~prime tm slv srt state : state =
    let names = snd state |> S.bindings |> List.map fst in

    let values = snd state |> S.bindings |> List.map snd in
    let var_inputs = List.map (Term.mk_var_s tm srt) names |> Array.of_list in

    let funcs =
      List.map
        (fun n ->
          (n, Cvc5.Solver.synth_fun slv tm ("f_" ^ n) var_inputs srt None))
        names
    in
    List.iter (fun a -> snd a |> SolverUtils.Printing.pp_func) funcs;

    let ufs =
      List.fold_left
        (fun acc (k, v) ->
          S.add k
            (Term.mk_term tm Kind.Apply_uf (Array.of_list (v :: values)))
            acc)
        S.empty funcs
    in

    (fst state, ufs)

  let link_aliases slv srt (pairs : (string * string) list)
      (ssyms : string list) (state : state) =
    let aliasing =
      List.fold_left (fun acc (n1, n2) -> S.add n1 n2 acc) (fst state) pairs
    in

    let bound = List.map fst @@ S.bindings aliasing in
    let unbound =
      List.filter (fun n -> not @@ List.exists (String.equal n) bound) ssyms
    in

    ( aliasing,
      List.fold_left
        (fun acc name -> S.add name (fresh_nondeterminism slv srt) acc)
        (snd state) unbound )

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

  let constrain_eq tm slv srt (s1 : state) (s2 : state) =
    let s1_contents = snd s1 |> S.bindings in

    let print = SolverUtils.Printing.pp_constrain ~human:true in

    List.iter
      (fun (k, v) ->
        find_opt s2 k |> Option.get |> SolverUtils.term_eq tm v |> fun t ->
        ignore @@ print t;
        Cvc5.Solver.add_sygus_constraint slv t)
      s1_contents

  let assert_over tm slv srt (pred : state_constraints) (func : state_function)
      (state : state) =
    let result = apply_inst slv srt func state in

    List.iter (Cvc5.Solver.add_sygus_constraint slv) (pred state result);

    (fst state, snd result)

  let apply_preconditions tm slv srt state (conds : (string * string * bool) list) =
    let pred_sort = Sort.mk_pred_sort tm (Array.of_list [srt]) in

    let preds = List.fold_left (fun acc (n,_,_) -> S.add n (Term.mk_const_s tm pred_sort n) acc) S.empty conds in

    let applies = List.map (fun (name, input, value) ->
      let pred = S.find name preds in
      let input = find_opt state input |> Option.get in
      let applied = Term.mk_term tm Kind.Apply_uf (Array.of_list [pred; input]) in
      match value with
      | false -> Term.mk_term tm Kind.Not (Array.of_list [applied])
      | _ -> applied
    ) conds in

    List.iter (Cvc5.Solver.add_sygus_assume slv) applies;
    preds
end
