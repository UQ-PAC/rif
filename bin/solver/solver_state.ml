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

  let verbose = false

  let nondeterminism_counter = ref 0

  let fresh_nondeterminism slv srt =
    incr nondeterminism_counter;
    Cvc5.Solver.declare_sygus_var slv
      ("???_" ^ string_of_int !nondeterminism_counter)
      srt

          (* 'x' -> 'mr0' / 'mr0' -> term /  *)
  type state = {
    aliasing : string S.t;
    terms : Term.term S.t;
    predicates : (Term.term S.t) S.t;
  }

  let empty_state = {
    aliasing = S.empty;
    terms = S.empty;
    predicates = S.empty;
  }

  type spec_predicates = Term.term S.t

  let dump (s : state) : unit =
    List.iter (fun (k, v) ->
        print_endline k;
        print_endline v)
    @@ S.bindings @@ s.aliasing;

    s.aliasing |> S.bindings
    |> List.map (fun (k, v) ->
           s.terms |> S.find v |> Term.to_string
           |> Printf.sprintf "%s -> %s -> %s" k v)
    |> List.iter print_endline;

    s.terms |> S.bindings
    |> List.map (fun (k, v) -> Term.to_string v |> Printf.sprintf "%s -> %s" k)
    |> List.iter print_endline

  let find_opt (s : state) (k : string) : Term.term option =
    match S.find_opt k (s.aliasing) with
    | Some alias -> S.find_opt alias (s.terms)
    | None -> S.find_opt k (s.terms)

  let apply_predicate (s : state) (pred : string) (name : string) : Term.term option =
    match S.find_opt pred s.predicates with
    | Some map -> S.find_opt name map
    | None -> None

  let find_predicate p n = S.find n p

  type state_function = state -> string -> Term.term option
  type state_constraints = state -> state -> Term.term list

  let initialise slv srt (names : string list) : state =
    if verbose then List.iter SolverUtils.Printing.pp_newterm names;
    { empty_state with terms = List.fold_left
        (fun acc n -> S.add n (Cvc5.Solver.declare_sygus_var slv n srt) acc)
        S.empty names }

  let reinitialise ~prime tm slv srt (s : state) : state =
    let names = s.terms |> S.bindings |> List.map fst in
    let values = s.terms |> S.bindings |> List.map snd in

    let var_inputs = List.map (Term.mk_var_s tm srt) names |> Array.of_list in

    let funcs =
      List.map
        (fun n ->
          (n, Cvc5.Solver.synth_fun slv tm ("f_" ^ n) var_inputs srt None))
        names
    in
    if verbose then List.iter (fun a -> snd a |> SolverUtils.Printing.pp_func) funcs;

    let ufs =
      List.fold_left
        (fun acc (k, v) ->
          S.add k
            (Term.mk_term tm Kind.Apply_uf (Array.of_list (v :: values)))
            acc)
        S.empty funcs
    in

    { s with terms = ufs }

  let link_aliases slv srt (pairs : (string * string) list)
      (ssyms : string list) (s : state) : state =
    let aliasing =
      List.fold_left (fun acc (n1, n2) -> S.add n1 n2 acc) (s.aliasing) pairs
    in

    let bound = List.map fst @@ S.bindings aliasing in
    let unbound =
      List.filter (fun n -> not @@ List.exists (String.equal n) bound) ssyms
    in

    { s with aliasing = aliasing;
      terms = List.fold_left
        (fun acc name -> S.add name (fresh_nondeterminism slv srt) acc)
        (s.terms) unbound;
    }

  let apply_pred slv srt (func : state_function) (s : state) : state =
    let promote = function
      | None -> fresh_nondeterminism slv srt
      | Some v -> v
    in

    let updated =
      S.fold (fun k v acc -> (v, func s k) :: acc) (s.aliasing) []
    in

    let map =
      List.fold_left
        (fun acc (k, v) -> S.add k (promote v) acc)
        (s.terms) updated
    in

    { s with terms = map }

  let apply_inst slv srt (func : state_function) (s : state) : state =
    let map = s.terms |> S.mapi (fun k v -> func s k |> Option.get_or "Instruction references undefined variable?") in
    { s with terms = map }

  let constrain_eq tm slv srt (s1 : state) (s2 : state) =
    let s1_contents = s1.terms |> S.bindings in

    if verbose then let print = SolverUtils.Printing.pp_constrain ~human:true in

    List.iter
      (fun (k, v) ->
        find_opt s2 k |> Option.get_or (Printf.sprintf "%s not bound in second-state" k) |> SolverUtils.term_eq tm v |> fun t ->
        ignore @@ print t;
        Cvc5.Solver.add_sygus_constraint slv t)
      s1_contents

  let assert_over tm slv srt (pred : state_constraints) (func : state_function)
      (s : state) : state =
    let result = apply_inst slv srt func s in

    List.iter (Cvc5.Solver.add_sygus_constraint slv) (pred s result);

    { s with terms = result.terms }

  let apply_preconditions tm slv srt (s : state) (conds : (string * string * bool) list) =
    let pred_sort = Sort.mk_pred_sort tm (Array.of_list [srt]) in

    let preds = List.fold_left (fun acc (n,_,_) -> S.add n (Term.mk_const_s tm pred_sort n) acc) S.empty conds in

    let applies = List.map (fun (name, input, value) ->
      let pred = S.find name preds in
      let input = find_opt s input |> Option.get_or "Predicate references undefined variable?" in
      let applied = Term.mk_term tm Kind.Apply_uf (Array.of_list [pred; input]) in
      match value with
      | false -> Term.mk_term tm Kind.Not (Array.of_list [applied])
      | _ -> applied
    ) conds in

    List.iter (Cvc5.Solver.add_sygus_assume slv) applies;
    preds
end
