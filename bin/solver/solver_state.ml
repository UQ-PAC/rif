open Cvc5
open Solver_utils

module type SolverState = sig
  type state
  type state_function = state -> string -> Term.term option
  type state_constraints = state -> state -> Term.term option list

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
  val get_predicate : state -> string -> string -> Term.term option
  val dump : state -> unit

  val add_preconditions :
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    (string * string * bool) list ->
    state ->
    state

  val apply_pred :
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state_function ->
    state ->
    state

  val apply_inst :
    TermManager.tm ->
    Cvc5.Solver.solver ->
    Sort.sort ->
    state_function ->
    state ->
    state

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

  let fresh_boolean_nondeterminism tm slv =
    incr nondeterminism_counter;
    Cvc5.Solver.declare_sygus_var slv
      ("???_" ^ string_of_int !nondeterminism_counter)
      (Sort.mk_bool_sort tm)

  type state = {
    aliasing : string S.t; (* "x" -> "MR0"                  *)
    terms : Term.term S.t; (* "MR0" -> Term(MR0)            *)
    predicates : Term.term S.t S.t; (* "MR0" -> "secret" -> true *)
  }

  let empty_state =
    { aliasing = S.empty; terms = S.empty; predicates = S.empty }

  let dump (s : state) : unit =
    print_endline "Aliasing in state:";
    s.aliasing |> S.bindings
    |> List.map (fun (k, v) ->
           s.terms |> S.find v |> Term.to_string
           |> Printf.sprintf "%s -> %s -> %s" k v)
    |> List.iter print_endline;

    print_endline "Terms in state:";
    s.terms |> S.bindings
    |> List.map (fun (k, v) -> Term.to_string v |> Printf.sprintf "%s -> %s" k)
    |> List.iter print_endline;

    print_endline "Predicates in state:";
    s.predicates |> S.bindings
    |> List.map (fun (k, v) ->
           List.map (fun (a, b) -> (k, a, b)) @@ S.bindings v)
    |> List.flatten
    |> List.iter (fun (name, predicate, value) ->
           print_endline
           @@ Printf.sprintf "%s(%s) : %s" predicate name
           @@ Term.to_string value)

  let find_opt (s : state) (k : string) : Term.term option =
    match S.find_opt k s.aliasing with
    | Some alias -> S.find_opt alias s.terms
    | None -> S.find_opt k s.terms

  let get_predicate (s : state) (pred : string) (name : string) :
      Term.term option =
    let real_name =
      match S.find_opt name s.aliasing with Some v -> v | None -> name
    in

    match S.find_opt real_name s.predicates with
    | Some value -> S.find_opt pred value
    | None -> None

  type state_function = state -> string -> Term.term option
  type state_constraints = state -> state -> Term.term option list

  let initialise slv srt (names : string list) : state =
    if verbose then List.iter SolverUtils.Printing.pp_newterm names;
    {
      empty_state with
      terms =
        List.fold_left
          (fun acc n -> S.add n (Cvc5.Solver.declare_sygus_var slv n srt) acc)
          S.empty names;
    }

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
    if verbose then
      List.iter (fun a -> snd a |> SolverUtils.Printing.pp_func) funcs;

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
      List.fold_left (fun acc (n1, n2) -> S.add n1 n2 acc) s.aliasing pairs
    in

    let bound = List.map fst @@ S.bindings aliasing in
    let unbound =
      List.filter (fun n -> not @@ List.exists (String.equal n) bound) ssyms
    in

    {
      s with
      aliasing;
      terms =
        List.fold_left
          (fun acc name -> S.add name (fresh_nondeterminism slv srt) acc)
          s.terms unbound;
    }

  let update_predicates tm slv (s : state) map =
    S.bindings map
    |> List.fold_left
         (fun acc (modified_key, modified_term) ->
           let modified_val = Term.to_string modified_term in
           let modified_map =
             S.find_opt modified_key s.predicates
             |> Option.value ~default:S.empty
           in

           match S.find_opt modified_val s.predicates with
           | Some m -> S.add modified_key m acc
           | None ->
               S.add modified_key
                 (S.map
                    (fun _ -> fresh_boolean_nondeterminism tm slv)
                    modified_map)
                 acc)
         s.predicates

  let apply_pred tm slv srt (func : state_function) (s : state) : state =
    let promote = function
      | None -> fresh_nondeterminism slv srt
      | Some v -> v
    in

    let updated = S.fold (fun k v acc -> (v, func s k) :: acc) s.aliasing [] in

    let map =
      List.fold_left (fun acc (k, v) -> S.add k (promote v) acc) s.terms updated
    in

    { s with terms = map; predicates = update_predicates tm slv s map }

  let apply_inst tm slv srt (func : state_function) (s : state) : state =
    let map =
      s.terms
      |> S.mapi (fun k v ->
             func s k
             |> Option.get_or "Instruction references undefined variable?")
    in

    { s with terms = map; predicates = update_predicates tm slv s map }

  let constrain_eq tm slv srt (s1 : state) (s2 : state) =
    let s1_contents = s1.terms |> S.bindings in

    if verbose then
      let print = SolverUtils.Printing.pp_constrain ~human:true in

      List.iter
        (fun (k, v) ->
          find_opt s2 k
          |> Option.get_or (Printf.sprintf "%s not bound in second-state" k)
          |> SolverUtils.term_eq tm v
          |> fun t ->
          ignore @@ print t;
          Cvc5.Solver.add_sygus_constraint slv t)
        s1_contents

  let assert_over tm slv srt (pred : state_constraints) (func : state_function)
      (s : state) : state =
    let result = apply_inst tm slv srt func s in

    pred s result
    |> List.fold_left
         (fun acc -> function None -> acc | Some v -> v :: acc)
         []
    |> List.iter (Cvc5.Solver.add_sygus_constraint slv);

    { s with terms = result.terms }

  let add_preconditions tm slv srt (conds : (string * string * bool) list)
      (s : state) : state =
    let real_name input =
      match S.find_opt input s.aliasing with Some v -> v | None -> input
    in

    let toplevel =
      List.map (fun (_, input, _) -> real_name input) conds
      |> List.fold_left (fun acc input -> S.add input S.empty acc) S.empty
    in

    {
      s with
      predicates =
        List.fold_left
          (fun acc (predicate, input, value) ->
            S.add (real_name input)
              (S.find (real_name input) acc
              |> S.add predicate (Term.mk_bool tm value))
              acc)
          toplevel conds;
    }
end
