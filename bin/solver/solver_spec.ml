open Cvc5
open Spec
open Solver_state

module type SolverSpec = sig
  val translate_fn :
    TermManager.tm -> Spec.Lang.spec -> SolverState.state_function

  val translate_cn :
    TermManager.tm -> Spec.Lang.spec -> SolverState.state_constraints

  val generate_pres :
    TermManager.tm -> Spec.Lang.spec * Spec.Lang.spec -> Term.term list list
end

module SolverSpec : SolverSpec = struct
  type abstraction = Term.term list

  let rec ast_convert tm (b : Spec.Lang.body) (s : SolverState.state)
      (s2 : SolverState.state option) : Term.term option =
    let input_term n = SolverState.find_opt s n |> Option.get in
    let output_term n = SolverState.find_opt (Option.get s2) n |> Option.get in
    match b with
    | Term (k, ns) ->
        Some
          (Term.mk_term tm k
             (Array.of_list
             @@ List.map (fun r -> ast_convert tm r s s2 |> Option.get) ns))
    | Const i -> Some (Term.mk_int tm i)
    | Bool b -> Some (Term.mk_bool tm b)
    | Pre (pred, name) -> Some (input_term name)
    | Post (pred, name) -> Some (output_term name)
    | Nondeterminism -> None

  let translate_fn tm (spec : Spec.Lang.spec) : SolverState.state_function =
    let functions =
      List.filter_map
        (function
          | Spec.Lang.Constraint _ -> None
          | Spec.Lang.Function (a, b) -> Some (a, b))
        spec
    in

    fun state s ->
      let body =
        List.find_opt (fun var -> fst var |> String.equal s) functions
        |> Option.map snd
      in
      Option.bind body (fun b -> ast_convert tm b state None)

  let translate_cn tm (spec : Spec.Lang.spec) : SolverState.state_constraints =
    let constraints =
      List.filter_map
        (function
          | Spec.Lang.Constraint b -> Some b | Spec.Lang.Function _ -> None)
        spec
    in
    fun s1 s2 ->
      List.map
        (fun b -> ast_convert tm b s1 (Some s2) |> Option.get)
        constraints

  (* TODO *)
  let generate_pres _ _ = [ [] ]
end
