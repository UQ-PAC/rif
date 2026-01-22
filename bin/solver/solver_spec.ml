open Cvc5
open Spec
open Solver_state

module type SolverSpec = sig
  val translate : TermManager.tm -> Spec.Lang.spec -> SolverState.state_function
end

module SolverSpec : SolverSpec = struct
  let rec ast_convert tm (b : Spec.Lang.spec_body) (s : SolverState.state) :
      Term.term option =
    let input_term n = SolverState.find_opt s n |> Option.get in
    match b with
    | Term (k, ns) ->
        Some
          (Term.mk_term tm k
             (Array.of_list
             @@ List.map (fun r -> ast_convert tm r s |> Option.get) ns))
    | Const i -> Some (Term.mk_int tm i)
    | Bool b -> Some (Term.mk_bool tm b)
    | Pre (pred, name) -> Some (input_term name)
    | Post (pred, name) -> Some (input_term name)
    | Nondeterminism -> None

  let translate tm (s : Spec.Lang.spec) : SolverState.state_function =
   fun _ _ -> None
end
