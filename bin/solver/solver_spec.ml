open Cvc5
open Spec
open Solver_state
open Solver_utils

module type SolverSpec = sig
  val translate_fn :
    TermManager.tm -> Spec.Lang.spec -> SolverState.state_function

  val translate_cn :
    TermManager.tm -> Spec.Lang.spec -> SolverState.state_constraints

  val generate_stage1_pres :
    Spec.Lang.spec * Spec.Lang.spec -> (string * string * bool) list list
end

module SolverSpec : SolverSpec = struct
  let rec ast_convert tm (b : Spec.Lang.body) (s : SolverState.state)
      (s2 : SolverState.state option) : Term.term option =
    let input_term n =
      SolverState.find_opt s n
      |> Option.get_or "Spec references undefined input term?"
    in
    let output_term n =
      SolverState.find_opt
        (Option.get_or "Undefined reference to post-state" s2)
        n
      |> Option.get_or "Spec references undefined output term?"
    in
    match b with
    | Term (k, ns) ->
        let next_layer =
          List.map (fun b -> ast_convert tm b s s2) ns
          |> List.fold_left
               (function
                 | None -> fun _ -> None
                 | Some ls -> (
                     function None -> None | Some v -> Some (v :: ls)))
               (Some [])
        in
        Option.bind next_layer (fun vs ->
            Some (Term.mk_term tm k (Array.of_list vs)))
    | Const i -> Some (Term.mk_int tm i)
    | Bool b -> Some (Term.mk_bool tm b)
    | Pre (pred, name) when String.equal pred "" -> Some (input_term name)
    | Post (pred, name) when String.equal pred "" -> Some (output_term name)
    | Pre (pred, name) -> SolverState.get_predicate s pred name
    | Post (pred, name) ->
        SolverState.get_predicate
          (Option.get_or "Undefined reference to post-state" s2)
          pred name
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
    fun s1 s2 -> List.map (fun b -> ast_convert tm b s1 (Some s2)) constraints

  let generate_stage1_pres spec =
    let rec collect_preds : Spec.Lang.body -> (string * string) list = function
      | Term (_, ns) -> List.flatten @@ List.map collect_preds ns
      | Pre (pred, name) when not @@ String.equal pred "" -> [ (pred, name) ]
      | Post (pred, name) when not @@ String.equal pred "" -> [ (pred, name) ]
      | _ -> []
    in

    let sort_pair a b =
      let c1 = String.compare (fst a) (fst b) in
      if c1 == 0 then String.compare (snd a) (snd b) else c1
    in

    let pred_uses =
      fst spec @ snd spec
      |> List.map (function
             | Spec.Lang.Constraint b | Spec.Lang.Function (_, b) -> b)
      |> List.map collect_preds |> List.flatten |> List.sort_uniq sort_pair
    in

    let all = List.length pred_uses |> SolverUtils.combine in

    List.map (List.map2 (fun (a, b) c -> (a, b, c)) pred_uses) all
end
