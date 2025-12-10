open Cvc5
open Util

module RGSpec = struct
  type speclang =
    | Term of Kind.t * speclang list
    | Const of int
    | Bool of bool
    | Pre of string
    | Post of string

  let rec collect_globs s =
    match s with
    | Post n -> [ n ]
    | Pre n -> [ n ]
    | Term (_, ss) -> List.flatten @@ List.map collect_globs ss
    | _ -> []

  let rec sanity_guar_uses_posts s =
    match s with
    | Post _ -> failwith "Sanity check: guarantee includes a post-state?"
    | Term (_, ss) -> List.iter sanity_guar_uses_posts ss
    | _ -> ()

  let input (r : string) (g : string) : speclang * speclang =
    (* TODO: this is a dummy impl *)
    let parse s =
      ignore s;
      Bool true
    in
    let guar = parse g in

    sanity_guar_uses_posts guar;
    (parse r, guar)

  type spec_behaviour =
    | ConstrainFuncsUnchanged of (Util.Cvc.terms * Util.Cvc.terms)
    | AssumeRegsUnchanged of (Util.Cvc.terms * Util.Cvc.terms)
    | Nothing

  let cvc_of_spec tm fromv tov spec =
    let rec subcall node =
      match node with
      | Term (k, ts) -> Term.mk_term tm k (Array.of_list @@ List.map subcall ts)
      | Const i -> Term.mk_int tm i
      | Bool b -> Term.mk_bool tm b
      | Pre s -> Util.Cvc.find_glob fromv s
      | Post s -> Util.Cvc.find_glob tov s
    in

    (* 
    let auto =
      match behaviour with
      | Nothing -> []
      | AssumeRegsUnchanged (m1, m2) | ConstrainFuncsUnchanged (m1, m2) ->
          List.filter_map
            (fun (k, v) ->
              if k.[0] != 'R' then None
              else Some (Util.Cvc.term_eq tm v (Util.Cvc.TermMap.find k m2)))
            (Util.Cvc.TermMap.bindings m1)
    in
    *)
    [ subcall spec ]
end
