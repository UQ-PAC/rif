open Spec_lang

module type SpecAnalysis = sig
  (* Sanity-check a parsed spec for loops *)
  val sanity : SpecLang.spec -> unit
  val spec_syms : SpecLang.spec * SpecLang.spec -> string list

  (* Iterate, or map, through a spec, in topological order
     i.e. if R_MR0() calls R_MR2() then we will see R_MR0() before R_MR2() *)
  val topo_iter :
    (string -> SpecLang.spec_body -> unit) -> SpecLang.spec -> unit
end

module SpecAnalysis : SpecAnalysis = struct
  open Graph
  module Lang = SpecLang

  module Node = struct
    type t = string

    let compare = String.compare
    let equal = String.equal
    let hash = Hashtbl.hash

    let find_in spec name =
      snd @@ List.find (fun n -> String.equal name @@ fst n) spec
  end

  module G = Persistent.Digraph.Concrete (Node)
  module J = Cycles.Johnson (G)
  module T = Topological.Make (G)

  let rec outgoing_edges = function
    | SpecLang.Post (_, n) -> [ n ]
    | SpecLang.Term (_, ss) -> List.map outgoing_edges ss |> List.flatten
    | _ -> []

  let rec global_variables = function
    | SpecLang.Post (_, n) -> [ n ]
    | SpecLang.Pre (_, n) -> [ n ]
    | SpecLang.Term (_, ss) -> List.map global_variables ss |> List.flatten
    | _ -> []

  let rec has_nondeterminism = function
    | SpecLang.Nondeterminism -> true
    | SpecLang.Term (_, ss) ->
        List.fold_left (fun a b -> a || has_nondeterminism b) false ss
    | _ -> false

  let spec_syms spec =
    let sum_spec = fst spec @ snd spec in
    List.map (fun (s, b) -> s :: global_variables b) sum_spec
    |> List.flatten
    |> List.sort_uniq String.compare

  let nodes spec = List.map fst spec |> List.fold_left G.add_vertex G.empty

  let edges spec graph =
    List.map (fun (k, v) -> List.map (fun e -> (k, e)) @@ outgoing_edges v) spec
    |> List.flatten
    |> List.fold_left (fun gr (name, calls) -> G.add_edge gr name calls) graph

  let induce_graph s = nodes s |> edges s

  let sanity_check_for_cyclic_rely rely =
    J.iter_cycles (failwith "Sanity check: cyclic specification detected?") rely

  let sanity spec =
    () (*
    let g = induce_graph spec in
    sanity_check_for_cyclic_rely g *)

  let topo_fold action spec =
    induce_graph spec |> T.fold (fun s -> action s (Node.find_in spec s))

  let topo_iter action spec =
    induce_graph spec |> T.iter (fun s -> action s (Node.find_in spec s))
end
