open Spec_lang

module type SpecAnalysis = sig
  (* Sanity-check a parsed spec for loops *)
  val sanity : SpecLang.spec -> unit

  (* Iterate, or map, through a spec, in topological order
     i.e. if R_MR0() calls R_MR2() then we will see R_MR0() before R_MR2() *)
  val topo_iter : (string -> SpecLang.spec_body -> unit) -> SpecLang.spec -> unit
  val topo_map : (SpecLang.spec_body -> 'a) -> SpecLang.spec -> 'a SpecLang.M.t
end

module SpecAnalysis : SpecAnalysis = struct
  open Graph

  module Node = struct
    type t = string
    let compare = String.compare
    let equal = String.equal
    let hash = Hashtbl.hash

    let find_in spec name = SpecLang.M.find name spec
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
    | SpecLang.Term (_, ss) -> List.fold_left (fun a b -> a || has_nondeterminism b) false ss
    | _ -> false

  let nodes spec =
    SpecLang.M.bindings spec |>
    List.map fst |>
    List.fold_left G.add_vertex G.empty

  let edges spec graph =
    SpecLang.M.bindings spec |>
    List.map (fun (k,v) -> List.map (fun e -> (k,e)) @@ outgoing_edges v) |>
    List.flatten |>
    List.fold_left (fun gr (name, calls) -> G.add_edge gr name calls) graph
  let induce_graph s = nodes s |> edges s

  let sanity_check_for_cyclic_rely = J.iter_cycles (failwith "Sanity check: cyclic specification detected?")

  let sanity spec =
    let g = induce_graph spec in
    sanity_check_for_cyclic_rely g

  let topo_fold action spec =
    induce_graph spec |> T.fold (fun s -> action s (Node.find_in spec s))

  let topo_iter action spec =
    induce_graph spec |> T.iter (fun s -> action s (Node.find_in spec s))

  let topo_map action spec =
    topo_fold (fun k v acc -> SpecLang.M.add k (action v) acc) spec SpecLang.M.empty
end

