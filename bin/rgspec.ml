open Util

module RGSpec = struct
  type spec_body =
    | Term of Cvc5.Kind.t * spec_body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  type spec = (string * spec_body) list

  module Parser = struct
    open Angstrom
    open Cvc5

    let with_parens p = char '(' *> p <* char ')'

    let is_digit = function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false
    let is_word = function '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
    let is_space = function ' ' -> false | _ -> true

    let is_true = string "true" <|> string "True" >>| fun _ -> true
    let is_false = string "false" <|> string "False" >>| fun _ -> false

    let var = take_while1 is_word
    let whitespace = skip_while is_space

    let kind = take_while1 (compose not is_space) >>| function
      | "==" -> Kind.Equal
      | "!=" -> Kind.Distinct
      | "~" | "!" -> Kind.Not
      | "&&" -> Kind.And
      | "==>" -> Kind.Implies
      | "||" -> Kind.Or
      | "^" -> Kind.Xor
      | "?" -> Kind.Ite
      | "+" -> Kind.Add
      | "*" -> Kind.Mult
      | "&" -> Kind.Iand
      | "-" -> Kind.Sub
      | "/" -> Kind.Division
      | "<" -> Kind.Lt
      | ">" -> Kind.Gt
      | "<=" -> Kind.Leq
      | ">=" -> Kind.Geq
      | _ -> Kind.Null_term

    let spec_body = fix (fun (recurse : spec_body t) ->
      let pre = string "pre" *> with_parens var >>| (fun a b -> Pre (b, a)) in
      let post = string "post" *> with_parens var >>| (fun a b -> Pre (b, a)) in
      let predicate = (with_parens (pre <|> post)) <*> (take_while is_word) in

      let const = take_while1 is_digit >>| int_of_string >>| (fun i -> Const i) in
      let bool = is_true <|> is_false >>| (fun b -> Bool b) in
      let non = string "???" >>| (fun _ -> Nondeterminism) in

      let term_inner = both (kind <* whitespace)
                            (sep_by1 whitespace @@ with_parens recurse) in

      let term = with_parens term_inner >>| (fun (k, subs) -> Term (k, subs)) in

      predicate <|> const <|> bool <|> non <|> term
    )

    let spec = both var @@ string " -> " *> spec_body
    let all_specs = sep_by1 (char ';' <* whitespace) (with_parens spec)

    let parse s = parse_string ~consume:All all_specs s |>
      function
      | Ok a -> a
      | Error s -> failwith s
  end

  module Analysis = struct
    open Graph

    module Node = struct
      type t = string
      let compare = String.compare
      let equal = String.equal
      let hash = Hashtbl.hash

      let find_in spec name = List.find (compose (String.equal name) @@ fst) spec
    end

    module G = Persistent.Digraph.Concrete (Node)
    module J = Cycles.Johnson (G)
    module T = Topological.Make (G)

    let rec outgoing_edges = function
      | Post (_, n) -> [ n ]
      | Term (_, ss) -> List.map outgoing_edges ss |> List.flatten
      | _ -> []
    let rec global_variables = function
      | Post (_, n) -> [ n ]
      | Pre (_, n) -> [ n ]
      | Term (_, ss) -> List.map global_variables ss |> List.flatten
      | _ -> []
    let rec has_nondeterminism = function
      | Nondeterminism -> true
      | Term (_, ss) -> List.fold_left (fun a b -> a || has_nondeterminism b) false ss
      | _ -> false

    let nodes = List.fold_left (fun gr sp -> G.add_vertex gr (fst sp)) G.empty
    let edges = List.fold_left
      (fun gr (name, sc) -> List.fold_left (fun g s -> G.add_edge g name s) gr @@ outgoing_edges sc)
    let induce_graph s = edges (nodes s) s

    let sanity_check_for_cyclic_rely = J.iter_cycles (failwith "Sanity check: cyclic specification detected?")

    let sanity spec =
      let g = induce_graph spec in
      sanity_check_for_cyclic_rely g

    let topo_fold action spec =
      induce_graph spec |> T.fold (compose action @@ Node.find_in spec)

    let topo_iter action spec =
      induce_graph spec |> T.iter (compose action @@ Node.find_in spec)

    let topo_map action spec =
      topo_fold (fun sp l -> l @ [ action sp ]) spec []
  end

  module Translate = struct
    open Cvc5

    module M = Map.Make (String)
    type m = Term.term M.t

    (* 
    let rec convert_body tm pres posts = function
      | Term (k, ts) -> Term.mk_term tm k (Array.of_list @@ List.map (convert_body tm pres posts) ts)
      | Const i -> Term.mk_int tm i
      | Bool b -> Term.mk_bool tm b
      | Pre s -> M.find s pres
      | Post s -> M.find s posts
      | Nondeterminism -> M.find "???" pres

    let convert_function tm solver sort pres spec =
      let (name, body) = spec in

      let pres = match Analysis.has_nondeterminism body with
        | false -> pres
        | true -> M.add "???" (Cvc5.Solver.declare_sygus_var solver "???" sort) pres (* introduce new forall variable for nondeterminism *)
      in

      Cvc5.Solver.define_fun solver name () sort (convert_body tm pres posts body)
*)
  end

  let input (r : string) (g : string) : spec * spec =
    let rely = Parser.parse r in
    let guar = Parser.parse g in

    Analysis.sanity rely;
    Analysis.sanity guar;

    (rely, guar)
end
