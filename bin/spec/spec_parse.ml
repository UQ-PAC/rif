open Cvc5
open Spec_lang

module type SpecParse = sig
  (* Parse a string to a SpecLang AST *)
  val parse : string -> SpecLang.spec
  val pp_spec : SpecLang.spec -> unit
end

module SpecParse : SpecParse = struct
  open Angstrom

  let with_parens p = char '(' *> p <* char ')'

  let is_digit = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false

  let is_word = function
    | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false

  let is_space = function ' ' -> false | _ -> true
  let is_true = string "true" <|> string "True" >>| fun _ -> true
  let is_false = string "false" <|> string "False" >>| fun _ -> false
  let var = take_while1 is_word
  let whitespace = skip_while is_space

  let kind =
    take_while1 (fun c -> is_space c |> not) >>| function
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

  let spec_body =
    fix (fun (recurse : SpecLang.spec_body t) ->
        let pre =
          string "pre" *> with_parens var >>| fun a b -> SpecLang.Pre (b, a)
        in
        let post =
          string "post" *> with_parens var >>| fun a b -> SpecLang.Pre (b, a)
        in
        let predicate = with_parens (pre <|> post) <*> take_while is_word in

        let const =
          take_while1 is_digit >>| int_of_string >>| fun i -> SpecLang.Const i
        in
        let bool = is_true <|> is_false >>| fun b -> SpecLang.Bool b in
        let non = string "???" >>| fun _ -> SpecLang.Nondeterminism in

        let term_inner =
          both (kind <* whitespace) (sep_by1 whitespace @@ with_parens recurse)
        in

        let term =
          with_parens term_inner >>| fun (k, subs) -> SpecLang.Term (k, subs)
        in

        predicate <|> const <|> bool <|> non <|> term)

  let spec = both var @@ (string " -> " *> spec_body)
  let all_specs = sep_by1 (char ';' <* whitespace) (with_parens spec)

  let parse s =
    if String.equal s "" then []
    else
      parse_string ~consume:All all_specs s |> function
      | Ok r -> r
      | Error e -> failwith e

  let pp_spec =
    List.iter (fun (name, body) ->
        let rec pp_body indent = function
          | SpecLang.Term (k, b) ->
              Printf.sprintf "(%s %s)" (Kind.to_string k) "..."
          | SpecLang.Nondeterminism -> "???"
          | SpecLang.Bool b -> string_of_bool b
          | SpecLang.Const i -> string_of_int i
          | SpecLang.Pre (pred, var) -> pred ^ "(pre(" ^ var
          | SpecLang.Post (pred, var) -> pred ^ "(post(" ^ var
        in
        print_endline (name ^ " -> " ^ pp_body 0 body))
end
