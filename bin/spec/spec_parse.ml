open Cvc5
open Spec_lang

module type SpecParse = sig
  (* Parse a string to a SpecLang AST *)
  val parse : string -> SpecLang.spec
  val pp_spec : SpecLang.spec -> unit
end

module SpecParse : SpecParse = struct
  open Angstrom

  let ( <?> ) p l =
    let* remaining = available in
    let remaining = min remaining 20 in
    let* s = peek_string remaining in
    p <?> Printf.sprintf "%s, got: [%s]" l s

  let with_parens p = char '(' *> p <* char ')'

  let is_digit = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false

  let is_word = function
    | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false

  let prime = char '\''
  let is_space = function ' ' -> true | _ -> false
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
    | a when String.starts_with ~prefix:"(" a ->
        failwith "Extra bracket in operation-kind"
    | _ -> Kind.Null_term

  let body =
    fix (fun (recurse : SpecLang.body t) ->
        (* word+ *)
        let pre pred = var >>| fun v -> SpecLang.Pre (pred, v) in

        (* word+' *)
        let post pred = var <* prime >>| fun v -> SpecLang.Post (pred, v) in

        (* word*(pre/post) *)
        let predicate =
          take_while is_word >>= fun pred ->
          with_parens @@ post pred <|> with_parens @@ pre pred
        in

        (* 0-9+ *)
        let const =
          take_while1 is_digit >>| int_of_string >>| fun i -> SpecLang.Const i
        in
        (* true / false *)
        let bool = is_true <|> is_false >>| fun b -> SpecLang.Bool b in

        (* ??? *)
        let non = string "???" >>| fun _ -> SpecLang.Nondeterminism in

        (* Kd[ ]+(inner) (inner) ... *)
        let term_inner =
          both (kind <* whitespace) (sep_by1 whitespace @@ with_parens recurse)
        in

        (* (term_inner) *)
        let term =
          with_parens term_inner <?> "expected a term" >>| fun (k, subs) ->
          SpecLang.Term (k, subs)
        in

        (*
          pred(pre/post)  OR
          [0-9]+          OR
          true/false      OR
          ???             OR
          (kd (rec) (rec))
        *)
        predicate <|> const <|> bool <|> non <|> term
        <?> "expected a body expression")

  let spec =
    (* var -> body *)
    let fn =
      both var @@ (string " -> " *> body)
      >>| (fun (n, b) -> SpecLang.Function (n, b))
      <?> "expected a function"
    in
    (* body *)
    let cn =
      body >>| (fun b -> SpecLang.Constraint b) <?> "expected a constraint"
    in
    (* (fn/cn) *)
    let element =
      with_parens (fn <|> cn) <?> "expected a function or constraint"
    in
    (* (fn/cn); (fn/cn); ... *)
    sep_by1 (char ';' <* whitespace) element

  let parse s =
    if String.equal s "" then []
    else
      parse_string ~consume:All spec s |> function
      | Ok r -> r
      | Error e -> failwith e

  let pp_spec =
    let rec pp_body idt = function
      | SpecLang.Term (k, b) ->
          Printf.sprintf "(%s %s)" (Kind.to_string k) "..."
      | SpecLang.Nondeterminism -> "???"
      | SpecLang.Bool b -> string_of_bool b
      | SpecLang.Const i -> string_of_int i
      | SpecLang.Pre (pred, var) -> pred ^ "(pre(" ^ var
      | SpecLang.Post (pred, var) -> pred ^ "(post(" ^ var
    in

    let pp_contents = function
      | SpecLang.Function (n, b) -> print_endline (n ^ " -> " ^ pp_body 0 b)
      | SpecLang.Constraint b ->
          print_endline ("with constraint: " ^ pp_body 0 b)
    in

    List.iter pp_contents
end
