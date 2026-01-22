open Cvc5

module type SpecLang = sig
  type spec_body =
    | Term of Kind.t * spec_body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  type spec = (string * spec_body) list
end

module SpecLang : SpecLang = struct
  type spec_body =
    | Term of Kind.t * spec_body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  type spec = (string * spec_body) list
end
