open Cvc5

module type SpecLang = sig
  type body =
    | Term of Kind.t * body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  type contents = Function of string * body | Constraint of body
  type spec = contents list
end

module SpecLang : SpecLang = struct
  type body =
    | Term of Kind.t * body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  type contents = Function of string * body | Constraint of body
  type spec = contents list
end
