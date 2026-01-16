open Cvc5

module type SpecLang = sig
  type spec_body =
    | Term of Kind.t * spec_body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  module M : Map.S with type key = string

  type spec = spec_body M.t
end

module SpecLang : SpecLang = struct
  type spec_body =
    | Term of Kind.t * spec_body list
    | Const of int
    | Bool of bool
    | Pre of string * string
    | Post of string * string
    | Nondeterminism

  module M = Map.Make (String)

  type spec = spec_body M.t
end
