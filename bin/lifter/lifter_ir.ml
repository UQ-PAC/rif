open LibASL

module type LifterIR = sig
  type var = Register of int | PC | SP | PSTATE
  val string_of_var : var -> string
  val var_of_string : string -> var
  val var_eq : var -> var -> bool

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;
  }

  val instruction_syms : instruction -> string list

  type edgetype = Linear | Call | Entry
  type outgoing_edge = string * edgetype

  module I : Map.S with type key = int

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    instructions : instruction I.t;
  }
  module B : Map.S with type key = string

  type blocks = blockdata B.t
end

module LifterIR : LifterIR = struct
  module I = Map.Make (Int)
  module B = Map.Make (String)

  type var = Register of int | PC | SP | PSTATE

  let string_of_var = function
    | Register i -> "R" ^ string_of_int i
    | PC -> "PC"
    | SP -> "SP"
    | PSTATE -> "PSTATE"

  let var_of_string = function
    | "PC" -> PC
    | "SP" -> SP
    | "PSTATE" -> PSTATE
    | s when s.[0] = 'R' -> Register ((String.sub s 1 (String.length s)) |> int_of_string)
    | _ -> failwith "Invalid string"

  let var_eq a b = String.equal (string_of_var a) (string_of_var b)

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;
  }

  let instruction_syms i =
    List.map (fun v -> string_of_var v |> (^) "M") (i.load @ i.store)

  type edgetype = Linear | Call | Entry
  type outgoing_edge = string * edgetype

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    instructions : instruction I.t;
  }

  type blocks = blockdata B.t
end
