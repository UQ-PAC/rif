open LibASL

module type LifterIR = sig
  type var = Memory of var | Add of var * int64 | Register of int | PC | SP | PSTATE
  type edgetype = Linear | Branch | Entry
  type edge = string * edgetype
  type edges = edge list

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;

    readable : string;
    block : string;
    index : int;
  }
  val instruction_eq : instruction -> instruction -> bool

  module I : Map.S with type key = int

  type block = {
    name : string;
    offset : int;
    edges : edges;
    instructions : instruction I.t;
  }

  module B : Map.S with type key = string

  type blocks = block B.t

  val format_aslp : LibASL.Asl_ast.stmt -> string
  val string_of_var : var -> string
  val var_of_string : string -> var
  val var_eq : var -> var -> bool
  val pair_syms : instruction * instruction -> string list
end

module LifterIR : LifterIR = struct
  module I = Map.Make (Int)
  module B = Map.Make (String)

  type var = Register of string | PC | SP | PSTATE

  let string_of_var = function
    | Register i -> "R" ^ i
    | PC -> "PC"
    | SP -> "SP"
    | PSTATE -> "PSTATE"

  let var_of_string = function
    | "PC" -> PC
    | "SP" -> SP
    | "PSTATE" -> PSTATE
    | s when s.[0] = 'R' -> Register (String.sub s 1 (String.length s))
    | _ -> failwith "Invalid string"

  let var_eq a b = String.equal (string_of_var a) (string_of_var b)

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;

    readable : string;
    block : string;
    index : int;
  }

  let instruction_eq i1 i2 =
    let c1 = String.compare (i1.block) (i2.block) in
    match c1 with
    | 0 -> i1.index == i2.index
    | _ -> false

  let pair_syms p =
    let inst_syms i =
      List.map (fun v -> string_of_var v |> ( ^ ) "M") (i.load @ i.store)
      @ List.map string_of_var (i.read @ i.write)
    in
    inst_syms (fst p) @ inst_syms (snd p)

  type edgetype = Linear | Branch | Entry
  type edge = string * edgetype
  type edges = edge list

  type block = {
    name : string;
    offset : int;
    edges : edges;
    instructions : instruction I.t;
  }

  type blocks = block B.t

  open LibASL

  let format_aslp = Asl_utils.pp_stmt
end
