open Rif

(****************************************************************************************
  Wrapper around GTIRB serialised data, ASLp parsing, etc. Basically all the binary stuff.
*)
module type Lifter = sig
  module Blocks : Map.S with type key = bytes
  module Instructions : Map.S with type key = int

  type var = Register of int | PC | SP | PSTATE | Global of int

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;
  }

  type edgetype = Linear | Call | Entry
  type outgoing_edge = bytes * edgetype

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    instructions : instruction Instructions.t;
  }

  val opcode_length : int
  val parse : IR.Gtirb.Proto.IR.t -> string -> bool -> blockdata Blocks.t
  val all_syms : instruction -> string list
  val varEq : var -> var -> bool
  val varSym : ?mem:bool -> var -> string

  val cvc_of_inst :
    Cvc5.TermManager.tm ->
    Util.Cvc.terms ->
    Util.Cvc.terms ->
    instruction ->
    Cvc5.Term.term list
end

module Lifter = struct
  type var = Register of int | PC | SP | PSTATE | Global of int

  let b64_bytes b = Base64.encode_exn (Bytes.to_string b)

  type instruction = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
    semantics : LibASL.Asl_ast.stmt list;
  }

  let varEq a b =
    match (a, b) with
    | PC, PC -> true
    | SP, SP -> true
    | PSTATE, PSTATE -> true
    | Register ai, Register bi -> ai == bi
    | _, _ -> false

  let varSym ?(mem = false) (v : var) =
    let s =
      match v with
      | PC -> "PC"
      | SP -> "SP"
      | PSTATE -> "PSTATE"
      | Register i -> "R" ^ string_of_int i
      | Global i -> "G" ^ string_of_int i
    in
    if mem then "M" ^ s else s

  type edgetype = Linear | Call | Entry
  type outgoing_edge = bytes * edgetype

  module Instructions = Map.Make (Int)

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    instructions : instruction Instructions.t;
  }

  module Blocks = Map.Make (Bytes)

  (****************************************************************************************
  Creating and filtering semantic data from ASLp
  *)
    let lift_block_from_interval (mod_endianness : bool) (cblock : p_code)
        (i : p_interval) (block_offset : int) : instruction Instructions.t =
      let endian_reverse b =
        let len = Bytes.length b in
        let getrev i = Bytes.get b (len - 1 - i) in
        Bytes.init len getrev
      in
      let cut_opcodes contents idx =
        let b = Bytes.sub contents (idx * opcode_length) opcode_length in
        ( i.address + block_offset + (idx * opcode_length),
          if mod_endianness then endian_reverse b else b )
      in

      let size = cblock.size in
      let num_opcodes = size / opcode_length in
      if size <> num_opcodes * opcode_length then failwith "Internal error :(";

      let contents = Bytes.sub i.contents block_offset size in
      let opcodes = List.init num_opcodes (cut_opcodes contents) in

      List.fold_left
        (fun acc i ->
          Instructions.add (fst i)
            (Asl_lib.collapse @@ Asl_lib.lift_one_op i)
            acc)
        Instructions.empty opcodes
  end

  (****************************************************************************************
  Main Lifter interface
  *)
  let parse (ir : p_ir) (component : string) (verb : bool) =
    print_endline "[!] Parsing GTIRB IR...";
    let modules = ir.modules in
    let symbols = List.concat_map (fun (m : p_module) -> m.symbols) modules in
    let cfg =
      match ir.cfg with Some c -> c | _ -> failwith "Bad IR: no CFG found!"
    in

    let component_block_uuid = Lookup.symbol_to_uuid symbols component in
    if verb then
      print_endline
        (Printf.sprintf "    [!] Found entrypoint block %s"
           (b64_bytes component_block_uuid));

    let do_interval (mod_endian : p_bo) (i : p_interval) :
        (bytes * blockdata) list option =
      if Option.is_some (Lookup.codeblock_by_uuid component_block_uuid i.blocks)
      then
        (* This interval has the entrypoint block. Start extracting! *)
        let component_cfg =
          CFG.construct_function_cfg cfg component_block_uuid i
        in

        let needs_flipping = mod_endian == LittleEndian in

        let do_uuid (uuid : bytes) : blockdata =
          let offset, cblock = Lookup.expect_codeblock_by_uuid uuid i.blocks in
          {
            name = b64_bytes uuid;
            offset = offset + i.address;
            outgoing_edges = CFG.cfg_by_block uuid component_cfg;
            instructions =
              Semantics.lift_block_from_interval needs_flipping cblock i offset;
          }
        in

        let result =
          List.map (fun u -> (u, do_uuid u)) (CFG.unpack_uuids component_cfg)
        in

        Some result
      else None
    in
    let do_section (mod_endian : p_bo) (s : p_section) =
      List.find_map (do_interval mod_endian) s.byte_intervals
    in
    let do_module (m : p_module) =
      List.find_map (do_section m.byte_order) m.sections
    in
    let extracted_info = List.find_map do_module modules in

    match extracted_info with
    | Some e ->
        List.fold_left
          (fun map block -> match block with u, b -> Blocks.add u b map)
          Blocks.empty e
    | None -> failwith "Internal error :("

  let all_registers (i : instruction) : var list =
    List.sort_uniq
      (fun a b -> String.compare (varSym a) (varSym b))
      (i.read @ i.write)

  let all_addresses (i : instruction) : var list =
    List.sort_uniq
      (fun a b -> String.compare (varSym a) (varSym b))
      (i.load @ i.store)

  let all_syms (i : instruction) : string list =
    List.map varSym (all_registers i)
    @ List.map (varSym ~mem:true) (all_addresses i)

  (****************************************************************************
   * Lifter to Cvc5
   ****************************************************************************)
end
