open Ocaml_protoc_plugin
open Lifter_ir

module type LifterElf = sig
  type elf_blockdata = {
    name : string;
    address : int;
    edges : string list;
    instructions : (int * bytes) list;
  }
  module B : Map.S with type key = string
  type blocks = elf_blockdata B.t

  val parse : string -> string -> bool -> blocks option
end

module LifterElf : LifterElf = struct
  open Rif

  type p_ir = IR.Gtirb.Proto.IR.t
  type p_cfg = CFG.Gtirb.Proto.CFG.t
  type p_module = Module.Gtirb.Proto.Module.t
  type p_bo = Module.Gtirb.Proto.ByteOrder.t
  type p_symbol = Symbol.Gtirb.Proto.Symbol.t
  type p_section = Section.Gtirb.Proto.Section.t
  type p_interval = ByteInterval.Gtirb.Proto.ByteInterval.t
  type p_block = ByteInterval.Gtirb.Proto.Block.t
  type p_code = CodeBlock.Gtirb.Proto.CodeBlock.t

  let read_gtirb filename =
    let bytes_in =
      let gtirb = open_in_bin filename in
      let len = in_channel_length gtirb in
      let magic = really_input_string gtirb 8 in
      let rest = really_input_string gtirb (len - 8) in
      let res =
        if String.starts_with ~prefix:"GTIRB" magic then rest else magic ^ rest
      in
      close_in gtirb;
      res
    in
    let gtirb = IR.Gtirb.Proto.IR.from_proto (Reader.create bytes_in) in
    match gtirb with
    | Ok a -> a
    | Error e ->
        failwith
          (Printf.sprintf "Bad IR: could not reply request: %s"
             (Ocaml_protoc_plugin.Result.show_error e))


  let b64_bytes b = Base64.encode_exn (Bytes.to_string b)

  module GtirbLookups = struct
    let symbol_to_uuid (syms : p_symbol list) (name : string) : bytes =
      let symbol_by_name (ss : p_symbol list) (name : string) : p_symbol =
        let matches (s : p_symbol) =
          if String.equal s.name name then Some s else None
        in
        match List.find_map matches ss with
        | Some sym -> sym
        | _ ->
            failwith (Printf.sprintf "Bad input: could not find symbol %s" name)
      in
      let expect_referent_uuid (s : p_symbol) : bytes =
        match s.optional_payload with
        | `Referent_uuid (uuid : bytes) -> uuid
        | _ ->
            failwith
              (Printf.sprintf "Bad input: symbol %s does not refer to a block!"
                 s.name)
      in
      symbol_by_name syms name |> expect_referent_uuid

    let uuid_to_block (uuid : bytes) (blocks : p_block list) :
        (int * p_code) =
      let matches (b : p_block) =
        match b.value with
        | `Code (c : p_code) when Bytes.equal c.uuid uuid -> Some (b.offset, c)
        | _ -> None
      in
      List.find_map matches blocks |> function
        | Some r -> r
        | None -> failwith "Bad input: could not find codeblock for uuid"

    let interval_codeblock_uuids (i : p_interval) =
      List.filter_map
        (fun (b : p_block) ->
          match b.value with `Code (c : p_code) -> Some c.uuid | _ -> None)
        i.blocks
  end

 type elf_blockdata = {
    name : string;
    address : int;
    edges : string list;
    instructions : (int * bytes) list;
  }
  module B = Map.Make (String)
  type blocks = elf_blockdata B.t

  module CFG = struct
    open Graph

    open CFG.Gtirb.Proto
    type p_edge = Edge.t
    type p_edgelabel = EdgeLabel.t
    type p_edgetype = EdgeType.t

    module Node = struct
      type t = bytes
      let compare = Bytes.compare
      let equal = Bytes.equal
      let hash = Hashtbl.hash
      let fold_vertex = failwith "A"
    end

    module Edge = struct
      type t = p_edgetype
      let compare (a : t) (b : t) = compare a b
      let equal a b = 0 == compare a b
      let hash = Hashtbl.hash
      let default = EdgeType.Type_Fallthrough
    end

    module G = Persistent.Digraph.ConcreteLabeled (Node) (Edge)
    module L = Leaderlist.Make (G)

    let induce_graph (g : p_cfg) : G.t =
      let nodes = List.fold_left G.add_vertex G.empty g.vertices in
      List.fold_left (fun g (e : p_edge) -> G.add_edge g e.source_uuid e.target_uuid) nodes g.edges

    let component_subgraph uuid g = L.leader_lists (induce_graph g) uuid
    let filter g _ = g
    let outgoing_edges g uuid = G.succ_e g uuid |> List.map (fun (_, _, v) -> b64_bytes v)

    let make_map f g = G.fold_vertex (fun v m -> B.add (b64_bytes v) (f v) m) g B.empty
  end

  let opcode_length = 4

  let split_instructions ~do_reverse address offset block_size meat =
    let endian_reverse b =
      let len = Bytes.length b in
      let getrev i = Bytes.get b (len - 1 - i) in
      Bytes.init len getrev
    in
    let cut_opcodes contents idx =
      let b = Bytes.sub contents (idx * opcode_length) opcode_length in
      ( address + offset + (idx * opcode_length),
        if do_reverse then endian_reverse b else b )
    in

    let size = block_size in
    let num_opcodes = size / opcode_length in
    if size <> num_opcodes * opcode_length then failwith "Internal error :(";

    let contents = Bytes.sub meat offset size in
    List.init num_opcodes (cut_opcodes contents)

  let parse (filename : string) (component : string) (verb : bool) =
    let ir = read_gtirb filename in

    let modules = ir.modules in
    let symbols = List.concat_map (fun (m : p_module) -> m.symbols) modules in

    let component_block_uuid = GtirbLookups.symbol_to_uuid symbols component in

    let cfg = Option.get ir.cfg |> CFG.induce_graph in

    if verb then
      print_endline
        (Printf.sprintf "    [!] Found entrypoint block %s"
           (b64_bytes component_block_uuid));

    let do_interval ~(do_reverse : bool) (i : p_interval) : blocks option =
      try Some (
        (* Cause Not_found and return None if we aren't in the right interval yet *)
        ignore @@ GtirbLookups.uuid_to_block component_block_uuid i.blocks;

        let component_cfg = CFG.filter cfg @@ GtirbLookups.interval_codeblock_uuids i in
        CFG.make_map (fun uuid ->
          let offset, cblock = GtirbLookups.uuid_to_block uuid i.blocks in
          {
            name = b64_bytes uuid;
            address = offset + i.address;
            edges = CFG.outgoing_edges component_cfg uuid;
            instructions = split_instructions ~do_reverse:do_reverse i.address offset cblock.size i.contents
          }
        ) component_cfg
      ) with Not_found -> None
    in

    List.find_map (fun (m : p_module) ->
      List.find_map (fun (s : p_section) ->
        List.find_map (fun (i : p_interval) ->
          do_interval ~do_reverse:(m.byte_order == LittleEndian) i
        ) s.byte_intervals
      ) m.sections
    ) modules
end
