open Ocaml_protoc_plugin
open Lifter_ir

module type LifterElf = sig
  type extracted_block = {
    name : string;
    address : int;
    edges : LifterIR.edges;
    instructions : (int * bytes) list;
  }

  module B : Map.S with type key = string

  type blocks = extracted_block B.t

  val parse : string -> string -> bool -> blocks option
end

module LifterElf : LifterElf = struct
  (* TODO(architecture): DIY / library elf parser, take binary input instead of GTIRB *)
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
  let bytes_b64 b = Bytes.of_string (Base64.decode_exn b)

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

    let uuid_to_block (uuid : bytes) (blocks : p_block list) : int * p_code =
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

  type extracted_block = {
    name : string;
    address : int;
    edges : LifterIR.edges;
    instructions : (int * bytes) list;
  }

  module B = Map.Make (String)

  type blocks = extracted_block B.t

  module CFG = struct
    open CFG.Gtirb.Proto
    open Graph

    type p_edge = Edge.t
    type p_edgelabel = EdgeLabel.t
    type p_edgetype = EdgeType.t

    module Block = struct
      type t = string

      let compare = String.compare
      let equal = String.equal
      let hash = Hashtbl.hash
    end

    module Edge = struct
      type t = LifterIR.edgetype

      let compare = compare
      let equal a b = 0 == compare a b
      let default = LifterIR.Entry
    end

    module G = Persistent.Digraph.ConcreteLabeled (Block) (Edge)

    module F =
      Fixpoint.Make
        (G)
        (struct
          type vertex = G.E.vertex
          type edge = G.E.t
          type g = G.t
          type data = bool

          let direction = Fixpoint.Forward
          let equal = ( = )
          let join = ( || )
          let analyze _ a = a
        end)

    let induce_graph (g : p_cfg) : G.t =
      let nodes = List.map b64_bytes g.vertices in
      let edges =
        List.filter_map
          (fun (e : p_edge) ->
            Option.bind e.label
              (let src = b64_bytes e.source_uuid in
               let dst = b64_bytes e.target_uuid in
               fun (l : p_edgelabel) ->
                 match l.type' with
                 | EdgeType.Type_Fallthrough -> Some (src, dst, LifterIR.Linear)
                 | EdgeType.Type_Branch -> Some (src, dst, LifterIR.Branch)
                 | _ -> None))
          g.edges
      in

      let graph = List.fold_left G.add_vertex G.empty nodes in

      List.map (fun (s, d, l) -> G.E.create s l d) edges
      |> List.fold_left G.add_edge_e graph

    let filter (is : string list) root (g : G.t) : G.t =
      let blocks_outside_interval =
        G.fold_vertex List.cons g []
        |> List.filter (fun b -> not @@ List.exists (( = ) b) is)
      in
      let naive_filtered =
        List.fold_left G.remove_vertex g blocks_outside_interval
      in

      let reachable = F.analyze (( = ) root) g in

      let non_reachable_blocks =
        G.fold_vertex List.cons naive_filtered []
        |> List.filter (fun b -> not @@ reachable b)
      in
      List.fold_left G.remove_vertex naive_filtered non_reachable_blocks

    let all_blocks g = G.fold_vertex List.cons g [] |> List.map bytes_b64

    let block_edges from g =
      List.map (fun e -> (G.E.dst e, G.E.label e)) (G.succ_e g from)
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

    let cfg =
      Option.get_or "GTIRB didn't produce a CFG!" ir.cfg |> CFG.induce_graph
    in

    if verb then
      print_endline
        (Printf.sprintf "    [!] Found entrypoint block %s"
           (b64_bytes component_block_uuid));

    let do_interval ~(do_reverse : bool) (i : p_interval) : blocks option =
      try
        Some
          ((* Cause Not_found and return None if we aren't in the right interval yet *)
           ignore @@ GtirbLookups.uuid_to_block component_block_uuid i.blocks;

           let uuids = GtirbLookups.interval_codeblock_uuids i in
           let component_cfg =
             CFG.filter (List.map b64_bytes uuids)
               (b64_bytes component_block_uuid)
               cfg
           in

           List.fold_left
             (fun acc uuid ->
               let offset, cblock = GtirbLookups.uuid_to_block uuid i.blocks in
               let name = b64_bytes uuid in

               let block : extracted_block =
                 {
                   name;
                   address = offset + i.address;
                   edges = CFG.block_edges name component_cfg;
                   instructions =
                     split_instructions ~do_reverse i.address offset cblock.size
                       i.contents;
                 }
               in

               B.add name block acc)
             B.empty
             (CFG.all_blocks component_cfg))
      with Failure _ -> None
    in

    List.find_map
      (fun (m : p_module) ->
        List.find_map
          (fun (s : p_section) ->
            List.find_map
              (fun (i : p_interval) ->
                do_interval ~do_reverse:(m.byte_order == LittleEndian) i)
              s.byte_intervals)
          m.sections)
      modules
end
