let flatmap f ls = List.flatten @@ List.map f ls
let b64_bytes b = Base64.encode_exn @@ Bytes.to_string @@ b

module Lifter = struct
  (* Protobuf types, shouldn't be needed outside *)
  type p_ir = Rif.IR.Gtirb.Proto.IR.t
  type p_cfg = Rif.CFG.Gtirb.Proto.CFG.t
  type p_cfgedge = Rif.CFG.Gtirb.Proto.Edge.t
  type p_module = Rif.Module.Gtirb.Proto.Module.t
  type p_symbol = Rif.Symbol.Gtirb.Proto.Symbol.t
  type p_section = Rif.Section.Gtirb.Proto.Section.t
  type p_interval = Rif.ByteInterval.Gtirb.Proto.ByteInterval.t
  type p_block = Rif.ByteInterval.Gtirb.Proto.Block.t
  type p_code = Rif.CodeBlock.Gtirb.Proto.CodeBlock.t
  type p_data = Rif.DataBlock.Gtirb.Proto.DataBlock.t
  type p_symexprs = Rif.SymbolicExpression.Gtirb.Proto.SymbolicExpression.t
  type p_addrconst = Rif.SymbolicExpression.Gtirb.Proto.SymAddrConst.t
  type p_seattr = Rif.SymbolicExpression.Gtirb.Proto.SymAttribute.t
  type p_aux = Rif.AuxData.Gtirb.Proto.AuxData.t

  (* Actual output types *)
  module Blocks = Map.Make (Bytes)

  (* Edges in our sub-CFG are either straight instruction-to-instruction or call-and-return
     Reordering over call-and-return is not considered. Bonus "entry" edge for the first block.
   *)
  type edgetype = Linear | Call | Entry
  type outgoing_edge = bytes * edgetype
  type instruction_semantics = string list

  type blockdata = {
    outgoing_edges : outgoing_edge list;
    block_semantics : instruction_semantics list;
    offset : int;
  }

  (* Internal, pre-map CFG type *)
  type edge = bytes * bytes * edgetype
  type cfg = edge list

  (* Symbol -> block UUID lookup *)
  let symbol_to_uuid (syms : p_symbol list) (name : string) : bytes =
    let symbol_by_name (ss : p_symbol list) (name : string) : p_symbol =
      let matches (s : p_symbol) =
        if String.equal s.name name then Some s else None
      in
      match List.find_map matches ss with
      | Some sym -> sym
      | _ -> failwith (Printf.sprintf "Could not find symbol %s" name)
    in

    let expect_referent_uuid (s : p_symbol) : bytes =
      match s.optional_payload with
      | `Referent_uuid (uuid : bytes) -> uuid
      | _ ->
          failwith
            (Printf.sprintf "Symbol %s does not refer to a block!" s.name)
    in
    expect_referent_uuid (symbol_by_name syms name)

  (* UUID -> codeblock option lookup *)
  let codeblock_by_uuid (uuid : bytes) (blocks : p_block list) : p_code option =
    let matches (b : p_block) =
      match b.value with
      | `Code (c : p_code) when Bytes.equal c.uuid uuid -> Some c
      | _ -> None
    in
    List.find_map matches blocks

  (* UUID -> codeblock lookup that fails if not found *)
  let expect_uuid_codeblock uuid blocks : p_code =
    match codeblock_by_uuid uuid blocks with
    | Some c -> c
    | None ->
        failwith
          (Printf.sprintf "No codeblock found with uuid %s!" (b64_bytes uuid))

  (* UUID -> interval lookup (i.e. which interval has this codeblock) *)
  let expect_containing_interval (uuid : bytes) (is : p_interval list) =
    List.find
      (fun (i : p_interval) -> Option.is_some (codeblock_by_uuid uuid i.blocks))
      is

  (* Interval -> codeblock list filtering *)
  let interval_codeblock_uuids (i : p_interval) =
    List.filter_map
      (fun (b : p_block) ->
        match b.value with `Code (c : p_code) -> Some c.uuid | _ -> None)
      i.blocks

  (* Interval -> codeblock offset finding *)
  let interval_codeblock_offset (u : bytes) (i : p_interval) =
    List.find_map
      (fun (b : p_block) ->
        match b.value with
        | `Code (c : p_code) ->
            if Bytes.equal c.uuid u then Some b.offset else None
        | _ -> None)
      i.blocks

  let expect_interval_codeblock_offset (u : bytes) (i : p_interval) =
    match interval_codeblock_offset u i with
    | Some o -> o
    | _ -> failwith "Internal error: no codeblock with uuid %s!"

  (* Constructs a subset-CFG for just the function we care about
     (identified by its entrypoint being the codeblock with "uuid")
  *)
  let construct_function_cfg (cfg : p_cfg) (uuid : bytes)
      (interval : p_interval) : cfg =
    (* ASSUMPTION: A function lives entirely inside one ByteInterval
       Therefore, filter cfgedges to those pointing back towards the given interval.
     *)
    let in_interval u =
      let interval_uuids = interval_codeblock_uuids interval in
      let opt = List.find_opt (Bytes.equal u) interval_uuids in
      match opt with Some _ -> true | _ -> false
    in
    let relevant_edges =
      List.filter (fun (e : p_cfgedge) -> in_interval e.target_uuid) cfg.edges
    in

    (* Follow calls-and-returns back to the original function. *)
    let call_and_return (ct : Rif.CFG.Gtirb.Proto.EdgeType.t) (uuid : bytes) =
      let (relevant_returntype : Rif.CFG.Gtirb.Proto.EdgeType.t) =
        match ct with
        | Type_Call -> Type_Return
        | Type_Syscall -> Type_Sysret
        | _ -> failwith "Internal error: bad edge type."
      in
      let matching_edge (e : p_cfgedge) =
        if Bytes.equal e.source_uuid uuid then
          match e.label with
          | Some l when l.type' == relevant_returntype -> Some e.target_uuid
          | _ -> None
        else None
      in
      List.filter_map matching_edge cfg.edges
    in

    (* Is this cfgedge coming from a source-block-uuid that we've currently collected?
       If so, make an edge in the sub-CFG, including the correct type (linear vs call)
     *)
    let from_source_block (u : bytes) (e : p_cfgedge) =
      if Bytes.equal e.source_uuid u then
        match e.label with
        | Some l when l.type' == Type_Branch || l.type' == Type_Fallthrough ->
            Some [ (u, e.target_uuid, Linear) ]
        | Some l when l.type' == Type_Call || l.type' == Type_Syscall ->
            Some
              (List.map
                 (fun b -> (u, b, Call))
                 (call_and_return l.type' e.target_uuid))
        | _ -> None
      else None
    in

    (* Turn a sub-CFG edge into a list of directly-connected sub-CFG edges *)
    let find_following_edges (e : edge) : edge list =
      match e with
      | _, t, _ ->
          List.flatten @@ List.filter_map (from_source_block t) relevant_edges
    in

    (* Get a list of "next" edges, add it to the current cfg, and if we gained edges, then recurse. *)
    let rec traverse_until_fixpoint (u : cfg) : cfg =
      let next = u @ flatmap find_following_edges u in
      if List.compare_lengths u next == 0 then u
      else traverse_until_fixpoint next
    in

    traverse_until_fixpoint [ (Bytes.of_string "", uuid, Entry) ]

  (* Given a constructed sub-cfg, unpack just the block UUIDs from it *)
  let unpack_uuids (cfg : cfg) : bytes list =
    List.map (fun e -> match e with _, t, _ -> t) cfg

  let cfg_by_block (uuid : bytes) (cfg : cfg) : (bytes * edgetype) list =
    let matches edge =
      match edge with
      | i, o, t -> if Bytes.equal i uuid then Some (o, t) else None
    in
    List.filter_map matches cfg

  (* AuxData/Semantics helpers *)
  let parse_semantics (as' : p_aux list) =
    List.map
      (fun (a : p_aux) -> Yojson.Safe.from_string (Bytes.to_string a.data))
      as'

  let find_for_blocks (us : bytes list) (js : Yojson.Safe.t list) =
    (* Drops any input except a list of strings *)
    let single_instruction (j : Yojson.Safe.t) =
      match j with
      | `List ls ->
          List.filter_map
            (fun l -> match l with `String s -> Some s | _ -> None)
            ls
      | _ -> []
    in

    (* Check that a base64-encoded json uuid matches a straight bytestring uuid *)
    let json_uuid_check s u = String.equal s (b64_bytes u) in

    (* Unpacks js as a list of json dictionaries and applies f to each key/value pair *)
    let unpack_dict (f : (string * Yojson.Safe.t) list -> _ option)
        (js : Yojson.Safe.t list) =
      List.filter_map
        (fun (j : Yojson.Safe.t) ->
          match j with `Assoc al -> f al | _ -> None)
        js
    in

    (* Finds the key/value pair where the key is a b64 representation of the bytes u

         ^ Find, not map, because the JSON spec ensures that dictionary keys are unique.
       *)
    let find_matching_uuid u dict =
      List.find_map
        (fun (a : string * Yojson.Safe.t) ->
          match a with s, k when json_uuid_check s u -> Some k | _ -> None)
        dict
    in

    (* unpacks j as a json list and applies f to each element *)
    let unpack_list (f : Yojson.Safe.t -> _) (j : Yojson.Safe.t) =
      match j with `List ls -> List.map f ls | _ -> []
    in

    (* Find up to one block^ with matching UUID in each semantic JSON bundle.
         Unpack that block as a JSON list and drop any decode errors,
         ending up with a list of opcode sematics (list of list of string ASL statements)

         Sanity check that we only had one matching UUID
         (i.e. there aren't duplicate UUIDs cross-module)
      *)
    let sem_of_uuid u =
      let uuid_blocks = unpack_dict (find_matching_uuid u) js in
      match uuid_blocks with
      | [ one ] -> unpack_list single_instruction one
      | [] ->
          failwith
            (Printf.sprintf
               "Bad IR: no semantic information present for this block %s!"
               (b64_bytes u))
      | _ ->
          failwith
            (Printf.sprintf
               "Bad IR: found multiple (%i) semantic blocks for this uuid!"
               (List.length uuid_blocks))
    in

    (* make map-ish for uuid -> list of list of string *)
    List.map (fun u -> (u, sem_of_uuid u)) us

  (* IR helpers / aka main Lifter entrypoint *)
  let parse (ir : p_ir) (component : string) (verb : bool) =
    let modules = ir.modules in
    let cfg =
      match ir.cfg with Some c -> c | _ -> failwith "Bad IR: no CFG found!"
    in
    let sections = flatmap (fun (m : p_module) -> m.sections) modules in
    let auxs = flatmap (fun (m : p_module) -> m.aux_data) modules in
    let symbols = flatmap (fun (m : p_module) -> m.symbols) modules in
    let intervals =
      flatmap (fun (s : p_section) -> s.byte_intervals) sections
    in

    let json_semantics =
      match
        parse_semantics
          (List.filter_map
             (fun (a : string * p_aux option) ->
               match a with k, v when String.equal k "ast" -> v | _ -> None)
             auxs)
      with
      | [] -> failwith "Bad IR: no semantics found!"
      | l -> l
    in

    let () = if verb then print_endline "[!] Successfully read IR..." in

    (* mainline reading-stuff *)
    let component_block_uuid = symbol_to_uuid symbols component in
    let component_interval =
      expect_containing_interval component_block_uuid intervals
    in
    let component_cfg =
      construct_function_cfg cfg component_block_uuid component_interval
    in

    let () =
      if verb then
        print_endline
          (Printf.sprintf "[!] Constructed CFG for function %s..." component)
    in

    let component_codeblock_uuids = unpack_uuids component_cfg in
    let block_semantics =
      find_for_blocks component_codeblock_uuids json_semantics
    in

    let () =
      if verb then
        print_endline
          (Printf.sprintf
             "[!] Found semantic information for %i instructions..."
             (List.fold_left
                (fun c (_, l) -> c + List.length l)
                0 block_semantics))
    in

    List.fold_left
      (fun map (sem : bytes * string list list) ->
        match sem with
        | u, s ->
            let block =
              {
                outgoing_edges = cfg_by_block u component_cfg;
                block_semantics = s;
                offset = expect_interval_codeblock_offset u component_interval;
              }
            in
            Blocks.add u block map)
      Blocks.empty block_semantics
end
