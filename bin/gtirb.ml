let flatmap f ls = List.flatten @@ List.map f ls

module Gtirb = struct
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

  (* IR helpers *)
  let parse (ir : p_ir) =
    let modules = ir.modules in
    let cfg =
      match ir.cfg with Some c -> c | _ -> failwith "No CFG in this IR!"
    in
    let sections = flatmap (fun (m : p_module) -> m.sections) modules in
    let symbols = flatmap (fun (m : p_module) -> m.symbols) modules in
    let intervals =
      flatmap (fun (s : p_section) -> s.byte_intervals) sections
    in
    let blocks = flatmap (fun (i : p_interval) -> i.blocks) intervals in

    (* symbolic_expressions is originally a map (int * p_symexprs option)
       we don't need it yet, but it's a hassle to extract, so the code is staying in *)
    let unmap t =
      List.filter_map
        (fun (i : int * p_symexprs option) -> match i with _, a -> a)
        t
    in
    let exprs =
      flatmap (fun (i : p_interval) -> unmap i.symbolic_expressions) intervals
    in
    ignore exprs;

    (cfg, symbols, blocks)

  (* Symbol helpers *)
  (* Given a name, search the list of symbols for a symbol with that name. If you can't find one, die. *)
  let symbol_by_name (ss : p_symbol list) (name : string) : p_symbol =
    let matches (s : p_symbol) =
      if String.equal s.name name then Some s else None
    in
    match List.find_map matches ss with
    | Some sym -> sym
    | _ -> failwith (Printf.sprintf "Could not find symbol %s" name)

  (* Given a symbol, expect it to reference a block UUID, and return that block.
       If it doesn't reference a block UUID, die. *)
  let expect_referent_uuid (s : p_symbol) : bytes =
    match s.optional_payload with
    | `Referent_uuid (uuid : bytes) -> uuid
    | _ ->
        failwith (Printf.sprintf "Symbol %s does not refer to a block!" s.name)

  (* Block helpers *)
  (* Given a UUID, search the list of blocks for a block with that UUID. If you can't find one, die. *)
  let block_by_uuid (bs : p_block list) (uuid : bytes) : p_block =
    let matches (b : p_block) =
      match b.value with
      | `Code (c : p_code) -> if Bytes.equal c.uuid uuid then Some b else None
      | `Data (d : p_data) -> if Bytes.equal d.uuid uuid then Some b else None
      | _ -> None
    in
    match List.find_map matches bs with
    | Some b -> b
    | _ ->
        failwith (Printf.sprintf "No block with uuid %s" (Bytes.to_string uuid))

  (* Given a uuid, search the list of blocks for a block with that UUID, then expect it to be a codeblock.
       If you can't find a block with that UUID, or it's not a codeblock, die.*)
  let codeblock_by_uuid (bs : p_block list) (uuid : bytes) : p_code =
    match (block_by_uuid bs uuid).value with
    | `Code (cb : p_code) -> cb
    | _ ->
        failwith
          (Printf.sprintf "Referenced block %s is not a code block!"
             (Bytes.to_string uuid))

  (* CFG helpers *)
  let traverse (cfg : p_cfg) (uuid : bytes) =
    (* Edges of type Branch or Fallthrough mean the other block is still in "this function" *)
    let find_targets_of (u : bytes) (e : p_cfgedge) =
      if Bytes.equal e.source_uuid u then
        match e.label with
        | Some l -> (
            match l.type' with
            | Type_Branch | Type_Fallthrough -> Some e.target_uuid
            | _ -> None)
        | _ -> None
      else None
    in

    let traverse_once (u : bytes) : bytes list =
      List.filter_map (find_targets_of u) cfg.edges
    in

    let rec traverse_until (u : bytes list) : bytes list =
      let next = flatmap traverse_once u in
      if List.compare_lengths u next == 0 then u else traverse_until next
    in

    traverse_until [ uuid ]

  let all_func_codeblocks (bs : p_block list) (cfg : p_cfg) (u : bytes) :
      p_code list =
    List.map (codeblock_by_uuid bs) (traverse cfg u)
end
