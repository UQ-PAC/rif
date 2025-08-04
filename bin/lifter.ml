let flatmap f ls = List.flatten @@ List.map f ls
let b64_bytes b = Base64.encode_exn @@ Bytes.to_string @@ b

module Lifter = struct
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
      | `Code (c : p_code) when Bytes.equal c.uuid uuid -> Some b
      | `Data (d : p_data) when Bytes.equal d.uuid uuid -> Some b
      | _ -> None
    in
    match List.find_map matches bs with
    | Some b -> b
    | _ -> failwith (Printf.sprintf "No block with uuid %s" (b64_bytes uuid))

  (* Given a UUID, search the list of blocks for a block with that UUID, then expect it to be a codeblock.
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
    (* TODO: Double-follow edges: call + return = fallthrough with fence *)
    let find_targets_of (u : bytes) (e : p_cfgedge) =
      if Bytes.equal e.source_uuid u then
        match e.label with
        | Some l when l.type' == Type_Branch || l.type' == Type_Fallthrough ->
            Some e.target_uuid
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
            (Printf.sprintf "No semantic information present for this block %s!"
               (b64_bytes u))
      | _ ->
          failwith
            (Printf.sprintf "Found multiple (%i) semantic blocks for this uuid!"
               (List.length uuid_blocks))
    in

    (* make map-ish for uuid -> list of list of string *)
    List.map (fun u -> (u, sem_of_uuid u)) us

  (* Lifter-related things that dont directly twiddle with gtirb *)
  let instruction_view (ss : (bytes * string list) list) (bs : p_interval list)
      =
    ignore ss;
    ignore bs;
    ()

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
    let component_uuid =
      expect_referent_uuid (symbol_by_name symbols component)
    in

    let () =
      if verb then
        print_endline
          (Printf.sprintf "[!] Found entrypoint for function %s..." component)
    in

    let codeblocks =
      [ codeblock_by_uuid blocks component_uuid ]
      @ all_func_codeblocks blocks cfg component_uuid
    in
    let code_uuids = List.map (fun (c : p_code) -> c.uuid) codeblocks in

    let semantics_per_block = find_for_blocks code_uuids json_semantics in

    let () =
      if verb then
        print_endline
          (Printf.sprintf
             "[!] Found semantic information for %i instructions..."
             (List.fold_left
                (fun c (_, l) -> c + List.length l)
                0 semantics_per_block))
    in

    semantics_per_block
end
