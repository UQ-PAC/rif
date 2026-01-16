module type LifterElf = sig
  val parse : unit
end

module LifterElf : LifterElf = struct
  open Rif

  type p_ir = IR.Gtirb.Proto.IR.t
  type p_cfg = CFG.Gtirb.Proto.CFG.t
  type p_cfgedge = CFG.Gtirb.Proto.Edge.t
  type p_module = Module.Gtirb.Proto.Module.t
  type p_bo = Module.Gtirb.Proto.ByteOrder.t
  type p_symbol = Symbol.Gtirb.Proto.Symbol.t
  type p_section = Section.Gtirb.Proto.Section.t
  type p_interval = ByteInterval.Gtirb.Proto.ByteInterval.t
  type p_block = ByteInterval.Gtirb.Proto.Block.t
  type p_code = CodeBlock.Gtirb.Proto.CodeBlock.t

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
    expect_referent_uuid (symbol_by_name syms name)

    (* UUID -> codeblock option lookup *)
    let codeblock_by_uuid (uuid : bytes) (blocks : p_block list) :
        (int * p_code) option =
      let matches (b : p_block) =
        match b.value with
        | `Code (c : p_code) when Bytes.equal c.uuid uuid -> Some (b.offset, c)
        | _ -> None
      in
      List.find_map matches blocks

    let expect_codeblock_by_uuid (uuid : bytes) (blocks : p_block list) :
        int * p_code =
      match codeblock_by_uuid uuid blocks with
      | Some r -> r
      | None -> failwith "Internal error :("

    (* Interval -> codeblock list filtering *)
    let interval_codeblock_uuids (i : p_interval) =
      List.filter_map
        (fun (b : p_block) ->
          match b.value with `Code (c : p_code) -> Some c.uuid | _ -> None)
        i.blocks

  module CFG = struct
    (* Internal, pre-map CFG type *)
    type edge = bytes * bytes * edgetype
    type cfg = edge list

    (* This module is just an easy way to enforce uniqueness among CFG edges *)
    module Cfg = Set.Make (struct
      type t = edge

      let compare (ai, ao, _) (bi, bo, _) =
        match compare ai bi with 0 -> compare ao bo | c -> c
    end)

    let setflatmap f s =
      Cfg.fold
        (fun next acc -> Cfg.union (Cfg.of_list (f next)) acc)
        Cfg.empty s

    (* Constructs a subset-CFG for just the function we care about
     (identified by its entrypoint being the codeblock with "uuid")
  *)
    let construct_function_cfg (cfg : p_cfg) (uuid : bytes)
        (interval : p_interval) : cfg =
      (* ASSUMPTION: A function lives entirely inside one ByteInterval
       Therefore, filter cfgedges to those pointing back towards the given interval.
     *)
      let in_interval u =
        let interval_uuids = Lookup.interval_codeblock_uuids interval in
        let opt = List.find_opt (Bytes.equal u) interval_uuids in
        match opt with Some _ -> true | _ -> false
      in
      let relevant_edges =
        List.filter (fun (e : p_cfgedge) -> in_interval e.target_uuid) cfg.edges
      in

      (* Follow calls-and-returns back to the original function. *)
      let call_and_return (ct : CFG.Gtirb.Proto.EdgeType.t) (uuid : bytes) =
        let (relevant_returntype : CFG.Gtirb.Proto.EdgeType.t) =
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
        if Bytes.equal e.source_uuid u then (
          print_endline
            (Printf.sprintf "Found edge from %s to %s" (b64_bytes e.source_uuid)
               (b64_bytes u));
          match e.label with
          | Some l when l.type' == Type_Branch || l.type' == Type_Fallthrough ->
              Some [ (u, e.target_uuid, Linear) ]
          | Some l when l.type' == Type_Call || l.type' == Type_Syscall ->
              Some
                (List.map
                   (fun b -> (u, b, Call))
                   (call_and_return l.type' e.target_uuid))
          | _ -> None)
        else None
      in

      (* Turn a sub-CFG edge into a list of directly-connected sub-CFG edges *)
      let find_following_edges (e : edge) : edge list =
        let out =
          match e with
          | _, t, _ ->
              List.flatten
              @@ List.filter_map (from_source_block t) relevant_edges
        in
        print_int (List.length out);
        out
      in

      (* Get a list of "next" edges, add it to the current cfg, and if we gained edges, then recurse. *)
      let rec traverse_until_fixpoint (u : Cfg.t) : Cfg.t =
        let result = setflatmap find_following_edges u in
        let next = Cfg.union u result in
        if Cfg.compare u next == 0 then u else traverse_until_fixpoint next
      in

      Cfg.elements
        (traverse_until_fixpoint
           (Cfg.singleton (Bytes.of_string "", uuid, Entry)))

    (* Given a constructed sub-cfg, unpack just the block UUIDs from it *)
    let unpack_uuids (cfg : cfg) : bytes list =
      List.map (fun e -> match e with _, t, _ -> t) cfg

    let cfg_by_block (uuid : bytes) (cfg : cfg) : (bytes * edgetype) list =
      let matches edge =
        match edge with
        | i, o, t -> if Bytes.equal i uuid then Some (o, t) else None
      in
      List.filter_map matches cfg
  end
end
