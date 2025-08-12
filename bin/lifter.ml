(****************************************************************************************
  Wrapper around GTIRB serialised data, ASLp parsing, etc. Basically all the binary stuff.
*)
open Util

module Lifter : sig
  module Blocks : Map.S with type key = bytes

  type var = Register of int | PC | SP | PSTATE

  type instruction_summary = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
  }

  type edgetype = Linear | Call | Entry
  type outgoing_edge = bytes * edgetype

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    block_semantics : (int * instruction_summary) list;
  }

  val parse : Rif.IR.Gtirb.Proto.IR.t -> string -> bool -> blockdata Blocks.t
  val varEq : var -> var -> bool
end = struct
  (* Protobuf types, shouldn't be needed outside *)
  type p_ir = Rif.IR.Gtirb.Proto.IR.t
  type p_cfg = Rif.CFG.Gtirb.Proto.CFG.t
  type p_cfgedge = Rif.CFG.Gtirb.Proto.Edge.t
  type p_module = Rif.Module.Gtirb.Proto.Module.t
  type p_bo = Rif.Module.Gtirb.Proto.ByteOrder.t
  type p_symbol = Rif.Symbol.Gtirb.Proto.Symbol.t
  type p_section = Rif.Section.Gtirb.Proto.Section.t
  type p_interval = Rif.ByteInterval.Gtirb.Proto.ByteInterval.t
  type p_block = Rif.ByteInterval.Gtirb.Proto.Block.t
  type p_code = Rif.CodeBlock.Gtirb.Proto.CodeBlock.t
  type var = Register of int | PC | SP | PSTATE

  type instruction_summary = {
    read : var list;
    write : var list;
    load : var list;
    store : var list;
    fence : bool;
  }

  let varEq a b =
    match (a, b) with
    | PC, PC -> true
    | SP, SP -> true
    | PSTATE, PSTATE -> true
    | Register ai, Register bi -> ai == bi
    | _, _ -> false

  type edgetype = Linear | Call | Entry
  type outgoing_edge = bytes * edgetype

  type blockdata = {
    name : string;
    offset : int;
    outgoing_edges : outgoing_edge list;
    block_semantics : (int * instruction_summary) list;
  }

  module Blocks = Map.Make (Bytes)

  (****************************************************************************************
  Lookups of things inside GTIRB / GTS intermediate representation
*)
  module Lookup = struct
    (* Symbol -> block UUID lookup *)
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
  end

  (****************************************************************************************
  Construction of a CFG subset representing only the target "component" function
*)
  module CFG = struct
    (* Internal, pre-map CFG type *)
    type edge = bytes * bytes * edgetype
    type cfg = edge list

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
        let next = u @ List.concat_map find_following_edges u in
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
  end

  (****************************************************************************************
  Creating and filtering semantic data from ASLp
  *)
  let opcode_length = 4

  module Semantics = struct
    module Asl_lib = struct
      open LibASL

      let mkReg s = Register (int_of_string s)

      (*
        useful refs
        https://github.com/UQ-PAC/aslp/blob/partial_eval/libASL/symbolic.ml#L981
      *)
      class collector =
        object (this)
          inherit Asl_visitor.nopAslVisitor

          val mutable gathered_facts : instruction_summary =
            { read = []; write = []; load = []; store = []; fence = false }

          method get = gathered_facts

          (* track whether we're doing children of a memory-indexing function *)
          val mutable sub_load = false
          val mutable sub_store = false

          (* maintain uniqueness in our gathered facts *)
          method addReadReg (v : var) =
            match List.find_opt (varEq v) gathered_facts.read with
            | None ->
                gathered_facts <-
                  { gathered_facts with read = v :: gathered_facts.read }
            | _ -> ()

          method addWriteReg (v : var) =
            match List.find_opt (varEq v) gathered_facts.write with
            | None ->
                gathered_facts <-
                  { gathered_facts with write = v :: gathered_facts.write }
            | _ -> ()

          method addLoadReg (v : var) =
            match List.find_opt (varEq v) gathered_facts.load with
            | None ->
                gathered_facts <-
                  { gathered_facts with load = v :: gathered_facts.load }
            | _ -> ()

          method addStoreReg (v : var) =
            match List.find_opt (varEq v) gathered_facts.store with
            | None ->
                gathered_facts <-
                  { gathered_facts with store = v :: gathered_facts.store }
            | _ -> ()

          method! vstmt s =
            sub_load <- false;
            sub_store <- false;
            (match s with
            (* Assign to register, stack pointer, program counter, or PSTATE *)
            | Stmt_Assign
                (LExpr_Array (LExpr_Var (Ident n), Expr_LitInt i), _, _)
              when String.equal n "_R" ->
                this#addWriteReg (mkReg i)
            | Stmt_Assign (LExpr_Var (Ident n), _, _)
              when String.equal n "SP_EL0" ->
                this#addWriteReg SP
            | Stmt_Assign (LExpr_Var (Ident n), _, _) when String.equal n "_PC"
              ->
                this#addWriteReg PC
            | Stmt_Assign (LExpr_Field (LExpr_Var (Ident n), _), _, _)
              when String.equal n "PSTATE" ->
                this#addWriteReg PSTATE
            (* Calls to memory-affecting functions; mark it *)
            | Stmt_TCall (Ident n, _, _, _) when String.equal n "Mem.set.0" ->
                sub_store <- true
            | Stmt_TCall (Ident n, _, _, _) when String.equal n "Mem.read.0" ->
                sub_load <- true
            | _ -> ());
            DoChildren

          method! vexpr e =
            match e with
            (* if we're doing children of a memory-affecting function, or we find a memory-affecting function, collect as addresses
             otherwise, collect as normally read registers *)
            | Expr_TApply (Ident n, _, _) when String.equal n "Mem.set.0" ->
                ChangeDoChildrenPost
                  (e, this#exprAction ~action:this#addStoreReg)
            | Expr_TApply (Ident n, _, _) when String.equal n "Mem.read.0" ->
                ChangeDoChildrenPost (e, this#exprAction ~action:this#addLoadReg)
            | _ when sub_store ->
                ChangeDoChildrenPost
                  (e, this#exprAction ~action:this#addStoreReg)
            | _ when sub_load ->
                ChangeDoChildrenPost (e, this#exprAction ~action:this#addLoadReg)
            | _ ->
                ignore (this#exprAction e);
                DoChildren

          method exprAction ?(action = this#addReadReg) e =
            match e with
            (* Access of register, stack pointer, program counter, or PSTATE *)
            | Expr_Array (Expr_Var (Ident n), Expr_LitInt i)
              when String.equal n "_R" ->
                action (mkReg i);
                e
            | Expr_Var (Ident n) when String.equal n "SP_EL0" ->
                action SP;
                e
            | Expr_Var (Ident n) when String.equal n "_PC" ->
                action PC;
                e
            | Expr_Field (Expr_Var (Ident n), _) when String.equal n "PSTATE" ->
                action PSTATE;
                e
            | _ -> e

          (* Nothing for LExprs yet *)
          method! vlexpr _ = DoChildren
        end

      let collapse (ss : Asl_ast.stmt list) : instruction_summary =
        let c = new collector in
        ignore (Asl_visitor.visit_stmts c ss);
        c#get

      let lift_one_op (address : int) (op : bytes) =
        let opcode = Primops.mkBits 32 (Z.of_int32 (Bytes.get_int32_be op 0)) in
        (* Ignore unsupported opcodes *)
        match OfflineASL_pc.Offline.run ~pc:address opcode with
        | result -> result
        | exception _ -> []

      let lift_and_collapse (addr : int) (op : bytes) : instruction_summary =
        collapse (lift_one_op addr op)
    end

    let lift_block_from_interval (mod_endianness : bool) (cblock : p_code)
        (i : p_interval) (block_offset : int) : (int * instruction_summary) list
        =
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

      List.map (fun (i, op) -> (i, Asl_lib.lift_and_collapse i op)) opcodes
  end

  (****************************************************************************************
  Main Lifter interface
  *)
  let parse (ir : p_ir) (component : string) (verb : bool) =
    let modules = ir.modules in
    let symbols = List.concat_map (fun (m : p_module) -> m.symbols) modules in
    let cfg =
      match ir.cfg with Some c -> c | _ -> failwith "Bad IR: no CFG found!"
    in

    let component_block_uuid = Lookup.symbol_to_uuid symbols component in

    let do_interval (mod_endian : p_bo) (i : p_interval) :
        (bytes * blockdata) list option =
      if Option.is_some (Lookup.codeblock_by_uuid component_block_uuid i.blocks)
      then (
        (* This interval has the entrypoint block. Start extracting! *)
        let component_cfg =
          CFG.construct_function_cfg cfg component_block_uuid i
        in
        if verb then print_endline "[!] Constructed component CFG...";

        let needs_flipping = mod_endian = LittleEndian in

        let do_uuid (uuid : bytes) : blockdata =
          let offset, cblock = Lookup.expect_codeblock_by_uuid uuid i.blocks in
          {
            name = b64_bytes uuid;
            offset;
            outgoing_edges = CFG.cfg_by_block uuid component_cfg;
            block_semantics =
              Semantics.lift_block_from_interval needs_flipping cblock i offset;
          }
        in

        let result =
          List.map (fun u -> (u, do_uuid u)) (CFG.unpack_uuids component_cfg)
        in

        Some result)
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
end
