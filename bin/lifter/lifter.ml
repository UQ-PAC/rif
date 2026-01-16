(****************************************************************************************
  Wrapper around GTIRB serialised data, ASLp parsing, etc. Basically all the binary stuff.
*)
module Lifter : sig
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
end = struct
  (* Protobuf types, shouldn't be needed outside *)
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

  (****************************************************************************************
  Creating and filtering semantic data from ASLp
  *)
  let opcode_length = 4

  module Semantics = struct
    module Asl_lib = struct
      open LibASL

      let env =
        match Arm_env.aarch64_evaluation_environment () with
        | Some e -> e
        | None -> failwith "AAA"

      let lift _pc op = Dis.retrieveDisassembly env (Dis.build_env env) op
      let mkReg s = Register (int_of_string s)

      (*
        useful refs
        https://github.com/UQ-PAC/aslp/blob/partial_eval/libASL/symbolic.ml#L981
      *)
      class collector =
        object (this)
          inherit Asl_visitor.nopAslVisitor

          val mutable gathered_facts : instruction =
            {
              read = [];
              write = [];
              load = [];
              store = [];
              fence = false;
              semantics = [];
            }

          val mutable taints = []
          method get = gathered_facts

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

          method addLoadRegs (vs : var list) = List.iter this#addLoadReg vs

          method addStoreReg (v : var) =
            match List.find_opt (varEq v) gathered_facts.store with
            | None ->
                gathered_facts <-
                  { gathered_facts with store = v :: gathered_facts.store }
            | _ -> ()

          method addStoreRegs (vs : var list) = List.iter this#addStoreReg vs

          method sanityOnlyRead =
            if
              List.length gathered_facts.write > 0
              || List.length gathered_facts.load > 0
              || List.length gathered_facts.store > 0
            then failwith "Internal error :(";
            gathered_facts.read

          method! vstmt s =
            match s with
            (* Assign to register, stack pointer, program counter, or PSTATE *)
            | Stmt_Assign
                (LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i), _, _) ->
                this#addWriteReg (mkReg i);
                DoChildren
            | Stmt_Assign (LExpr_Var (Ident "SP_EL0"), _, _) ->
                this#addWriteReg SP;
                DoChildren
            | Stmt_Assign (LExpr_Var (Ident "_PC"), _, _) ->
                this#addWriteReg PC;
                DoChildren
            | Stmt_Assign (LExpr_Field (LExpr_Var (Ident "PSTATE"), _), _, _) ->
                this#addWriteReg PSTATE;
                DoChildren
            (* Calls to memory-affecting functions; mark it *)
            | Stmt_TCall (FIdent ("Mem.set", _), _, addr :: values, _) ->
                this#addStoreRegs (this#subcontract addr);
                ignore (Asl_visitor.visit_exprs this values);
                SkipChildren
            | Stmt_TCall (FIdent ("Mem.read", _), _, addr :: values, _) ->
                this#addLoadRegs (this#subcontract addr);
                ignore (Asl_visitor.visit_exprs this values);
                SkipChildren
            | _ -> DoChildren

          method! vexpr e =
            match e with
            (* if we're doing children of a memory-affecting function, or we find a memory-affecting function, collect as addresses
             otherwise, collect as normally read registers *)
            | Expr_TApply (FIdent ("Mem.set", _), _, addr :: values) ->
                this#addStoreRegs (this#subcontract addr);
                ignore (Asl_visitor.visit_exprs this values);
                SkipChildren
            | Expr_TApply (FIdent ("Mem.read", _), _, addr :: values) ->
                this#addLoadRegs (this#subcontract addr);
                ignore (Asl_visitor.visit_exprs this values);
                SkipChildren
            | _ ->
                ignore (this#exprAction e);
                DoChildren

          method subcontract e =
            let memc = new collector in
            ignore (Asl_visitor.visit_expr memc e);
            memc#sanityOnlyRead

          method exprAction ?(action = this#addReadReg) e =
            match e with
            (* Access of register, stack pointer, program counter, or PSTATE *)
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                action (mkReg i);
                e
            | Expr_Var (Ident "SP_EL0") ->
                action SP;
                e
            | Expr_Var (Ident "_PC") ->
                action PC;
                e
            | Expr_Field (Expr_Var (Ident "PSTATE"), _) ->
                action PSTATE;
                e
            | _ -> e

          (* Nothing for arbitrary LExprs *)
          method! vlexpr _ = DoChildren
        end

      (* 
      class cleanup =
        object (_this)
          inherit Asl_visitor.nopAslVisitor

          method! vexpr e =
            match e with
            | Expr_TApply (FIdent ("Mem.set", _), _, addr :: _values) ->
                ChangeTo addr
            | Expr_TApply (FIdent ("Mem.read", _), _, addr :: _values) ->
                ChangeTo addr
            | _ -> DoChildren
        end
      *)

      let collapse (ss : Asl_ast.stmt list) : instruction =
        let c = new collector in
        ignore (Asl_visitor.visit_stmts c ss);
        { (c#get) with semantics = ss }

      let lift_one_op ((address, op) : int * bytes) : Asl_ast.stmt list =
        let opcode = Printf.sprintf "0x%08lx" (Bytes.get_int32_be op 0) in
        (* Ignore unsupported opcodes *)
        match lift address opcode with
        | result -> result
        | exception _ ->
            print_endline "error";
            []
    end

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
  module Cvc = struct
    open LibASL
    open Cvc5

    type errnode =
      | Slice of Asl_ast.slice
      | LExpr of Asl_ast.lexpr
      | Expr of Asl_ast.expr
      | Addr of Asl_ast.expr
      | Stmt of Asl_ast.stmt
      | Fun of string

    let unexpected (node : errnode) =
      match node with
      | Slice n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected slice %s"
               (Utils.to_string @@ Asl_utils.PP.pp_slice n))
      | LExpr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected lexpr %s"
               (Asl_utils.pp_lexpr n))
      | Expr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected expr %s"
               (Asl_utils.pp_expr n))
      | Addr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected address expr %s"
               (Asl_utils.pp_expr n))
      | Stmt n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected stmt %s"
               (Asl_utils.pp_stmt n))
      | Fun n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected function %s" n)

    class translator =
      object (this)
        val mutable ivars = Util.Cvc.TermMap.empty
        val mutable updated : string list = []

        method was_updated s =
          Option.is_some (List.find_opt (String.equal s) updated)

        method cvc_of_stmtlist (tm : TermManager.tm) (fromv : Util.Cvc.terms)
            (tov : Util.Cvc.terms) (stmts : Asl_ast.stmt list) =
          let cvc_of_slice (s : Asl_ast.slice) : Op.op =
            match s with
            | Slice_LoWd (Expr_LitInt l, Expr_LitInt h) ->
                Op.mk_op tm Kind.Bitvector_extract
                  (Array.of_list [ int_of_string h - 1; int_of_string l ])
            | _ -> unexpected @@ Slice s
          in

          let cvc_of_lexpr (e : Asl_ast.lexpr) : Term.term =
            match e with
            | LExpr_Var (Ident "SP_EL0") ->
                updated <- "SP" :: updated;
                Util.Cvc.find_sp tov
            | LExpr_Var (Ident "_PC") ->
                updated <- "PC" :: updated;
                Util.Cvc.find_pc tov
            | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
                updated <- ("R" ^ i) :: updated;
                Util.Cvc.find_reg tov i
            | _ -> unexpected @@ LExpr e
          in

          let cvc_of_function (s : string) : Kind.t =
            match s with
            (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
            | _ when String.equal s "ZeroExtend" -> Kind.Null_term
            | _ when String.equal s "add_bits" -> Kind.Add
            | _ -> unexpected @@ Fun s
          in

          let cvc_of_addr (write : bool) (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                if write then updated <- ("MR" ^ i) :: updated;
                Util.Cvc.find_mem_reg (if write then tov else fromv) i
            | Expr_TApply
                ( FIdent ("add_bits", _),
                  _,
                  [
                    Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i);
                    Expr_LitBits _;
                  ] ) ->
                (* Collapse mem[R1 + X] into mem[R0] *)
                if write then updated <- ("MR" ^ i) :: updated;
                Util.Cvc.find_mem_reg (if write then tov else fromv) i
            | _ -> unexpected @@ Addr e
          in

          let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                Util.Cvc.find_reg fromv i
            | Expr_Var (Ident n) -> Util.Cvc.TermMap.find n ivars
            | Expr_TApply (FIdent ("Mem.set", _), _, es) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Term.mk_term tm Kind.Equal
                  (Array.of_list [ cvc_of_addr true addr; cvc_of_expr value ])
            | Expr_TApply (FIdent ("Mem.read", _), _, es) ->
                cvc_of_addr false (List.hd es)
            | Expr_TApply (FIdent (f, _), _, es) -> (
                match cvc_of_function f with
                | Kind.Null_term -> cvc_of_expr (List.hd es)
                | k ->
                    Term.mk_term tm k (Array.of_list (List.map cvc_of_expr es)))
            | Expr_Slices (e, slices) ->
                (* Pretend slices aren't real *)
                ignore (List.map cvc_of_slice slices);
                cvc_of_expr e
                (* let sliced =
                  List.fold_left
                    (fun acc s ->
                      Term.mk_term_op tm (cvc_of_slice s)
                        (Array.of_list [ acc ]))
                    (cvc_of_expr e) slices *)
            | Expr_Field _ -> Term.mk_true tm
            | Expr_LitInt s -> Term.mk_int tm @@ int_of_string s
            | Expr_LitBits s ->
                Term.mk_int tm @@ Int64.to_int @@ Int64.of_string @@ "0b" ^ s
            | _ -> unexpected @@ Expr e
          in

          let cvc_of_stmt (s : Asl_ast.stmt) =
            match s with
            | Stmt_Assign (l, r, _) ->
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list [ cvc_of_lexpr l; cvc_of_expr r ]))
            | Stmt_ConstDecl (_, Ident n, exp, _) ->
                ivars <- Util.Cvc.TermMap.add n (cvc_of_expr exp) ivars;
                None
            | Stmt_VarDecl _ -> None
            | Stmt_VarDeclsNoInit _ -> None
            | Stmt_Assert _ -> None
            | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list
                        [ cvc_of_addr true addr; cvc_of_expr value ]))
            | Stmt_TCall (FIdent (_f, _), _, _es, _) -> None
            | Stmt_If _ -> None
            | Stmt_Throw _ -> None
            | _ -> unexpected @@ Stmt s
          in

          let updates = List.filter_map cvc_of_stmt stmts in
          let no_updates =
            Util.Cvc.TermMap.fold
              (fun key term acc ->
                if this#was_updated key then acc
                else
                  Term.mk_term tm Kind.Equal
                    (Array.of_list [ term; Util.Cvc.TermMap.find key tov ])
                  :: acc)
              fromv []
          in
          updates @ no_updates
      end
  end

  let semantics_to_cvc tm fromv tov stmts =
    (new Cvc.translator)#cvc_of_stmtlist tm fromv tov stmts

  let cvc_of_inst tm fromv tov (i : instruction) =
    semantics_to_cvc tm fromv tov i.semantics
end
