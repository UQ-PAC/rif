open Lifter_ir
open Lifter_elf

module type LifterDisassembly = sig
  val do_all : LifterElf.blocks -> LifterIR.blocks
end

module LifterDisassembly = struct
  open LibASL

  class collector = object (this)
    inherit Asl_visitor.nopAslVisitor
    val mutable gathered_facts : LifterIR.instruction =
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
    method addReadReg (v : LifterIR.var) =
      match List.find_opt (LifterIR.var_eq v) gathered_facts.read with
      | None ->
        gathered_facts <- { gathered_facts with read = v :: gathered_facts.read }
      | _ -> ()

    method addWriteReg (v : LifterIR.var) =
      match List.find_opt (LifterIR.var_eq v) gathered_facts.write with
      | None ->
        gathered_facts <- { gathered_facts with write = v :: gathered_facts.write }
      | _ -> ()

    method addLoadReg (v : LifterIR.var) =
      match List.find_opt (LifterIR.var_eq v) gathered_facts.load with
      | None ->
        gathered_facts <- { gathered_facts with load = v :: gathered_facts.load }
      | _ -> ()

    method addLoadRegs (vs : LifterIR.var list) = List.iter this#addLoadReg vs

    method addStoreReg (v : LifterIR.var) =
      match List.find_opt (LifterIR.var_eq v) gathered_facts.store with
      | None ->
        gathered_facts <- { gathered_facts with store = v :: gathered_facts.store }
      | _ -> ()

    method addStoreRegs (vs : LifterIR.var list) = List.iter this#addStoreReg vs

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
          this#addWriteReg (Register (int_of_string i));
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
          action (Register (int_of_string i));
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

  let lift _pc op = 
    let env = Arm_env.aarch64_evaluation_environment () |> Option.get in
    Dis.retrieveDisassembly env (Dis.build_env env) op

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

    let collapse (ss : Asl_ast.stmt list) : LifterIR.instruction =
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

  let lift_all map =
    LifterElf.B.bindings map |>
    List.fold_left (fun acc (k, v) ->
      let do_block (b : LifterElf.extracted_block) : LifterIR.block =
        {
        name = b.name;
        offset = b.address;
        edges = b.edges;
        instructions = LifterIR.I.empty
        }
      in

      LifterIR.B.add k (do_block v) acc
    ) LifterIR.B.empty
end
