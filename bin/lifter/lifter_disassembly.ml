open Lifter_ir
open Lifter_elf
open Llvm_disass

module type LifterDisassembly = sig
  val do_all : LifterElf.blocks -> LifterIR.blocks
end

module LifterDisassembly = struct
  open LibASL
  module S = Map.Make (String)

  class collector =
    object (this)
      inherit Asl_visitor.nopAslVisitor
      val mutable cse_prop : Asl_ast.expr S.t = S.empty

      val mutable gathered_facts : LifterIR.instruction =
        {
          read = [];
          write = [];
          fence = false;
          semantics = [];
          readable = "";
          block = "";
          index = -1;
        }

      method get =
        (* Collapse Add (Add (v, 1), 2) into Add (v, 3) *)
        let collapse =
          let rec inner (count : int64) = function
            | LifterIR.Memory v -> LifterIR.Memory (inner 0L v)
            | Add (v, i) -> inner (Int64.add count i) v
            | v -> if count == 0L then v else LifterIR.Add (v, count)
          in
          List.map (fun e -> inner 0L e)
        in

        (* Scrub any top-level Adds *)
        let scrub =
          List.map (function LifterIR.Add (v, _) -> v | other -> other)
        in

        let process = fun v -> collapse v |> scrub in

        {
          gathered_facts with
          read = process gathered_facts.read;
          write = process gathered_facts.write;
        }

      method passin map = cse_prop <- map

      (* maintain uniqueness in our gathered facts *)
      method addReadReg (v : LifterIR.var) =
        match List.find_opt (LifterIR.var_eq v) gathered_facts.read with
        | None ->
            gathered_facts <-
              { gathered_facts with read = v :: gathered_facts.read }
        | _ -> ()

      method addWriteReg (v : LifterIR.var) =
        match List.find_opt (LifterIR.var_eq v) gathered_facts.write with
        | None ->
            gathered_facts <-
              { gathered_facts with write = v :: gathered_facts.write }
        | _ -> ()

      method sanityOnlyRead =
        if List.length gathered_facts.write > 0 then
          failwith "Internal error :(";
        gathered_facts.read

      method! vstmt s =
        let takeReg : Asl_ast.lexpr -> LifterIR.var option = function
          | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
              Some (Register (int_of_string i))
          | LExpr_Var (Ident "SP_EL0") -> Some SP
          | LExpr_Var (Ident "_PC") -> Some PC
          | LExpr_Var (Ident "BTypeNext") -> Some PSTATE
          | LExpr_Field (LExpr_Var (Ident "PSTATE"), _) -> Some PSTATE
          | _ -> None
        in
        match s with
        (* Assign to register, stack pointer, program counter, or PSTATE *)
        | Stmt_Assign (lhs, e, _) ->
            Option.iter this#addWriteReg (takeReg lhs);
            ignore (Asl_visitor.visit_expr this e);
            SkipChildren
        (* Calls to memory-affecting functions; mark it *)
        | Stmt_TCall (FIdent ("Mem.set", _), _, addr :: values, _) ->
            let subcontract e =
              let memc = new collector in
              memc#passin cse_prop;
              ignore @@ Asl_visitor.visit_expr memc e;
              memc#sanityOnlyRead
            in

            List.iter
              (fun v -> this#addWriteReg (LifterIR.Memory v))
              (subcontract addr);
            ignore (Asl_visitor.visit_exprs this values);
            SkipChildren
        | Stmt_TCall (FIdent ("Mem.read", _), _, addr :: values, _) ->
            failwith "stmt tcall read"
        | Stmt_ConstDecl (_, Ident n, exp, _) ->
            cse_prop <- S.add n exp cse_prop;
            DoChildren
        | _ -> DoChildren

      (* If this expression is directly translatable to a LifterIR.Var, then do that & don't recurse *)
      method! vexpr e =
        if Option.is_some @@ this#takeExpr e then SkipChildren else DoChildren

      (*
        If the expression is a base-level variable that we care about,
          add it to the read regs, and return Some ()
        If the expression is an add where the LHS is a base-level variable
          that we care about, parse it and return Some ()
        Otherwise, return None
      *)
      method takeExpr : Asl_ast.expr -> unit option =
        let takeOff : Asl_ast.expr -> int64 = function
          | Expr_LitBits b -> Int64.of_string ("0b" ^ b)
          | _ -> Int64.of_int 0
        in
        let rec takeReg : Asl_ast.expr -> LifterIR.var option = function
          | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
              Some (Register (int_of_string i))
          | Expr_Var (Ident "SP_EL0") -> Some SP
          | Expr_Var (Ident "_PC") -> Some PC
          | Expr_Var (Ident "BTypeNext") -> Some PSTATE
          | Expr_Var (Ident n) -> Option.bind (S.find_opt n cse_prop) takeReg
          | Expr_Field (Expr_Var (Ident "PSTATE"), _) -> Some PSTATE
          | Expr_TApply (FIdent ("add_bits", _), _, [ reg; off ]) ->
              takeReg reg |> Option.map (fun v -> LifterIR.Add (v, takeOff off))
          | Expr_TApply (FIdent ("Mem.read", _), _, addr :: _tl) ->
              takeReg addr |> Option.map (fun v -> LifterIR.Memory v)
          | _ -> None
        in
        fun e -> takeReg e |> Option.map this#addReadReg
    end

  (* Make env separately, we don't need to re-make it every time *)
  let env =
    Arm_env.aarch64_evaluation_environment ()
    |> Option.get_or "Failed to create aarch64 environment"

  let lift _pc op = Dis.retrieveDisassembly env (Dis.build_env env) op

  let collapse (ss : Asl_ast.stmt list) : LifterIR.instruction =
    let c = new collector in
    ignore (Asl_visitor.visit_stmts c ss);
    { (c#get) with semantics = ss }

  let lift_one_op (verb : bool) ((address, op) : int * bytes) :
      Asl_ast.stmt list =
    let opcode = Printf.sprintf "0x%08lx" (Bytes.get_int32_be op 0) in

    (* Don't die on unsupported opcodes *)
    match lift address opcode with
    | result -> result
    | exception _ ->
        if verb then print_endline ("[?] Unsupported opcode detected: " ^ opcode);
        []

  let lift_and_summarise verb block addr op =
    let r = lift_one_op verb (addr, op) |> collapse in
    let endian_reverse b =
      let len = Bytes.length b in
      let getrev i = Bytes.get b (len - 1 - i) in
      Bytes.init len getrev
    in
    {
      r with
      block;
      index = addr;
      readable =
        endian_reverse op |> assembly_of_bytes_opt |> Option.value ~default:"";
    }

  let lift_all verb map =
    let a =
      LifterElf.B.bindings map
      |> List.fold_left
           (fun acc (k, v) ->
             let do_instructions bname (is : (int * bytes) list) :
                 LifterIR.instruction LifterIR.I.t =
               List.fold_left
                 (fun acc (k, v) ->
                   LifterIR.I.add k (lift_and_summarise verb bname k v) acc)
                 LifterIR.I.empty is
             in

             let do_block (b : LifterElf.extracted_block) : LifterIR.block =
               {
                 name = b.name;
                 offset = b.address;
                 edges = b.edges;
                 instructions = do_instructions b.name b.instructions;
               }
             in

             LifterIR.B.add k (do_block v) acc)
           LifterIR.B.empty
    in
    a
end
