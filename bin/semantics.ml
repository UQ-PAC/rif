open Lifter

(*
  Wrapper around architecture-specific or ASLi-specific information.
*)
module Semantics = struct
  let instruction_width = 4

  let generate_addresses (block : Lifter.blockdata) =
    List.mapi
      (fun ins _ -> block.offset + (ins * instruction_width))
      block.block_semantics

  type var = Register of int | PC | SP | PSTATE
  type facts = { read : var list; write : var list; addr : var list }

  (* make a register given a string *)
  let mkReg s = Register (int_of_string s)

  (* equality on `var` type *)
  let varEq a b =
    match (a, b) with
    | PC, PC -> true
    | SP, SP -> true
    | PSTATE, PSTATE -> true
    | Register ai, Register bi -> ai == bi
    | _, _ -> false

  (* does our set of facts include a write to the program counter *)
  let hasCtrl (f : facts) =
    match List.find_opt (varEq PC) f.write with Some _ -> true | _ -> false

  module Lib = struct
    open LibASL

    (*
        useful refs
        https://github.com/UQ-PAC/aslp/blob/partial_eval/libASL/symbolic.ml#L981
    *)

    (* 3 special-cases we care about: the registers, the program counter, the stack pointer
       3 general-cases we have to parse anyway

      LExpr_Array(LExpr_Var("_R"), x) | Expr_Array(Expr_Var("_R"), x) --> Register x
      LExpr_Var("_PC") | Expr_Var("_PC")                              --> PC
      LExpr_Var("SP_EL0") | Expr_Var("SP_EL0")                        --> SP
      
    *)
    class collector =
      object (this)
        inherit Asl_visitor.nopAslVisitor

        val mutable gathered_facts : facts =
          { read = []; write = []; addr = [] }

        method get = gathered_facts

        (* track whether we're doing children of a memory-indexing function *)
        val mutable sub_addr = false

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

        method addAddrReg (v : var) =
          match List.find_opt (varEq v) gathered_facts.addr with
          | None ->
              gathered_facts <-
                { gathered_facts with addr = v :: gathered_facts.addr }
          | _ -> ()

        method! vstmt s =
          sub_addr <- false;
          (match s with
          (* Assign to register, stack pointer, program counter, or PSTATE *)
          | Stmt_Assign (LExpr_Array (LExpr_Var (Ident n), Expr_LitInt i), _, _)
            when String.equal n "_R" ->
              this#addWriteReg (mkReg i)
          | Stmt_Assign (LExpr_Var (Ident n), _, _) when String.equal n "SP_EL0"
            ->
              this#addWriteReg SP
          | Stmt_Assign (LExpr_Var (Ident n), _, _) when String.equal n "_PC" ->
              this#addWriteReg PC
          | Stmt_Assign (LExpr_Field (LExpr_Var (Ident n), _), _, _)
            when String.equal n "PSTATE" ->
              this#addWriteReg PSTATE
          (* Calls to memory-affecting functions; mark it *)
          | Stmt_TCall (Ident n, _, _, _) when String.equal n "Mem.set.0" ->
              sub_addr <- true
          | Stmt_TCall (Ident n, _, _, _) when String.equal n "Mem.read.0" ->
              sub_addr <- true
          | _ -> ());
          DoChildren

        method! vexpr e =
          match e with
          (* if we're doing children of a memory-affecting function, or we find a memory-affecting function, collect as addresses
             otherwise, collect as normally read registers *)
          | Expr_TApply (Ident n, _, _) when String.equal n "Mem.set.0" ->
              ChangeDoChildrenPost (e, this#exprAction ~action:this#addAddrReg)
          | Expr_TApply (Ident n, _, _) when String.equal n "Mem.read.0" ->
              ChangeDoChildrenPost (e, this#exprAction ~action:this#addAddrReg)
          | _ when sub_addr ->
              ChangeDoChildrenPost (e, this#exprAction ~action:this#addAddrReg)
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

    (* Use above visitor to collapse a stmt list into just facts *)
    let collapse (ss : Asl_ast.stmt list) : facts =
      let c = new collector in
      ignore (Asl_visitor.visit_stmts c ss);
      c#get

    (* parse ASL into AST *)
    let parse_all_stmts =
      let parse_one_stmt =
        LoadASL.read_stmt @@ Tcheck.Env.mkEnv @@ Tcheck.GlobalEnv.mkempty @@ ()
      in
      List.map parse_one_stmt
  end

  let facts ss = Lib.collapse @@ Lib.parse_all_stmts ss
end
