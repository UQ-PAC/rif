open Cvc5
open Lifter
open LibASL
open Solver_utils
open Solver_state

module type SolverInst = sig
  val translate :
    TermManager.tm -> Lifter.IR.instruction -> SolverState.state_function
end

module SolverInst : SolverInst = struct
  module S = Map.Make (String)

  class translator =
    object (this)
      val mutable cse_prop : Term.term S.t = S.empty

      method stmtlist tm state =
        let input_term n =
          SolverState.find_opt state n
          |> Option.get_or "Instruction references undefined variable?"
        in

        let _cvc_of_slice (s : Asl_ast.slice) : Op.op =
          match s with _ -> SolverUtils.unexpected @@ Slice s
        in

        let cvc_of_lexpr (e : Asl_ast.lexpr) : string =
          (* LExpr values are collected as "outputs" for functions *)
          match e with
          | LExpr_Var (Ident "SP_EL0") -> "SP"
          | LExpr_Var (Ident "_PC") -> "PC"
          | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) -> "R" ^ i
          | _ -> SolverUtils.unexpected @@ LExpr e
        in

        let cvc_of_function (s : string) : Kind.t =
          (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
          match s with
          | _ when String.equal s "ZeroExtend" -> Kind.Null_term
          | _ when String.equal s "add_bits" -> Kind.Add
          | _ when String.equal s "Mem.write" ->
              failwith "Found mem-write as RHS expression...?"
          | _ -> SolverUtils.unexpected @@ Fun s
        in

        let cvc_of_write (e : Asl_ast.expr) : string =
          match e with
          | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) -> "MR" ^ i
          | Expr_TApply
              ( FIdent ("add_bits", _),
                _,
                [
                  Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i);
                  Expr_LitBits b;
                ] ) ->
              Printf.sprintf "MR%s+%i" i (int_of_string ("0b" ^ b))
          | _ -> SolverUtils.unexpected @@ Addr e
        in

        let cvc_of_read (e : Asl_ast.expr) : Term.term =
          input_term @@ cvc_of_write e
        in

        let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
          match e with
          | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
              input_term ("R" ^ i)
          | Expr_Var (Ident n) -> S.find n cse_prop
          | Expr_TApply (FIdent ("Mem.read", _), _, es) ->
              cvc_of_read (List.hd es)
          | Expr_TApply (FIdent (f, _), _, es) -> (
              match cvc_of_function f with
              | Kind.Null_term -> cvc_of_expr (List.hd es)
              | k -> Term.mk_term tm k (Array.of_list (List.map cvc_of_expr es))
              )
          | Expr_Slices (e, slices) ->
              (* Skip over slices for now
              let _bits = List.map cvc_of_slice slices in *)
              cvc_of_expr e
          | Expr_LitInt s -> Term.mk_int tm @@ int_of_string s
          | Expr_LitBits s ->
              Term.mk_int tm @@ Int64.to_int @@ Int64.of_string @@ "0b" ^ s
          | Expr_Field _ | _ -> SolverUtils.unexpected @@ Expr e
        in

        let cvc_of_stmt (s : Asl_ast.stmt) : (string -> Term.term option) option
            =
          match s with
          | Stmt_Assign (l, r, _) ->
              Some
                (fun s ->
                  if String.equal s (cvc_of_lexpr l) then Some (cvc_of_expr r)
                  else None)
          | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
              let addr = List.hd es in
              let value = List.hd (List.rev es) in
              Some
                (fun s ->
                  if String.equal s (cvc_of_write addr) then
                    Some (cvc_of_expr value)
                  else None)
          | Stmt_ConstDecl (_, Ident n, exp, _) ->
              cse_prop <- S.add n (cvc_of_expr exp) cse_prop;
              None
          | Stmt_VarDecl _ | Stmt_VarDeclsNoInit _ | Stmt_Assert _
          | Stmt_TCall (FIdent (_, _), _, _, _)
          | Stmt_If _ | Stmt_Throw _ | _ ->
              SolverUtils.unexpected @@ Stmt s
        in

        cse_prop <- S.empty;
        List.filter_map cvc_of_stmt
    end

  let translate tm (i : Lifter.IR.instruction) state =
    let fns = (new translator)#stmtlist tm state i.semantics in

    fun name ->
      List.find_map (fun f -> f name) fns
      |>
      (* If the instruction does not modify <name> then just find it in the input *)
      function
      | None -> SolverState.find_opt state name
      | value -> value
end
