open Cvc5
open Lifter
open LibASL
open Solver_utils
open Solver_state

module type SolverInst = sig
  val translate :
    TermManager.tm -> Lifter.IR.instruction -> SolverState.state_function

  val pair_taints :
    Lifter.IR.instruction * Lifter.IR.instruction -> (string * string list) list
end

module SolverInst : SolverInst = struct
  module S = Map.Make (String)

  let name_of_lexpr (e : Asl_ast.lexpr) : string =
    (* LExpr values are collected as "outputs" for functions *)
    (match e with
      | LExpr_Var (Ident "SP_EL0") -> Lifter.IR.SP
      | LExpr_Var (Ident "_PC") -> Lifter.IR.PC
      | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
          Lifter.IR.Register (int_of_string i)
      | LExpr_Var (Ident "BTypeNext") -> Lifter.IR.PSTATE
      | LExpr_Field (LExpr_Var (Ident "PSTATE"), _) -> Lifter.IR.PSTATE
      | _ -> SolverUtils.unexpected @@ LExpr e)
    |> Lifter.IR.string_of_var

  let kind_of_func_name (s : string) : Kind.t =
    (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
    match s with
    | _ when String.equal s "ZeroExtend" -> Kind.Null_term
    | _ when String.equal s "add_bits" -> Kind.Add
    | _ when String.equal s "Mem.write" ->
        failwith "Found mem-write as RHS expression...?"
    | _ -> SolverUtils.unexpected @@ Fun s

  let cvc_of_slice (s : Asl_ast.slice) : Op.op =
    match s with _ -> SolverUtils.unexpected @@ Slice s

  class ast_traverse =
    object (this)
      val mutable cse_prop : Asl_ast.expr S.t = S.empty

      method ir_of_expr e =
        let dump_fail s v =
          if Option.is_none v then SolverUtils.unexpected @@ Expr e else v
        in

        (* If memory, then maybe an add of variables or variables
           Otherwise just variables
         *)
        let takeOff : Asl_ast.expr -> int64 = function
          | Expr_LitBits b -> Int64.of_string ("0b" ^ b)
          | _ -> Int64.of_int 0
        in
        let rec lv1 (e : Asl_ast.expr) : Lifter.IR.var option =
          match e with
          | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
              Some (Register (int_of_string i))
          | Expr_Var (Ident "SP_EL0") -> Some SP
          | Expr_Var (Ident "_PC") -> Some PC
          | Expr_Var (Ident "BTypeNext") -> Some PSTATE
          | Expr_Field (Expr_Var (Ident "PSTATE"), _) -> Some PSTATE
          | Expr_Var (Ident n) when S.find_opt n cse_prop |> Option.is_some ->
              S.find n cse_prop |> lv2
          | v -> SolverUtils.unexpected @@ Expr e (* dump_fail "lv1" None *)
        and lv2 : Asl_ast.expr -> Lifter.IR.var option = function
          | Expr_TApply (FIdent ("add_bits", _), _, [ reg; off ]) ->
              lv1 reg |> dump_fail "lv2"
              |> Option.map (fun v -> Lifter.IR.Add (v, takeOff off))
          | v -> lv1 v
        and lv3 : Asl_ast.expr -> Lifter.IR.var option = function
          | Expr_TApply (FIdent ("Mem.read", _), _, addr :: _tl) ->
              lv2 addr |> dump_fail "lv3"
              |> Option.map (fun v -> Lifter.IR.Memory v)
          | v -> lv1 v
        in

        lv3 e |> dump_fail "top"
        |> Option.map (fun v ->
            let rec inner (count : int64) = function
              | Lifter.IR.Memory v -> Lifter.IR.Memory (inner 0L v)
              | Lifter.IR.Add (v, i) -> inner (Int64.add count i) v
              | v -> if count == 0L then v else Lifter.IR.Add (v, count)
            in
            inner 0L v)
        |> Option.map Lifter.IR.string_of_var

      (* We know we're under a stmt_tcall Mem.set, so construct a dummy Mem.read
         to tell `takeExpr` that we should look for memory-at-E variables
      *)
      method ir_of_write (e : Asl_ast.expr) : string =
        this#ir_of_expr (Expr_TApply (FIdent ("Mem.read", 0), [], [ e ]))
        |> Option.get

      method translate_stmtlist tm state =
        let input_term n =
          SolverState.find_opt state n
          |> Option.get_or "Instruction references undefined variable?"
        in

        let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
          match e with
          | Expr_LitInt s -> Term.mk_int tm @@ int_of_string s
          | Expr_LitBits s -> Term.mk_int64 tm @@ Int64.of_string @@ "0b" ^ s
          | Expr_TApply (FIdent (n, _), _, vs)
            when not @@ String.equal n "Mem.read" -> (
              kind_of_func_name n |> function
              | Kind.Null_term -> List.hd vs |> cvc_of_expr
              | v -> Term.mk_term tm v (List.map cvc_of_expr vs |> Array.of_list)
              )
          | Expr_Var (Ident n) when S.find_opt n cse_prop |> Option.is_some ->
              S.find n cse_prop |> cvc_of_expr
          | Expr_Slices (v, _) | v ->
              this#ir_of_expr v |> Option.map input_term |> Option.get
        in

        let cvc_of_stmt (s : Asl_ast.stmt) : (string -> Term.term option) option
            =
          match s with
          | Stmt_Assign (l, r, _) ->
              Some
                (fun s ->
                  if String.equal s (name_of_lexpr l) then Some (cvc_of_expr r)
                  else None)
          | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
              let addr = List.hd es in
              let value = List.hd (List.rev es) in
              Some
                (fun s ->
                  if String.equal s (this#ir_of_write addr) then
                    Some (cvc_of_expr value)
                  else None)
          | Stmt_ConstDecl (_, Ident n, exp, _) ->
              cse_prop <- S.add n exp cse_prop;
              None
          | Stmt_VarDecl _ | Stmt_VarDeclsNoInit _ | Stmt_Assert _
          | Stmt_TCall (FIdent (_, _), _, _, _)
          | Stmt_If _ | Stmt_Throw _ | _ ->
              SolverUtils.unexpected @@ Stmt s
        in

        cse_prop <- S.empty;
        List.filter_map cvc_of_stmt

      method calculate_taints : Asl_ast.stmt list -> string list S.t =
        let add k v m =
          match S.find_opt k m with
          | None -> S.add k v m
          | Some ts -> S.add k (v @ ts) m
        in

        let rec taint_expr : Asl_ast.expr -> string list = function
          | Expr_TApply (FIdent (n, _), _, vs)
            when not @@ String.equal n "Mem.read" ->
              List.flatten @@ List.map taint_expr vs
          | Expr_LitInt _ | Expr_LitHex _ | Expr_LitReal _ | Expr_LitBits _
          | Expr_LitMask _ | Expr_LitString _ ->
              []
          | Expr_Var (Ident n) when S.find_opt n cse_prop |> Option.is_some ->
              S.find n cse_prop |> taint_expr
          | Expr_Slices (v, _) | Expr_Unop (_, v) | v ->
              [ this#ir_of_expr v ] |> List.filter_map (fun i -> i)
        in

        let taint_stmt taints (s : Asl_ast.stmt) : string list S.t =
          match s with
          | Stmt_Assign (l, r, _) -> (
              match taint_expr r with
              | t :: ts -> add (name_of_lexpr l) (t :: ts) taints
              | [] -> S.remove (name_of_lexpr l) taints)
          | Stmt_TCall (FIdent ("Mem.set", _), _, addr :: es, _) -> (
              match List.rev es |> List.hd |> taint_expr with
              | t :: ts -> S.add (this#ir_of_write addr) (t :: ts) taints
              | [] -> S.remove (this#ir_of_write addr) taints)
          | Stmt_ConstDecl (_, Ident n, exp, _) ->
              cse_prop <- S.add n exp cse_prop;
              taints
          | _ -> taints
        in
        cse_prop <- S.empty;
        List.fold_left taint_stmt S.empty
    end

  let translate tm (i : Lifter.IR.instruction) state =
    let fns = (new ast_traverse)#translate_stmtlist tm state i.semantics in

    fun name ->
      List.find_map (fun f -> f name) fns
      |>
      (* If the instruction does not modify <name> then just find it in the input *)
      function
      | None -> SolverState.find_opt state name
      | value -> value

  let taints (i : Lifter.IR.instruction) : string list S.t =
    let taints = (new ast_traverse)#calculate_taints i.semantics in

    let reachable =
      S.bindings taints
      |> List.map (fun (k, vs) ->
          let rec fixpoint (current : string list) : string list =
            let next =
              List.filter_map (fun k -> S.find_opt k taints) current
              |> List.flatten
            in
            let maybe = List.sort_uniq String.compare (current @ next) in
            if List.length maybe > List.length current then fixpoint maybe
            else current
          in
          (k, k :: fixpoint vs))
    in
    List.fold_left (fun m (k, v) -> S.add k v m) S.empty reachable

  let pair_taints (i1, i2) : (string * string list) list =
    S.union (fun _ _ _ -> None) (i1 |> taints) (i2 |> taints) |> S.bindings
end
