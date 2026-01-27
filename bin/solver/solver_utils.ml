open Cvc5
open LibASL

module type SolverUtils = sig
  type mode = Easy | Safe
end

module SolverUtils = struct
  type mode = Easy | Safe

  let c f g x = f (g x)

  module Printing = struct
    let pp_stmt = c print_endline Asl_utils.pp_stmt
    let pp_expr = c print_endline Asl_utils.pp_expr
    let pp_type = c print_endline Asl_utils.pp_type
    let pp_lexpr = c print_endline Asl_utils.pp_lexpr
    let pp_term = c print_endline Term.to_string
    let rxp = Str.regexp {|(|f_\([MR0-9'_]+\)| [^)]+)|}

    let pp_assume ?(human = false) t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match human with
        | true -> Str.global_replace rxp {|(|f_\1| ...)|} s
        | false -> s)
        |> Printf.sprintf "(assume %s)"
        |> print_endline;
      t

    let pp_constrain ?(human = false) t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match human with
        | true -> Str.global_replace rxp {|(|f_\1| ...)|} s
        | false -> s)
        |> Printf.sprintf "(constraint %s)"
        |> print_endline;
      t

    let pp_newterm name =
      Printf.sprintf "(declare-var %s Int)" name |> print_endline
  end

  let term_eq tm l r = Term.mk_term tm Kind.Equal (Array.of_list [ l; r ])

  let trivial_sygus tm srt slv =
    let zero = Term.mk_int tm 0 in

    let dummy_in = Term.mk_var_s tm srt "dummy_in" in
    let s =
      Cvc5.Solver.synth_fun slv tm "dummy" (Array.of_list [ dummy_in ]) srt None
    in
    let uf = Term.mk_term tm Kind.Apply_uf (Array.of_list [ s; zero ]) in
    Cvc5.Solver.add_sygus_constraint slv (term_eq tm uf zero)

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
          (Printf.sprintf "Internal: encountered unexpected slice %s"
             (Utils.to_string @@ Asl_utils.PP.pp_slice n))
    | LExpr n ->
        failwith
          (Printf.sprintf "Internal: encountered unexpected lexpr %s"
             (Asl_utils.pp_lexpr n))
    | Expr n ->
        failwith
          (Printf.sprintf "Internal: encountered unexpected expr %s"
             (Asl_utils.pp_expr n))
    | Addr n ->
        failwith
          (Printf.sprintf "Internal: encountered unexpected address expr %s"
             (Asl_utils.pp_expr n))
    | Stmt n ->
        failwith
          (Printf.sprintf "Internal: encountered unexpected stmt %s"
             (Asl_utils.pp_stmt n))
    | Fun n ->
        failwith
          (Printf.sprintf "Internal: encountered unexpected function %s" n)

  let mk_solver tm =
    let solver = Cvc5.Solver.mk_solver ~logic:"ALL" tm in
    Cvc5.Solver.set_option solver "sygus" "true";
    Cvc5.Solver.set_option solver "full-sygus-verify" "true";
    Cvc5.Solver.set_option solver "sygus-enum" "smart";
    Cvc5.Solver.set_option solver "sygus-si" "all";
    Cvc5.Solver.set_option solver "incremental" "true";

    solver

  (* TODO *)
  let combine (_ : 'a list) (_ : 'b list) : ('a * 'b) list = []
end
