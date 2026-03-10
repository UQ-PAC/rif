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

    let pp_assert ?(human = false) t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match human with
          | true -> Str.global_replace rxp {|(|f_\1| ...)|} s
          | false -> s)
        |> Printf.sprintf "(assert %s)"
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

    let pp_func term =
      Term.to_string term
      |> Printf.sprintf "(define-fun %s -> Int)"
      |> print_endline
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
    Cvc5.Solver.set_option solver "wf-checking" "false";

    solver

  let cross_product (l : 'a list) (l' : 'b list) : ('a * 'b) list =
    List.map (fun e -> List.map (fun e' -> (e, e')) l') l |> List.concat

  let rec powerset = function
    | [] -> [ [] ]
    | x :: xs ->
        let ps = powerset xs in
        ps @ List.map (fun ss -> x :: ss) ps

  let rec combine = function
    | 0 -> [ [] ]
    | n ->
        let c = combine (n - 1) in
        List.map (List.cons true) c @ List.map (List.cons false) c

  let make_aliases (inst_syms : string list) (spec_syms : string list) :
      (string * string) list list =
    let inst_mem_syms =
      List.filter (String.starts_with ~prefix:"M") inst_syms
    in

    cross_product spec_syms inst_mem_syms
    |> powerset
    |>
    (* Filter out aliases where two mappings start from the same spec-variable. *)
    List.filter (fun l ->
        List.length l
        == (List.map fst l |> List.sort_uniq String.compare |> List.length))
    |>
    (* TODO(completeness): consider, should code generate X->MR3 *and* Y->MR3? *)
    List.filter (fun l ->
        List.length l
        == (List.map snd l |> List.sort_uniq String.compare |> List.length))

  type combination = (string * string) list * (string * string * bool) list

  let generate_stage2_pres (preds : (string * string) list)
      (taints : (string * string list) list) (inst_vars : string list)
      (comb : combination list) : combination list =
    (* For every inst_var that isn't pointed to by an alias, make more combinations for it *)
    let expand_combination ((aliasing, combination) : combination) :
        combination list =
      let unaliased_vars =
        List.filter
          (fun v ->
            not @@ List.exists (fun a -> String.equal v @@ snd a) aliasing)
          inst_vars
      in
      let all_preds =
        List.map (fun (p, _, _) -> p) combination
        |> List.sort_uniq String.compare
      in

      let new_predicates = cross_product all_preds unaliased_vars in
      let all = List.length new_predicates |> combine in

      let new_combs =
        List.map
          (fun l -> List.map2 (fun (a, b) c -> (a, b, c)) new_predicates l)
          all
      in

      List.map (fun a -> combination @ a) new_combs
      |> List.map (fun a -> (aliasing, a))
    in

    (* TODO(performance): Mini-taint-analysis, don't generate unnecessary register-value predicates. *)
    List.flatten @@ List.map expand_combination comb
end
