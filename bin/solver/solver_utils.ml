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
    |>
    (* Filter out all series of aliasing where a spec sym isn't mapped *)
    List.filter (fun l ->
        List.for_all
          (fun sp -> List.exists (fun (a, _) -> String.equal sp a) l)
          spec_syms)

  type combination = (string * string) list * (string * string * bool) list

  (*
    pred_uses: function * specvar list    e.g. [(locked, lock), (secret, x)]
    taints: instvar * instvar list list   e.g. [(r0, [m@r1]), (r2, [m@sp+2])]
    inst_vars: instruction variable list  e.g. [r0, m@r0, m@sp+2]
    comb: alias list * pred list          e.g. ([(x,m@r0), (lock,m@r1)], [(secret,x,true), (locked,x,false)])
  *)
  let generate_stage2_pres (pred_uses : (string * string) list)
      (taints : (string * string list) list) (inst_vars : string list)
      (comb : combination list) : combination list =
    let pred_uses =
      List.filter (fun (a, _) -> not @@ String.equal a "") pred_uses
      |> List.sort_uniq (fun (a, b) (c, d) ->
          match String.compare a c with 0 -> String.compare b d | v -> v)
    in

    (* For every inst_var that isn't pointed to by an alias, make more combinations for it *)
    let expand_combination ((aliasing, combination) : combination) :
        combination list =
      let unaliased_vars =
        List.filter
          (fun v ->
            not @@ List.exists (fun a -> String.equal v @@ snd a) aliasing)
          inst_vars
      in

      (* Given taint (r0, [M@R0, M@R2]), pred_uses (locked, x), and aliasing (x,M@R0)
         compute (locked, [r0, ...]) and therefore compute [(locked, r0) ...] *)

      (*
        Step 1: turn pred_uses (locked,x) into pred_alias_uses (locked,M@R0)
      *)
      let pred_alias_uses =
        List.map
          (fun (pred, var) ->
            ( pred,
              List.find (fun (fromv, _) -> String.equal fromv var) aliasing
              |> snd ))
          pred_uses
      in

      (*
        Step 2: turn pred_alias_uses (locked,M@R0) into taint_per_pred (locked,[R0,M@R0])
      *)
      let taint_per_pred =
        List.map
          (fun (pred, var) ->
            ( pred,
              List.filter_map
                (fun (taintfrom, tainting) ->
                  if List.exists (String.equal var) tainting then Some taintfrom
                  else None)
                taints ))
          pred_alias_uses
      in

      (*
        Step 3: turn taint_per_pred into new_predicates [(locked,R0),(locked,M@R0)]
      *)
      let new_preds =
        List.flatten
        @@ List.map (fun (a, b) -> List.map (fun c -> (a, c)) b) taint_per_pred
      in

      (*
        Step 4: filter based on whether the var is already aliased (and therefore already combined-over)
      *)
      let filtered_new_preds =
        List.filter
          (fun (_, var) -> List.exists (String.equal var) unaliased_vars)
          new_preds
      in

      (*
        Step 5: generate 2^n "combinations" for true/false * every necessary predicate
      *)
      let all = List.length filtered_new_preds |> combine in

      (*
        Step 6: massage this back into the right format: [(locked, R0, true), ...]
      *)
      let new_combs =
        List.map
          (fun l -> List.map2 (fun (a, b) c -> (a, b, c)) filtered_new_preds l)
          all
      in

      List.map (fun a -> combination @ a) new_combs
      |> List.map (fun a -> (aliasing, a))
    in

    List.map expand_combination comb |> List.flatten
end
