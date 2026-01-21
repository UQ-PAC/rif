open Cvc5
open LibASL

module type SolverUtils = sig
  type mode = Easy | Safe

end

module SolverUtils : SolverUtils = struct
  type mode = Easy | Safe

  let c f g x = f (g x)

  module Printing = struct
    let pp_stmt = c print_endline Asl_utils.pp_stmt
    let pp_expr = c print_endline Asl_utils.pp_expr
    let pp_type = c print_endline Asl_utils.pp_type
    let pp_lexpr = c print_endline Asl_utils.pp_lexpr

    let pp_term = c print_endline Term.to_string

    let rxp = Str.regexp {|(|f_\([MR0-9'_]+\)| [^)]+)|}

    let pp_assume ?(human=false) t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match human with true -> (Str.global_replace rxp {|(|f_\1| ...)|} s) | false -> s)
        |> Printf.sprintf "(assume %s)" |> print_endline;
      t

    let pp_constrain ?(human=false) t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match human with true -> (Str.global_replace rxp {|(|f_\1| ...)|} s) | false -> s)
        |> Printf.sprintf "(constraint %s)" |> print_endline;
      t
  end

  let term_eq tm l r = Term.mk_term tm Kind.Equal (Array.of_list [ l; r ])

  let trivial_sygus tm solver sort =
    let zero = Term.mk_int tm 0 in

    let dummy_in = Term.mk_var_s tm sort "dummy_in" in
    let s =
      Cvc5.Solver.synth_fun solver tm "dummy"
        (Array.of_list [ dummy_in ])
        sort None
    in
    let uf = Term.mk_term tm Kind.Apply_uf (Array.of_list [ s; zero ]) in
    Cvc5.Solver.add_sygus_constraint solver (term_eq tm uf zero)

end
