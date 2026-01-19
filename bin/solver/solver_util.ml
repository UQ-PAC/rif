let uncurry f (x, y) = f x y
let compose f g x = f (g x)
let contains f l = match List.find_opt f l with Some _ -> true | _ -> false
let ( => ) = fun a b -> (not a) || b

type specmode = Easy | Safe

module Util = struct
  module Aslp = struct
    open LibASL

    let pp_stmt = compose print_endline Asl_utils.pp_stmt
    let pp_expr = compose print_endline Asl_utils.pp_expr
    let pp_type = compose print_endline Asl_utils.pp_type
    let pp_lexpr = compose print_endline Asl_utils.pp_lexpr
  end

  module Cvc = struct
    open Cvc5

    let ordinary_states = [ 1; 2; 3; 4; 5; 6; 7; 8 ]
    let function_states = [ (-1); (-2) ]
    let all_states = ordinary_states @ function_states

    let ordinary_rely = [ (1, 2); (3, 4); (5, 8); (7, 8) ]
    let function_rely = [ (1, (-1)); (6, (-2)) ]

    let ordinary_inst = [ (2, 3); (4, 5) ]
    let function_inst = [ ((-1), 6); ((-2), 7) ]

    let ordinary_trans = ordinary_rely @ ordinary_inst
    let function_trans = function_rely @ function_inst

    let rxp = Str.regexp {|(|f_\([MR0-9'_]+\)| [^)]+)|}
    let doRxp = false

    let pp_assume t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match doRxp with true -> (Str.global_replace rxp {|(|f_\1| ...)|} s) | false -> s)
        |> Printf.sprintf "(assume %s)" |> print_endline;
      t

    let pp_constrain t =
      Term.to_string t |> fun s ->
      if String.equal s "true" then ()
      else
        (match doRxp with true -> (Str.global_replace rxp {|(|f_\1| ...)|} s) | false -> s)
        |> Printf.sprintf "(constraint %s)" |> print_endline;
      t

    let pp_term = compose print_endline Term.to_string

    module TermMap = Map.Make (String)
    module Primes = Map.Make (Int)

    type terms = Term.term TermMap.t
    type primes = terms Primes.t

    let nested_union (m1 : primes) (m2 : primes) : primes =
      Primes.union
        (fun _ t1 t2 -> Some (TermMap.union (fun _ _ t -> Some t) t1 t2))
        m1 m2

    let make_term tm srt name =
      if (not doRxp) then Printf.sprintf "(declare-var %s Int)" name |> print_endline;
      Term.mk_var_s tm srt name

    let make_vars ?(init = TermMap.empty) tm srt names : terms =
      List.fold_left
        (fun map name -> TermMap.add name (make_term tm srt name) map)
        init names

    (* adds a level of "prime" to all variables in this map
       keeps keys the same for lookup purposes *)
    let promote_variables ?(ext = "'") tm srt map : terms =
      TermMap.fold
        (fun name _ acc ->
          let prime = name ^ ext in
          TermMap.add name (make_term tm srt prime) acc)
        map TermMap.empty

    let find_sp map = TermMap.find "SP" map
    let find_pc map = TermMap.find "PC" map
    let mapFindPrint = false

    let find_reg ?(p = mapFindPrint) map i =
      if p then print_endline ("looking for R" ^ i);
      TermMap.find ("R" ^ i) map

    let find_mem_reg ?(p = mapFindPrint) map i =
      if p then print_endline ("looking for MR" ^ i);
      TermMap.find ("MR" ^ i) map

    let find_glob map n = TermMap.find n map
    let term_eq tm l r = Term.mk_term tm Kind.Equal (Array.of_list [ l; r ])

    let make_solver tm verb =
      let solver = Cvc5.Solver.mk_solver ~logic:"ALL" tm in
      Cvc5.Solver.set_option solver "sygus" "true";
      Cvc5.Solver.set_option solver "sygus-out" "status-and-def";
      Cvc5.Solver.set_option solver "sygus-enum" "fast";
      Cvc5.Solver.set_option solver "sygus-si" "all";
      Cvc5.Solver.set_option solver "sygus-stream" "true";

      Cvc5.Solver.set_option solver "full-sygus-verify" "true";
      Cvc5.Solver.set_option solver "sygus-core-connective" "true";
      Cvc5.Solver.set_option solver "incremental" "false";

      if verb then Cvc5.Solver.set_option solver "output" "sygus";
      solver

    let solver_setup tm ?(doMakeFuncs = false) (terms : primes * primes) sort =
      let solver = make_solver tm true in

      let make_sygus =
        Primes.map (fun m ->
            TermMap.map
              (fun t ->
                Cvc5.Solver.declare_sygus_var solver (Term.to_string t) sort)
              m)
      in

      let sygus_spec, sygus_inst =
        match terms with s, i -> (make_sygus s, make_sygus i)
      in

      let sygus_spec, sygus_inst =
        match doMakeFuncs with
        | false -> (sygus_spec, sygus_inst)
        | true ->
            let everyITerm =
              sygus_inst |> Primes.bindings |> List.map snd
              |> List.map TermMap.bindings |> List.flatten |> List.map snd
            in

            let makeFuncsOfMap i =
              sygus_inst |> Primes.find i
              |> TermMap.map (fun v ->
                      let name = Term.to_string v |> Str.global_replace (Str.regexp "|") "_" |> (^) "f" in

                      Printf.sprintf "(synth-fun %s ( " name |> print_string;
                      List.iter (fun i -> Term.to_string i |> Printf.sprintf "(%s Int) " |> print_string) everyITerm;
                      print_endline ") Int)";

                     Cvc5.Solver.synth_fun solver tm
                       (name)
                       (Array.of_list everyITerm) sort None)
              |> TermMap.map (fun v ->
                     Term.mk_term tm Kind.Apply_uf
                       (Array.of_list (v :: everyITerm)))
            in

            let withFuncs =
              List.fold_left
              (fun acc i -> Primes.add i (makeFuncsOfMap (-i)) acc)
              sygus_inst function_states in

            (sygus_spec, withFuncs)
      in

      (solver, sygus_spec, sygus_inst)

    (* Adds a dummy sygus problem: create a function f(x) s.t. f(0) = 0
       Functionally this is easy to solve, so it turns a sygus problem into a
       regular sat problem over the constraints. *)
    let add_dummy_sygus tm solver sort =
      let zero = Term.mk_int tm 0 in

      let dummy_in = Term.mk_var_s tm sort "dummy_in" in
      let s =
        Cvc5.Solver.synth_fun solver tm "dummy"
          (Array.of_list [ dummy_in ])
          sort None
      in
      let uf = Term.mk_term tm Kind.Apply_uf (Array.of_list [ s; zero ]) in
      Cvc5.Solver.add_sygus_constraint solver (term_eq tm uf zero)

    type terms_primes = (int * terms) list

    let declare_as_sygus (terms : terms_primes) (solver : Cvc5.Solver.solver)
        (sort : Cvc5.Sort.sort) =
      List.map
        (fun (i, m) ->
          ( i,
            TermMap.map
              (fun t ->
                Term.to_string t |> Printf.sprintf "(declare-var %s)" |> print_endline;
                Cvc5.Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        terms
  end
end
