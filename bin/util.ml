let b64_bytes b = Base64.encode_exn (Bytes.to_string b)
let bytes_b64 b = Bytes.of_string (Base64.decode_exn b)
let access_index idx l = List.hd (List.filteri (fun i _ -> idx == i) l)
let access_primes idx l = snd @@ List.find (fun (i, _) -> i == idx) l
let uncurry f (x, y) = f x y
let compose f g x = f (g x)
let contains f l = match List.find_opt f l with Some _ -> true | _ -> false
let ( => ) = fun a b -> (not a) || b

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

    let pp_term = compose print_endline Term.to_string

    module TermMap = Map.Make (String)
    module Primes = Map.Make (Int)

    type terms = Term.term TermMap.t
    type primes = terms Primes.t

    let nested_union =
      Primes.union (fun _ v1 v2 ->
          Some (TermMap.union (fun _ t _ -> Some t) v1 v2))

    let make_term tm srt name = Term.mk_var_s tm srt name

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

    let middlestate_functions ?(ext = "") solver tm srt map inputs : terms =
      TermMap.fold
        (fun name _ acc ->
          let f = "f" ^ name ^ ext in
          TermMap.add name
            (Cvc5.Solver.synth_fun solver tm f (Array.of_list inputs) srt None)
            acc)
        map TermMap.empty

    let find_sp map = TermMap.find "SP" map
    let find_pc map = TermMap.find "PC" map
    let find_reg map i = TermMap.find ("R" ^ i) map
    let find_mem_reg map i = TermMap.find ("MR" ^ i) map
    let find_glob map n = TermMap.find n map
    let term_eq tm l r = Term.mk_term tm Kind.Equal (Array.of_list [ l; r ])

    let make_solver tm verb =
      let solver = Cvc5.Solver.mk_solver ~logic:"ALL" tm in
      Cvc5.Solver.set_option solver "sygus" "true";
      Cvc5.Solver.set_option solver "full-sygus-verify" "true";
      Cvc5.Solver.set_option solver "sygus-enum" "smart";
      Cvc5.Solver.set_option solver "sygus-si" "all";
      Cvc5.Solver.set_option solver "incremental" "true";

      ignore verb;
      (* if verb then Cvc5.Solver.set_option solver "output" "sygus"; *)
      solver

    let solver_setup tm (terms : primes * primes * primes) sort =
      let solver = make_solver tm true in

      let make_sygus =
        Primes.map (fun m ->
            TermMap.map
              (fun t ->
                Cvc5.Solver.declare_sygus_var solver (Term.to_string t) sort)
              m)
      in

      let sygus_spec, sygus_i1, sygus_i2 =
        match terms with
        | s, i1, i2 -> (make_sygus s, make_sygus i1, make_sygus i2)
      in

      let inst_terms = Primes.find 0 @@ nested_union sygus_i1 sygus_i2 in

      ignore inst_terms;
      (solver, sygus_spec, sygus_i1, sygus_i2)

    (* Adds a dummy sygus problem: create a function f(x) s.t. f(0) = 0
       Functionally this is easy to solve, so it turns a sygus problem into a
       regular sat problem over the constraints. *)
    let add_dummy_sygus tm solver =
      let intsort = Sort.mk_int_sort tm in
      let zero = Term.mk_int tm 0 in

      let dummy_in = Term.mk_var_s tm intsort "dummy_in" in
      let s =
        Cvc5.Solver.synth_fun solver tm "dummy"
          (Array.of_list [ dummy_in ])
          intsort None
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
                Cvc5.Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        terms
  end
end
