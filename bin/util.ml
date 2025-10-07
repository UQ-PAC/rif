let b64_bytes b = Base64.encode_exn (Bytes.to_string b)
let bytes_b64 b = Bytes.of_string (Base64.decode_exn b)
let access_index idx l = List.hd (List.filteri (fun i _ -> idx == i) l)
let access_primes idx l = snd @@ List.find (fun (i, _) -> i == idx) l
let uncurry f (x, y) = f x y
let compose f g x = f (g x)
let contains f l = match List.find_opt f l with Some _ -> true | _ -> false
let ( => ) = fun a b -> (not a) || b

module Util = struct
  module Cvc = struct
    open Cvc5
    module TermMap = Map.Make (String)

    type terms = Term.term TermMap.t

    let make_term tm srt name = Term.mk_var_s tm srt name

    let make_register_vars tm srt names : terms =
      List.fold_left
        (fun map name -> TermMap.add name (make_term tm srt name) map)
        TermMap.empty names

    let make_spec_vars tm srt gs : terms =
      List.fold_left
        (fun map name -> TermMap.add name (make_term tm srt name) map)
        TermMap.empty gs

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

    let new_solver (tm, _verb) =
      let solver = Cvc5.Solver.mk_solver ~logic:"ALL" tm in
      Cvc5.Solver.set_option solver "sygus" "true";
      Cvc5.Solver.set_option solver "full-sygus-verify" "true";
      Cvc5.Solver.set_option solver "sygus-enum" "smart";
      Cvc5.Solver.set_option solver "sygus-si" "all";
      Cvc5.Solver.set_option solver "incremental" "true";

      Cvc5.Solver.set_option solver "output" "sygus";
      Cvc5.Solver.set_option solver "output" "sygus-enumerator";
      solver

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
  end
end
