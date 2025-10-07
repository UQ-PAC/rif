open Cvc5
open Lifter
open Util
open Spec

module Solver = struct
  type style = Integers | BitVectors

  let subset_only_mem vars : string list =
    Util.Cvc.TermMap.fold
      (fun k _ (l : string list) : string list ->
        if Char.equal k.[0] 'M' then k :: l else l)
      vars []

  let unpack_sem (blocks : Lifter.blockdata Lifter.Blocks.t) ((b1, i1), (b2, i2))
      =
    ( (match access_index i1 (Lifter.Blocks.find b1 blocks).block_semantics with
      | _, r -> r),
      match access_index i2 (Lifter.Blocks.find b2 blocks).block_semantics with
      | _, r -> r )

  let unpack_sum (blocks : Lifter.blockdata Lifter.Blocks.t) ((b1, i1), (b2, i2))
      =
    ( (match access_index i1 (Lifter.Blocks.find b1 blocks).block_summary with
      | _, r -> r),
      match access_index i2 (Lifter.Blocks.find b2 blocks).block_summary with
      | _, r -> r )

  let get_uni_quant_vars l =
    (* All universally-quantified variables, for skolem functions.
       Note that spec_terms are not included as they're fixed to the same value as inst_terms referencing memory, so it's functionally
       not an increase to the valid state space of the search.
       (i.e. forall a,b s.t. a = b, finding f(a) is the same as finding f(b) ) *)
    List.flatten
    @@ List.map
         (fun m -> List.map snd (Util.Cvc.TermMap.bindings m))
         (List.map snd l)

  let generate_combinations (snames : string list) (inames : string list) =
    (* cross is a list of all possible individual mappings, e.g. [mr1 x; mr2 x; mr1 y; mr2 y; mr1 ""; mr2 ""] *)
    let cross =
      List.flatten
      @@ List.map (fun n1 -> List.map (fun n2 -> (n1, n2)) inames) ("" :: snames)
    in

    (* is "x" a global variable that is already mapped by this proto-mapping *)
    let already_mapped x s =
      if String.equal x "" then false
      else Option.is_some @@ List.find_opt (fun (_, b) -> String.equal x b) s
    in

    (* powerset but excluding duplicate-second-elements *)
    let rec pset ls =
      match ls with
      | [] -> [ [] ]
      | x :: xs ->
          let ps = pset xs in
          ps
          @ List.map
              (fun s -> if already_mapped (snd x) s then s else x :: s)
              ps
    in

    (* All combinations of mappings except those where aliasing occurs i.e. the mapping [mr1 x; mr2 x] does not occur
       Also filter to ones where the mapping is complete. TODO: optimise this. *)
    List.filter (fun m -> List.length m == List.length inames) (pset cross)

  let create_combination tm c sm im =
    List.flatten
    @@ List.map
         (fun (i, s) ->
           if String.equal i "" then []
           else
             List.map
               (fun lv ->
                 (* for all prime-states, get the global and memory we're mapping (i,s) and '=' them *)
                 let glob = Util.Cvc.TermMap.find i (access_primes lv sm) in
                 let mem = Util.Cvc.TermMap.find s (access_primes lv im) in
                 Util.Cvc.term_eq tm glob mem)
               [ 0; 1; 2; 3; 4; 5; 6; 7 ])
         c

  let solver_specific_setup sp spec_terms inst_terms sort =
    let tm = fst sp in
    let solver = Util.Cvc.new_solver sp in

    let decl_as_sygus tms =
      List.map
        (fun (i, m) ->
          ( i,
            Util.Cvc.TermMap.map
              (fun t -> Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        tms
    in
    let sy_spec_terms = decl_as_sygus spec_terms in
    let sy_inst_terms = decl_as_sygus inst_terms in

    let first_state_map = access_primes 0 sy_inst_terms in

    let all_state_vars =
      List.flatten
      @@ List.map
           (fun i -> (List.map snd) (Util.Cvc.TermMap.bindings @@ snd i))
           sy_inst_terms
    in

    let state_funcs =
      Util.Cvc.middlestate_functions solver tm sort first_state_map
        all_state_vars
    in
    let state_funcs_two =
      Util.Cvc.middlestate_functions ~ext:"'" solver tm sort first_state_map
        all_state_vars
    in

    let apply_uf =
      Util.Cvc.TermMap.map (fun t ->
          Term.mk_term tm Kind.Apply_uf (Array.of_list (t :: all_state_vars)))
    in
    let sygus_funcs_one = apply_uf state_funcs in
    let sygus_funcs_two = apply_uf state_funcs_two in

    (sy_spec_terms, sy_inst_terms, sygus_funcs_one, sygus_funcs_two)

  let check_in_order sp (i1, i2) (r, g) (inst_terms, spec_terms) sort
      combination =
    let tm = fst sp in
    let solver = Util.Cvc.new_solver sp in

    let decl_as_sygus tms =
      List.map
        (fun (i, m) ->
          ( i,
            Util.Cvc.TermMap.map
              (fun t -> Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        tms
    in
    let sy_spec_terms = decl_as_sygus spec_terms in
    let sy_inst_terms = decl_as_sygus inst_terms in

    let spec_from_to p1 p2 spec =
      Spec.cvc_of_spec
        ~b:
          (Spec.AssumeRegsUnchanged
             (access_primes p1 sy_inst_terms, access_primes p2 sy_inst_terms))
        tm
        (access_primes p1 sy_spec_terms)
        (access_primes p2 sy_spec_terms)
        spec
    in

    let inst_from_to p1 p2 inst =
      Lifter.cvc_of_stmtlist tm
        (access_primes p1 sy_inst_terms)
        (access_primes p2 sy_inst_terms)
        inst
    in

    let assume_transitions =
      (* S0 to S1 over R *)
      spec_from_to 0 1 r
      (* S1 to S2 over i1 *)
      @ inst_from_to 1 2 i1
      (* S2 to S3 over R *)
      @ spec_from_to 2 3 r
      (* S3 to S4 over i2 *)
      @ inst_from_to 3 4 i2
      (* S4 to S5 over R *)
      @ spec_from_to 4 5 r
    in
    List.iter (Solver.add_sygus_assume solver) assume_transitions;

    let assume_combination =
      create_combination tm combination sy_spec_terms sy_inst_terms
    in
    List.iter (Solver.add_sygus_assume solver) assume_combination;

    let constrain_guarantees = spec_from_to 2 2 g @ spec_from_to 4 4 g in
    List.iter (Solver.add_sygus_constraint solver) constrain_guarantees;

    Util.Cvc.add_dummy_sygus tm solver;
    let result = Solver.check_synth solver in
    SynthResult.has_solution result

  let check_out_order sp (i1, i2) (r, _g) (inst_terms, spec_terms) sort
      combination =
    let tm = fst sp in
    let solver = Util.Cvc.new_solver sp in

    let sy_spec_terms, sy_inst_terms, sy_funcs_one, sy_funcs_two =
      solver_specific_setup sp spec_terms inst_terms sort
    in

    let spec_from_to p1 p2 spec =
      Spec.cvc_of_spec
        ~b:
          (Spec.AssumeRegsUnchanged
             (access_primes p1 sy_inst_terms, access_primes p2 sy_inst_terms))
        tm
        (access_primes p1 sy_spec_terms)
        (access_primes p2 sy_spec_terms)
        spec
    in

    let inst_from_to p1 p2 inst =
      Lifter.cvc_of_stmtlist tm
        (access_primes p1 sy_inst_terms)
        (access_primes p2 sy_inst_terms)
        inst
    in

    List.iter (compose print_endline Term.to_string) (spec_from_to 0 1 r);
    let assume_transitions =
      (* S0 to S1 over R *)
      spec_from_to 0 1 r
      (* S1 to S2 over i2 *)
      @ inst_from_to 1 2 i2
      (* S2 to S3 over R *)
      @ spec_from_to 2 3 r
      (* S3 to S4 over i1 *)
      @ inst_from_to 3 4 i1
      (* S4 to S5 over R *)
      @ spec_from_to 4 5 r
    in
    List.iter (Solver.add_sygus_assume solver) assume_transitions;
    (* print_endline "assume tran";
    List.iter (compose print_endline Term.to_string) assume_transitions; *)
    let assume_combination =
      create_combination tm combination sy_spec_terms sy_inst_terms
    in
    List.iter (Solver.add_sygus_assume solver) assume_combination;

    (* print_endline "assume comb";
    List.iter (compose print_endline Term.to_string) assume_combination; *)
    print_endline "ct";
    let constrain_transitions =
      (* S0 to f0 over R *)
      Spec.cvc_of_spec ~b:Spec.ConstrainFuncsUnchanged tm
        (access_primes 0 sy_inst_terms)
        sy_funcs_one r
      (* f0 to S6 over i1 *)
      @ Lifter.cvc_of_stmtlist tm sy_funcs_one
          (access_primes 6 sy_inst_terms)
          i1
      (* S6 to f1 over R *)
      @ Spec.cvc_of_spec ~b:Spec.ConstrainFuncsUnchanged tm
          (access_primes 6 sy_inst_terms)
          sy_funcs_two r
      (* f6 to S7 over i2 *)
      @ Lifter.cvc_of_stmtlist tm sy_funcs_two
          (access_primes 7 sy_inst_terms)
          i2
    in
    List.iter (Solver.add_sygus_constraint solver) constrain_transitions;

    print_endline "aft";
    let assume_final_transition =
      (* S7 back to S5 over R *)
      spec_from_to 7 5 r
    in
    (* print_endline "assume tran";
    List.iter (compose print_endline Term.to_string) assume_final_transition; *)
    List.iter (Solver.add_sygus_assume solver) assume_final_transition;

    (* print_endline "constrain tran";
    List.iter (compose print_endline Term.to_string) constrain_transitions; *)
    let result = Solver.check_synth solver in
    not (SynthResult.has_solution result)

  let solve ~verb block_semantics (style : style) spec idx pair : bool =
    print_endline (Printf.sprintf "[!] Solving pair %i..." (idx + 1));
    let tm = TermManager.mk_tm () in
    let sp = (tm, verb) in

    let var_sort =
      match style with
      | Integers -> Sort.mk_int_sort tm
      | BitVectors -> Sort.mk_bv_sort tm 64
    in

    let code = unpack_sem block_semantics pair in
    let rely, guarantee = spec in

    let inst_terms =
      Util.Cvc.make_register_vars tm var_sort
        (List.map Lifter.varSym
           (Lifter.all_variables @@ unpack_sum block_semantics pair))
    in

    let spec_names = Spec.collect_globs rely @ Spec.collect_globs guarantee in
    let spec_terms = Util.Cvc.make_spec_vars tm var_sort spec_names in

    let inst_terms_primes =
      (0, inst_terms)
      :: List.map
           (fun i ->
             ( i,
               Util.Cvc.promote_variables
                 ~ext:("'" ^ string_of_int i)
                 tm var_sort inst_terms ))
           [ 1; 2; 3; 4; 5; 6; 7 ]
    in
    let spec_terms_primes =
      (0, spec_terms)
      :: List.map
           (fun i ->
             ( i,
               Util.Cvc.promote_variables
                 ~ext:("'" ^ string_of_int i)
                 tm var_sort spec_terms ))
           [ 1; 2; 3; 4; 5; 6; 7 ]
    in

    (* inst_terms_primes (int * string->term map) ->
         all registers & memory-locations in the instructions with 0-7 prime
       spec_terms_primes (int * string->term map) ->
         all variables in the spec with 0-7 prime *)
    let terms = (inst_terms_primes, spec_terms_primes) in
    let all_possible_solver_combinations =
      generate_combinations spec_names (subset_only_mem inst_terms)
    in
    let countall = List.length all_possible_solver_combinations in

    let valid_in_order =
      List.filter
        (check_in_order sp code spec terms var_sort)
        all_possible_solver_combinations
    in

    if List.length valid_in_order == 0 then (
      print_endline "!!! No mappings were valid in-order. Check your spec!";
      ignore (exit 1));

    if verb then
      print_endline
        (Printf.sprintf "    [!] %i/%i address mappings are valid in-order"
           (List.length valid_in_order)
           countall);

    let invalid_out_order =
      List.filter (check_out_order sp code spec terms var_sort) valid_in_order
    in

    if verb then
      print_endline
        (Printf.sprintf "    [!] %i/%i address mappings are valid out-of-order"
           (countall - List.length invalid_out_order)
           countall);

    if List.length invalid_out_order != 0 then
      print_endline
        (Printf.sprintf "[!] Failed for mappings:\n    %s"
           (String.concat "\n    "
              (List.map
                 (fun m ->
                   String.concat ";"
                     (List.map
                        (fun (s1, s2) ->
                          Printf.sprintf "%s->%s" s2
                            (if String.equal s1 "" then "{any var}" else s1))
                        m))
                 invalid_out_order)));

    (* If these are different then at least one valid in-order combination couldn't prove validity out-of-order *)
    List.length invalid_out_order != 0
end
