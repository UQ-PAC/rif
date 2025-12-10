open Cvc5
open Lifter
open Util
open Rgspec

module Solver = struct
  type three_primes = Util.Cvc.primes * Util.Cvc.primes * Util.Cvc.primes

  let generate_combination_maps
      ((spec_vars, inst_one_vars, inst_two_vars) : three_primes) :
      (string * string) list list =
    let map_names m =
      List.map fst @@ Util.Cvc.TermMap.bindings @@ Util.Cvc.Primes.find 0 m
    in

    let spec_names = map_names spec_vars in
    let inst_names =
      List.sort_uniq String.compare
        (map_names inst_one_vars @ map_names inst_two_vars)
    in

    (* Get only the names of memory-variables from the inst_vars *)
    let only_mem = List.filter (fun n -> Char.equal n.[0] 'M') inst_names in

    (* cross is a list of all possible individual mappings, e.g. [mr1 x; mr2 x; mr1 y; mr2 y; mr1 ""; mr2 ""] *)
    let cross =
      List.flatten
      @@ List.map
           (fun n1 -> List.map (fun n2 -> (n1, n2)) only_mem)
           ("" :: spec_names)
    in

    (* is "x" a global variable that is already mapped by this proto-mapping? *)
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
    List.filter (fun m -> List.length m == List.length only_mem) (pset cross)

  (* Generate the constraints that connect all MR'x with <var>'x for this combination *)
  let create_combination_terms tm (combination : (string * string) list)
      (terms : three_primes) : Term.term list =
    let spec_terms, i1, i2 = terms in
    let inst_terms = Util.Cvc.nested_union i1 i2 in
    List.flatten
    @@ List.map
         (fun (i, s) ->
           (* If x maps to "" then it's considered "unmapped", i.e. "no memory in this pair aliases x" *)
           if String.equal i "" then []
           else
             List.map
               (fun lv ->
                 (* for all prime-states, get the global and memory we're mapping (i,s) and '=' them *)
                 let glob =
                   Util.Cvc.TermMap.find i (Util.Cvc.Primes.find lv spec_terms)
                 in
                 let mem =
                   Util.Cvc.TermMap.find s (Util.Cvc.Primes.find lv inst_terms)
                 in
                 Util.Cvc.term_eq tm glob mem)
               [ 0; 1; 2; 3; 4; 5; 6; 7 ])
         combination

  let check_in_order ((i1, i2) : Lifter.instruction * Lifter.instruction)
      ((rely, guar) : RGSpec.speclang * RGSpec.speclang) (terms : three_primes)
      (tm, sort) (combination : (string * string) list) : bool =
    let solver, spec, i1t, i2t = Util.Cvc.solver_setup tm terms sort in
    let spec_terms i = Util.Cvc.Primes.find i spec in
    let inst_terms i =
      Util.Cvc.Primes.find i @@ Util.Cvc.nested_union i1t i2t
    in

    let assumes =
      (* State Transitions:
         S0 to S1 over R, S1 to S2 over i1, etc *)
      RGSpec.cvc_of_spec tm (spec_terms 0) (spec_terms 1) rely
      @ Lifter.cvc_of_inst tm (inst_terms 1) (inst_terms 2) i1
      @ RGSpec.cvc_of_spec tm (spec_terms 2) (spec_terms 3) rely
      @ Lifter.cvc_of_inst tm (inst_terms 3) (inst_terms 4) i2
      @ RGSpec.cvc_of_spec tm (spec_terms 4) (spec_terms 5) rely
      (* Spec->Instruction "combination" *)
      @ create_combination_terms tm combination (spec, i1t, i2t)
    in
    List.iter (Solver.add_sygus_assume solver) assumes;

    let constrains =
      (* Guarantees: *)
      RGSpec.cvc_of_spec tm (spec_terms 1) (spec_terms 2) guar
      @ RGSpec.cvc_of_spec tm (spec_terms 3) (spec_terms 4) guar
    in
    List.iter (Solver.add_sygus_constraint solver) constrains;

    Util.Cvc.add_dummy_sygus tm solver;
    let result = Solver.check_synth solver in
    SynthResult.has_solution result

  let solve (verb : bool) (pair : Lifter.instruction * Lifter.instruction)
      (spec : RGSpec.speclang * RGSpec.speclang) cvc
      (terms : Util.Cvc.primes * Util.Cvc.primes * Util.Cvc.primes) : bool =
    let all_possible_solver_combinations = generate_combination_maps terms in
    let countall = List.length all_possible_solver_combinations in
    if verb then
      print_endline
        (Printf.sprintf "        [!] Identified %i combinations" countall);

    let valid_in_order =
      List.filter
        (check_in_order pair spec terms cvc)
        all_possible_solver_combinations
    in
    if verb then
      print_endline
        (Printf.sprintf "        [!] %i combinations are valid-in-order"
        @@ List.length valid_in_order);

    let valid_out_order =
      List.filter (check_out_order pair spec terms cvc) valid_in_order
    in
    if verb then
      print_endline
        (Printf.sprintf "        [!] %i combinations are valid-out-of-order"
        @@ List.length valid_out_order);

    List.length valid_in_order == List.length valid_out_order

  (*
    let invalid_out_order =
      List.filter (check_out_order pair spec terms cvc) valid_in_order
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
    *)

  let solve_all ~verb (pairs : (Lifter.instruction * Lifter.instruction) list)
      (rely, guar) =
    let tm = TermManager.mk_tm () in
    let var_sort = Sort.mk_int_sort tm in

    let promote i =
      Util.Cvc.promote_variables ~ext:("'" ^ string_of_int i) tm var_sort
    in

    let spec_names = RGSpec.collect_globs rely @ RGSpec.collect_globs guar in
    let spec_terms = Util.Cvc.make_vars tm var_sort spec_names in
    let spec_terms_primes =
      List.fold_left
        (fun acc i -> Util.Cvc.Primes.add i (promote i spec_terms) acc)
        (Util.Cvc.Primes.add 0 spec_terms Util.Cvc.Primes.empty)
        [ 1; 2; 3; 4; 5; 6; 7 ]
    in

    let all_instruction_names =
      List.sort_uniq String.compare
      @@ List.flatten
      @@ List.map
           (fun (i1, i2) -> Lifter.all_syms i1 @ Lifter.all_syms i2)
           pairs
    in
    let all_instruction_terms =
      Util.Cvc.make_vars tm var_sort all_instruction_names
    in
    let all_instruction_terms_primes =
      List.fold_left
        (fun acc i ->
          Util.Cvc.Primes.add i (promote i all_instruction_terms) acc)
        (Util.Cvc.Primes.add 0 spec_terms Util.Cvc.Primes.empty)
        [ 1; 2; 3; 4; 5; 6; 7 ]
    in

    let filter_instruction_terms (i : Lifter.instruction) =
      Util.Cvc.Primes.map
        (Util.Cvc.TermMap.filter (fun k _ ->
             let syms = Lifter.all_syms i in
             Option.is_some @@ List.find_opt (String.equal k) syms))
        all_instruction_terms_primes
    in

    List.filteri
      (fun idx pair ->
        ignore (Printf.sprintf "[!] Solving pair %i...\n" (idx + 1));
        let spec = (rely, guar) in
        let cvc = (tm, var_sort) in
        let terms =
          ( spec_terms_primes,
            filter_instruction_terms (fst pair),
            filter_instruction_terms (snd pair) )
        in
        solve verb pair spec cvc terms)
      pairs
end
