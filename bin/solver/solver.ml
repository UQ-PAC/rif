open Cvc5
open Util

module Solver = struct
  type term_maps = Util.Cvc.primes * Util.Cvc.primes

  let generate_aliasing_maps ((spec_vars, inst_vars) : term_maps) :
      (string * string) list list =
    let map_names m =
      Util.Cvc.Primes.find 0 m |> Util.Cvc.TermMap.bindings |> List.map fst
    in

    let spec_names = map_names spec_vars in
    let inst_names = map_names inst_vars in

    (* Get only the names of memory-variables from the inst_vars *)
    let only_mem = List.filter (fun n -> Char.equal n.[0] 'M') inst_names in

    (* cross is a list of all possible individual mappings, e.g. [mr1 x; mr2 x; mr1 y; mr2 y; mr1 ""; mr2 ""] *)
    let cross =
      List.map
        (fun n1 -> List.map (fun n2 -> (n1, n2)) only_mem)
        ("" :: spec_names)
      |> List.flatten
    in

    (* is "x" a global variable that is already mapped by this proto-mapping? *)
    let already_mapped x s =
      if String.equal x "" then false
      else List.find_opt (fun (_, b) -> String.equal x b) s |> Option.is_some
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

  (* Generate the constraints that connect all MR'x with <var>'x for this aliasing *)
  let create_aliasing_terms tm (aliasing : (string * string) list)
      (terms : term_maps) : Term.term list =
    let spec_terms, inst_terms = terms in
    List.map
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
            Util.Cvc.ordinary_states)
      aliasing
    |> List.flatten

  let check_in_order ((i1, i2) : Lifter.instruction * Lifter.instruction)
      ((rely, guar) : RGSpec.speclang * RGSpec.speclang) (terms : term_maps)
      (tm, sort) (aliasing : (string * string) list) : bool =
    let solver, spec, inst = Util.Cvc.solver_setup tm terms sort in
    let spec_terms i = Util.Cvc.Primes.find i spec in
    let inst_terms i = Util.Cvc.Primes.find i inst in
    let assume = List.iter (Solver.add_sygus_assume solver) in
    let constrain = List.iter (Solver.add_sygus_constraint solver) in

    assume @@ RGSpec.cvc_of_spec tm (spec_terms 1) (spec_terms 2) rely;
    assume @@ Lifter.cvc_of_inst tm (inst_terms 2) (inst_terms 3) i1;
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 3) (spec_terms 4) rely;
    assume @@ Lifter.cvc_of_inst tm (inst_terms 4) (inst_terms 5) i2;
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 5) (spec_terms 6) rely;

    assume @@ create_aliasing_terms tm aliasing (spec, inst);

    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 2) (spec_terms 3) guar;
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 4) (spec_terms 5) guar;

    Util.Cvc.add_dummy_sygus tm solver sort;
    let result = Solver.check_synth solver in
    SynthResult.has_solution result

  let equal_in_states tm inst check ss =
    List.flatten @@ List.map
      (fun (i1, i2) ->
        let s1, s2 = (Util.Cvc.Primes.find i1 inst, Util.Cvc.Primes.find i2 inst) in
        Util.Cvc.TermMap.bindings s1
        |> List.filter (fun (s, _) -> check s)
        |> List.map (fun (k, v) ->
          Util.Cvc.TermMap.find k s2 |> Util.Cvc.term_eq tm v)) ss

  let check_out_order (mode : mode) ((i1, i2) : Lifter.instruction * Lifter.instruction)
      ((rely, guar) : RGSpec.speclang * RGSpec.speclang) (terms : term_maps)
      (tm, sort) (aliasing : (string * string) list) : bool =
    print_endline "I1:";
    List.iter Util.Aslp.pp_stmt i1.semantics;
    print_endline "I2:";
    List.iter Util.Aslp.pp_stmt i2.semantics;

    let solver, spec, inst =
      Util.Cvc.solver_setup tm ~doMakeFuncs:true terms sort
    in

    (* "Unspecified" things are M[r-something]'s that do not appear on either
       side of any aliasing. *)
    let unspecified s =
      let x = List.find_opt (fun (a,b) ->
        String.equal a s || String.equal b s) aliasing in
      s.[0] == 'M' && Option.is_none x
    in
    let register s = s.[0] == 'R' in

    let spec_terms i = Util.Cvc.Primes.find i spec in
    let inst_terms i = Util.Cvc.Primes.find i inst in
    let assume =
      List.iter (compose (Solver.add_sygus_assume solver) Util.Cvc.pp_assume)
    in
    let constrain =
      List.iter
        (compose (Solver.add_sygus_constraint solver) Util.Cvc.pp_constrain)
    in

    (* Generate assumed transitions for the out-of-order execution from 1-6 *)
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 1) (spec_terms 2) rely;
    assume @@ Lifter.cvc_of_inst tm (inst_terms 2) (inst_terms 3) i2;
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 3) (spec_terms 4) rely;
    assume @@ Lifter.cvc_of_inst tm (inst_terms 4) (inst_terms 5) i1;
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 5) (spec_terms 8) rely;

    (* Generate aliasing between spec and MR[x] for every state *)
    assume @@ create_aliasing_terms tm aliasing (spec, inst);

    (* Generate registers-are-unchanged-over-rely transitions *)
    assume @@ equal_in_states tm inst register
        Util.Cvc.ordinary_rely;
    constrain @@ equal_in_states tm inst register
        Util.Cvc.function_rely;

    (* In safe-mode, assume nothing, in easy-mode, assume/constrain un-specified memory
       isn't modified *)
    assume @@ (match mode with
               | Safe -> []
               | Easy -> equal_in_states tm inst unspecified Util.Cvc.ordinary_rely);
    constrain @@ (match mode with
                  | Safe -> []
                  | Easy -> equal_in_states tm inst unspecified Util.Cvc.function_rely);

    (* Generate constraints for the guarantee *)
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 2) (spec_terms 3) guar;
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 4) (spec_terms 5) guar;
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms (-1)) (spec_terms 6) guar;
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms (-2)) (spec_terms 7) guar;

    (* Generate transitions for 1-7 for the in-order execution *)
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 1) (spec_terms (-1)) rely;
    assume @@ Lifter.cvc_of_inst tm (inst_terms (-1)) (inst_terms 6) i1;
    constrain @@ RGSpec.cvc_of_spec tm (spec_terms 6) (spec_terms (-2)) rely;
    constrain @@ Lifter.cvc_of_inst tm (inst_terms (-2)) (inst_terms 7) i2;
    assume @@ RGSpec.cvc_of_spec tm (spec_terms 7) (spec_terms 8) rely;

    let result = Solver.check_synth solver in
    SynthResult.has_solution result

  let solve (verb : bool) (mode : mode) (pair : Lifter.instruction * Lifter.instruction)
      (spec : RGSpec.speclang * RGSpec.speclang) cvc (terms : term_maps) : bool
      =
    let all_possible_solver_aliasings = generate_aliasing_maps terms in
    let countall = List.length all_possible_solver_aliasings in
    if verb then
      print_endline (Printf.sprintf "    [!] Identified %i aliasings" countall);

    let valid_in_order =
      List.filter
        (check_in_order pair spec terms cvc)
        all_possible_solver_aliasings
    in
    if verb then
      print_endline
        (List.length valid_in_order
        |> Printf.sprintf "    [!] %i aliasings are valid-in-order");

    let valid_out_order =
      List.filter (check_out_order mode pair spec terms cvc) valid_in_order
    in
    if verb then
      print_endline
        (List.length valid_out_order
        |> Printf.sprintf "    [!] %i aliasings are valid out-of-order");
    List.length valid_out_order == List.length valid_in_order

  (*
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
    *)

  let solve_all ~verb ~mode (pairs : (Lifter.instruction * Lifter.instruction) list)
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
        Util.Cvc.all_states
    in

    let all_instruction_names =
      List.map (fun (i1, i2) -> Lifter.all_syms i1 @ Lifter.all_syms i2) pairs
      |> List.flatten
      |> List.sort_uniq String.compare
    in
    let all_instruction_terms =
      Util.Cvc.make_vars tm var_sort all_instruction_names
    in
    let all_instruction_terms_primes =
      List.fold_left
        (fun acc i ->
          Util.Cvc.Primes.add i (promote i all_instruction_terms) acc)
        (Util.Cvc.Primes.add 0 spec_terms Util.Cvc.Primes.empty)
        Util.Cvc.ordinary_states
    in

    let filter_instruction_terms (i : Lifter.instruction) =
      Util.Cvc.Primes.map
        (Util.Cvc.TermMap.filter (fun k _ ->
             let syms = Lifter.all_syms i in
             List.find_opt (String.equal k) syms |> Option.is_some))
        all_instruction_terms_primes
    in

    List.filteri
      (fun idx pair ->
        if verb then
          print_endline (Printf.sprintf "[!] Solving pair %i..." (idx + 1));
        let spec = (rely, guar) in
        let cvc = (tm, var_sort) in
        let terms =
          ( spec_terms_primes,
            Util.Cvc.nested_union
              (filter_instruction_terms (fst pair))
              (filter_instruction_terms (snd pair)) )
        in
        let r = solve verb mode pair spec cvc terms in
        if verb then (
          match r with
          | true -> print_endline (Printf.sprintf "  [!] Pair %i succeeded in all states" (idx+1))
          | false -> print_endline (Printf.sprintf "  [!] Pair %i failed for at least one state" (idx+1))
        );
        r)
      pairs
end
