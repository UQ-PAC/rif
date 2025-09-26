open Cvc5
open Lifter
open Util

module Solver = struct
  type style = Integers | BitVectors

  module Cvc_util = struct
    module Variables = Map.Make (String)
    module Globals = Map.Make (String)

    let make_term tm srt name = Term.mk_var_s tm srt name

    let make_register_vars tm srt (i1, i2) : Term.term Variables.t =
      let extract_names (i : Lifter.instruction_summary) =
        List.map Lifter.varSym (i.read @ i.write)
        @ List.map (fun v -> "M" ^ Lifter.varSym v) (i.load @ i.store)
      in

      List.fold_left
        (fun map name -> Variables.add name (make_term tm srt name) map)
        Variables.empty
        (extract_names i1 @ extract_names i2)

    let make_spec_vars tm srt gs : Term.term Globals.t =
      List.fold_left
        (fun map name -> Globals.add name (make_term tm srt name) map)
        Globals.empty gs

    (* adds a level of "prime" to all variables in this map
       keeps keys the same for lookup purposes *)
    let promote_variables ?(ext = "'") tm srt map : Term.term Variables.t =
      Variables.fold
        (fun name _ acc ->
          let prime = name ^ ext in
          Variables.add name (make_term tm srt prime) acc)
        map Variables.empty

    let middlestate_functions solver tm srt map inputs : Term.term Variables.t =
      Variables.fold
        (fun name _ acc ->
          let f = "f" ^ name in
          Variables.add name
            (Solver.synth_fun solver tm f (Array.of_list inputs) srt None)
            acc)
        map Variables.empty

    let find_sp map = Variables.find "SP" map
    let find_pc map = Variables.find "PC" map
    let find_reg map i = Variables.find ("R" ^ i) map
    let find_mem_reg map i = Variables.find ("MR" ^ i) map
    let find_glob map n = Globals.find n map
    let term_eq tm l r = Term.mk_term tm Kind.Equal (Array.of_list [ l; r ])

    let new_solver (tm, verb) =
      let solver = Solver.mk_solver ~logic:"ALL" tm in
      Solver.set_option solver "sygus" "true";
      Solver.set_option solver "full-sygus-verify" "true";
      Solver.set_option solver "sygus-enum" "fast";
      Solver.set_option solver "sygus-si" "all";
      Solver.set_option solver "incremental" "true";

      if verb then Solver.set_option solver "output" "sygus";
      solver

    (* Adds a dummy sygus problem: create a function f(x) s.t. f(0) = 0
       Functionally this turns a sygus problem into a regular sat problem over the constraints. *)
    let add_dummy_sygus tm solver =
      let intsort = Sort.mk_int_sort tm in
      let zero = Term.mk_int tm 0 in

      let dummy_in = Term.mk_var_s tm intsort "dummy_in" in
      let s =
        Solver.synth_fun solver tm "dummy"
          (Array.of_list [ dummy_in ])
          intsort None
      in
      let uf = Term.mk_term tm Kind.Apply_uf (Array.of_list [ s; zero ]) in
      Solver.add_sygus_constraint solver (term_eq tm uf zero)
  end

  module Asl_util = struct
    open LibASL

    type vmap = Term.term Cvc_util.Variables.t

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
            (Printf.sprintf "Internal: converting unexpected slice %s"
               (Utils.to_string @@ Asl_utils.PP.pp_slice n))
      | LExpr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected lexpr %s"
               (Asl_utils.pp_lexpr n))
      | Expr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected expr %s"
               (Asl_utils.pp_expr n))
      | Addr n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected address expr %s"
               (Asl_utils.pp_expr n))
      | Stmt n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected stmt %s"
               (Asl_utils.pp_stmt n))
      | Fun n ->
          failwith
            (Printf.sprintf "Internal: converting unexpected function %s" n)

    class translator =
      object (this)
        val mutable ivars = Cvc_util.Variables.empty
        val mutable updated : string list = []

        method was_updated s =
          Option.is_some (List.find_opt (String.equal s) updated)

        method cvc_of_stmtlist (tm : TermManager.tm) (fromv : vmap) (tov : vmap)
            (stmts : Asl_ast.stmt list) =
          let cvc_of_slice (s : Asl_ast.slice) : Op.op =
            match s with
            | Slice_LoWd (Expr_LitInt l, Expr_LitInt h) ->
                Op.mk_op tm Kind.Bitvector_extract
                  (Array.of_list [ int_of_string h - 1; int_of_string l ])
            | _ -> unexpected @@ Slice s
          in

          let cvc_of_lexpr (e : Asl_ast.lexpr) : Term.term =
            match e with
            | LExpr_Var (Ident "SP_EL0") ->
                updated <- "SP" :: updated;
                Cvc_util.find_sp tov
            | LExpr_Var (Ident "_PC") ->
                updated <- "PC" :: updated;
                Cvc_util.find_pc tov
            | LExpr_Array (LExpr_Var (Ident "_R"), Expr_LitInt i) ->
                updated <- ("R" ^ i) :: updated;
                Cvc_util.find_reg tov i
            | _ -> unexpected @@ LExpr e
          in

          let cvc_of_function (s : string) : Kind.t =
            match s with
            (* for simplicity, everything is an int, so ZeroExtending can be treated as a noop *)
            | _ when String.equal s "ZeroExtend" -> Kind.Null_term
            | _ when String.equal s "add_bits" -> Kind.Add
            | _ -> unexpected @@ Fun s
          in

          let cvc_of_addr (write : bool) (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                if write then updated <- ("MR" ^ i) :: updated;
                Cvc_util.find_mem_reg (if write then tov else fromv) i
            | _ -> unexpected @@ Addr e
          in

          let rec cvc_of_expr (e : Asl_ast.expr) : Term.term =
            match e with
            | Expr_Array (Expr_Var (Ident "_R"), Expr_LitInt i) ->
                Cvc_util.find_reg fromv i
            | Expr_Var (Ident n) -> Cvc_util.Variables.find n ivars
            | Expr_TApply (FIdent ("Mem.set", _), _, es) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Term.mk_term tm Kind.Equal
                  (Array.of_list [ cvc_of_addr true addr; cvc_of_expr value ])
            | Expr_TApply (FIdent ("Mem.read", _), _, es) ->
                cvc_of_addr false (List.hd es)
            | Expr_TApply (FIdent (f, _), _, es) -> (
                match cvc_of_function f with
                | Kind.Null_term -> cvc_of_expr (List.hd es)
                | k ->
                    Term.mk_term tm k (Array.of_list (List.map cvc_of_expr es)))
            | Expr_Slices (e, slices) ->
                (* Pretend slices aren't real *)
                ignore (List.map cvc_of_slice slices);
                cvc_of_expr e
                (* let sliced =
                  List.fold_left
                    (fun acc s ->
                      Term.mk_term_op tm (cvc_of_slice s)
                        (Array.of_list [ acc ]))
                    (cvc_of_expr e) slices *)
            | Expr_Field _ -> Term.mk_true tm
            | Expr_LitInt s -> Term.mk_int tm @@ int_of_string s
            | Expr_LitBits s ->
                Term.mk_int tm @@ Int64.to_int @@ Int64.of_string @@ "0b" ^ s
            | _ -> unexpected @@ Expr e
          in

          let cvc_of_stmt (s : Asl_ast.stmt) =
            match s with
            | Stmt_Assign (l, r, _) ->
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list [ cvc_of_lexpr l; cvc_of_expr r ]))
            | Stmt_ConstDecl (_, Ident n, exp, _) ->
                ivars <- Cvc_util.Variables.add n (cvc_of_expr exp) ivars;
                None
            | Stmt_VarDecl _ -> None
            | Stmt_VarDeclsNoInit _ -> None
            | Stmt_Assert _ -> None
            | Stmt_TCall (FIdent ("Mem.set", _), _, es, _) ->
                let addr = List.hd es in
                let value = List.hd (List.rev es) in
                Some
                  (Term.mk_term tm Kind.Equal
                     (Array.of_list
                        [ cvc_of_addr true addr; cvc_of_expr value ]))
            | Stmt_TCall (FIdent (_f, _), _, _es, _) -> None
            | Stmt_If _ -> None
            | Stmt_Throw _ -> None
            | _ -> unexpected @@ Stmt s
          in

          let updates = List.filter_map cvc_of_stmt stmts in
          let no_updates =
            Cvc_util.Variables.fold
              (fun key term acc ->
                if this#was_updated key then acc
                else
                  Term.mk_term tm Kind.Equal
                    (Array.of_list [ term; Cvc_util.Variables.find key tov ])
                  :: acc)
              fromv []
          in
          updates @ no_updates
      end

    let cvc_of_stmtlist tm fromv tov stmts =
      (new translator)#cvc_of_stmtlist tm fromv tov stmts
  end

  module Spec = struct
    type speclang =
      | Term of Kind.t * speclang list
      | Const of int
      | Bool of bool
      | Pre of string
      | Post of string

    let rec collect_globs s =
      match s with
      | Post n -> [ n ]
      | Pre n -> [ n ]
      | Term (_, ss) -> List.flatten @@ List.map collect_globs ss
      | _ -> []

    let rec sanity_guar_uses_posts s =
      match s with
      | Post _ -> failwith "Sanity check: guarantee includes a post-state?"
      | Term (_, ss) -> List.iter sanity_guar_uses_posts ss
      | _ -> ()

    let input (r : string) (g : string) : speclang * speclang =
      (* TODO: this is a dummy impl *)
      let parse s =
        ignore s;
        Bool true
      in
      let guar = parse g in

      sanity_guar_uses_posts guar;
      (parse r, guar)

    let rec cvc_of_spec tm fromv tov spec =
      let subcall = cvc_of_spec tm fromv tov in

      match spec with
      | Term (k, ts) -> Term.mk_term tm k (Array.of_list @@ List.map subcall ts)
      | Const i -> Term.mk_int tm i
      | Bool b -> Term.mk_bool tm b
      | Pre s -> Cvc_util.find_glob fromv s
      | Post s -> Cvc_util.find_glob tov s
  end

  let subset_only_mem vars : string list =
    Cvc_util.Variables.fold
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
         (fun m -> List.map snd (Cvc_util.Variables.bindings m))
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
                 let glob = Cvc_util.Globals.find i (access_primes lv sm) in
                 let mem = Cvc_util.Variables.find s (access_primes lv im) in
                 Cvc_util.term_eq tm glob mem)
               [ 0; 1; 2; 3; 4; 5; 6; 7 ])
         c

  let check_in_order sp (i1, i2) (r, g) (iterms, sterms) sort combination =
    let tm = fst sp in
    let solver = Cvc_util.new_solver sp in

    let decl_as_sygus tms =
      List.map
        (fun (i, m) ->
          ( i,
            Cvc_util.Variables.map
              (fun t -> Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        tms
    in
    let sy_sterms = decl_as_sygus sterms in
    let sy_iterms = decl_as_sygus iterms in

    let assume_transitions =
      (* S0 to S1 over R *)
      [
        Spec.cvc_of_spec tm
          (access_primes 0 sy_sterms)
          (access_primes 1 sy_sterms)
          r;
      ]
      (* S1 to S2 over i1 *)
      @ Asl_util.cvc_of_stmtlist tm
          (access_primes 1 sy_iterms)
          (access_primes 2 sy_iterms)
          i1
      (* S2 to S3 over R *)
      @ [
          Spec.cvc_of_spec tm
            (access_primes 2 sy_sterms)
            (access_primes 3 sy_sterms)
            r;
        ]
      (* S3 to S4 over i2 *)
      @ Asl_util.cvc_of_stmtlist tm
          (access_primes 3 sy_iterms)
          (access_primes 4 sy_iterms)
          i2
      (* S4 to S5 over R *)
      @ [
          Spec.cvc_of_spec tm
            (access_primes 4 sy_sterms)
            (access_primes 5 sy_sterms)
            r;
        ]
    in
    List.iter (Solver.add_sygus_assume solver) assume_transitions;

    let assume_combination =
      create_combination tm combination sy_sterms sy_iterms
    in
    List.iter (Solver.add_sygus_assume solver) assume_combination;

    let constrain_guarantees =
      [
        Spec.cvc_of_spec tm
          (access_primes 2 sy_sterms)
          (access_primes 2 sy_sterms)
          g;
        Spec.cvc_of_spec tm
          (access_primes 4 sy_sterms)
          (access_primes 4 sy_sterms)
          g;
      ]
    in
    List.iter (Solver.add_sygus_constraint solver) constrain_guarantees;

    Cvc_util.add_dummy_sygus tm solver;
    let result = Solver.check_synth solver in
    SynthResult.has_solution result

  let check_out_order sp (i1, i2) (r, _g) (iterms, sterms) sort combination =
    let tm = fst sp in
    let solver = Cvc_util.new_solver sp in

    let decl_as_sygus tms =
      List.map
        (fun (i, m) ->
          ( i,
            Cvc_util.Variables.map
              (fun t -> Solver.declare_sygus_var solver (Term.to_string t) sort)
              m ))
        tms
    in
    let sy_sterms = decl_as_sygus sterms in
    let sy_iterms = decl_as_sygus iterms in

    let first_state_map = access_primes 0 sy_iterms in
    let first_state_vars =
      List.map snd @@ Cvc_util.Variables.bindings first_state_map
    in
    let state_funcs =
      Cvc_util.middlestate_functions solver tm sort first_state_map
        first_state_vars
    in
    ignore state_funcs;

    (* TODO: segfaulting
    let all_state_vars =
      List.flatten
      @@ List.map
           (fun i -> (List.map snd) (Cvc_util.Variables.bindings @@ snd i))
           sy_iterms
    in

    let sygus_funcs_one =
      Cvc_util.Variables.map
        (fun t ->
          Term.mk_term tm Kind.Apply_uf (Array.of_list (t :: all_state_vars)))
        state_funcs
    in
    let sygus_funcs_two = Cvc_util.promote_variables tm sort sygus_funcs_one in
    *)
    let assume_transitions =
      (* S0 to S1 over R *)
      [
        Spec.cvc_of_spec tm
          (access_primes 0 sy_sterms)
          (access_primes 1 sy_sterms)
          r;
      ]
      (* S1 to S2 over i2 *)
      @ Asl_util.cvc_of_stmtlist tm
          (access_primes 1 sy_iterms)
          (access_primes 2 sy_iterms)
          i2
      (* S2 to S3 over R *)
      @ [
          Spec.cvc_of_spec tm
            (access_primes 2 sy_sterms)
            (access_primes 3 sy_sterms)
            r;
        ]
      (* S3 to S4 over i1 *)
      @ Asl_util.cvc_of_stmtlist tm
          (access_primes 3 sy_iterms)
          (access_primes 4 sy_iterms)
          i1
      (* S4 to S5 over R *)
      @ [
          Spec.cvc_of_spec tm
            (access_primes 4 sy_sterms)
            (access_primes 5 sy_sterms)
            r;
        ]
    in
    List.iter (Solver.add_sygus_assume solver) assume_transitions;
    let assume_combination =
      create_combination tm combination sy_sterms sy_iterms
    in
    List.iter (Solver.add_sygus_assume solver) assume_combination;

    (* TODO: depends on segfaulting
    let constrain_transitions =
      (* S0 to f0 over R *)
      [ Spec.cvc_of_spec tm (access_primes 0 sy_sterms) sygus_funcs_one r ]
      (* f0 to S6 over i1 *)
      @ Asl_util.cvc_of_stmtlist tm sygus_funcs_one
          (access_primes 6 sy_iterms)
          i1
      (* S6 to f1 over R *)
      @ [ Spec.cvc_of_spec tm (access_primes 6 sy_iterms) sygus_funcs_two r ]
      (* f6 to S7 over i2 *)
      @ Asl_util.cvc_of_stmtlist tm sygus_funcs_two
          (access_primes 7 sy_iterms)
          i2
      (* S7 back to S5 over R *)
      @ [
          Spec.cvc_of_spec tm
            (access_primes 7 sy_iterms)
            (access_primes 5 sy_iterms)
            r;
        ]
    in
    List.iter (Solver.add_sygus_constraint solver) constrain_transitions;
    *)
    let result = Solver.check_synth solver in
    SynthResult.has_solution result

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
      Cvc_util.make_register_vars tm var_sort (unpack_sum block_semantics pair)
    in

    let spec_names = Spec.collect_globs rely @ Spec.collect_globs guarantee in
    let spec_terms = Cvc_util.make_spec_vars tm var_sort spec_names in

    let inst_terms_primes =
      (0, inst_terms)
      :: List.map
           (fun i ->
             ( i,
               Cvc_util.promote_variables
                 ~ext:("'" ^ string_of_int i)
                 tm var_sort inst_terms ))
           [ 1; 2; 3; 4; 5; 6; 7 ]
    in
    let spec_terms_primes =
      (0, spec_terms)
      :: List.map
           (fun i ->
             ( i,
               Cvc_util.promote_variables
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

    let valid_in_order =
      List.filter
        (check_in_order sp code spec terms var_sort)
        all_possible_solver_combinations
    in
    if verb then
      print_endline
        (Printf.sprintf "    [!] %i/%i address mappings are valid in-order"
           (List.length valid_in_order)
           (List.length all_possible_solver_combinations));

    let valid_out_order =
      List.filter (check_out_order sp code spec terms var_sort) valid_in_order
    in

    (* If these are different then at least one valid in-order combination couldn't prove validity out-of-order *)
    List.length valid_out_order == List.length valid_in_order
end
