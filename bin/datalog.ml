module DL = Datalog_caml_interface
open Lifter

(*
  Wrapper around the datalog engine
*)
module type Datalog = sig
  val compute_reorderable_pairs :
    Lifter.IR.blocks -> bool -> ((string * int) * (string * int)) list
end

module Datalog : Datalog = struct
  type db = DL.Logic.DB.t

  let load () =
    let db = DL.Logic.DB.create () in
    let () =
      if not (DL.Parse.load_file db "bin/reorderRules.dl") then
        failwith "Internal error: failed to initialise datalog"
    in
    db

  module VisitAST = struct end

  module Helpers = struct
    let get_rel1 ~k name = DL.Rel1.create ~k name
    let get_rel2 ~k1 ~k2 name = DL.Rel2.create ~k1 ~k2 name
    let _get_rel3 ~k1 ~k2 ~k3 name = DL.Rel3.create ~k1 ~k2 ~k3 name
    let add_rel1 db rel arg = DL.Rel1.add_list db rel [ arg ]
    let add_rel2 db rel arg = DL.Rel2.add_list db rel [ arg ]
    let _add_rel3 db rel arg = DL.Rel3.add_list db rel [ arg ]
    let query_rel1 = DL.Rel1.find
    let query_rel2 = DL.Rel2.find

    let func_rel2_int db rel arg =
      List.find_map
        (fun ((k1 : int), k2) -> if k1 == arg then Some k2 else None)
        (DL.Rel2.find db rel)

    let reorderable = get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "reorderable"

    let instruction_order =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "instruction_order"

    let instruction_in_block =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "instruction_in_block"

    let block_order =
      get_rel2 ~k1:DL.Univ.string ~k2:DL.Univ.string "block_order"

    let execution_order =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "execution_order"

    let source_register =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "source_register"

    let dest_register =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "dest_register"

    let load_register =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "load_register"

    let store_register =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "store_register"

    let control_instruction = get_rel1 ~k:DL.Univ.int "control_instruction"
    let fence_instruction = get_rel1 ~k:DL.Univ.int "fence_instruction"

    let add_instruction_order (db : db) (ins1 : int) (ins2 : int) =
      add_rel2 db instruction_order (ins1, ins2)

    let add_instruction_in_block (db : db) (block : string) (ins : int) =
      add_rel2 db instruction_in_block (ins, block)

    let add_block_order (db : db) (block1 : string) (block2 : string) =
      add_rel2 db block_order (block1, block2)

    let add_source_reg (db : db) (ins : int) (reg : string) =
      add_rel2 db source_register (ins, reg)

    let add_dest_reg (db : db) (ins : int) (reg : string) =
      add_rel2 db dest_register (ins, reg)

    let add_load_reg (db : db) (ins : int) (reg : string) =
      add_rel2 db load_register (ins, reg)

    let add_store_reg (db : db) (ins : int) (reg : string) =
      add_rel2 db store_register (ins, reg)

    let add_control_inst (db : db) (ins : int) =
      add_rel1 db control_instruction ins

    let add_fence_inst (db : db) (ins : int) = add_rel1 db fence_instruction ins
    let query_execution_order (db : db) = query_rel2 db execution_order
    let query_reorderable (db : db) = query_rel2 db reorderable
  end

  let hasCtrl (i : Lifter.IR.instruction) =
    Option.is_some (List.find_opt (Lifter.IR.var_eq Lifter.IR.PC) i.write)

  let _memop_explain (db : db) =
    let memop = Helpers.get_rel1 ~k:DL.Univ.int "memOp" in
    List.iter
      (fun i -> print_endline (Printf.sprintf "memOp: %i" i))
      (Helpers.query_rel1 db memop);

    let load = Helpers.get_rel1 ~k:DL.Univ.int "load" in
    List.iter
      (fun i -> print_endline (Printf.sprintf "load: %i" i))
      (Helpers.query_rel1 db load);

    let store = Helpers.get_rel1 ~k:DL.Univ.int "store" in
    List.iter
      (fun i -> print_endline (Printf.sprintf "store: %i" i))
      (Helpers.query_rel1 db store)

  let _linear_explain (db : db) =
    let linear = Helpers.get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "linear" in

    List.iter
      (fun (i1, i2) ->
        print_endline (Printf.sprintf "(%i -> %i)" i1 i2);
        let why_ppo =
          DL.Logic.ask db
            (DL.Parse.term_of_string (Printf.sprintf "ppo(%i,%i)" i1 i2))
        in
        List.iter (fun x -> print_endline (DL.Logic.T.to_string x)) why_ppo)
      (Helpers.query_rel2 db linear)

  let compute_reorderable_pairs (blocks : Lifter.IR.blocks) (verb : bool) =
    let db = load () in
    _linear_explain db;

    let base_facts_for_block (name : string) (block : Lifter.IR.block) : unit =
      (* This block's position relative to other blocks *)
      List.iter (fun (n, _) -> Helpers.add_block_order db name n) block.edges;

      let gen_facts_over_instructions (i1 : int * Lifter.IR.instruction)
          (i2 : int * Lifter.IR.instruction) =
        (* instructions have order relative to each other *)
        Helpers.add_instruction_order db (fst i1) (fst i2);
        (* instructions have membership in a block *)
        Helpers.add_instruction_in_block db name (fst i1);

        (* Individual instruction facts for i1; i2 happens in the next "fold" *)
        List.iter
          (fun var ->
            Helpers.add_source_reg db (fst i1) (Lifter.IR.string_of_var var))
          (snd i1).read;
        List.iter
          (fun var ->
            Helpers.add_dest_reg db (fst i1) (Lifter.IR.string_of_var var))
          (snd i1).write;
        List.iter
          (fun var ->
            Helpers.add_load_reg db (fst i1) (Lifter.IR.string_of_var var))
          (snd i1).load;
        List.iter
          (fun var ->
            Helpers.add_store_reg db (fst i1) (Lifter.IR.string_of_var var))
          (snd i1).store;
        if (snd i1).fence then Helpers.add_fence_inst db (fst i1);
        if hasCtrl (snd i1) then Helpers.add_control_inst db (fst i1);

        i2
      in

      let instructions = Lifter.IR.I.bindings block.instructions in
      ignore
      @@ List.fold_left gen_facts_over_instructions (List.hd instructions)
           (List.tl instructions)
    in

    _linear_explain db;

    Lifter.IR.B.iter (fun k v -> base_facts_for_block k v) blocks;

    if verb then
      print_endline
        (Printf.sprintf
           "    [!] Generated execution order infers %i total pairs"
           (List.length (Helpers.query_execution_order db)));

    let reord = Helpers.query_reorderable db in
    print_endline
      (Printf.sprintf "[!] Found %i reorderable pairs..." (List.length reord));

    let find_block i =
      Option.get (Helpers.func_rel2_int db Helpers.instruction_in_block i)
    in

    List.map (fun (i1, i2) -> ((find_block i1, i1), (find_block i2, i2))) reord
end
