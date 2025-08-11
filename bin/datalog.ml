module DL = Datalog_caml_interface
open Util
open Lifter

(*
  Wrapper around the datalog engine
*)
module Datalog : sig
  val compute_reorderable_pairs :
    Lifter.blockdata Lifter.Blocks.t -> bool -> (int * int) list
end = struct
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
    let _query_rel1 = DL.Rel1.find
    let query_rel2 = DL.Rel2.find

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

    let addr_register =
      get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "addr_register"

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

    let add_addr_reg (db : db) (ins : int) (reg : string) =
      add_rel2 db addr_register (ins, reg)

    let add_control_inst (db : db) (ins : int) =
      add_rel1 db control_instruction ins

    let add_fence_inst (db : db) (ins : int) = add_rel1 db fence_instruction ins
    let query_execution_order (db : db) = query_rel2 db execution_order
  end

  let compute_reorderable_pairs (blocks : Lifter.blockdata Lifter.Blocks.t)
      (verb : bool) =
    let db = load () in

    let base_facts_for_block (name : string) (block : Lifter.blockdata) : unit =
      let instruction_addresses = Lifter.generate_addresses block in
      let only_address item = match item with i, _ -> i in
      let only_sem item = match item with _, s -> s in

      let gen_facts_over_instructions i1 i2 =
        Helpers.add_instruction_order db (only_address i1) (only_address i2);
        Helpers.add_instruction_in_block db name (only_address i1);

        let facts = Semantics.facts (only_sem i1) in
        List.iter
          (fun v ->
            Helpers.add_source_reg db (only_address i1) (Semantics.regSymb v))
          facts.read;
        List.iter
          (fun v ->
            Helpers.add_dest_reg db (only_address i1) (Semantics.regSymb v))
          facts.write;
        List.iter
          (fun v ->
            Helpers.add_addr_reg db (only_address i1) (Semantics.regSymb v))
          facts.addr;
        if Semantics.hasCtrl facts then
          Helpers.add_control_inst db (only_address i1);
        if facts.fence then Helpers.add_fence_inst db (only_address i1);
        i2
      in

      (* Add all facts that are per-instruction *)
      ignore
        (List.fold_left gen_facts_over_instructions
           (List.hd instruction_addresses)
           (List.tl instruction_addresses));
      (* Add ordering of blocks *)
      List.iter
        (fun (n, _) -> Helpers.add_block_order db name (b64_bytes n))
        block.outgoing_edges
    in

    Lifter.Blocks.iter (fun k v -> base_facts_for_block (b64_bytes k) v) blocks;

    List.iter
      (fun i ->
        match i with i1, i2 -> print_endline (Printf.sprintf "(%i %i)" i1 i2))
      (Helpers.query_execution_order db);

    ignore verb;
    []
end
