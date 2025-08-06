module DL = Datalog_caml_interface
open Util
open Lifter
open Semantics

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

  module Helpers = struct
    let _get_rel1 ~k name = DL.Rel1.create ~k name
    let get_rel2 ~k1 ~k2 name = DL.Rel2.create ~k1 ~k2 name
    let _get_rel3 ~k1 ~k2 ~k3 name = DL.Rel3.create ~k1 ~k2 ~k3 name
    let _add_rel1 db rel arg = DL.Rel1.add_list db rel [ arg ]
    let add_rel2 db rel arg = DL.Rel2.add_list db rel [ arg ]
    let _add_rel3 db rel arg = DL.Rel3.add_list db rel [ arg ]
    let _query_rel1 = DL.Rel1.find
    let query_rel2 = DL.Rel2.find
  end

  module Relations = struct
    let instruction_order =
      Helpers.get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "instruction_order"

    let instruction_in_block =
      Helpers.get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.string "instruction_in_block"

    let block_order =
      Helpers.get_rel2 ~k1:DL.Univ.string ~k2:DL.Univ.string "block_order"

    let execution_order =
      Helpers.get_rel2 ~k1:DL.Univ.int ~k2:DL.Univ.int "execution_order"
  end

  let add_instruction_order (db : db) (ins1 : int) (ins2 : int) =
    Helpers.add_rel2 db Relations.instruction_order (ins1, ins2)

  let add_instruction_in_block (db : db) (block : string) (ins : int) =
    Helpers.add_rel2 db Relations.instruction_in_block (ins, block)

  let add_block_order (db : db) (block1 : string) (block2 : string) =
    Helpers.add_rel2 db Relations.block_order (block1, block2)

  let query_execution_order (db : db) =
    Helpers.query_rel2 db Relations.execution_order

  let compute_reorderable_pairs (blocks : Lifter.blockdata Lifter.Blocks.t)
      (verb : bool) =
    let db = load () in
    let base_facts_for_block (name : string) (block : Lifter.blockdata) : unit =
      let instruction_addresses = Semantics.generate_addresses block in
      let instruction_folder i1 i2 =
        add_instruction_order db i1 i2;
        i2
      in

      ignore
        (List.fold_left instruction_folder
           (List.hd instruction_addresses)
           (List.tl instruction_addresses));
      List.iter (add_instruction_in_block db name) instruction_addresses;
      List.iter
        (fun (n, _) -> add_block_order db name (b64_bytes n))
        block.outgoing_edges
    in

    Lifter.Blocks.iter (fun k v -> base_facts_for_block (b64_bytes k) v) blocks;

    List.iter
      (fun i ->
        match i with i1, i2 -> print_endline (Printf.sprintf "(%i %i)" i1 i2))
      (query_execution_order db);

    ignore verb;
    []
end
