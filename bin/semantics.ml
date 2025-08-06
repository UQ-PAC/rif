let instruction_width = 4

let generate_addresses (block : Lifter.blockdata) =
      List.mapi (fun ins _ -> block.offset + (ins * instruction_width)) block.block_semantics
