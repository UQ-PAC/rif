# rif
---
A tool to uncover and resolve the effects of weak memory on a binary executable

## Map
- `lifter/`: files that define and produce the RIF tool's IR
  - `lifter_ir.ml`: the IR (basic blocks & instructions) and basic utilities
  - `lifter_elf.ml`: reading & processing GTIRB input from a file
  - `lifter_disassembly.ml`: feeding semi-processed GTIRB input into ASLp and generating semantics
  - `lifter.ml`: exposes "parse" (filename -> IR) and "resolve_ids" (blocks -> datalog output -> instructions)

- `spec/`: files that define and produce the specification
  - `spec_lang.ml`: the IR for the spec (constraints over two states, or functions from state 1 to 2)
  - `spec_parse.ml`: Angstrom parser for the spec language
  - `spec_analysis.ml`: very basic analysis for the spec, mostly unimplemented
  - `spec.ml`: exposes "input" (string, string -> spec, spec)

- `solver/`: files that take IRs and speak to the solver
  - `solver_state.ml`: custom state type.
    Has a map of "spec name" -> "memory at register" aliasing *and* a map of "memory at register" to "cvc5 term".
    Defines the "state_function", which is state -> string -> term option and "state_constraints" of state -> state -> term list.
    Defines functions for applying those to states.
  - `solver_utils.ml`: various utilities, pretty-printing, non-problem-specific setup, etc
  - `solver_instruction.ml`: turning an instruction into a state function
  - `solver_spec.ml`: turning a specification into a state function / state constraints
  - `solver.ml`: manages all interaction with cvc5.
    Exposes "solve_all" (pair list -> pair_list) and uses many intermediaries "down the stack" to a single cvc5 solver problem.

- `reorderRules.dl` and `datalog.ml`: rules definining the memory model (when can instructions reorder), and then code to read and process those rules. Exposes "compute_reorderable_pairs" (basic blocks -> list of pair identifiers)

- `main.ml`: read command-line flags and call everything else

Also in `lib/`:
- a git submodule for GTIRB protobuf definitions
- another git submodule for bindings that connect cvc5's C++ API to OCaml
- `option.ml` which just provides `Option.get` but with nicer error messages.
