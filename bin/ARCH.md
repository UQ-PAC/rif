main:
    deps Protobuf, Gtirb
    open Lifter, Datalog, Solver, RGSpec, Util

    parse arguments
    read GTIRB file
    Lifter,     lift binary into semantics
    RGSpec,     read R/G specification
    Datalog,    generate pairs
    Solver,     solve pairs
    report errors

Lifter:
    deps Gtirb, ASL
    open Util

    map through GTIRB file to generate instruction_summary, and
    map through ASL ast to generate CVC constraints

Datalog:
    deps Datalog, reorderRules.dl
    open Lifter, Util

    map through lifter summary to generate pairs

Solver:
    deps Cvc5
    open Lifter, RGSpec, Util

    map through var combinations to see which ones fail

RGSpec:
    deps Cvc5
    open Util

    map through provided spec to generate CVC constraints

Util:
    deps Cvc5

    misc, and
    Cvc submodule to setup solver
