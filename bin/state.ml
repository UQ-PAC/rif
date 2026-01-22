open Cvc5

module State = struct
  module M = Map.Make (String)

  type t = { map : Term.term M.t; solver : Solver.solver; sort : Sort.sort }

  (*
  let apply (state : t) (f : Func.t) : t =
    let values = List.map snd @@ M.bindings state.map |>
      fun v ->
        match Func.nondet f with
        | true -> Solver.declare_sygus_var state.solver ("???_" ^ fresh) state.sort :: v
        | false -> v
    in

    List.map (

    ) values
    *)
end

module MultiFunc = struct
  module M = Map.Make (String)

  type single = { nondet : bool; func : Term.term -> Term.term }
  type t = single M.t

  let id = ref 0

  let fresh =
    incr id;
    string_of_int !id

  let nondet_for (mf : t) s = (M.find s mf).nondet
  let apply_for (mf : t) s = (M.find s mf).func

  let fresh_nondeterminism solver sort =
    Solver.declare_sygus_var solver ("???_" ^ fresh) sort

  let apply (mf : t) (s : State.t) =
    let apply_for (mf : t) s =
      let single = M.find s mf in
      if single.nondet then ();
      (M.find s mf).func
    in
    ()
end
