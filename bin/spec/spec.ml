open Spec_analysis
open Spec_lang
open Spec_parse
open Cvc5

module type Spec = sig
  module Lang : SpecLang

  (* Re-type the Analysis module using the types from the imported Lang *)
  module Analysis : sig
    val sanity : Lang.spec -> unit
    val spec_syms : Lang.spec * Lang.spec -> string list
    val topo_iter : (string -> Lang.spec_body -> unit) -> Lang.spec -> unit
  end

  module Parse : SpecParse

  val input : string -> string -> Lang.spec * Lang.spec
end

module Spec : Spec = struct
  module Lang = SpecLang
  module Analysis = SpecAnalysis
  module Parse = SpecParse

  let input (r : string) (g : string) : Lang.spec * Lang.spec =
    let rely = SpecParse.parse r in
    let guar = SpecParse.parse g in

    Analysis.sanity rely;
    Analysis.sanity guar;

    (rely, guar)
end
