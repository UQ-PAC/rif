open Spec_analysis
open Spec_lang
open Spec_parse

module type Spec = sig
  module Analysis : SpecAnalysis
  module Lang : SpecLang
  module Parse : SpecParse

  val input : string -> string -> Lang.spec * Lang.spec
end

module Spec : Spec = struct
  module Analysis = SpecAnalysis
  module Lang = SpecLang
  module Parse = SpecParse

  let input (r : string) (g : string) : Lang.spec * Lang.spec =
    let rely = SpecParse.parse r in
    let guar = SpecParse.parse g in

    Analysis.sanity rely;
    Analysis.sanity guar;

    (rely, guar)
end
