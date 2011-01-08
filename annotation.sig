signature annotation =
sig
  type term             = Abbrev.term
  type 'a quotation     = 'a Abbrev.quotation
  type annotation
  val ST                : string -> annotation
  val Q                 : term quotation -> annotation
  type tactic           = Abbrev.tactic
  val anno_tac          : annotation list -> tactic
  val anno_subgoals_tac : annotation list -> tactic -> tactic
  val anno_final_tac    : annotation list -> tactic -> tactic
  type thm              = Abbrev.thm
  type proof
  val anno_prove        : string * term quotation * tactic -> thm * proof
  val anno_store_thm    : string * term quotation * tactic -> thm * proof
  val pp_proof_as_tex   : EmitTeX.override_map -> proof -> (unit,unit) smpp.t
  val pp_term_as_tex    : EmitTeX.override_map -> term -> (unit,unit) smpp.t
  val proof_name        : proof -> string
  type data             = Theory.LoadableThyData.t
  val thydataty         : string
  val encode_proofs     : proof list -> {thydataty:string,data:data}
  val decode_proofs     : data -> proof list option
end
