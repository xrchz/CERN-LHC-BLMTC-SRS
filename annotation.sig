signature annotation =
sig
  include Abbrev
  type annotation
  val ST                : string -> annotation
  val Q                 : term quotation -> annotation
  val anno_tac          : annotation list -> tactic
  val anno_subgoals_tac : annotation list -> tactic -> tactic
  val anno_final_tac    : annotation list -> tactic -> tactic
  val init_proof        : tactic
  val pp_proof          : PP.ppstream -> unit
  val overrides         : EmitTeX.override_map
end
