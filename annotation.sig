signature annotation =
sig
  include Abbrev
  type annotation
  type printer = (unit,unit) smpp.t
  val ST                : string -> annotation
  val Q                 : term quotation -> annotation
  val anno_tac          : annotation list -> tactic
  val anno_subgoals_tac : annotation list -> tactic -> tactic
  val anno_final_tac    : annotation list -> tactic -> tactic
  val init_proof        : string -> tactic
  val pp_proof          : unit -> printer
  val add_tex           : term -> printer
end
