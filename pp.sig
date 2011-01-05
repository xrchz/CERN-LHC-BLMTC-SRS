signature pp = sig
  val adjoin_rules : unit -> unit
  val write_proof : string -> unit
  val write_thm_only : Thm.thm -> string -> unit
  val SIGMA_count_printer : term_grammar.userprinter
end
