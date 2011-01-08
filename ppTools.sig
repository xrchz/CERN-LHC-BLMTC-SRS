signature ppTools = sig
  type rule = {term_name : string, fixity : Parse.fixity,
               pp_elements: Parse.pp_element list, paren_style : Parse.ParenStyle,
               block_style : Parse.PhraseBlockStyle * Parse.block_info}
  val exp_rule    : rule
  val sum_rule    : string * Term.term * term_grammar.userprinter
  val sum_printer : term_grammar.userprinter
  val write_proof : EmitTeX.override_map -> annotation.proof -> unit
  val write_thm_only : EmitTeX.override_map -> string * Thm.thm -> unit
end
