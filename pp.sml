structure pp :> pp = struct
open Parse term_pp_types annotation Thm Term boolSyntax smpp infix >>
val width = 80
val exp_rule = {
  block_style = (NoPhrasing, (PP.INCONSISTENT, 0)),
  paren_style = OnlyIfNecessary,
  pp_elements = [TOK "<EXP0>", TM, TOK "<EXP1>", TM, TOK "<EXP2>"],
  term_name = "**",
  fixity = Closefix }
fun SIGMA_count_printer (tyg,tmg) _ sysprinter {add_string,add_break,...} _ d tm = let
  val sys_add_term = sysprinter (Top,Top,Top) (d-1)
  fun pp_zero ppf pps x = PP.add_stringsz pps (PP.pp_to_string width ppf x,0)
  fun add_term tm = liftpp (fn pps => pp_zero (term_pp.pp_term tmg tyg PPBackEnd.raw_terminal) pps tm)
  val (_,[f,s]) = strip_comb tm
  val (m,fm) = dest_abs f
  val (_,n) = dest_comb s
  local open numSyntax Feedback in
  val n = dest_suc n handle HOL_ERR _ => mk_minus(n,term_of_int 1)
  end
in (add_string "<SUM0>" >>
    add_term m >>
    liftpp (fn pps => PP.add_stringsz pps ("=0",0)) >>
    add_string "<SUM1>" >>
    add_term n >>
    add_string "<SUM2>" >>
    sys_add_term fm)
end
val sum_user_printer = ("pp.SIGMA_count_printer",``SIGMA (λm. f m) (count n)``,SIGMA_count_printer)
fun load_rules (a1,a2) = ( a1 exp_rule; a2 sum_user_printer)
fun unload_rules (r1,r2) = ( r1 "sum_user_printer"; r2 {term_name="**",tok="<EXP0>"})
fun rules_around f x = (load_rules(temp_add_rule,temp_add_user_printer); f x; unload_rules(temp_remove_user_printer,temp_remove_termtok))
fun spaceless s = String.translate (fn #" " => "" | c => String.str c) s
fun write_file name (ppf : (unit,unit) smpp.t) =
  TextIO.output(TextIO.openOut ((spaceless name)^"Proof.tex"),
    PP.pp_to_string width (fn pps=>fn()=> #1(valOf(ppf((),pps)))) ())
val write_proof = rules_around (fn name => write_file name (pp_proof()))
fun write_thm_only thm = rules_around (fn name =>
  write_file name (block PP.CONSISTENT 0 (
     add_string "Theorem: " >> add_string name >>
     add_newline >> add_string "\\begin{alltt}" >>
     add_tex (concl thm) >>
     add_newline >> add_string "\\end{alltt}" >> add_newline)))
fun adjoin_rules () = load_rules (add_rule, add_user_printer)
end
