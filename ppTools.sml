structure ppTools :> ppTools = struct
open Parse term_pp_types annotation Thm Term boolSyntax smpp infix >> infix >-
type rule = {
term_name : string, fixity : fixity,
pp_elements: pp_element list,
paren_style : ParenStyle, block_style : PhraseBlockStyle * block_info}
val exp_rule = {
  block_style = (NoPhrasing, (PP.INCONSISTENT, 0)),
  paren_style = OnlyIfNecessary,
  pp_elements = [TOK "<EXP0>", TM, TOK "<EXP1>", TM, TOK "<EXP2>"],
  term_name = "**",
  fixity = Closefix }
fun pp_to_string w pp a = PP.pp_to_string w (fn pps=>fn()=>()before(pp(a,pps)))()
val get_info = fupdate Lib.I >- return
val infinity = 99999
fun sum_printer _ _ sysprinter {add_string,...} (gp,_,_) d tm = let
  val add_term = sysprinter (gp,Top,Top) (d-1)
  val pp_term = sysprinter (RealTop,RealTop,RealTop) d
  fun add_stringsz ssz = liftpp (fn pps => PP.add_stringsz pps ssz)
  fun term_to_string tm info = pp_to_string infinity (pp_term tm) info
  fun add_small_term (tm,k) = get_info >- (fn info => let
    val s = term_to_string tm info
    val sz = if k = 0 then 0 else Int.max(4,((String.size s) div k)+2)
  in add_stringsz (s,sz) end)
  val (_,[f,s]) = strip_comb tm
  val (m,fm) = dest_abs f
  val (_,n) = dest_comb s
  local open numSyntax Feedback in
  val n = dest_suc n handle HOL_ERR _ => mk_minus(n,term_of_int 1)
  end
in (add_string "<SUM0>" >>
    add_small_term (m,0) >>
    add_stringsz ("=0",0) >>
    add_string "<SUM1>" >>
    add_small_term (n,5) >>
    add_string "<SUM2>" >>
    add_term fm)
end
val sum_rule = ("ppTools.sum_printer",``SIGMA (λm. f m) (count n)``,sum_printer)
fun spaceless s = String.translate (fn #" " => "" | c => String.str c) s
val width = 80
fun write_file name ppf =
  TextIO.output(TextIO.openOut ((spaceless name)^"Proof.tex"), pp_to_string width ppf ())
fun write_proof ors proof = write_file (proof_name proof) (pp_proof_as_tex ors proof)
fun write_thm_only ors (name,thm) =
  write_file name (block PP.CONSISTENT 0 (
     add_string "Theorem: " >> add_string name >>
     add_newline >> add_string "\\begin{HOLblock}" >>
     pp_term_as_tex ors (concl thm) >>
     add_newline >> add_string "\\end{HOLblock}" >> add_newline))
end
