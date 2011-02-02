structure annotation :> annotation =
struct

open bossLib smpp infix >>

datatype proof_state = Goal of goal | Goals of goal list | Done

datatype description_element = String of string | Term of term

type description = description_element list

type proof_element = description * proof_state

type proof = string * (proof_element list)

val proof_name = #1

local
  open Pickle
  val term = con1 (fn s => Parse.Term [QUOTE s]) (Parse.term_to_string) string
  val goal = pairGen (listGen term, term)
  val description_element = dataGen ("description_element",(fn String _ => 0 | Term _ => 1),
    [(fn pu => con1 String (fn String x => x) string),
     (fn pu => con1 Term (fn Term x => x) term)])
  val proof_state = dataGen ("proof_state",(fn Goal _ => 0 | Goals _ => 1 | Done => 2),
    [(fn pu => con1 Goal (fn Goal x => x) goal),
     (fn pu => con1 Goals (fn Goals x => x) (listGen goal)),
     (fn pu => con0 Done pu)])
  val description = listGen description_element
  val proof_element = pairGen (description, proof_state)
  val proof = pairGen (string, listGen proof_element)
in
  val proofs_pu = listGen proof
end

fun write_proofs (proofs : proof list) =
  Pickle.toString ((Feedback.trace("Unicode",0)
                     (Lib.with_flag(Globals.linewidth,10000)
                       (Pickle.pickler proofs_pu proofs)))
                   (Pickle.empty()))

fun read_proofs s = let
  val (proofs,_) = Pickle.unpickler proofs_pu (Pickle.fromString s)
in SOME proofs end

type data = Theory.LoadableThyData.t
val thydataty = "anno_proofs"
val (encode_proofs',decode_proofs) = Theory.LoadableThyData.new {
  thydataty=thydataty, merge=(fn(ps,more)=>more@ps),
  read=read_proofs, write=write_proofs}
fun encode_proofs x = {thydataty=thydataty,data=encode_proofs' x}

datatype predescription_element = ST of string | Q of term quotation

type annotation = predescription_element

fun predesc_to_desc (asl,w) = let
  val fvs = Term.free_varsl(w::asl)
  val parse = Parse.parse_in_context fvs
  fun f [] = []
    | f (ST s :: x) = String s :: f x
    | f (Q q :: x) = Term (parse q) :: f x
in f end

val ALL_TAC = Tactical.ALL_TAC

val proof = ref ([] : proof_element list)

fun anno_tac predesc goal = ALL_TAC goal before proof := (predesc_to_desc goal predesc,Goal goal) :: !proof

fun anno_subgoals_tac predesc tac goal = let val r as (subgoals,_) = tac goal
in r before proof := (predesc_to_desc goal predesc, Goals subgoals) :: !proof end

fun anno_final_tac predesc tac goal = tac goal before proof := (predesc_to_desc goal predesc, Done) :: !proof

fun init_proof s goal = ALL_TAC goal before proof := [([String "Theorem: ", String s, String "\n\n", String "Initial goal:"],Goal goal)]

fun anno_prove (name,q,tac) = let
  val thm = Q.prove(q, Tactical.THEN(init_proof name,tac))
in (thm,(name,List.rev(!proof))) end

fun anno_store_thm (name,q,tac) = let
  val thm = Q.store_thm(name, q, Tactical.THEN(init_proof name,tac))
in (thm,(name,List.rev(!proof))) end

fun pp_term_as_tex overrides tm =
  liftpp (fn pps => EmitTeX.raw_pp_term_as_tex overrides pps tm)

fun pp_proof_as_tex overrides = let
  val add_tex = pp_term_as_tex overrides
  val pp_asl = let
    fun f n [] = nothing
      | f n (a::asl) = (
          add_string (Int.toString n) >>
          add_string ": " >>
          add_tex a >>
          add_newline >>
          f (n+1) asl )
  in f 0 end
  fun pp_goal (asl,w) = (
    add_string "\\begin{HOLblock}" >>
    add_newline >>
    add_tex w >>
    add_newline >>
    add_string "\\HOLAsmSep{}" >>
    add_newline >>
    pp_asl asl >>
    add_string "\\end{HOLblock}")
  val pp_proof_state = let
    fun f (Goal g) = pp_goal g
      | f (Goals gs) = (
          add_string ("\\\\ "^(Int.toString(List.length gs))^" subgoals:") >>
          add_newline >>
          pr_list pp_goal add_newline gs)
      | f Done = (add_string " and we're done." >> add_newline)
  in f end
  val pp_description_element = let
    fun f (String s) = add_string s
      | f (Term t) = (
          add_string "\\HOLinline{" >>
          add_tex t >>
          add_string "}")
  in f end
  val pp_description = let
    fun f [] = nothing
      | f (d::ds) = (
          pp_description_element d >>
          f ds)
  in f end
  fun f [] = nothing
    | f ((desc,state)::xs) =
      (block PP.CONSISTENT 0 (
         pp_description desc >>
         add_newline >>
         pp_proof_state state >>
         add_newline ) >>
       f xs)
in f o #2 end

end
