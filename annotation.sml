structure annotation :> annotation =
struct

open bossLib smpp infix >>

datatype proof_state = Goal of goal | Goals of goal list | Done

datatype description_element = String of string | Term of term

type description = description_element list

type proof_element = description * proof_state

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

fun init_proof s goal = ALL_TAC goal before proof := [([String s, String "\n\n", String "Initial goal:"],Goal goal)]

fun anno_tac predesc goal = ALL_TAC goal before proof := (predesc_to_desc goal predesc,Goal goal) :: !proof

fun anno_subgoals_tac predesc tac goal = let val r as (subgoals,_) = tac goal
in r before proof := (predesc_to_desc goal predesc, Goals subgoals) :: !proof end

fun anno_final_tac predesc tac goal = tac goal before proof := (predesc_to_desc goal predesc, Done) :: !proof

val overrides = let val m = mungeTools.read_overrides "overrides" in fn x => Binarymap.peek(m,x) end

type printer = (unit,unit) smpp.t

fun add_tex tm = liftpp (fn pps => EmitTeX.raw_pp_term_as_tex overrides pps tm)

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

val pp_a_proof = let
  fun f [] = nothing
    | f ((desc,state)::xs) =
      (block PP.CONSISTENT 0 (
         pp_description desc >>
         add_newline >>
         pp_proof_state state >>
         add_newline ) >>
       f xs)
in f end

fun pp_proof () = pp_a_proof (List.rev (!proof))

end
