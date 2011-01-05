structure annotation :> annotation =
struct

open bossLib

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

fun pp_description_element pps = let
  fun f (String s) = PP.add_string pps s
    | f (Term t) = (
        PP.add_string pps "\\texttt{";
        EmitTeX.raw_pp_term_as_tex overrides pps t;
        PP.add_string pps "}")
in f end

fun pp_description pps = let
  fun f [] = ()
    | f (d::ds) = (
        pp_description_element pps d;
        f ds)
in f end

fun pp_asl pps = let
  fun f n [] = ()
    | f n (a::asl) = (
        PP.add_string pps (Int.toString n);
        PP.add_string pps ": ";
        EmitTeX.raw_pp_term_as_tex overrides pps a;
        PP.add_newline pps;
        f (n+1) asl )
in f 0 end

fun pp_goal pps (asl,w) = (
  PP.add_string pps "\\begin{alltt}";
  PP.add_newline pps;
  EmitTeX.raw_pp_term_as_tex overrides pps w;
  PP.add_newline pps;
  PP.add_string pps "----------";
  PP.add_newline pps;
  pp_asl pps asl;
  PP.add_string pps "\\end{alltt}")

fun pp_proof_state pps = let
  fun f (Goal g) = pp_goal pps g
    | f (Goals gs) = (
        PP.add_string pps ("\\\\ "^(Int.toString(List.length gs))^" subgoals:");
        PP.add_newline pps;
        List.app (fn g => (pp_goal pps g; PP.add_newline pps)) gs)
    | f Done = (PP.add_string pps " and we're done."; PP.add_newline pps)
in f end

fun pp_a_proof pps = let
  fun f [] = ()
    | f ((desc,state)::xs) =
      (PP.begin_block pps PP.CONSISTENT 0;
       pp_description pps desc;
       PP.add_newline pps;
       pp_proof_state pps state;
       PP.add_newline pps;
       PP.end_block pps;
       f xs)
in f end

fun pp_proof pps = pp_a_proof pps (List.rev (!proof))

end
