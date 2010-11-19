open HolKernel bossLib boolLib designTheory specificationTheory lcsymtacs

val _ = new_theory "correctness"

val correctness = Q.store_thm("correctness",
`∀signals. RSDesign signals ⇒ RSBehaviour signals`,
FAIL_TAC "no proof yet")

val _ = export_theory ()
