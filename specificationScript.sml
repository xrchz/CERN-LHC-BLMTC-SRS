open HolKernel bossLib Parse preliminariesTheory

val _ = new_theory "specification"

val valN_def = Define`
  valN n w =
  (* uncurried *)
    if n = 0 then 0 else
    (if w (n-1) then pwr (2,n-1) else 0) + valN (n-1) w`

val _ = overload_on("val20",``λw. valN 20 w``)

val SumOfPrevious_def = Define`
  SumOfPrevious n l t =
  (* capitalized sumOfPrevious *)
    if n = 0 then 0 else
    val20 (l (t-n)) + SumOfPrevious (n-1) l t`

val _ = set_fixity "IsWithin20PercentOf" (Infix(NONASSOC,450))

val IsWithin20PercentOf_def = Define`
  x IsWithin20PercentOf y = 4*y ≤ 5*x ∧ 5*x ≤ 6*y`
  (* changed definition to work on natural numbers *)
  (* maybe that's completely implausible... *)

val RSBehaviour_def = Define`
  RSBehaviour (datain, RSum00, RSum01, RSum02, RSum03, RSum04, RSum05,
                       RSum06, RSum07, RSum08, RSum09, RSum10, RSum11) =
  ∀t. t > 2097152 ⇒
    ((valN 20 (RSum00 t)) IsWithin20PercentOf (SumOfPrevious 0 datain t)) ∧
    (* changed ? to 0 *)
    ((valN 22 (RSum01 t)) IsWithin20PercentOf (SumOfPrevious 2 datain t)) ∧
    ((valN 22 (RSum02 t)) IsWithin20PercentOf (SumOfPrevious 8 datain t)) ∧
    ((valN 22 (RSum03 t)) IsWithin20PercentOf (SumOfPrevious 16 datain t)) ∧
    ((valN 26 (RSum04 t)) IsWithin20PercentOf (SumOfPrevious 64 datain t)) ∧
    ((valN 26 (RSum05 t)) IsWithin20PercentOf (SumOfPrevious 256 datain t)) ∧
    ((valN 32 (RSum06 t)) IsWithin20PercentOf (SumOfPrevious 2084 datain t)) ∧
    ((valN 32 (RSum07 t)) IsWithin20PercentOf (SumOfPrevious 8192 datain t)) ∧
    ((valN 36 (RSum08 t)) IsWithin20PercentOf (SumOfPrevious 32768 datain t)) ∧
    ((valN 36 (RSum09 t)) IsWithin20PercentOf (SumOfPrevious 131072 datain t)) ∧
    ((valN 40 (RSum10 t)) IsWithin20PercentOf (SumOfPrevious 524288 datain t)) ∧
    ((valN 40 (RSum11 t)) IsWithin20PercentOf (SumOfPrevious 2097152 datain t))
    (* changed RSum10 to RSum11 *)
    (* Changed Within20PercentOf to IsWithin20PercentOf in all the above *)`

val _ = export_theory ()
