open HolKernel boolSimps bossLib Parse arithmeticTheory pred_setLib pred_setTheory lcsymtacs

val _ = new_theory "simplified"

(* Global Parameters:
     the width of every slice, width (or w);
     the input series, input.
   Each slice has
     w shift registers, named SR 0, SR 1, ..., SR (w-1);
     an output register.
   Each SR has a source:
     The source for SR 0 of slice 0 is the global input.
     The source for SR 0 of slice (SUC n) is the output of slice n.
     The source for SR (SUC m) is SR m of the same slice.
   Each SR has a series of update times:
     Update times for SR m of slice n: n + ((m + (SUC x)) * (w ** n)), for all x.
   At each update time, the SR gets the value of its source at the previous time step.
   The output of a slice at some time is the sum of its shift registers at the same time.  *)

val _ = Hol_datatype`
  parameters = <| width : num ; input : num -> num |>`;

(* update_times p n m = set of update times for SR m of slice n *)
val update_times_def = Define`
  update_times p n m = {n + ((m + (SUC x)) * (p.width ** n)) | 0 ≤ x}`;

(* last_update p n m t = the greatest update time of SR m of slice n that is not above t *)
(* note (count z = set of numbers less than z) *)
val last_update_def = Define`
  last_update p n m t = MAX_SET (update_times p n m ∩ count (SUC t))`;

val FINITE_INTER_count = Q.store_thm(
"FINITE_INTER_count",
`FINITE (s ∩ (count n))`,
match_mp_tac FINITE_INTER >> srw_tac [][])
val _ = export_rewrites["FINITE_INTER_count"]

(* source p n m = the source of input for SR m of slice n *)
(* output p n t = the output of slice n at time t *)
(* SR p n m t = the value of SR m of slice n at time t *)
val Slice_def = tDefine "Slice" `
  (source p 0 0 t = p.input t) ∧
  (source p (SUC n) 0 t = output p n t) ∧
  (source p n (SUC m) t = SR p n m t) ∧
  (output p n t = SIGMA (λm. SR p n m t) (count p.width)) ∧
  (SR p n m t = source p n m (last_update p n m t - 1))`
(*
Call graph, with termination measure:
                   (SR n m)  (n,m,2)
                 (source n m)  (n,m,1)
  (n-1,w,3)  (output (n-1)) (SR n (m-1))  (n,m-1,2)
(n-1,_,2)  (SR (n-1) _)
*)
(WF_REL_TAC
`inv_image ($< LEX $< LEX $<)
 (λx. case x of
      (INL (p,n,m,t)) -> (n,m,1) ||
      (INR (INR (p,n,m,t))) -> (n,m,2) ||
      (INR (INL (p,n,t))) -> (n,p.width,3))` >>
srw_tac [][IN_COUNT]);

open listTheory sortingTheory rich_listTheory

val source_0_thm = Q.store_thm(
"source_0_thm",
`!n t. n <= t ==> (source p 0 n t = p.input (t - n))`,
Induct >> srw_tac [][Slice_def] >>
srw_tac [][last_update_def] >>
MAX_SET_elim_tac >>
srw_tac [DNF_ss,ARITH_ss][NOT_EQUAL_SETS,update_times_def,EXP] >- (
  qexists_tac `0` >> DECIDE_TAC ) >>
fsrw_tac [ARITH_ss][ADD1] >>
AP_TERM_TAC >>
qmatch_rename_tac `z = t - (n + 1)` [] >>
qsuff_tac `t - (n + 1) <= z` >- DECIDE_TAC >>
first_x_assum match_mp_tac >>
DECIDE_TAC )

val output_0_thm = Q.store_thm(
"output_0_thm",
`∀t. p.width ≤ t ⇒ (output p 0 t = SIGMA (λx. p.input (t - x - 1)) (count p.width))`,
srw_tac [][Slice_def] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [ARITH_ss][last_update_def] >>
MAX_SET_elim_tac >>
srw_tac [ARITH_ss,DNF_ss][NOT_EQUAL_SETS,update_times_def,EXP] >- (
  qexists_tac `0` >> DECIDE_TAC ) >>
srw_tac [ARITH_ss][source_0_thm] >>
AP_TERM_TAC >>
fsrw_tac [ARITH_ss][ADD1] >>
qmatch_rename_tac `z = t - (n + 1)` [] >>
qsuff_tac `t - (n + 1) <= z` >- DECIDE_TAC >>
first_x_assum match_mp_tac >>
DECIDE_TAC);

val SIGMA_opposites = Q.store_thm(
"SIGMA_opposites",
`(!n. n < w ==> (f1 n = f2 (w - n - 1))) ==> (SIGMA f1 (count w) = SIGMA f2 (count w))`,
srw_tac [][SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST] >>
match_mp_tac PERM_SUM >>
qsuff_tac `PERM (MAP f1 (COUNT_LIST w)) (MAP f2 (REVERSE (COUNT_LIST w)))` >- (
  qmatch_abbrev_tac `PERM l1 l2 ==> PERM l3 l4` THEN
  qsuff_tac `PERM l1 l3 /\ PERM l2 l4` >- PROVE_TAC [PERM_SYM,PERM_TRANS] >>
  srw_tac [][Abbr`l1`,Abbr`l2`,Abbr`l3`,Abbr`l4`] >>
  match_mp_tac PERM_MAP >>
  PROVE_TAC [PERM_SET_TO_LIST_count_COUNT_LIST,PERM_REVERSE,PERM_SYM,PERM_TRANS] ) >>
match_mp_tac PERM_INTRO >>
match_mp_tac LIST_EQ >>
srw_tac [][EL_MAP,EL_REVERSE,LENGTH_COUNT_LIST,EL_COUNT_LIST] >>
`PRE (w - x) < w` by DECIDE_TAC THEN
fsrw_tac [][EL_COUNT_LIST,PRE_SUB1]);

val output_0_thm_alt = Q.store_thm(
"output_0_thm_alt",
`!t. p.width <= t ==> (output p 0 t = SIGMA (λx. p.input (t - p.width + x)) (count p.width))`,
srw_tac [][output_0_thm] >>
match_mp_tac SIGMA_opposites >>
srw_tac [ARITH_ss][]);

val source_def = Q.store_thm(
"source_def",
`(source p n m = if m = 0 then if n = 0 then p.input else output p (n - 1) else SR p n (m - 1))`,
Cases_on `n` >> Cases_on `m` >> srw_tac [][FUN_EQ_THM,Slice_def] );

val ZERO_EXP = Q.store_thm(
"ZERO_EXP",
`0 ** n = if n = 0 then 1 else 0`,
srw_tac [][] >> DECIDE_TAC);

val source_thm = Q.store_thm(
"source_thm",
`!m t. n + (SUC m) * p.width ** n <= t ==> (source p n m t = source p n 0 (t - m * p.width ** n))`,
Induct >> srw_tac [][Once source_def]
>- srw_tac [][source_def]
>- srw_tac [][source_def] >>
srw_tac [][Slice_def,last_update_def] >>
MAX_SET_elim_tac >>
srw_tac [DNF_ss,ARITH_ss][NOT_EQUAL_SETS,update_times_def,EXP] >- (
  qexists_tac `0` >>
  fsrw_tac [][ADD1] >>
  DECIDE_TAC ) >>
fsrw_tac [ARITH_ss][ADD1] >>
qmatch_rename_tac `source p n m (n + (m + (x + 1)) * w ** n - 1) = source p n 0 (t - (m + 1) * w ** n)` [] >>
`source p n 0 (t - w ** n - m * w ** n) = source p n m (t - w ** n)` by (
  first_x_assum (match_mp_tac o GSYM) >>
  DECIDE_TAC ) >>
`t - w ** n - m * w ** n = t - (m + 1) * w ** n` by DECIDE_TAC >>
fsrw_tac [][] >>
AP_TERM_TAC >>
Cases_on `(w = 0) /\ 0 < n` >- (
  fsrw_tac [ARITH_ss][ZERO_EXP]

val output_thm = Q.store_thm(
"output_thm"
`!n t. n + p.width ** (SUC n) <= t ==> (output p n t = SIGMA (λx. source p n 0 (t - x - 1)) (count p.width))`,
srw_tac [][Slice_def] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [ARITH_ss][last_update_def] >>
MAX_SET_elim_tac >>
srw_tac [ARITH_ss,DNF_ss][NOT_EQUAL_SETS,update_times_def,EXP] >- (
  qexists_tac `0` >>
  fsrw_tac [][GSYM LE_LT1,ADD1,EXP] >>
  qsuff_tac `(x+1) * p.width ** n <= p.width * p.width ** n` >- DECIDE_TAC >>
  srw_tac [][LE_MULT_RCANCEL] >> DECIDE_TAC ) >>

srw_tac [ARITH_ss][source_0_thm] >>
AP_TERM_TAC >>
fsrw_tac [ARITH_ss][ADD1] >>
qmatch_rename_tac `z = t - (n + 1)` [] >>
qsuff_tac `t - (n + 1) <= z` >- DECIDE_TAC >>
first_x_assum match_mp_tac >>
DECIDE_TAC);


(* Think of a as the period number and (p.width ** (SUC n)) as the size of the period.
   The correctness statement is that the output after period a (delayed by n time steps)
   is equal to the sum of input values over period a. *)
val correctness = Q.store_thm("correctness",
`∀n a. output p n (n + ((SUC a) * (p.width ** (SUC n)))) =
       SIGMA (λx. p.input ((a * (p.width ** (SUC n))) + x))
             (count (p.width ** (SUC n)))`,
Induct >- srw_tac [][output_0_thm_alt,MULT] >>
srw_tac [][Slice_def]

val _ = export_theory ()
