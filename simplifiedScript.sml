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

(* need more theorems like the above to build the result up slowly *)

(* Think of a as the period number and (p.width ** (SUC n)) as the size of the period.
   The correctness statement is that the output after period a (delayed by n time steps)
   is equal to the sum of input values over period a. *)
val correctness = Q.store_thm("correctness",
`∀n a. output p n (n + ((SUC a) * (p.width ** (SUC n)))) =
       SIGMA (λx. p.input ((a * (p.width ** (SUC n))) + x))
             (count (p.width ** (SUC n)))`,
Induct >> Induct >- (
  srw_tac [ARITH_ss][Slice_def,last_update_def] >>
  SRW_TAC [][SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST] THEN
  MATCH_MP_TAC PERM_SUM THEN
  qmatch_abbrev_tac `PERM (MAP f1 ls) (MAP f2 ls)` THEN
  qsuff_tac `PERM (MAP f1 (COUNT_LIST p.width)) (MAP f2 (REVERSE (COUNT_LIST p.width)))` >- (
    qmatch_abbrev_tac `PERM l1 l2 ==> PERM l3 l4` THEN
    qsuff_tac `PERM l1 l3 /\ PERM l2 l4` >- PROVE_TAC [PERM_SYM,PERM_TRANS] >>
    srw_tac [][Abbr`l1`,Abbr`l2`,Abbr`l3`,Abbr`l4`,Abbr`ls`] >>
    match_mp_tac PERM_MAP >>
    PROVE_TAC [PERM_SET_TO_LIST_count_COUNT_LIST,PERM_REVERSE,PERM_SYM,PERM_TRANS] ) >>
  match_mp_tac PERM_INTRO >>
  match_mp_tac LIST_EQ >>
  srw_tac [][EL_MAP,rich_listTheory.EL_REVERSE,rich_listTheory.LENGTH_COUNT_LIST,rich_listTheory.EL_COUNT_LIST] >>
  `PRE (p.width - x) < p.width` by DECIDE_TAC THEN
  fsrw_tac [][rich_listTheory.EL_COUNT_LIST,PRE_SUB1] THEN
  unabbrev_all_tac >> srw_tac [][] >>
  MAX_SET_elim_tac >>
  srw_tac [ARITH_ss,DNF_ss][NOT_EQUAL_SETS,update_times_def,EXP,ADD1] >- (
    qexists_tac `0` >> DECIDE_TAC ) >>
  qmatch_rename_tac `source p 0 n (n + z) = p.input (p.width - (n + 1))` [] >>
  `n <= n + z` by DECIDE_TAC >>
  srw_tac [][source_0_thm] >>
  AP_TERM_TAC >>
  qsuff_tac `n + ((p.width - n - 1) + 1) <= n + (z + 1)` >- DECIDE_TAC >>
  first_x_assum match_mp_tac >> DECIDE_TAC )
>- (
  fsrw_tac [ARITH_ss][Slice_def,EXP,last_update_def] >>
  srw_tac [][SUM_IMAGE_eq_SUM_MAP_SET_TO_LIST] >>
  MATCH_MP_TAC PERM_SUM


  Induct_on `x` >> srw_tac [][] >- (
    srw_tac [][Slice_def,update_times_def,EXP] >>
    MAX_SET_elim_tac >> srw_tac [][NOT_EQUAL_SETS,ADD1] >- (
      qexists_tac `p.width` >> srw_tac [ARITH_ss][] >>
      qexists_tac `PRE p.width` >> DECIDE_TAC ) >>
    fsrw_tac [ARITH_ss][] >>
    AP_TERM_TAC >>
    qmatch_rename_tac `z = w - 1` [] >>
    qsuff_tac `w <= z + 1` >- DECIDE_TAC >>
    first_x_assum match_mp_tac >>
    srw_tac [ARITH_ss][]
    qexists_tac `PRE w` >> DECIDE_TAC ) >>
  fsrw_tac [ARITH_ss][PRE_SUB1] >>
  srw_tac [][Slice_def] >>
  MAX_SET_elim_tac >> srw_tac [][NOT_EQUAL_SETS,update_times_def] >- (
    srw_tac [boolSimps.DNF_ss][update_times_def,EXP] >>
    qexists_tac `0` >> DECIDE_TAC ) >>
  fsrw_tac [boolSimps.DNF_ss,ARITH_ss][ADD1,last_update_def]

  Induct_on `x` >> srw_tac [][] >- (
    Cases_
  Cases_on `p.width - x` >- DECIDE_TAC >>
  fsrw_tac [][] >>
  MAX_SET_elim_tac >>
  srw_tac [][] >- (
    srw_tac [][NOT_EQUAL_SETS] >>
    srw_tac [boolSimps.DNF_ss,ARITH_ss][update_times_def,EXP,ADD1] >>
    qexists_tac `0` >> DECIDE_TAC ) >>
  srw_tac [][Slice_def]
  Induct_on `n` >> srw_tac [][Slice_def,update_times_def]
  DB.match [] ``EL n (COUNT_LIST m)``
  DB.match [] ``PRE``
  DB.match [] ``LENGTH (COUNT_LIST n)``
  DB.match [] ``MAP f1 l1 = MAP f2 l2``
  SRW_TAC [][Abbr`f2`,MAP_GENLIST,COUNT_LIST_GENLIST,MAP_REVERSE,Abbr`f1`]
    LIST_EQ
    DB.match [] ``REVERSE (GENLIST f n)``
    DB.match [] ``PERM l1 l2 ==> PERM l3 l4``
  PERM_MAP
  DB.match [] ``PERM (MAP f ls)``


  match_mp_tac SUM_IMAGE_CONG >>
  conj_tac >- srw_tac [][] >>
  simp_tac (srw_ss()) []
  Induct >> srw_tac [][Slice_def] >- (
    MAX_SET_elim_tac >>
    srw_tac [][ADD1,update_times_def,NOT_EQUAL_SETS,EXP] >-
      (qexists_tac `p.width` >> DECIDE_TAC) >>
    Cases_on `p.width` >> fsrw_tac [][ADD1]
    fsrw_tac [][ADD1]

  srw_tac [ARITH_ss][Slice_def,last_update_def,ADD1,EXP] >>
  match_mp_tac SUM_IMAGE_CONG >>
  srw_tac [][] >>
  Induct_on `x` >> srw_tac [][] >- (
    srw_tac [][Slice_def] >>
    MAX_SET_elim_tac >>
    srw_tac [boolSimps.DNF_ss][update_times_def,NOT_EQUAL_SETS,ADD1,EXP] >-
      (qexists_tac `0` >> DECIDE_TAC) >>
    fsrw_tac [ARITH_ss][] >>
    AP_TERM_TAC
  MAX_SET_elim_tac >>
  srw_tac [][] >- (
    srw_tac [][update_times_def] >>
    srw_tac [][NOT_EQUAL_SETS,EXP] >>
    qexists_tac `x` >> srw_tac [][] >-
      PROVE_TAC [ADD_0] >>
    srw_tac [][ADD1] >>
    DECIDE_TAC ) >>
  fsrw_tac [boolSimps.DNF_ss][update_times_def,EXP] >>
  srw_tac [][]
  Slice_def

val _ = export_theory ()
