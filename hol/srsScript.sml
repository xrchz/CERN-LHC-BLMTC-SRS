open HolKernel boolLib boolSimps bossLib arithmeticTheory pred_setTheory listTheory sortingTheory lcsymtacs

val _ = new_theory "srs"

(* Slice 0 is a fake slice whose output register copies the global input.
Slices 1 through 6 are as in the schematics. Slices 7 onwards are posited by
extrapolating formulas, except they don't have taps defined, so most things
won't be provable about them. *)

(* tap n x is the location of tap x of slice n *)
val tap_def = Define`
  (tap 0 x = 0) ∧
  (tap 1 0 = 1  -1) ∧
  (tap 1 x = 2  -1) ∧
  (tap 2 0 = 8  -1) ∧
  (tap 2 x = 16 -1) ∧
  (tap 3 0 = 32 -1) ∧
  (tap 3 x = 128-1) ∧
  (tap 4 0 = 32 -1) ∧
  (tap 4 x = 256-1) ∧
  (tap 5 0 = 16 -1) ∧
  (tap 5 x = 64 -1) ∧
  (tap 6 0 = 32 -1) ∧
  (tap 6 x = 128 -1)`

(* input n = the slice and tap connected to the input of slice n *)
val input_def = Define`
  (input 0 = (0,0)) ∧
  (input 1 = (0,0)) ∧
  (input 2 = (0,0)) ∧
  (input 3 = (1,1)) ∧
  (input 4 = (3,0)) ∧
  (input 5 = (4,0)) ∧
  (input 6 = (4,1)) ∧
  (input n = (n-1,0))`

val input_earlier = Q.store_thm(
"input_earlier",
`0 < n ⇒ FST (input n) < n`,
Induct_on `n` >> srw_tac [][input_def] >>
ntac 6 (
qabbrev_tac `v=n` >> pop_assum (K ALL_TAC) >>
Cases_on `v` >> fsrw_tac [][input_def] ) >>
srw_tac [ARITH_ss][])

(* delay n = time steps between updates of slice n *)
val delay_def = tDefine "delay"`
  (delay 0 = 1) ∧
  (delay n = delay (FST (input n)) * SUC (tap (FST (input n)) (SND (input n))))`
(WF_REL_TAC `$<` >>
 Induct >> srw_tac [][input_def] >>
 ntac 4 (
 Cases_on `v` >> fsrw_tac [][input_def] >>
 qabbrev_tac `v=n` >> pop_assum (K ALL_TAC) ) >>
 Cases_on `v` >> fsrw_tac [][input_def] >>
 srw_tac [ARITH_ss][])
(* update_time n t <=> t is an update time for slice n *)
val update_time_def = Define`
  (update_time n t = (t MOD (delay n) = 0))`

(* source D n m = the source of input for SR m of slice n *)
(* output D n x = output at tap x of slice n *)
(* SR D n m = shift register m of slice n *)
val Slice_def = tDefine "Slice" `
  (source D n 0 t = output D (FST (input n)) (SND (input n)) t) ∧
  (source D n (SUC m) t = SR D n m t) ∧
  (output D 0 x t = D t) ∧
  (output D n x 0 = 0) ∧
  (output D n x (SUC t) =
   if update_time n (SUC t)
   then ((output D n x t) + (source D n 0 t)) - (SR D n (tap n x) t)
   else output D n x t) ∧
  (SR D n m 0 = 0) ∧
  (SR D n m (SUC t) =
   if update_time n (SUC t)
   then source D n m t
   else SR D n m t)`
(WF_REL_TAC
`inv_image ($< LEX $< LEX $< LEX $<)
 (λx. case x of
      (INL (D,n,m,t)) -> (n,m,t,3) ||
      (INR (INR (D,n,m,t))) -> (n,m,t,2) ||
      (INR (INL (D,n,x,t))) -> (n,tap n x,t,1))` >>
srw_tac [ARITH_ss][] >>
Cases_on `n` >- fsrw_tac [][input_def,tap_def] >>
disj1_tac >> match_mp_tac input_earlier >>
srw_tac [][])

val RS_def = Define`
  (RS D n = output D (SUC (n DIV 2)) (n MOD 2))`

val output_def = Q.store_thm(
"output_def",
`output D n x t =
 if (n = 0) then D t
 else if t = 0 then 0
 else if update_time n t then output D n x (t - 1) + source D n 0 (t - 1) - SR D n (tap n x) (t - 1)
 else output D n x (t - 1)`,
Cases_on `n` >> Cases_on `x` >> Cases_on `t` >> srw_tac [][Slice_def])

val SR_def = Q.store_thm(
"SR_def",
`SR D n m t = if t = 0 then 0 else if update_time n t then source D n m (t - 1) else SR D n m (t - 1)`,
Cases_on `t` >> srw_tac [][Slice_def])

val source_def = Q.store_thm(
"source_def",
`source D n m t = if m = 0 then output D (FST (input n)) (SND (input n)) t else SR D n (m - 1) t`,
Cases_on `m` >> srw_tac [][Slice_def])

val tap_thm = Q.store_thm("tap_thm",
`(tap 0 0 = 0) ∧
  (tap 1 0 = 1  -1) ∧
  (tap 1 1 = 2  -1) ∧
  (tap 2 0 = 8  -1) ∧
  (tap 2 1 = 16 -1) ∧
  (tap 3 0 = 32 -1) ∧
  (tap 3 1 = 128-1) ∧
  (tap 4 0 = 32 -1) ∧
  (tap 4 1 = 256-1) ∧
  (tap 5 0 = 16 -1) ∧
  (tap 5 1 = 64 -1) ∧
  (tap 6 0 = 32 -1) ∧
  (tap 6 1 = 128 -1)`,
srw_tac [][tap_def] >>
qmatch_abbrev_tac `tap x 1 = z` >> (
qsuff_tac `tap x (SUC 0) = z` >- srw_tac [][] >>
unabbrev_all_tac >>
simp_tac bool_ss [tap_def] >>
srw_tac [][] ))

val delay_thm = Q.store_thm(
"delay_thm",
`(delay 0 = 1) ∧
 (delay 1 = 1) ∧
 (delay 2 = 1) ∧
 (delay 3 = 2) ∧
 (delay 4 = 64) ∧
 (delay 5 = 2048) ∧
 (delay 6 = 16384)`,
conj_asm1_tac >- srw_tac [][delay_def] >>
conj_asm1_tac >- srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`0`] delay_def),input_def,tap_def] >>
conj_asm1_tac >- srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`1`] delay_def),input_def,tap_def] >>
conj_asm1_tac >- srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`2`] delay_def),input_def,tap_thm] >>
conj_asm1_tac >- srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`3`] delay_def),input_def,tap_thm] >>
conj_asm1_tac >- srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`4`] delay_def),input_def,tap_thm] >>
srw_tac [ARITH_ss][SIMP_RULE (srw_ss()) [] (Q.INST[`v`|->`5`] delay_def),input_def,tap_thm])

val source_1_thm = Q.store_thm(
"source_1_thm",
`source D 1 n t = if n <= t then D (t - n) else 0`,
qid_spec_tac `t` >> Induct_on `n` >> srw_tac [][source_def,input_def,delay_thm] >>
fsrw_tac [ARITH_ss][Once output_def, Once SR_def, update_time_def,delay_thm,ADD1])

val delay_above_0 = Q.store_thm(
"delay_above_0",
`0 < delay n`,
qid_spec_tac `n` >>
ho_match_mp_tac COMPLETE_INDUCTION >>
Cases >> srw_tac [][delay_def,MULT_SUC] >>
qmatch_abbrev_tac `0 < x + y` >>
qsuff_tac `0 < x` >- DECIDE_TAC >>
qunabbrev_tac `x` >>
first_x_assum match_mp_tac >>
match_mp_tac input_earlier >>
srw_tac [][])

val SR_0_until = Q.store_thm(
"SR_0_until",
`t < (SUC m) * (delay n) ⇒ (SR D n m t = 0)`,
map_every qid_spec_tac [`t`,`m`] >>
Induct >- (
  fsrw_tac [][] >>
  Induct >- srw_tac [][Once SR_def] >>
  srw_tac [][Once SR_def,update_time_def] >>
  imp_res_tac prim_recTheory.SUC_LESS >>
  fsrw_tac [][] ) >>
Induct >- srw_tac [][Once SR_def] >>
srw_tac [][Once SR_def,update_time_def,source_def] >- (
  (MULT_EQ_DIV |> Q.INST[`x`|->`delay n`,`z`|->`SUC t`,`y`|->`SUC t DIV delay n`]
   |> GSYM |> mp_tac) >>
  fsrw_tac [][delay_above_0] >>
  qabbrev_tac `y = SUC t DIV delay n` >>
  strip_tac >>
  pop_assum (assume_tac o REWRITE_RULE [Once MULT_SYM] o SYM) >>
  fsrw_tac [][] >>
  first_x_assum match_mp_tac >>
  srw_tac [ARITH_ss][MULT] >>
  Cases_on `y` >> fsrw_tac [][] >>
  match_mp_tac LESS_MONO_REV >>
  full_simp_tac bool_ss [] >>
  srw_tac [ARITH_ss][MULT] >>
  fsrw_tac [][GSYM ADD1,prim_recTheory.LESS_THM] ) >>
fsrw_tac [][] >>
first_x_assum match_mp_tac >>
fsrw_tac [][prim_recTheory.SUC_LESS])

val last_update_def = Define
`(last_update n 0 = 0) ∧
 (last_update n (SUC t) = if update_time n (SUC t) then (SUC t) else last_update n t)`

val last_update_upper_bound = Q.store_thm(
"last_update_upper_bound",
`last_update n t ≤ t`,
Induct_on `t` >> srw_tac [ARITH_ss][last_update_def])

val last_update_mono = Q.store_thm(
"last_update_mono",
`x ≤ y ⇒ last_update n x ≤ last_update n y`,
Induct_on `y` >> srw_tac [][] >>
`(x = SUC y) \/ x <= y` by DECIDE_TAC >>
fsrw_tac [][] >> srw_tac [][last_update_def] >>
PROVE_TAC [last_update_upper_bound,LESS_EQ_TRANS]);

val update_time_0 = Q.store_thm(
"update_time_0",
`update_time 0 t`,
srw_tac [][update_time_def,delay_thm])

val SR_last_update = Q.store_thm(
"SR_last_update",
`SR D n m t = SR D n m (last_update n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
srw_tac [][Once SR_def])

val update_time_last_update = Q.store_thm(
"update_time_last_update",
`update_time n (last_update n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
srw_tac [][update_time_def,ZERO_MOD,delay_above_0])

val last_update_eq_iff_update_time = Q.store_thm(
"last_update_eq_iff_update_time",
`(last_update n t = t) ⇔ update_time n t`,
EQ_TAC >> strip_tac >- PROVE_TAC [update_time_last_update] >>
Cases_on `t` >> srw_tac [][last_update_def])

val last_update_zero = Q.store_thm(
"last_update_zero",
`(last_update n t = 0) ⇔ (t < delay n)`,
Induct_on `t` >- srw_tac [][last_update_def,delay_above_0] >>
srw_tac [][EQ_IMP_THM] >- (
  (last_update_mono |> Q.INST [`x`|->`t`,`y`|->`SUC t`] |> mp_tac) >>
  srw_tac [][] >>
  fsrw_tac [][last_update_def,update_time_def] >>
  match_mp_tac LESS_SUC_EQ_COR >>
  fsrw_tac [][] >>
  spose_not_then strip_assume_tac >>
  assume_tac delay_above_0 >>
  imp_res_tac DIVMOD_ID >>
  fsrw_tac [ARITH_ss][] ) >>
imp_res_tac prim_recTheory.SUC_LESS >>
fsrw_tac [][] >>
srw_tac [][last_update_def,update_time_def])

val last_update_thm = Q.store_thm(
"last_update_thm",
`last_update n t = t - t MOD (delay n)`,
Induct_on `t` >> srw_tac [][last_update_def,update_time_def] >>
qabbrev_tac `dn = delay n` >>
qabbrev_tac `tm = t MOD dn` >>
qabbrev_tac `td = t DIV dn` >>
qabbrev_tac `sm = SUC t MOD dn` >>
qabbrev_tac `sd = SUC t DIV dn` >>
`t = td * dn + tm` by metis_tac [DIVISION,delay_above_0] >>
`sm = SUC tm` by (
  map_every qunabbrev_tac [`sm`,`tm`] >>
  match_mp_tac MOD_SUC >>
  qabbrev_tac `tm = t MOD dn` >>
  fsrw_tac [][ADD_SUC,MULT_SUC,MULT] >>
  conj_asm1_tac >- srw_tac [][delay_above_0,Abbr`dn`] >>
  fsrw_tac [][MOD_TIMES] >>
  spose_not_then strip_assume_tac >>
  fsrw_tac [][] ) >>
srw_tac [][])

val last_update_lower_bound = Q.store_thm(
"last_update_lower_bound",
`u ≤ t ∧ update_time n u ⇒ u ≤ last_update n t`,
Induct_on `t` >> srw_tac [][] >>
srw_tac [][last_update_def] >>
Cases_on `u = SUC t` >> fsrw_tac [][] >>
`u ≤ t` by DECIDE_TAC >> fsrw_tac [][]);

val last_update_sub1 = Q.store_thm(
"last_update_sub1",
`0 < t ∧ update_time n t ⇒ (last_update n (t - 1) = t - delay n)`,
srw_tac [][last_update_thm,update_time_def] >>
qabbrev_tac `dn = delay n` >>
qabbrev_tac `tm = t MOD dn` >>
qabbrev_tac `td = t DIV dn` >>
`t = td * dn + tm` by metis_tac [DIVISION,delay_above_0] >>
srw_tac [][] >> fsrw_tac [][] >>
`0 < td` by (Cases_on `td` >> fsrw_tac [][]) >>
`0 < dn` by METIS_TAC [delay_above_0] >>
`1 ≤ dn` by DECIDE_TAC >>
srw_tac [][MOD_TIMES_SUB] >>
DECIDE_TAC)

val SR_prev = Q.store_thm(
"SR_prev",
`SR D n (SUC m) t = if t < SUC (SUC m) * delay n then 0 else SR D n m (t - delay n)`,
srw_tac [][SR_0_until] >>
srw_tac [][Once SR_last_update] >>
srw_tac [][Once SR_def] >- (
  imp_res_tac last_update_zero >>
  fsrw_tac [ARITH_ss][NOT_LESS,MULT])
>- (
  srw_tac [][source_def] >>
  srw_tac [][Once SR_last_update] >>
  `0 < last_update n t` by (Cases_on `last_update n t` >> srw_tac [][]) >>
  srw_tac [][last_update_sub1] >>
  srw_tac [][Once SR_last_update,SimpRHS] >>
  AP_TERM_TAC >>
  srw_tac [][last_update_thm] >>
  fsrw_tac [][NOT_LESS,MULT] >>
  `0 < delay n` by METIS_TAC [delay_above_0] >>
  `delay n ≤ t` by DECIDE_TAC >>
  srw_tac [ARITH_ss][SUB_MOD] ) >>
fsrw_tac [][update_time_last_update])

val SR_first = Q.store_thm(
"SR_first",
`SR D n m t = if t < SUC m then 0 else SR D n 0 (t - (m * delay n))`,
qid_spec_tac `t` >>
Induct_on `m` >> fsrw_tac [][SR_prev]
>- (Cases >> srw_tac [ARITH_ss][SR_0_until,delay_above_0]) >>
gen_tac >>
Cases_on `t < SUC (SUC m)` >- (
  srw_tac [][] >>
  assume_tac delay_above_0 >>
  DECIDE_TAC ) >>
Cases_on `t < SUC (SUC m) * delay n` >- (
  srw_tac [][] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac SR_0_until >>
  fsrw_tac [][MULT,delay_above_0] ) >>
Cases_on `t < delay n + SUC m` >- (
  srw_tac [][] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac SR_0_until >>
  fsrw_tac [][MULT,NOT_LESS,delay_above_0] >>
  match_mp_tac LESS_TRANS >>
  qexists_tac `delay n + SUC m` >>
  srw_tac [][ADD1] >>
  match_mp_tac LESS_EQ_LESS_TRANS >>
  qexists_tac `m + delay n` >>
  srw_tac [ARITH_ss][] ) >>
srw_tac [ARITH_ss][MULT])

val output_last_update = Q.store_thm(
"output_last_update",
`output D n x t = output D n x (last_update n t)`,
Induct_on `t` >> srw_tac [][Slice_def,last_update_def] >>
srw_tac [][Once output_def] >>
fsrw_tac [][update_time_def,delay_thm])

val output_sum = Q.store_thm(
"output_sum",
`0 < n ⇒ (output D n x t = SIGMA (λm. SR D n m t) (count (SUC (tap n x))))`,
strip_tac >>
Induct_on `t` >> srw_tac [ARITH_ss][Once output_def,Slice_def] >-
  srw_tac [][SUM_IMAGE_ZERO] >>
srw_tac [][SUM_IMAGE_count_SUM_GENLIST] >>
srw_tac [][GENLIST_CONS,SimpRHS] >>
srw_tac [][combinTheory.o_DEF] >>
srw_tac [ARITH_ss][GENLIST,SUM_SNOC,source_def])

val output_first = Q.store_thm(
"output_first",
`0 < n ⇒ (output D n x t = SIGMA (λm. if t ≤ m * (delay n) then 0 else SR D n 0 (t - m * (delay n))) (count (SUC (tap n x))))`,
srw_tac [][output_sum] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [][Once SR_first] >- (
  match_mp_tac (GSYM SR_0_until) >>
  fsrw_tac [][NOT_LESS_EQUAL,GSYM MULT,delay_above_0] >>
  match_mp_tac LESS_LESS_EQ_TRANS >>
  qmatch_assum_rename_tac `t < SUC z` [] >>
  qexists_tac `SUC z` >>
  srw_tac [][delay_above_0] ) >>
match_mp_tac SR_0_until >>
assume_tac delay_above_0 >>
DECIDE_TAC)

val prev1_update_time = Q.store_thm(
"prev1_update_time",
`0 < t ∧ update_time n t ⇒ update_time n (t - delay n)`,
srw_tac [][update_time_def] >>
Cases_on `t < delay n` >- (
  imp_res_tac (GSYM X_MOD_Y_EQ_X) >>
  fsrw_tac [][] ) >>
qsuff_tac `((t - delay n * 1) MOD delay n = t MOD delay n)` >- srw_tac [][] >>
match_mp_tac MOD_SUB >>
fsrw_tac [][NOT_LESS,delay_above_0])

val prev_update_time = Q.store_thm(
"prev_update_time",
`z * delay n < t ∧ update_time n t ⇒ update_time n (t - z * delay n)`,
Induct_on `z` >> srw_tac [][] >>
fsrw_tac [][MULT,SUB_PLUS] >>
`z * delay n < t` by DECIDE_TAC >>
`0 < t - z * delay n` by DECIDE_TAC >>
srw_tac [][prev1_update_time])

val output_source_at_update_times = Q.store_thm(
"output_source_at_update_times",
`0 < n ∧ update_time n t ⇒ (output D n x t = SIGMA (λm. if t ≤ m * (delay n) then 0 else source D n 0 (t - m * (delay n) - 1)) (count (SUC (tap n x))))`,
srw_tac [][output_first] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [ARITH_ss][Once SR_def] >>
fsrw_tac [][NOT_LESS_EQUAL] >>
imp_res_tac prev_update_time)

val input_SUC = Q.store_thm(
"input_SUC",
`FST (input n) ≤ FST (input (SUC n))`,
srw_tac [][input_def] >>
ntac 7 (
qabbrev_tac `m = n` >> pop_assum (K ALL_TAC) >>
Cases_on `m` >> srw_tac [ARITH_ss][] ))

val update_time_SUC = Q.store_thm(
"update_time_SUC",
`update_time (SUC n) t ⇒ update_time n t`,
ntac 4 (
qabbrev_tac `m = n` >> pop_assum (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][update_time_def,delay_thm] ) >- (
  fsrw_tac [][MOD_EQ_0_DIVISOR,delay_thm] >>
  qexists_tac `d * 32` >> srw_tac [ARITH_ss][] ) >>
qabbrev_tac `m = n` >> pop_assum (K ALL_TAC) >>
Cases_on `m` >> fsrw_tac [][update_time_def,delay_thm] >- (
  fsrw_tac [][MOD_EQ_0_DIVISOR] >>
  qexists_tac `d * (2048 DIV 64)` >> srw_tac [ARITH_ss][] ) >>
qabbrev_tac `m = n` >> pop_assum (K ALL_TAC) >>
Cases_on `m` >> fsrw_tac [][update_time_def,delay_thm] >- (
  fsrw_tac [][MOD_EQ_0_DIVISOR] >>
  qexists_tac `d * (16384 DIV 2048)` >> srw_tac [ARITH_ss][] ) >>
qabbrev_tac `m = n` >> pop_assum (K ALL_TAC) >>
Cases_on `m` >> fsrw_tac [][update_time_def,delay_thm] >- (
  `delay 7 = delay (SUC 6)` by srw_tac [][] >>
  fsrw_tac [][delay_def,input_def,tap_thm,delay_thm] >>
  fsrw_tac [][MOD_EQ_0_DIVISOR] >>
  qexists_tac `d * (524288 DIV 16384)` >>
  srw_tac [ARITH_ss][] ) >>
qmatch_abbrev_tac `t MOD delay m = 0` >>
`0 < delay m ∧ 0 < delay (SUC m)` by srw_tac [][delay_above_0] >>
fsrw_tac [][MOD_EQ_0_DIVISOR] >>
srw_tac [ARITH_ss][Once delay_def,input_def,Abbr`m`] >>
metis_tac [])

val update_time_prev = Q.store_thm(
"update_time_prev",
`n < m ∧ update_time m t ⇒ update_time n t`,
Induct_on `m` >- srw_tac [][update_time_def,delay_def] >>
srw_tac [][] >>
imp_res_tac update_time_SUC >>
Cases_on `n=m` >> srw_tac [][] >>
`n < m` by DECIDE_TAC >>
fsrw_tac [][])

val output_0_until = Q.store_thm(
"output_0_until",
`0 < n ∧ t < delay n ⇒ (output D n x t = 0)`,
srw_tac [][output_first,SUM_IMAGE_ZERO] >> srw_tac [][] >>
match_mp_tac SR_0_until >>
srw_tac [ARITH_ss][delay_above_0])

val output_0 = Q.prove(`output D 0 x t = D t`,srw_tac [][Once output_def])

val output_prev = Q.store_thm(
"output_prev",
`0 < n ⇒ (output D n x t = SIGMA (\m. if last_update n t < m * delay n + delay (FST (input n)) then 0 else output D (FST (input n)) (SND (input n)) (last_update n t - m * delay n - delay (FST (input n)))) (count (SUC (tap n x))))`,
strip_tac >>
qsuff_tac `
(output D n x t = SIGMA (\m. if last_update n t <= m * delay n then 0 else output D (FST (input n)) (SND (input n)) (last_update n t - m * delay n - delay (FST (input n)))) (count (SUC (tap n x))))` >- (
  srw_tac [][] >>
  match_mp_tac SUM_IMAGE_CONG >>
  srw_tac [][] >- (
    `0 < delay (FST (input n))` by metis_tac [delay_above_0] >>
    DECIDE_TAC ) >>
  qmatch_assum_rename_tac `z < SUC (tap n x)` [] >>
  Cases_on `FST (input n) = 0` >- (
    fsrw_tac [][output_0,delay_thm,NOT_LESS] >>
    `last_update n t = z * delay n` by DECIDE_TAC >>
    fsrw_tac [][] ) >>
  match_mp_tac output_0_until >>
  srw_tac [ARITH_ss][] ) >>
srw_tac [][Once output_last_update] >>
srw_tac [][output_source_at_update_times,update_time_last_update] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [][source_def] >>
srw_tac [][Once output_last_update,SimpLHS] >>
fsrw_tac [][NOT_LESS,NOT_LESS_EQUAL] >>
qmatch_assum_rename_tac `z < SUC (tap n x)` [] >>
`0 < last_update n t - z * delay n` by DECIDE_TAC >>
`update_time (FST (input n)) (last_update n t - z * delay n)` by (
  match_mp_tac (GEN_ALL update_time_prev) >>
  qexists_tac `n` >>
  srw_tac [][input_earlier] >>
  match_mp_tac prev_update_time >>
  srw_tac [][update_time_last_update] ) >>
srw_tac [][last_update_sub1])

val output_prev_at_update_times = Q.store_thm(
"output_prev_at_update_times",
`0 < n ∧ update_time n t ⇒
 (output D n x t =
  SIGMA (λm. if t < m * delay n + delay (FST (input n)) then 0
             else output D (FST (input n)) (SND (input n))
                    (t - m * delay n - delay (FST (input n))))
  (count (SUC (tap n x))))`,
metis_tac [output_prev,last_update_eq_iff_update_time])

val output_prev_update_time = Q.store_thm(
"output_prev_update_time",
`t ≥ m * delay n + delay (FST (input n)) ∧ update_time n t ⇒
 update_time (FST (input n)) (t - m * delay n - delay (FST (input n)))`,
reverse (Cases_on `0 < n`) >- (
  Cases_on `n` >>
  fsrw_tac [][delay_thm,input_def,update_time_def] ) >>
strip_tac >>
match_mp_tac prev1_update_time >>
`0 < delay (FST (input n))` by srw_tac [][delay_above_0] >>
srw_tac [][] >- DECIDE_TAC >>
match_mp_tac (GEN_ALL update_time_prev) >>
qexists_tac `n` >>
srw_tac [][input_earlier] >>
match_mp_tac prev_update_time >>
srw_tac [][] >> DECIDE_TAC)

val delay_sum_def = tDefine "delay_sum"`
  (delay_sum 0 = 0) ∧
  (delay_sum n = delay (FST (input n)) + delay_sum (FST (input n)))`
(WF_REL_TAC `$<` >> srw_tac [][input_earlier])

val delay_sum_thm = Q.store_thm(
"delay_sum_thm",
`(delay_sum 0 = 0) ∧
 (delay_sum 1 = 1) ∧
 (delay_sum 2 = 1) ∧
 (delay_sum 3 = 2) ∧
 (delay_sum 4 = 4) ∧
 (delay_sum 5 = 68) ∧
 (delay_sum 6 = 68)`,
srw_tac [][
  delay_sum_def,
  SIMP_RULE (srw_ss()) [] (SPEC ``0`` (GEN_ALL delay_sum_def)),
  SIMP_RULE (srw_ss()) [] (SPEC ``1`` (GEN_ALL delay_sum_def)),
  SIMP_RULE (srw_ss()) [] (SPEC ``2`` (GEN_ALL delay_sum_def)),
  SIMP_RULE (srw_ss()) [] (SPEC ``3`` (GEN_ALL delay_sum_def)),
  SIMP_RULE (srw_ss()) [] (SPEC ``4`` (GEN_ALL delay_sum_def)),
  SIMP_RULE (srw_ss()) [] (SPEC ``5`` (GEN_ALL delay_sum_def)),
  input_def,delay_thm])

val delay_sum_above_0 = Q.store_thm(
"delay_sum_above_0",
`0 < n ⇒ 0 < delay_sum n`,
Cases_on `n` >> srw_tac [][delay_sum_def] >>
qmatch_rename_tac `0 < delay x + y` [] >>
qsuff_tac `0 < delay x` >- srw_tac [ARITH_ss][] >>
srw_tac [][delay_above_0])

val output_input_at_update_times = Q.store_thm(
"output_input_at_update_times",
`0 < n ∧ update_time n t ⇒
 (output D n x t = SIGMA
   (λm. if t < m + delay_sum n then 0 else D (t - m - delay_sum n))
   (count (SUC (tap n x) * delay n)))`,
map_every qid_spec_tac [`t`,`x`,`n`] >>
ho_match_mp_tac COMPLETE_INDUCTION >>
Cases >> srw_tac [][] >>
srw_tac [][output_prev_at_update_times] >>
qmatch_assum_rename_tac `update_time (SUC n) t` [] >>
Cases_on `n=0` >- (
  srw_tac [][delay_thm,input_def,Once output_def,tap_def,delay_sum_thm] >>
  fsrw_tac [][GSYM ADD1,LESS_OR_EQ,prim_recTheory.LESS_THM,DISJ_SYM] ) >>
srw_tac [][MULT_SYM] >>
match_mp_tac EQ_SYM >>
match_mp_tac SUM_IMAGE_count_MULT >>
srw_tac [][SUM_IMAGE_ZERO] >- (
  srw_tac [][MULT_SYM] >>
  fsrw_tac [][delay_sum_def] >>
  DECIDE_TAC ) >>
reverse (Cases_on `0 < FST (input (SUC n))`) >- (
  `FST (input (SUC n)) = 0` by srw_tac [ARITH_ss][] >>
  srw_tac [][output_0,delay_sum_def] >>
  srw_tac [][delay_def,tap_def] >>
  srw_tac [][SUM_IMAGE_count_SUM_GENLIST] >>
  fsrw_tac [ARITH_ss][NOT_LESS_EQUAL,delay_def,tap_def]) >>
`update_time (FST (input (SUC n))) (t - m * delay (SUC n) - delay (FST (input (SUC n))))` by (
  match_mp_tac prev1_update_time >>
  `0 < delay (FST (input (SUC n)))` by metis_tac [delay_above_0] >>
  conj_tac >- DECIDE_TAC >>
  match_mp_tac (GEN_ALL update_time_prev) >>
  qexists_tac `SUC n` >>
  srw_tac [][input_earlier] >>
  match_mp_tac prev_update_time >>
  fsrw_tac [ARITH_ss][NOT_LESS_EQUAL] ) >>
first_x_assum (qspec_then `FST (input (SUC n))` mp_tac) >>
simp_tac (srw_ss()) [input_earlier] >> strip_tac >>
pop_assum (qspecl_then [`SND (input (SUC n))`,`t - m * delay (SUC n) - delay (FST (input (SUC n)))`] mp_tac) >>
srw_tac [][] >>
srw_tac [][Once delay_def,Cong(prove(``(a = b) ==> (SIGMA f a = SIGMA f b)``,srw_tac [][]))] >>
srw_tac [][MULT_SYM] >>
match_mp_tac SUM_IMAGE_CONG >>
fsrw_tac [][] >>
pop_assum (K ALL_TAC) >>
qabbrev_tac `u = FST (input (SUC n))` >>
qabbrev_tac `v = SND (input (SUC n))` >>
asm_simp_tac (srw_ss()) [delay_def,delay_sum_def] >>
asm_simp_tac (srw_ss()) [MULT,MULT_SUC] >>
qx_gen_tac `z` >> DISCH_TAC >>
srw_tac [ARITH_ss][] >>
fsrw_tac [ARITH_ss][NOT_LESS] >>
metis_tac [delay_above_0,delay_sum_above_0,prim_recTheory.NOT_LESS_0])

val output_input = Q.store_thm(
"output_input",
`0 < n ∧ update_time n t ∧ u < delay n ⇒
(output D n x (t + u) = SIGMA (λm. if t < m + delay_sum n then 0 else D (t - m - delay_sum n)) (count (SUC (tap n x) * delay n)))`,
srw_tac [][Once output_last_update] >>
`0 < delay n` by DECIDE_TAC >>
fsrw_tac [][last_update_thm,update_time_def,MOD_EQ_0_DIVISOR] >>
srw_tac [][MOD_MULT] >>
match_mp_tac output_input_at_update_times >>
srw_tac [][update_time_def,MOD_EQ_0])

val all_times_covered = Q.store_thm(
"all_times_covered",
`∃v u. update_time n v ∧ u < delay n ∧ (t = v + u)`,
qexists_tac `t DIV delay n * delay n` >>
qexists_tac `t MOD delay n` >>
qspec_then `delay n` assume_tac DIVISION >>
assume_tac delay_above_0 >>
fsrw_tac [][update_time_def,MOD_EQ_0])

val exact_def = Define`
  exact D n x t = SIGMA (λm. if t < SUC m then 0 else D (t - SUC m)) (count (SUC (tap n x) * delay n))`

val error_def = Define`
  error D n x t = ABS_DIFF (output D n x t) (exact D n x t)`

val ABS_DIFF_SUC = Q.store_thm(
"ABS_DIFF_SUC",
`ABS_DIFF (SUC n) m <= SUC (ABS_DIFF n m) /\
 PRE (ABS_DIFF n m) <= ABS_DIFF (SUC n) m`,
SRW_TAC [][ABS_DIFF_def] THEN DECIDE_TAC)

val max_diff = Q.store_thm(
"max_diff",
`(∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ⇒ ABS_DIFF (D t1) (D t2) ≤ k * ABS_DIFF t1 t2`,
qho_match_abbrev_tac `X t1 t2` >>
qsuff_tac `!t1 t2. t1 ≤ t2 ⇒ X t1 t2` >- (
  metis_tac [LESS_LESS_CASES,LESS_OR_EQ,ABS_DIFF_SYM] ) >>
unabbrev_all_tac >>
Induct_on `t2-t1` >>
srw_tac [][] >- (
  `t1=t2` by DECIDE_TAC >>
  srw_tac [][] ) >>
`v = t2 - (SUC t1)` by DECIDE_TAC >>
`SUC t1 ≤ t2` by DECIDE_TAC >>
first_x_assum (qspecl_then [`t2`,`SUC t1`] mp_tac) >>
srw_tac [][] >>
Cases_on `ABS_DIFF t1 t2 = 0` >- fsrw_tac [][ABS_DIFF_EQ_0] >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `ABS_DIFF (D t1) (D (SUC t1)) + ABS_DIFF (D (SUC t1)) (D t2)` >>
conj_tac >- srw_tac [][ABS_DIFF_TRIANGLE] >>
`ABS_DIFF (SUC t1) t2 = PRE (ABS_DIFF t1 t2)` by (
  srw_tac [ARITH_ss][ABS_DIFF_def] ) >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `k + k * PRE (ABS_DIFF t1 t2)` >>
conj_tac >- (
  qmatch_abbrev_tac `a + b <= c + d` >>
  qsuff_tac `a <= c /\ b <= d` >- (
    srw_tac [][] >>
    match_mp_tac LESS_EQ_TRANS >>
    qexists_tac `c + b` >> srw_tac [ARITH_ss][Abbr`c`] ) >>
  unabbrev_all_tac >> srw_tac [][] >> PROVE_TAC []) >>
METIS_TAC [NOT_ZERO_LT_ZERO,SUC_PRE,MULT_SUC,LESS_EQ_REFL])

val max_diff_eq = Q.store_thm(
"max_diff_eq",
`∃D. (∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ∧ (ABS_DIFF (D t1) (D t2) = k * ABS_DIFF t1 t2)`,
qexists_tac `λt. t * k` >>
srw_tac [][ABS_DIFF_def,MULT] >>
srw_tac [ARITH_ss][LEFT_SUB_DISTRIB] >>
fsrw_tac [ARITH_ss][NOT_LESS])

val ABS_DIFF_SUM_IMAGE_eq = Q.store_thm(
"ABS_DIFF_SUM_IMAGE_eq",
`!s. FINITE s ==> ∀f g. (∀x. x ∈ s ⇒ f x ≤ g x) ==> (ABS_DIFF (SIGMA f s) (SIGMA g s) = SIGMA (\x. ABS_DIFF (f x) (g x)) s)`,
ho_match_mp_tac FINITE_INDUCT >>
srw_tac [][ABS_DIFF_def,SUM_IMAGE_THM] >>
fsrw_tac [][DELETE_NON_ELEMENT] >>
`f e <= g e` by metis_tac [] >>
Cases_on `f e = g e` >- (
  first_x_assum (qspecl_then [`f`,`g`] (mp_tac o GSYM)) >>
  srw_tac [][] >> srw_tac [ARITH_ss][] ) >>
`f e < g e` by DECIDE_TAC >>
first_x_assum (qspecl_then [`f`,`g`] (mp_tac o GSYM)) >>
srw_tac [][] >> srw_tac [ARITH_ss][] >>
fsrw_tac [ARITH_ss][NOT_LESS] >> srw_tac [][] >>
`SIGMA f s <= SIGMA g s` by (
  match_mp_tac (MP_CANON SUM_IMAGE_MONO_LESS_EQ) >>
  srw_tac [][] ) >>
`SIGMA f s = SIGMA g s` by DECIDE_TAC >>
fsrw_tac [ARITH_ss][]);

val output_eq_exact = Q.store_thm(
"output_eq_exact",
`0 < n ⇒ (output D n x t = if SUC (last_update n t) < delay_sum n then 0 else exact D n x (SUC (last_update n t) - delay_sum n))`,
strip_tac >>
qsuff_tac `output D n x t = if last_update n t < delay n then 0 else exact D n x (SUC (last_update n t) - delay_sum n)` >- (
  srw_tac [][exact_def,SUM_IMAGE_ZERO] >- (
    fsrw_tac [][Once output_last_update] >>
    qpat_assum `0 < n` assume_tac >>
    assume_tac update_time_last_update >>
    fsrw_tac [][output_input_at_update_times,SUM_IMAGE_ZERO] >>
    first_x_assum (qspec_then `m` mp_tac) >>
    fsrw_tac [ARITH_ss][ADD1] ) >>
  srw_tac [ARITH_ss][]) >>
srw_tac [][exact_def,Once output_last_update] >- (
  match_mp_tac output_0_until >>
  srw_tac [][] ) >>
srw_tac [][output_input_at_update_times,update_time_last_update] >>
srw_tac [ARITH_ss][ADD1] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [][] >> DECIDE_TAC)

val max_error = Q.store_thm(
"max_error",
`(∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ∧
 0 < n ∧
 t > SUC (tap n x) * delay n + delay n + delay_sum n ⇒
 error D n x t ≤ SUC (tap n x) * delay n * k * (delay n + delay_sum n)`,
srw_tac [][error_def] >>
assume_tac delay_above_0 >>
`t MOD delay n < delay n` by METIS_TAC [MOD_LESS] >>
`0 < delay_sum n` by imp_res_tac delay_sum_above_0 >>
srw_tac [][output_eq_exact] >- (
  full_simp_tac bool_ss [last_update_thm,MULT] >>
  `t < 2 * delay n` by DECIDE_TAC >>
  `t > 2 * delay n` by fsrw_tac [ARITH_ss][] >>
  METIS_TAC [LESS_ANTISYM,GREATER_DEF]) >>
srw_tac [][exact_def] >>
qmatch_abbrev_tac `ABS_DIFF (SIGMA f s) (SIGMA g s) ≤ X` >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `SIGMA (λx. ABS_DIFF (f x) (g x)) s` >>
srw_tac [][Abbr`s`,ABS_DIFF_SUM_IMAGE,Abbr`X`] >>
srw_tac [][Abbr`f`,Abbr`g`,last_update_thm] >>
srw_tac [][Once (GSYM MULT_ASSOC),SimpR``$<=``] >>
qmatch_abbrev_tac `SIGMA f (count a) ≤ a * b` >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `CARD (count a) * b` >>
reverse conj_tac >- srw_tac [][] >>
match_mp_tac (MP_CANON SUM_IMAGE_upper_bound) >>
conj_tac >- srw_tac [][] >>
qx_gen_tac `z` >>
reverse (srw_tac [][Abbr`f`,Abbr`a`,Abbr`b`]) >- (
  qmatch_abbrev_tac `ABS_DIFF (D t1) (D t2) ≤ X` >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `k * ABS_DIFF t1 t2` >>
  srw_tac [][Abbr`X`] >- (
    match_mp_tac max_diff >>
    srw_tac [][] ) >>
  srw_tac [][Abbr`t1`,Abbr`t2`] >>
  Cases_on `k=0` >> srw_tac [][] >>
  srw_tac [][ADD1,SUB_LEFT_SUC] >- (
    imp_res_tac MOD_LESS_EQ >>
    `t MOD delay n ≤ t` by PROVE_TAC [] >>
    `t MOD delay n = t` by DECIDE_TAC >>
    `t < delay n` by PROVE_TAC [X_MOD_Y_EQ_X] >>
    DECIDE_TAC ) >>
  srw_tac [][ABS_DIFF_def] >>
  fsrw_tac [ARITH_ss][last_update_thm]) >>
fsrw_tac [ARITH_ss][MULT,last_update_thm])

val ABS_DIFF_SUB_SAME = Q.store_thm(
"ABS_DIFF_SUB_SAME",
`!n m p. ABS_DIFF (n - p) (m - p) = if n ≤ p then m - p else if m ≤ p then n - p else ABS_DIFF n m`,
SRW_TAC [][] THEN1 (
  `n - p = 0` by SRW_TAC [][] THEN SRW_TAC [][] )
THEN1 (
  `m - p = 0` by SRW_TAC [][] THEN SRW_TAC [][] ) THEN
FULL_SIMP_TAC (srw_ss()) [ABS_DIFF_def,NOT_LESS_EQUAL,GSYM SUB_LESS_0] THEN
SRW_TAC [ARITH_ss][])

val better_max_error = Q.store_thm(
"better_max_error",
`(∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ∧
 0 < n ∧
 t > SUC (tap n x) * delay n + delay n + delay_sum n ⇒
 error D n x t ≤ SUC (tap n x) * delay n * k * (t MOD delay n - 1 + delay_sum n)`,
srw_tac [][error_def] >>
`0 < delay n` by srw_tac [][delay_above_0] >>
`t MOD delay n < delay n` by srw_tac [][MOD_LESS] >>
`∀m. m < SUC (tap n x) * delay n ⇒ ¬(SUC (last_update n t) < delay_sum n + SUC m)` by (
  srw_tac [][last_update_thm] >>
  srw_tac [][SUB_LEFT_SUC] >>
  DECIDE_TAC ) >>
srw_tac [][output_eq_exact] >- (
  first_x_assum (qspec_then `0` mp_tac) >>
  srw_tac [][MULT] >> DECIDE_TAC ) >>
srw_tac [][exact_def] >>
qmatch_abbrev_tac `ABS_DIFF (SIGMA f s) (SIGMA g s) <= p * k * q` >>
`∀m. m ∈ s ⇒ (f m = D (SUC (last_update n t) - delay_sum n - SUC m))` by (
  srw_tac [][Abbr`f`,Abbr`s`] ) >>
`∀m. m ∈ s ⇒ (g m = D (t - SUC m))` by (
  srw_tac [][Abbr`g`,Abbr`s`] >>
  DECIDE_TAC ) >>
qpat_assum `Abbrev (f = X)` (K ALL_TAC) >>
qpat_assum `Abbrev (g = X)` (K ALL_TAC) >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `SIGMA (λm. ABS_DIFF (f m) (g m)) s` >>
conj_tac >- srw_tac [][ABS_DIFF_SUM_IMAGE,Abbr`s`] >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `CARD s * (k * (delay_sum n + t MOD delay n - 1))` >>
conj_tac >- (
  match_mp_tac (MP_CANON SUM_IMAGE_upper_bound) >>
  srw_tac [][Abbr`s`] >>
  qmatch_assum_rename_tac `m < p` [] >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `k * ABS_DIFF (SUC (last_update n t) - delay_sum n - SUC m) (t - SUC m)` >>
  conj_tac >- srw_tac [][max_diff] >>
  srw_tac [][last_update_thm] >>
  Cases_on `k=0` >> srw_tac [][] >>
  srw_tac [][ABS_DIFF_SUB_SAME] >- DECIDE_TAC >- DECIDE_TAC >>
  srw_tac [][ABS_DIFF_def] >- DECIDE_TAC >>
  reverse (fsrw_tac [][NOT_LESS]) >- DECIDE_TAC >>
  `0 < delay_sum n` by srw_tac [][delay_sum_above_0] >>
  DECIDE_TAC ) >>
srw_tac [ARITH_ss][] >>
srw_tac [][GSYM MULT_ASSOC] >>
Cases_on `k=0` >> srw_tac [][Abbr`s`] >>
srw_tac [ARITH_ss][Abbr`q`]);

(*
val max_error_relative = Q.store_thm(
"max_error_relative",
`(∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ∧
 0 < n ∧
 t > SUC (tap n x) * delay n + delay n + delay_sum n ⇒
 error D n x t ≤ k * ∑ (λm. D (t − SUC m) + D (t - SUC m - (SUC (tap n x) * delay n))) (count ((delay_sum n) - 1))`,
srw_tac [][error_def] >>
`0 < delay n` by srw_tac [][delay_above_0] >>
`t MOD delay n < delay n` by srw_tac [][MOD_LESS] >>
`∀m. m < SUC (tap n x) * delay n ⇒ ¬(SUC (last_update n t) < delay_sum n + SUC m)` by (
  srw_tac [][last_update_thm] >>
  srw_tac [][SUB_LEFT_SUC] >>
  DECIDE_TAC ) >>
srw_tac [][output_eq_exact] >- (
  first_x_assum (qspec_then `0` mp_tac) >>
  srw_tac [][MULT] >> DECIDE_TAC ) >>
srw_tac [][exact_def] >>
qmatch_abbrev_tac `ABS_DIFF (SIGMA f s) (SIGMA g s) <= k * (SIGMA h u)` >>
`∀m. m ∈ s ⇒ (f m = D (SUC (last_update n t) - delay_sum n - SUC m))` by (
  srw_tac [][Abbr`f`,Abbr`s`] ) >>
`∀m. m ∈ s ⇒ (g m = D (t - SUC m))` by (
  srw_tac [][Abbr`g`,Abbr`s`] >>
  DECIDE_TAC ) >>
qpat_assum `Abbrev (f = X)` (K ALL_TAC) >>
qpat_assum `Abbrev (g = X)` (K ALL_TAC) >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `SIGMA (λm. ABS_DIFF (f m) (g m)) s` >>
conj_tac >- srw_tac [][ABS_DIFF_SUM_IMAGE,Abbr`s`] >>
match_mp_tac LESS_EQ_TRANS >>
qexists_tac `CARD s * (k * (delay_sum n + t MOD delay n - 1))` >>
conj_tac >- (
  match_mp_tac (MP_CANON SUM_IMAGE_upper_bound) >>
  srw_tac [][Abbr`s`] >>
  qmatch_assum_rename_tac `m < SUC (tap n x) * delay n` [] >>
  match_mp_tac LESS_EQ_TRANS >>
  qexists_tac `k * ABS_DIFF (SUC (last_update n t) - delay_sum n - SUC m) (t - SUC m)` >>
  conj_tac >- srw_tac [][max_diff] >>
  srw_tac [][last_update_thm] >>
  Cases_on `k=0` >> srw_tac [][] >>
  srw_tac [][ABS_DIFF_SUB_SAME] >- DECIDE_TAC >- DECIDE_TAC >>
  srw_tac [][ABS_DIFF_def] >- DECIDE_TAC >>
  reverse (fsrw_tac [][NOT_LESS]) >- DECIDE_TAC >>
  `0 < delay_sum n` by srw_tac [][delay_sum_above_0] >>
  DECIDE_TAC ) >>
srw_tac [ARITH_ss][] >>
srw_tac [][GSYM MULT_ASSOC] >>
Cases_on `k=0` >> srw_tac [][Abbr`s`] >>
*)

val input_0 = Q.store_thm(
"input_0",
`(FST (input n) = 0) = (n < 3)`,
srw_tac [][EQ_IMP_THM] >- (
  qmatch_rename_tac `m < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC m < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC (SUC m) < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC (SUC (SUC m)) < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC (SUC (SUC (SUC m))) < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC (SUC (SUC (SUC (SUC m)))) < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  qmatch_rename_tac `SUC (SUC (SUC (SUC (SUC (SUC m))))) < 3` [] >>
  Cases_on `m` >> fsrw_tac [][input_def] >>
  fsrw_tac [ARITH_ss][] ) >>
qmatch_rename_tac `FST (input m) = 0` [] >>
Cases_on `m` >- srw_tac [][input_def] >>
qmatch_rename_tac `FST (input (SUC m)) = 0` [] >>
Cases_on `m` >- srw_tac [][input_def] >>
qmatch_rename_tac `FST (input (SUC (SUC m))) = 0` [] >>
Cases_on `m` >- srw_tac [][input_def] >>
fsrw_tac [ARITH_ss][]);

val delay_sum_0 = Q.store_thm(
"delay_sum_0",
`(delay_sum n = 0) = (n = 0)`,
srw_tac [][EQ_IMP_THM,delay_sum_thm] >>
pop_assum mp_tac >>
qid_spec_tac `n` >>
ho_match_mp_tac COMPLETE_INDUCTION >>
Cases >- srw_tac [][delay_sum_thm] >>
strip_tac >>
simp_tac (srw_ss()) [delay_sum_def] >>
qmatch_rename_tac `delay (FST (input (SUC n))) ≠ 0 ∨ X` ["X"] >>
`0 < delay (FST (input (SUC n)))` by srw_tac [][delay_above_0] >>
fsrw_tac [ARITH_ss][]);

val delay_sum_1 = Q.store_thm(
"delay_sum_1",
`(delay_sum n = 1) = ((n = 1) ∨ (n = 2))`,
srw_tac [][EQ_IMP_THM] >>
srw_tac [][delay_sum_thm] >>
pop_assum mp_tac >>
qid_spec_tac `n` >>
ho_match_mp_tac COMPLETE_INDUCTION >>
Cases >- srw_tac [][delay_sum_thm] >>
strip_tac >>
simp_tac (srw_ss()) [delay_sum_def,ADD_EQ_1,delay_sum_0] >>
strip_tac >- (
  fsrw_tac [][input_0] >>
  qmatch_assum_rename_tac `SUC n < 3` [] >>
  Cases_on `n` >- fsrw_tac [][input_def] >>
  qmatch_assum_rename_tac `SUC (SUC n) < 3` [] >>
  Cases_on `n` >- fsrw_tac [][input_def] >>
  fsrw_tac [ARITH_ss][] ) >>
qmatch_assum_rename_tac `delay_sum (FST (input (SUC n))) = 1` [] >>
`FST (input (SUC n)) < SUC n` by (
  match_mp_tac input_earlier >>
  srw_tac [][] ) >>
res_tac >>
fsrw_tac [][delay_thm]);

(*
val max_error_eq = Q.store_thm(
"max_error_eq",
`∃D. (∀t. ABS_DIFF (D t) (D (SUC t)) ≤ k) ∧
     (!n x t. 0 < n /\ t > SUC (tap n x) * delay n + delay n + delay_sum n ⇒
              (error D n x t = SUC (tap n x) * delay n * k * (delay n + delay_sum n)))`,
qexists_tac `λn. (n + q) * k` >>
srw_tac [][] >- (
  srw_tac [][ABS_DIFF_def,MULT,RIGHT_ADD_DISTRIB] >>
  DECIDE_TAC ) >>
`0 < delay n` by srw_tac [][delay_above_0] >>
`t MOD delay n < delay n` by srw_tac [][MOD_LESS] >>
`SUC (t - t MOD delay n) > delay_sum n` by DECIDE_TAC >>
srw_tac [][error_def,output_eq_exact,last_update_thm] >-
  fsrw_tac [ARITH_ss][] >>
srw_tac [][exact_def] >>
qmatch_abbrev_tac `ABS_DIFF (SIGMA f s) (SIGMA g s) = z` >>
`ABS_DIFF (SIGMA f s) (SIGMA g s) = SIGMA (λx. ABS_DIFF (f x) (g x)) s` by (
  match_mp_tac (MP_CANON ABS_DIFF_SUM_IMAGE_eq) >>
  srw_tac [][Abbr`f`,Abbr`g`,Abbr`s`] >>
  fsrw_tac [ARITH_ss][] >>
  fsrw_tac [ARITH_ss][NOT_LESS] >> srw_tac [][] >>
  srw_tac [ARITH_ss][ADD1] >>
  mp_tac delay_sum_above_0 >>
  srw_tac [ARITH_ss][] ) >>
srw_tac [][] >>
qsuff_tac `∀m. m ∈ s ⇒ (ABS_DIFF (f m) (g m) = k * (delay n + delay_sum n))` >- (
  strip_tac >>
  qmatch_abbrev_tac `SIGMA ff s = z` >>
  Q.ISPECL_THEN [`s`,`ff`,`0`] mp_tac (MP_CANON SUM_SAME_IMAGE) >>
  `0 ∈ s` by (
    srw_tac [][Abbr`s`,MULT] >> DECIDE_TAC ) >>
  `∀q. q ∈ s ⇒ (ff 0 = ff q)` by (
    srw_tac [][Abbr`s`,Abbr`ff`] ) >>
  srw_tac [][Abbr`s`,Abbr`z`,Abbr`ff`] >>
  srw_tac [ARITH_ss][] ) >>
srw_tac [][Abbr`s`,Abbr`g`] >- DECIDE_TAC >>
srw_tac [][Abbr`f`] >- DECIDE_TAC >>
srw_tac [][ABS_DIFF_def] >- (
  `SUC m + (t - SUC m) = t` by (
    pop_assum mp_tac >>
    rpt (pop_assum (K ALL_TAC)) >>
    DECIDE_TAC ) >>
  fsrw_tac [][NOT_LESS]

) >>
  pop_assum mp_tac >>
  simp_tac (std_ss) [NOT_LESS] >>
  Cases_on `k=0` >- srw_tac [][] >>
  fsrw_tac [][NOT_LESS] >>
  Cases_on `t ≤ SUC m` >- (
    `t = SUC m` by metis_tac [LESS_EQ_ANTISYM,LESS_OR_EQ] >>
    srw_tac [][] >>
    srw_tac [ARITH_ss][] ) >>
  fsrw_tac [][] >>
  `SUC m + (t - SUC m) = t` by (
    srw_tac [ARITH_ss][] ) >>
  fsrw_tac [][] >>
  `0 < delay_sum n` by srw_tac [][delay_sum_above_0] >>
  `delay_sum n + t = SUC t + (delay_sum n - 1)` by (
    pop_assum mp_tac >>
    rpt (pop_assum (K ALL_TAC)) >>
    DECIDE_TAC ) >>
  `SUC (t - t MOD delay n) = (SUC t) - t MOD delay n` by (
    `t MOD delay n <= t` by metis_tac [MOD_LESS_EQ]  >>
    pop_assum mp_tac >>
    rpt (pop_assum (K ALL_TAC)) >>
    DECIDE_TAC ) >>
  fsrw_tac [][] >>
  strip_tac >>
  `delay_sum n = 1` by (
    pop_assum mp_tac >>
    qpat_assum `0 < delay_sum n` mp_tac >>
    rpt (pop_assum (K ALL_TAC)) >>
    DECIDE_TAC ) >>
  fsrw_tac [][delay_sum_1] >> srw_tac [][delay_sum_thm,delay_thm] >>
  fsrw_tac [][delay_sum_thm,delay_thm] >> srw_tac [][] >>
  Cases_on `x` >> fsrw_tac [][tap_def,COUNT_SUC,SUM_IMAGE_count_SUM_GENLIST,NOT_LESS,NOT_LESS_EQUAL,ADD1] >>
  fsrw_tac [ARITH_ss][] >> srw_tac [][]
*)

(*
some sanity checks

val sanity = Q.prove(`(!t. D t = t) ==> (RS D 1 26 = 49)`,
srw_tac [][RS_def] >>
ntac 80 (
srw_tac [][Once output_def,update_time_def,delay_thm,tap_def] >>
srw_tac [][source_def,input_def,Once SR_def] >>
srw_tac [][Once SR_def,update_time_def,delay_thm] >>
srw_tac [][source_def,Once SR_def,update_time_def,delay_thm,input_def] ))

val sanity = Q.prove(
`(!t. D t = t) ==> (SR D 1 4 10 = 5)`,
strip_tac >>
ntac 5 (
srw_tac [][Once SR_def,update_time_def,delay_thm] >>
srw_tac [][source_def] ) >>
srw_tac [][input_def,Once output_def])

val sanity = Q.prove(
`(!t. D t = t) ==> (RS D 2 10 = 44)`,
srw_tac [][RS_def] >>
ntac 80 (
srw_tac [][Once output_def,update_time_def,delay_thm,source_def,input_def,Once SR_def,tap_def] ))

val sanity = Q.prove(
`(!t. D t = t) ==> (RS D 2 26 = 172)`,
srw_tac [][RS_def] >>
ntac 240 (
srw_tac [][Once output_def,update_time_def,delay_thm,source_def,input_def,Once SR_def,tap_def] ))

val sanity = Q.prove(
`(!t. D t = t) ==> (RS D 4 9 = 21)`,
srw_tac [][RS_def] >>
ntac 90 ( srw_tac [][Once output_def,update_time_def,delay_thm,source_def,input_def,Once SR_def,tap_def] ))
*)

val _ = export_theory ()
