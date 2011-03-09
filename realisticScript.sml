open HolKernel boolLib boolSimps bossLib arithmeticTheory pred_setTheory listTheory sortingTheory lcsymtacs

val _ = new_theory "realistic"

val RS0_def = Define`
  (RS0 D 0 = 0) ∧
  (RS0 D (SUC t) = D t)`

val RS1_def = Define`
  (RS1 D 0 = 0) ∧
  (RS1 D (SUC 0) = D 0) ∧
  (RS1 D (SUC (SUC t)) = D (SUC t) + D t)`

(* tap n x is the location of tap x of slice n *)
val tap_def = Define`
  (tap 0 0 = 8  -1) ∧
  (tap 0 1 = 16 -1) ∧
  (tap 1 0 = 32 -1) ∧
  (tap 1 1 = 128-1) ∧
  (tap 2 0 = 32 -1) ∧
  (tap 2 1 = 128-1) ∧
  (tap 3 0 = 16 -1) ∧
  (tap 3 1 = 64 -1) ∧
  (tap 4 0 = 16 -1) ∧
  (tap 4 1 = 64 -1)`

val delay_def = Define`
  (delay 0 = 1) ∧
  (delay 1 = 2) ∧
  (delay 2 = 64) ∧
  (delay 3 = 2048) ∧
  (delay 4 = 32768)`

(* update_time n t <=> t is an update time for slice n *)
val update_time_def = Define`
  update_time n t = (t MOD (delay n) = 0)`

(* source D n m = the source of input for SR m of slice n *)
(* output D n x = output x of slice n *)
(* SR D n m = shift register m of slice n *)
val Slice_def = tDefine "Slice" `
  (source D 0 0 t = D t) ∧
  (source D (SUC 0) 0 t = RS1 D t) ∧
  (source D (SUC n) 0 t = output D n 0 t) ∧
  (source D n (SUC m) t = SR D n m t) ∧
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
      (INL (D,n,m,t)) -> (n,m,t,1) ||
      (INR (INR (D,n,m,t))) -> (n,m,t,2) ||
      (INR (INL (D,n,x,t))) -> (n,tap n x,t,3))`)

val RS_def = Define`
  (RS D 0 = RS0 D) ∧
  (RS D 1 = RS1 D) ∧
  (RS D n = output D (n DIV 2 - 1) (n MOD 2))`

val output_def = Q.store_thm(
"output_def",
`output D n x t = if t = 0 then 0 else if update_time n t then output D n x (t - 1) + source D n 0 (t - 1) - SR D n (tap n x) (t - 1) else output D n x (t - 1)`,
Cases_on `t` >> srw_tac [][Slice_def])

val SR_def = Q.store_thm(
"SR_def",
`SR D n m t = if t = 0 then 0 else if update_time n t then source D n m (t - 1) else SR D n m (t - 1)`,
Cases_on `t` >> srw_tac [][Slice_def])

val RS1_thm = Q.store_thm(
"RS1_thm",
`RS1 D t = if t = 0 then 0 else if t = 1 then D 0 else D (t - 1) + D (t - 2)`,
Cases_on `t` >> simp_tac bool_ss [RS1_def,ONE] >> Cases_on `n` >> simp_tac arith_ss [RS1_def] >>
simp_tac bool_ss [TWO,ONE] >> srw_tac [ARITH_ss][])

val source_def = Q.store_thm(
"source_def",
`source D n m t = if m = 0 then if n = 0 then D t else if n = 1 then RS1 D t else output D (n - 1) 0 t else SR D n (m - 1) t`,
Cases_on `n` >> Cases_on `m` >> srw_tac [][SIMP_RULE (srw_ss()++ARITH_ss) [] Slice_def] >>
qmatch_rename_tac `source D (SUC a) X Y = Z` ["X","Y","Z"] >>
Cases_on `a` >> fsrw_tac [][Slice_def])

val SR_def = Q.store_thm(
"SR_def",
`SR D n m t = if t = 0 then 0 else if update_time n t then source D n m (t-1) else SR D n m (t-1)`,
Cases_on `t` >> srw_tac [][Slice_def]);

val source_0_thm = Q.store_thm(
"source_0_thm",
`source D 0 n t = if n <= t then D (t - n) else 0`,
qid_spec_tac `t` >> Induct_on `n` >> srw_tac [][source_def] >>
srw_tac [ARITH_ss][Once SR_def,update_time_def,delay_def,ADD1])

val delay_above_0 = Q.store_thm(
"delay_above_0",
`n < 5 ⇒ 0 < delay n`,
Cases_on `n` >> srw_tac [][delay_def] >>
qmatch_assum_rename_tac `SUC n < 5` [] >>
Cases_on `n` >> srw_tac [][delay_def] >>
qmatch_assum_rename_tac `SUC (SUC n) < 5` [] >>
Cases_on `n` >> srw_tac [][delay_def] >>
qmatch_assum_rename_tac `SUC (SUC (SUC n)) < 5` [] >>
Cases_on `n` >> srw_tac [][delay_def] >>
qmatch_assum_rename_tac `SUC (SUC (SUC (SUC n))) < 5` [] >>
Cases_on `n` >> srw_tac [][delay_def] >>
fsrw_tac [ARITH_ss][])

val SR_0_until = Q.store_thm(
"SR_0_until",
`0 < delay n ∧ t < (SUC m) * (delay n) ⇒ (SR D n m t = 0)`,
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
  fsrw_tac [][] >>
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

val SR_last_update = Q.store_thm(
"SR_last_update",
`SR D n m t = SR D n m (last_update n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
srw_tac [][Once SR_def]);

val update_time_last_update = Q.store_thm(
"update_time_last_update",
`0 < delay n ⇒ update_time n (last_update n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
srw_tac [][update_time_def,ZERO_MOD])

val last_update_eq_iff_update_time = Q.store_thm(
"last_update_eq_iff_update_time",
`0 < delay n ⇒ ((last_update n t = t) ⇔ update_time n t)`,
strip_tac >> EQ_TAC >> strip_tac >- PROVE_TAC [update_time_last_update] >>
Cases_on `t` >> srw_tac [][last_update_def])

val last_update_zero = Q.store_thm(
"last_update_zero",
`0 < delay n ⇒ ((last_update n t = 0) ⇔ (t < delay n))`,
Induct_on `t` >- srw_tac [][last_update_def] >>
srw_tac [][EQ_IMP_THM] >- (
  (last_update_mono |> Q.INST [`x`|->`t`,`y`|->`SUC t`] |> mp_tac) >>
  srw_tac [][] >>
  fsrw_tac [][last_update_def,update_time_def] >>
  match_mp_tac LESS_SUC_EQ_COR >>
  fsrw_tac [][] >>
  spose_not_then strip_assume_tac >>
  imp_res_tac DIVMOD_ID >>
  fsrw_tac [][] ) >>
imp_res_tac prim_recTheory.SUC_LESS >>
fsrw_tac [][] >>
srw_tac [][last_update_def,update_time_def])

val last_update_thm = Q.store_thm(
"last_update_thm",
`0 < delay n ⇒ (last_update n t = t - t MOD (delay n))`,
strip_tac >>
Induct_on `t` >> srw_tac [][last_update_def,update_time_def] >>
qabbrev_tac `dn = delay n` >>
qabbrev_tac `tm = t MOD dn` >>
qabbrev_tac `td = t DIV dn` >>
qabbrev_tac `sm = SUC t MOD dn` >>
qabbrev_tac `sd = SUC t DIV dn` >>
`t = td * dn + tm` by PROVE_TAC [DIVISION] >>
`sm = SUC tm` by (
  map_every qunabbrev_tac [`sm`,`tm`] >>
  match_mp_tac MOD_SUC >>
  qabbrev_tac `tm = t MOD dn` >>
  fsrw_tac [][ADD_SUC,MULT_SUC,MULT] >>
  qpat_assum `0 < dn` assume_tac >>
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
`0 < delay n ∧ 0 < t ∧ update_time n t ⇒ (last_update n (t - 1) = t - delay n)`,
srw_tac [][last_update_thm,update_time_def] >>
qabbrev_tac `dn = delay n` >>
qabbrev_tac `tm = t MOD dn` >>
qabbrev_tac `td = t DIV dn` >>
`t = td * dn + tm` by PROVE_TAC [DIVISION] >>
srw_tac [][] >> fsrw_tac [][] >>
`0 < td` by (Cases_on `td` >> fsrw_tac [][]) >>
`1 ≤ dn` by DECIDE_TAC >>
srw_tac [][MOD_TIMES_SUB] >>
DECIDE_TAC)

val SR_prev = Q.store_thm(
"SR_prev",
`0 < delay n ⇒ (SR D n (SUC m) t = if t < SUC (SUC m) * delay n then 0 else SR D n m (t - delay n))`,
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
  `delay n ≤ t` by DECIDE_TAC >>
  srw_tac [ARITH_ss][SUB_MOD] ) >>
imp_res_tac update_time_last_update >>
fsrw_tac [][])

val SR_first = Q.store_thm(
"SR_first",
`0 < delay n ⇒ (SR D n m t = if t < SUC m then 0 else SR D n 0 (t - (m * delay n)))`,
strip_tac >>
qid_spec_tac `t` >>
Induct_on `m` >> fsrw_tac [][SR_prev]
>- (Cases >> srw_tac [ARITH_ss][SR_0_until]) >>
gen_tac >>
Cases_on `t < SUC (SUC m)` >- (
  srw_tac [][] >>
  match_mp_tac SR_0_until >>
  srw_tac [ARITH_ss][] ) >>
Cases_on `t < SUC (SUC m) * delay n` >- (
  srw_tac [][] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac SR_0_until >>
  fsrw_tac [][MULT] ) >>
Cases_on `t < delay n + SUC m` >- (
  srw_tac [][] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac SR_0_until >>
  fsrw_tac [][MULT,NOT_LESS] >>
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
Induct_on `t` >> srw_tac [][Slice_def,last_update_def])

val tap_above_0 = Q.store_thm(
"tap_above_0",
`n < 5 ∧ x < 2 ⇒ 0 < tap n x`,
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
reverse (Cases_on `m`) >>
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
reverse (Cases_on `x`) >>
fsrw_tac [][tap_def] >- (
  Cases_on `n` >> srw_tac [ARITH_ss][] >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  fsrw_tac [ARITH_ss][] )
>- (
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
  Cases_on `m` >> srw_tac [][tap_def] >>
  fsrw_tac [ARITH_ss][] ) >>
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][tap_def] >>
fsrw_tac [ARITH_ss][])

val output_sum = Q.store_thm(
"output_sum",
`output D n x t = SIGMA (λm. SR D n m t) (count (SUC (tap n x)))`,
Induct_on `t` >> srw_tac [][Slice_def] >-
  srw_tac [][SUM_IMAGE_ZERO] >>
srw_tac [][SUM_IMAGE_count_SUM_GENLIST] >>
srw_tac [][GENLIST_CONS,SimpRHS] >>
srw_tac [][combinTheory.o_DEF] >>
`∀x. source D n (SUC x) t = SR D n x t` by srw_tac [][source_def] >>
srw_tac [ARITH_ss][GENLIST,SUM_SNOC])

val output_first = Q.store_thm(
"output_first",
`0 < delay n ⇒ (output D n x t = SIGMA (λm. if t ≤ m * (delay n) then 0 else SR D n 0 (t - m * (delay n))) (count (SUC (tap n x))))`,
srw_tac [][output_sum] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [][Once SR_first] >- (
  match_mp_tac (GSYM SR_0_until) >>
  fsrw_tac [][NOT_LESS_EQUAL,GSYM MULT] >>
  match_mp_tac LESS_LESS_EQ_TRANS >>
  qmatch_assum_rename_tac `t < SUC z` [] >>
  qexists_tac `SUC z` >>
  srw_tac [][] ) >>
match_mp_tac SR_0_until >>
DECIDE_TAC)

val prev1_update_time = Q.store_thm(
"prev1_update_time",
`0 < delay n ∧ 0 < t ∧ update_time n t ⇒ update_time n (t - delay n)`,
srw_tac [][update_time_def] >>
Cases_on `t < delay n` >- (
  imp_res_tac (GSYM X_MOD_Y_EQ_X) >>
  fsrw_tac [][] ) >>
qsuff_tac `((t - delay n * 1) MOD delay n = t MOD delay n)` >- srw_tac [][] >>
match_mp_tac MOD_SUB >>
fsrw_tac [][NOT_LESS])

val prev_update_time = Q.store_thm(
"prev_update_time",
`0 < delay n ∧ z * delay n < t ∧ update_time n t ⇒ update_time n (t - z * delay n)`,
Induct_on `z` >> srw_tac [][] >>
fsrw_tac [][MULT,SUB_PLUS] >>
`z * delay n < t` by DECIDE_TAC >>
`0 < t - z * delay n` by DECIDE_TAC >>
srw_tac [][prev1_update_time])

val output_source_at_update_times = Q.store_thm(
"output_source_at_update_times",
`0 < delay n ∧ update_time n t ⇒ (output D n x t = SIGMA (λm. if t ≤ m * (delay n) then 0 else source D n 0 (t - m * (delay n) - 1)) (count (SUC (tap n x))))`,
srw_tac [][output_first] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [ARITH_ss][Once SR_def] >>
fsrw_tac [][NOT_LESS_EQUAL] >>
imp_res_tac prev_update_time)

val delay_SUC = Q.store_thm(
"delay_SUC",
`0 < n ∧ n < 4 ⇒ (delay (SUC n) = delay n * SUC (tap n 0))`,
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][delay_def,tap_def] >>
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][delay_def,tap_def] >>
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][delay_def,tap_def] >>
qabbrev_tac `m = n` >> POP_ASSUM (K ALL_TAC) >>
Cases_on `m` >> srw_tac [][delay_def,tap_def] >>
fsrw_tac [ARITH_ss][])

val output_input_at_update_times = Q.store_thm(
"output_input_at_update_times",
`(∀k. k ≤ n ⇒ 0 < delay k) ∧
 (∀k t. k < n ⇒ update_time (SUC k) t ⇒ update_time k t) ∧ update_time n t
⇒ (output D n x t = SIGMA (λm. if t < m + SUC n then 0 else D (t - m - SUC n)) (count (SUC (tap n x) * delay n)))`,
map_every qid_spec_tac [`t`,`x`,`n`] >>
Induct >- (
  fsrw_tac [][output_source_at_update_times,delay_def,source_0_thm,
              GSYM ADD1,LESS_OR_EQ,prim_recTheory.LESS_THM,DISJ_SYM] ) >>
srw_tac [][output_source_at_update_times] >>
srw_tac [][source_def] >>
Cases_on `n=0` >- (
  srw_tac [][delay_def] >>
  srw_tac [][MULT_SYM] >>
  match_mp_tac EQ_SYM >>
  match_mp_tac SUM_IMAGE_count_MULT >>
  srw_tac [ARITH_ss][] >- (
    srw_tac [][SUM_IMAGE_ZERO] ) >>
  srw_tac [][SUM_IMAGE_count_SUM_GENLIST] >- (
    fsrw_tac [ARITH_ss][update_time_def,delay_def,NOT_LESS_EQUAL,GSYM EVEN_MOD2] >>
    `t = SUC (2 * m)` by DECIDE_TAC >>
    srw_tac [][] >>
    fsrw_tac [][EVEN,EVEN_DOUBLE] )
  >- (
    DECIDE_TAC )
  >- (
    fsrw_tac [ARITH_ss][NOT_LESS] >>
    `t = 2 * m + 2` by DECIDE_TAC >>
    srw_tac [ARITH_ss][RS1_thm] ) >>
  fsrw_tac [ARITH_ss][NOT_LESS,RS1_thm] ) >>
srw_tac [][]


val output_input_at_update_times = Q.store_thm(
"output_input_at_update_times",
`(∀k. k ≤ n ⇒ 0 < delay k) ∧
 (∀k t. k < n ⇒ update_time (SUC k) t ⇒ update_time k t) ∧
 update_time n t
⇒ (output D n x t = SIGMA (λm. if t < m + SUC n then 0 else D (t - m - SUC n)) (count (SUC (tap n x))))`,
map_every qid_spec_tac [`t`,`x`,`n`] >>
Induct >- (
  fsrw_tac [][output_source_at_update_times,delay_def,source_0_thm,
              GSYM ADD1,LESS_OR_EQ,prim_recTheory.LESS_THM,DISJ_SYM] ) >>
srw_tac [][] >>
srw_tac [][output_source_at_update_times] >>
srw_tac [][source_def]
tap_def

`update_time n t` by (
  first_x_assum (match_mp_tac o MP_CANON) >>
  srw_tac [][] ) >>
`∀k t. k < n ⇒ update_time (SUC k) t ⇒ update_time k t` by
  PROVE_TAC [prim_recTheory.LESS_SUC] >>
`∀k. k ≤ n ⇒ 0 < delay k` by
  PROVE_TAC [LESS_EQ_SUC_REFL,LESS_EQ_TRANS] >>
fsrw_tac [][] >>
simp_tac (srw_ss()) [source_def]
fsrw_tac [ARITH_ss][source_def,GSYM ADD1] >>
srw_tac [][]
qmatch_abbrev_tac `X = SIGMA f (count (SUC (tap (SUC n) x)))` >>
srw_tac [][EXP] >>
match_mp_tac EQ_SYM >>
srw_tac [][Once MULT_SYM] >>
qunabbrev_tac `X` >>
match_mp_tac SUM_IMAGE_count_MULT >>
qunabbrev_tac `m` >>
qx_gen_tac `m` >>
strip_tac >>
qunabbrev_tac `f` >>
srw_tac [][GSYM SUC_ADD_SYM] >- (
  srw_tac [ARITH_ss][SUM_IMAGE_ZERO] ) >>
`update_time p n (t - m * SUC p.w ** SUC n)` by (
  fsrw_tac [ARITH_ss][update_time_def,GSYM SUC_ADD_SYM] >>
  `m ≤ SUC x` by (
    srw_tac [][] >> fsrw_tac [ARITH_ss][] ) >>
  srw_tac [][LESS_EQ_ADD_SUB,GSYM RIGHT_SUB_DISTRIB] >>
  qexists_tac `PRE ((SUC x - m) * SUC p.w)` >>
  `0 < ((SUC x - m) * SUC p.w)` by fsrw_tac [ARITH_ss][MULT] >>
  fsrw_tac [][SUC_PRE,EXP,MULT_ASSOC] ) >>
first_x_assum (qspec_then `t - m * SUC p.w ** SUC n` mp_tac) >>
srw_tac [][] >>
match_mp_tac SUM_IMAGE_CONG >>
fsrw_tac [ARITH_ss][GSYM SUC_ADD_SYM,ADD_SYM] >>
fsrw_tac [ARITH_ss][SUC_ADD_SYM,Once ADD_SYM])

val last_updates_eq = Q.store_thm(
"last_updates_eq",
`(if t ≤ n then k + t < n + SUC p.w ** n else k < SUC p.w ** n - (t - n) MOD SUC p.w ** n) ⇔
 (last_update n (t + k) = last_update n t)`,
Cases_on `t ≤ n` >- (
  srw_tac [][] >>
  `0 < SUC p.w ** n` by srw_tac [][] >>
  `t < n + SUC p.w ** n` by DECIDE_TAC >>
  fsrw_tac [][SYM last_update_zero] >>
  srw_tac [ARITH_ss][last_update_zero] ) >>
fsrw_tac [][] >>
Cases_on `t < n + SUC p.w ** n` >- (
  fsrw_tac [][SYM last_update_zero] >>
  fsrw_tac [ARITH_ss][last_update_zero] ) >>
`¬(t + k < n + SUC p.w ** n)` by fsrw_tac [ARITH_ss][] >>
srw_tac [][last_update_thm] >>
qabbrev_tac `w = SUC p.w ** n` >>
`0 < w` by srw_tac [][Abbr`w`] >>
match_mp_tac EQ_SYM >>
`(t - n) MOD w < w` by PROVE_TAC [MOD_LESS] >>
match_mp_tac EQ_TRANS >>
qexists_tac `(t - n) MOD w + k = (t - n + k) MOD w` >>
conj_tac >- fsrw_tac [ARITH_ss][] >>
CONV_TAC (LAND_CONV SYM_CONV) >>
match_mp_tac MOD_LIFT_PLUS_IFF >>
first_assum ACCEPT_TAC)

val output_input = Q.store_thm(
"output_input",
`update_time p n t ∧ u < (SUC p.w ** n) ⇒
(output p n (t + u) = SIGMA (λm. if t < m + SUC n then 0 else p.input (t - m - SUC n)) (count (SUC p.w ** SUC n)))`,
srw_tac [][Once output_last_update] >>
`update_time p n (last_update p n (t + u))` by (
  fsrw_tac [ARITH_ss][update_time_def,MULT,SYM update_time_last_update_iff] ) >>
`last_update p n (t + u) = t` by (
  `t = last_update p n t` by (
    match_mp_tac EQ_SYM >>
    srw_tac [][last_update_eq_iff_update_time] ) >>
  qsuff_tac `last_update p n (t + u) = last_update p n t` >- srw_tac [][] >>
  srw_tac [][SYM last_updates_eq] >- DECIDE_TAC >>
  fsrw_tac [][last_update_eq_iff_update_time,update_time_def] >>
  qmatch_abbrev_tac `u < w - (q * w) MOD w` >>
  qsuff_tac ` u < w - (q * w + 0) MOD w` >- srw_tac [][] >>
  `0 < w` by srw_tac [][Abbr`w`] >>
  srw_tac [][MOD_MULT] ) >>
srw_tac [][output_input_at_update_times])

val output_0_until = Q.store_thm(
"output_0_until",
`t < n + width ** n ⇒ (output p n t = 0)`,
srw_tac [ARITH_ss][output_first,SUM_IMAGE_ZERO,SR_0_until])

val all_times_covered = Q.store_thm(
"all_times_covered",
`t < n + width ** n ∨ ∃v u. update_time p n v ∧ u < (SUC p.w ** n) ∧ (t = v + u)`,
Cases_on `t < n + width ** n` >>
fsrw_tac [DNF_ss,ARITH_ss][update_time_def,MULT,NOT_LESS,LESS_EQ_EXISTS] >>
qmatch_assum_rename_tac `t = n + (z + width ** n)` [] >>
qexists_tac `z MOD width ** n` >>
qexists_tac `z DIV width ** n` >>
srw_tac [ARITH_ss][MOD_LESS] >>
`0 < width ** n` by srw_tac [][] >>
qspec_then `width ** n` imp_res_tac DIVISION >>
REPEAT (first_x_assum (qspec_then `z` mp_tac)) >>
srw_tac [ARITH_ss][])

(* some sanity checks *)

Q.prove(`(!t. D t = t) ==> (RS1 D 26 = 49)`,
srw_tac [][RS1_thm])

Q.prove(
`(!t. D t = t) ==>
 (SR D 0 4 10 = 5)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 5 (srw_tac [][Once SR_def,source_def,delay_def,update_time_def]))

Q.prove(
`(!t. D t = t) ==>
 (RS D 2 10 = 44)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 16 (
ntac 2 (srw_tac [][RS_def,source_def,Once output_def,delay_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,delay_def,update_time_def])))

Q.prove(`(!t. D t = t) ==> (RS D 2 26 = 172)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 48 (
ntac 2 (srw_tac [][RS_def,source_def,Once output_def,delay_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,delay_def,update_time_def])))

val sanity = Q.prove(
`(!t. D t = t) ==> (RS D 4 9 = 21)`,
assume_tac (Slice_def |> CONJUNCT2 |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 5 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
strip_tac >>
ntac 8 (
ntac 2 (srw_tac [][RS_def,source_def,Once output_def,delay_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,delay_def,update_time_def]) >>
srw_tac [][RS1_thm] ))

val _ = export_theory ()
