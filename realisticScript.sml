open HolKernel boolLib boolSimps bossLib arithmeticTheory pred_setTheory lcsymtacs

val _ = new_theory "realistic"

val RS0_def = Define`
  (RS0 D 0 = 0) ∧
  (RS0 D (SUC t) = D t)`

val RS1_def = Define`
  (RS1 D 0 = 0) ∧
  (RS1 D (SUC 0) = 0) ∧
  (RS1 D (SUC (SUC t)) = D (SUC t) + D t)`

(* tap n x is the location of tap x of slice n *)
val tap_def = Define`
  (tap 1 0 = 8  -1) ∧
  (tap 1 1 = 16 -1) ∧
  (tap 2 0 = 32 -1) ∧
  (tap 2 1 = 128-1) ∧
  (tap 3 0 = 32 -1) ∧
  (tap 3 1 = 128-1) ∧
  (tap 4 0 = 16 -1) ∧
  (tap 4 1 = 64 -1) ∧
  (tap 5 0 = 16 -1) ∧
  (tap 5 1 = 64 -1)`

(* update_time n t <=> t is an update time for slice n *)
val update_time_def = Define`
  (update_time 1 t = ((SUC t) MOD 1    =0)) ∧
  (update_time 2 t = ((SUC t) MOD 2    =0)) ∧
  (update_time 3 t = ((SUC t) MOD 64   =0)) ∧
  (update_time 4 t = ((SUC t) MOD 2048 =0)) ∧
  (update_time 5 t = ((SUC t) MOD 32768=0))`

(* source D n m = the source of input for SR m of slice n *)
(* output D n x = output x of slice n *)
(* SR D n m = shift register m of slice n *)
val Slice_def = tDefine "Slice" `
  (source D (SUC 0) 0 t = D t) ∧
  (source D (SUC (SUC 0)) 0 t = RS1 D t) ∧
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
  (RS D n = output D (n DIV 2) (n MOD 2))`

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
`RS1 D t = if t = 0 then 0 else if t = 1 then 0 else D (t - 1) + D (t - 2)`,
Cases_on `t` >> simp_tac bool_ss [RS1_def,ONE] >> Cases_on `n` >> simp_tac arith_ss [RS1_def] >>
simp_tac bool_ss [TWO,ONE] >> srw_tac [ARITH_ss][])

Q.prove(`(!t. D t = t) ==> (RS1 D 26 = 49)`,
srw_tac [][RS1_thm])

Q.prove(
`(!t. D t = t) ==>
 (SR D 1 4 10 = 5)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 5 (srw_tac [][Once SR_def,update_time_def]))

Q.prove(
`(!t. D t = t) ==>
 (RS D 2 10 = 44)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 13 (
ntac 2 (srw_tac [][RS_def,Once output_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,update_time_def])))

Q.prove(`(!t. D t = t) ==> (RS D 2 26 = 172)`,
strip_tac >>
assume_tac (Slice_def |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 4 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
ntac 51 (
ntac 2 (srw_tac [][RS_def,Once output_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,update_time_def])))

val sanity = Q.prove(
`(!t. D t = t) ==> (RS D 4 9 = 28)`,
assume_tac (Slice_def |> CONJUNCT2 |> CONJUNCT1 |> Q.GEN `t` |> SIMP_RULE arith_ss []) >>
assume_tac (Slice_def |> funpow 5 CONJUNCT2 |> CONJUNCT1 |>
 Q.GEN `t` |> Q.INST[`m`|->`PRE m`] |>
 SIMP_RULE arith_ss [#1(EQ_IMP_RULE SUC_PRE),ASSUME``0<m``,PRE_SUB1] |>
 DISCH_ALL |> Q.GEN `m`) >>
strip_tac >>
ntac 7 (
ntac 2 (srw_tac [][RS_def,Once output_def,update_time_def,tap_def]) >>
ntac 4 (srw_tac [][Once SR_def,update_time_def]) >>
srw_tac [][RS1_thm] ))

(* old model from here onwards *)

val output2_def = Define`
  output2 p (SUC n) (SUC t) =
  if update_time p (SUC n) (SUC t)
  then output2 p n t
       + (output2 p n (SUC t)
          - SR p (SUC n) p.w (SUC t))
  else output2 p (SUC n) t`

val source_def = Q.store_thm(
"source_def",
`(source p n m t = if m = 0 then if n = 0 then p.input t else output p (n - 1) t else SR p n (m - 1) t)`,
Cases_on `n` >> Cases_on `m` >> srw_tac [][FUN_EQ_THM,Slice_def] );

val SR_def = Q.store_thm(
"SR_def",
`SR p n m t = if t = 0 then 0 else if update_time p n t then source p n m (t-1) else SR p n m (t-1)`,
Cases_on `t` >> srw_tac [][Slice_def]);

val source_0_thm = Q.store_thm(
"source_0_thm",
`source p 0 n t = if n <= t then p.input (t - n) else 0`,
qid_spec_tac `t` >> Induct_on `n` >>
srw_tac [ARITH_ss][Once SR_def,Slice_def,update_time_def] >-
  srw_tac [ARITH_ss][ADD1] >>
Cases_on `t` >> srw_tac [][]);

val SR_0_until = Q.store_thm(
"SR_0_until",
`t < n + (SUC m) * (SUC p.w) ** n ⇒ (SR p n m t = 0)`,
qid_spec_tac `t` >> Induct_on `m` >>
Induct >> srw_tac [][]
>- srw_tac [][Once SR_def]
>- (
  srw_tac [][Once SR_def,update_time_def] >>
  fsrw_tac [ARITH_ss][ADD1] )
>- srw_tac [][Once SR_def] >>
srw_tac [][Once SR_def,update_time_def] >>
fsrw_tac [ARITH_ss][ADD1] >> srw_tac [][] >>
fsrw_tac [ARITH_ss][EXP] >>
srw_tac [][source_def] >>
first_x_assum match_mp_tac >- (
  qmatch_rename_tac `t < n + (m + 1) * z` [] >>
  qsuff_tac `(x+1) * z <= (m+1) * z` >- DECIDE_TAC >>
  match_mp_tac LESS_MONO_MULT >>
  fsrw_tac [ARITH_ss][LESS_EQ,ADD1]
) >> DECIDE_TAC)

val last_update_def = Define
`(last_update p n 0 = 0) ∧
 (last_update p n (SUC t) = if update_time p n (SUC t) then (SUC t) else last_update p n t)`

val last_update_thm = Q.store_thm(
"last_update_thm",
`last_update p n t = if t < n + (SUC p.w)**n then 0 else t - (t-n) MOD (SUC p.w)**n`,
srw_tac [][] >- (
  Induct_on `t` >> srw_tac [][last_update_def,update_time_def] >-
    srw_tac [][NOT_LESS] >>
  first_x_assum match_mp_tac >>
  DECIDE_TAC ) >>
fsrw_tac [][NOT_LESS] >>
Induct_on `t` >> srw_tac [][last_update_def,update_time_def] >- (
  qmatch_rename_tac `z = z - (z - n) MOD (SUC w) ** n` [] >>
  qsuff_tac `(z - n) MOD (SUC w) ** n = 0` >- srw_tac [][] >>
  match_mp_tac MOD_UNIQUE >>
  qexists_tac `SUC x` >>
  srw_tac [ARITH_ss][] ) >>
Cases_on `n + SUC p.w ** n = SUC t` >- (
  fsrw_tac [ARITH_ss][] >> srw_tac [][] >>
  first_x_assum (qspec_then `0` mp_tac) >>
  srw_tac [ARITH_ss][] ) >>
`n + SUC p.w ** n ≤ t` by DECIDE_TAC >>
fsrw_tac [ARITH_ss][] >> srw_tac [][] >>
qabbrev_tac `b = SUC p.w ** n` >>
`0 < b` by srw_tac [][Abbr`b`] >>
qsuff_tac `(SUC (t - n)) MOD b = SUC ((t - n) MOD b)` >- DECIDE_TAC >>
match_mp_tac MOD_SUC >>
srw_tac [][] >>
qmatch_rename_tac `SUC (t - n) <> SUC z * b` [] >>
`SUC t <> n + SUC z * b` by PROVE_TAC [] >>
DECIDE_TAC);

val last_update_zero = Q.store_thm(
"last_update_zero",
`(last_update p n t = 0) ⇔ (t < n + (SUC p.w)**n)`,
srw_tac [][last_update_thm] >>
fsrw_tac [][NOT_LESS,NOT_LESS_EQUAL] >>
`(t - n) MOD SUC p.w ** n < SUC p.w ** n` by (
  match_mp_tac MOD_LESS >>
  MATCH_ACCEPT_TAC ZERO_LESS_EXP ) >>
DECIDE_TAC)

val SR_last_update = Q.store_thm(
"SR_last_update",
`SR p n m t = SR p n m (last_update p n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
srw_tac [][Once SR_def]);

val update_time_last_update = Q.store_thm(
"update_time_last_update",
`n + (SUC p.w ** n) ≤ t ⇒ update_time p n (last_update p n t)`,
Induct_on `t` >> srw_tac [][last_update_def] >>
fsrw_tac [][LESS_OR_EQ,prim_recTheory.LESS_THM] >>
fsrw_tac [][update_time_def] >>
first_x_assum (qspec_then `0` mp_tac) >>
srw_tac [][]);

val update_time_last_update_iff = Q.store_thm(
"update_time_last_update_iff",
`n + (SUC p.w ** n) ≤ t ⇔ update_time p n (last_update p n t)`,
EQ_TAC >- ACCEPT_TAC update_time_last_update >>
Induct_on `t` >> srw_tac [][update_time_def,last_update_def] >>
fsrw_tac [ARITH_ss][update_time_def]);

val last_update_upper_bound = Q.store_thm(
"last_update_upper_bound",
`last_update p n t ≤ t`,
srw_tac [][last_update_thm]);

val last_update_eq_iff_update_time = Q.store_thm(
"last_update_eq_iff_update_time",
`(last_update p n t = t) ⇔ (t = 0) ∨ update_time p n t`,
EQ_TAC >> strip_tac >- (
  Cases_on `t = 0` >> srw_tac [][] >>
  qsuff_tac `n + (SUC p.w ** n) ≤ t`
  >- PROVE_TAC [update_time_last_update_iff] >>
  qpat_assum `last_update p n t = t` mp_tac >>
  srw_tac [][last_update_thm] >>
  fsrw_tac [][NOT_LESS] )
>- srw_tac [][last_update_thm] >>
Cases_on `t` >> srw_tac [][last_update_def]);

val update_time_lower_bound = Q.store_thm(
"update_time_lower_bound",
`update_time p n t ==> n + SUC p.w ** n ≤ t`,
ntac 2 (srw_tac [ARITH_ss][update_time_def]));

val last_update_sub1 = Q.store_thm(
"last_update_sub1",
`update_time p n t ==> (last_update p n (t - 1) = if n + SUC p.w ** n < t then t - SUC p.w ** n else 0)`,
strip_tac >>
imp_res_tac update_time_lower_bound >>
fsrw_tac [][LESS_OR_EQ] >- (
  `~(t -1 < n + SUC p.w ** n)` by DECIDE_TAC >>
  srw_tac [][last_update_thm] >>
  fsrw_tac [][update_time_def,NOT_LESS] >>
  qabbrev_tac `b = SUC p.w ** n` >>
  qsuff_tac `b = 1 + (x * b + b - 1) MOD b` >- srw_tac [ARITH_ss][ADD1,LEFT_ADD_DISTRIB] >>
  `0 < b` by srw_tac [][Abbr`b`] >>
  `x * b + b - 1 = x * b + (b - 1)` by DECIDE_TAC >>
  fsrw_tac [][MOD_MULT] >>
  srw_tac [ARITH_ss][]) >>
srw_tac [][last_update_zero] >>
Cases_on `n` >> srw_tac [ARITH_ss][])

val last_update_mono = Q.store_thm(
"last_update_mono",
`x ≤ y ⇒ last_update p n x ≤ last_update p n y`,
Induct_on `y` >> srw_tac [][] >>
`(x = SUC y) \/ x <= y` by DECIDE_TAC >>
fsrw_tac [][] >> srw_tac [][last_update_def] >>
PROVE_TAC [last_update_upper_bound,LESS_EQ_TRANS]);

val last_update_lower_bound = Q.store_thm(
"last_update_lower_bound",
`u ≤ t ∧ update_time p n u ⇒ u ≤ last_update p n t`,
Induct_on `t` >> srw_tac [][] >>
srw_tac [][last_update_def] >>
Cases_on `u = SUC t` >> fsrw_tac [][] >>
`u ≤ t` by DECIDE_TAC >> fsrw_tac [][]);

val SR_prev = Q.store_thm(
"SR_prev",
`SR p n (SUC m) t = if t < n + (SUC p.w) ** n then 0 else SR p n m (t - (SUC p.w) ** n)`,
srw_tac [][Once SR_last_update] >- (
  imp_res_tac last_update_zero >>
  srw_tac [][Once SR_def] ) >>
fsrw_tac [][NOT_LESS] >>
imp_res_tac update_time_last_update >>
srw_tac [][Once SR_def] >>
fsrw_tac [][last_update_zero]
>- DECIDE_TAC >>
srw_tac [][source_def] >>
fsrw_tac [][NOT_LESS] >> srw_tac [][] >>
srw_tac [][Once SR_last_update,SimpLHS] >>
srw_tac [][Once SR_last_update,SimpRHS] >>
AP_TERM_TAC >>
srw_tac [][last_update_sub1] >- (
  srw_tac [][last_update_thm] >>
  fsrw_tac [ARITH_ss][NOT_LESS] >- (
    fsrw_tac [][update_time_def] >>
    qabbrev_tac `b = SUC p.w ** n` >>
    `n + SUC x * b <= t` by PROVE_TAC [last_update_upper_bound] >>
    `0 < b` by srw_tac [][Abbr`b`] >>
    `SUC x * b < 2 * b` by DECIDE_TAC >>
    Cases_on `x` >> fsrw_tac [ARITH_ss][ADD1] ) >>
  fsrw_tac [][update_time_def] >>
  qabbrev_tac `b = SUC p.w ** n` >>
  `0 < b` by srw_tac [][Abbr`b`] >>
  `t - (n + b) = (t - n) - b` by DECIDE_TAC >>
  `b <= t - n` by DECIDE_TAC >>
  fsrw_tac [][SUB_MOD] ) >>
srw_tac [][last_update_zero] >>
fsrw_tac [][NOT_LESS] >- (
  pop_assum mp_tac >>
  fsrw_tac [ARITH_ss][update_time_def,ADD1] >>
  srw_tac [][] >>
  `x = 0` by DECIDE_TAC >>
  srw_tac [][] >> fsrw_tac [][GSYM ADD1] >>
  spose_not_then strip_assume_tac >>
  fsrw_tac [][NOT_LESS] >>
  `update_time p n (n + 2 * SUC p.w ** n)` by srw_tac [][update_time_def] >>
  `n + 2 * SUC p.w ** n <= n + SUC p.w ** n` by PROVE_TAC [last_update_lower_bound] >>
  fsrw_tac [][] ) >>
Cases_on `n` >> srw_tac [ARITH_ss][])

val SR_first = Q.store_thm(
"SR_first",
`SR p n m t = if t ≤ m * SUC p.w ** n then 0 else SR p n 0 (t - (m * SUC p.w ** n))`,
qid_spec_tac `t` >>
Induct_on `m` >> fsrw_tac [][SR_prev]
>- (srw_tac [][] >> srw_tac [][Once SR_def]) >>
qabbrev_tac `b = SUC p.w ** n` >>
gen_tac >>
Cases_on `t < n + b` >- (
  srw_tac [][] >> fsrw_tac [ARITH_ss][NOT_LESS_EQUAL,ADD1] >>
  match_mp_tac (GSYM SR_0_until) >>
  srw_tac [ARITH_ss][] ) >>
Cases_on `t ≤ b + m * b` >-
  fsrw_tac [ARITH_ss][ADD1] >>
Cases_on `t ≤ SUC m * b` >- (
  fsrw_tac [ARITH_ss][NOT_LESS_EQUAL,NOT_LESS] >>
  match_mp_tac SR_0_until >>
  fsrw_tac [ARITH_ss][ADD1] ) >>
fsrw_tac [ARITH_ss][NOT_LESS_EQUAL,NOT_LESS,ADD1,LEFT_ADD_DISTRIB])

val output_last_update = Q.store_thm(
"output_last_update",
`output p n t = output p n (last_update p n t)`,
srw_tac [][Slice_def,Once SR_last_update])

val output_first = Q.store_thm(
"output_first",
`output p n t = SIGMA (λm. if t ≤ n + m * SUC p.w ** n then 0 else SR p n 0 (t - m * SUC p.w ** n)) (count (SUC p.w))`,
srw_tac [][Slice_def] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [][Once SR_first] >>
srw_tac [][Once SR_last_update] >- (
  match_mp_tac (GSYM SR_0_until) >>
  fsrw_tac [][NOT_LESS_EQUAL] >>
  full_simp_tac bool_ss [Once (SYM (SPEC_ALL SUB_EQ_0))] >>
  srw_tac [ARITH_ss][last_update_def] ) >>
match_mp_tac SR_0_until >>
fsrw_tac [][NOT_LESS_EQUAL] >>
match_mp_tac LESS_EQ_LESS_TRANS >>
qexists_tac `t - x * SUC p.w ** n` >>
srw_tac [ARITH_ss][last_update_upper_bound] >>
match_mp_tac LESS_EQ_LESS_TRANS >>
qexists_tac `n + x * SUC p.w ** n` >>
srw_tac [][])

val prev1_update_time = Q.store_thm(
"prev1_update_time",
`t ≠ n + SUC p.w ** n ∧ update_time p n t ⇒ update_time p n (t - SUC p.w ** n)`,
srw_tac [][update_time_def] >>
qabbrev_tac `w = SUC p.w ** n` >>
qabbrev_tac `a = SUC x` >>
`a > 0` by srw_tac [][Abbr`a`] >>
Cases_on `a = 1` >> fsrw_tac [][] >>
`a > 1` by DECIDE_TAC >>
`n + a * w - w = n + (a - 1) * w` by srw_tac [ARITH_ss][LEFT_SUB_DISTRIB,LESS_EQ_ADD_SUB] >>
fsrw_tac [][] >>
Cases_on `a-1` >> fsrw_tac [ARITH_ss][] >>
PROVE_TAC [])

val prev_update_time = Q.store_thm(
"prev_update_time",
`t > n + z * SUC p.w ** n ∧ update_time p n t ⇒ update_time p n (t - z * SUC p.w ** n)`,
Induct_on `z` >> srw_tac [][] >>
fsrw_tac [][] >>
qabbrev_tac `w = SUC p.w ** n` >>
srw_tac [][ADD1,RIGHT_ADD_DISTRIB,SUB_PLUS] >>
unabbrev_all_tac >>
match_mp_tac prev1_update_time >>
conj_tac >- (
  fsrw_tac [ARITH_ss][ADD1] ) >>
first_x_assum match_mp_tac >>
fsrw_tac [ARITH_ss][ADD1])

val output_source_at_update_times = Q.store_thm(
"output_source_at_update_times",
`update_time p n t ⇒ (output p n t = SIGMA (λm. if t ≤ n + m * SUC p.w ** n then 0 else source p n 0 (t - m * SUC p.w ** n - 1)) (count (SUC p.w)))`,
srw_tac [][output_first] >>
match_mp_tac SUM_IMAGE_CONG >>
srw_tac [ARITH_ss][Once SR_def] >>
fsrw_tac [][NOT_LESS_EQUAL,GSYM GREATER_DEF] >>
imp_res_tac prev_update_time)

val last_updates_eq = Q.store_thm(
"last_updates_eq",
`(if t ≤ n then k + t < n + SUC p.w ** n else k < SUC p.w ** n - (t - n) MOD SUC p.w ** n) ⇔
 (last_update p n (t + k) = last_update p n t)`,
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

val update_time_prev_slice = Q.store_thm(
"update_time_prev_slice",
`update_time p (SUC n) (SUC t) ⇒ update_time p n t`,
srw_tac [][update_time_def] >>
qabbrev_tac `w = SUC p.w` >>
qexists_tac `PRE (SUC x * w)` >>
fsrw_tac [ARITH_ss][EXP] >>
fsrw_tac [][GSYM SUC_ADD_SYM] >>
srw_tac [][ADD_SYM] >>
AP_THM_TAC >> AP_TERM_TAC >>
match_mp_tac EQ_SYM >>
srw_tac [ARITH_ss][Abbr`w`,MULT,SUC_PRE])

val update_time_slice_0 = Q.store_thm(
"update_time_slice_0",
`update_time p 0 t ⇔ (0 < t)`,
Cases_on `t` >> srw_tac [ARITH_ss][update_time_def,EQ_IMP_THM])

val output_input_at_update_times = Q.store_thm(
"output_input_at_update_times",
`update_time p n t ⇒
 (output p n t = SIGMA (λm. if t < m + SUC n then 0 else p.input (t - m - SUC n)) (count (SUC p.w ** SUC n)))`,
map_every qid_spec_tac [`t`,`n`] >>
Induct >- (
  fsrw_tac [][output_source_at_update_times] >>
  fsrw_tac [][update_time_slice_0,EXP,source_0_thm,GSYM ADD1,
              prim_recTheory.LESS_THM,LESS_OR_EQ,DISJ_SYM] ) >>
simp_tac bool_ss [output_source_at_update_times] >>
Cases >- ( srw_tac [][update_time_def] ) >>
strip_tac >>
qmatch_assum_rename_tac `update_time p (SUC n) (SUC t)` [] >>
fsrw_tac [ARITH_ss][source_def,GSYM ADD1] >>
qmatch_abbrev_tac `X = SIGMA f (count (SUC p.w ** SUC m))` >>
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

val _ = export_theory ()
