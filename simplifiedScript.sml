open HolKernel boolLib boolSimps bossLib arithmeticTheory pred_setTheory lcsymtacs

val _ = new_theory "simplified"

(* Global Parameters:
     the width of every slice, encoded as the index, w, of the last shift register
     the input series, input.
   Each slice has
     w+1 shift registers, named SR 0, SR 1, ..., SR w;
     an output register.
   Each SR has a source:
     The source for SR 0 of slice 0 is the global input.
     The source for SR 0 of slice (SUC n) is the output of slice n.
     The source for SR (SUC m) is SR m of the same slice.
   Each slice updates periodically:
     Slice n updates at time t iff ∃x. n + ((SUC x) * ((SUC w) ** n))
   At time 0, all shift registers have value 0.
   At each update time for its slice, a SR gets the value of its source at the previous time.
   The output of a slice at some time is the sum of its shift registers at the same time. *)

val _ = Hol_datatype`
  parameters = <| w : num ; input : num -> num |>`;

(* update_time p n t <=> t is an update time for slice n *)
val update_time_def = Define`
  update_time p n t = ∃x. t = n + ((SUC x) * ((SUC p.w) ** n))`;

(* source p n m = the source of input for SR m of slice n *)
(* output p n t = the output of slice n at time t *)
(* SR p n m t = the value of SR m of slice n at time t *)
val Slice_def = tDefine "Slice" `
  (source p 0 0 t = p.input t) ∧
  (source p (SUC n) 0 t = output p n t) ∧
  (source p n (SUC m) t = SR p n m t) ∧
  (output p n t = SIGMA (λm. SR p n m t) (count (SUC p.w))) ∧
  (SR p n m 0 = 0) ∧
  (SR p n m (SUC t) = if update_time p n (SUC t)
                      then source p n m t else SR p n m t)`
(WF_REL_TAC
`inv_image ($< LEX $< LEX $< LEX $<)
 (λx. case x of
      (INL (p,n,m,t)) -> (n,m,t,1) ||
      (INR (INR (p,n,m,t))) -> (n,m,t,2) ||
      (INR (INL (p,n,t))) -> (n,(SUC p.w),t,3))` >>
srw_tac [][IN_COUNT]);

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

val MOD_SUC = Q.store_thm(
"MOD_SUC",
`0 < y /\ (SUC x <> (SUC (x DIV y)) * y) ==> ((SUC x) MOD y = SUC (x MOD y))`,
STRIP_TAC THEN
MATCH_MP_TAC MOD_UNIQUE THEN
Q.EXISTS_TAC `x DIV y` THEN
`x = x DIV y * y + x MOD y` by PROVE_TAC [DIVISION] THEN
`x MOD y < y` by PROVE_TAC [MOD_LESS] THEN
FULL_SIMP_TAC arith_ss [ADD1])

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

local open sortingTheory in
val sanity = Q.prove(
`(p.width = 4) /\
 (p.input 0 = 3) /\
 (p.input 1 = 7) /\
 (p.input 2 = 1) /\
 (p.input 3 = 3) /\
 (p.input 4 = 6) /\
 (p.input 5 = 5) /\
 (p.input 6 = 0) /\
 (p.input 7 = 9) /\
 (p.input 8 = 8) /\
 (p.input 9 = 4) /\
 (p.input 10 = 6) /\
 (p.input 11 = 8) /\
 (p.input 12 = 5) /\
 (p.input 13 = 2) /\
 (p.input 14 = 5) /\
 (p.input 15 = 1) /\
 (p.input 16 = 1) /\
 (p.input 17 = 6) ==>
 (SR p 1 2 17 = 20)`,
srw_tac [ARITH_ss][Slice_def,Once SR_def,update_time_def] >>
srw_tac [ARITH_ss][source_def] >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 3 /\ x > 2` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 3 /\ x > 2` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 3 /\ x > 2` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >>
srw_tac [][source_def] >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 2 /\ x > 1` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 2 /\ x > 1` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >-
(`x < 2 /\ x > 1` by DECIDE_TAC >> DECIDE_TAC) >>
srw_tac [ARITH_ss][Once SR_def,update_time_def] >>
srw_tac [][source_def] >>
srw_tac [][Slice_def] >>
srw_tac [][SUM_IMAGE_count_SUM_GENLIST] >>
ntac 4 (srw_tac [ARITH_ss][Once SR_def,update_time_def]) >>
srw_tac [][source_def] >>
ntac 3 (srw_tac [ARITH_ss][Once SR_def,update_time_def]) >>
srw_tac [][source_def] >>
ntac 2 (srw_tac [ARITH_ss][Once SR_def,update_time_def]) >>
srw_tac [][source_def] >>
ntac 1 (srw_tac [ARITH_ss][Once SR_def,update_time_def]) >>
srw_tac [][source_def])
end

val _ = export_theory ()
