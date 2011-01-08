open Parse ppTools HolKernel simplifiedTheory
val _ = new_theory"pp"
val _ = add_rule exp_rule
val _ = add_user_printer sum_rule
val ors = let val m = mungeTools.read_overrides "overrides" in fn x => Binarymap.peek(m,x) end
val _ = write_thm_only ors ("SR First",SR_first)
val _ = write_thm_only ors ("SR Last Update",SR_last_update)
val _ = write_thm_only ors ("SR 0 Until",SR_0_until)
val _ = write_thm_only ors ("Sum In Chunks",sortingTheory.SUM_IMAGE_count_MULT)
val data = case
  LoadableThyData.segment_data {thy="simplified",thydataty=annotation.thydataty}
of SOME data => data | NONE => raise (Fail "segment_data failed")
val proofs = case annotation.decode_proofs data
of SOME proofs => proofs | NONE => raise Fail "decode_proofs failed"
val _ = List.app (write_proof ors) proofs
val _ = export_theory()
