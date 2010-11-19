open HolKernel bossLib Parse preliminariesTheory

val _ = new_theory "design"

val _ = overload_on("tapDistance",``8``)

val altshift_taps_def = Define`
  altshift_taps n (clken:boolsig,shiftin:wordsig,tap1x:wordsig,tap0x:wordsig) t =
  ∃regs. (∀i. i < n ⇒ (tap1x t i = regs t ((2 * tapDistance) - 1) i)) ∧
         (* shifted parentheses *)
         (∀i. i < n ⇒ (tap0x t i = regs t ((1 * tapDistance) - 1) i)) ∧
         (* shifted parentheses *)
         if ¬(clken t) then regs (t+1) = regs t else
         (* passed t to clken *)
         ∀i. i < n ⇒ ((regs (t+1) 0 i = shiftin t i) ∧
                      (∀j. ((0 < j) ∧ (j < (2 * tapDistance))) ⇒
                             regs (t+1) j i = regs t (j-1) i))`;

val HalfSubtractor_def = Define`
  HalfSubtractor (x,y,d,b) =
    ∃a. XORGate (x,y,d) ∧ NOTGate (x,a) ∧ ANDGate (y,a,b)`;

val FullSubtractor_def = Define`
  FullSubtractor (a,b,bin,d,bout) =
    ∃x y z. HalfSubtractor (a,b,x,y) ∧
            HalfSubtractor (bin,x,d,z) ∧
            ORGate (z,y,bout)`;

val FullSubtractorN_def = Define`
  FullSubtractorN n (x,y,d,bout) =
    if n = 0 then bout = F else
    ∃a. FullSubtractorN (n-1) (x,y,d,a) ∧
        FullSubtractor ((x (n-1)),(y (n-1)),a,(d (n-1)),bout)`;

val A_minus_B_def = Define`
  A_minus_B n (dataa:wordsig,datab:wordsig,result:wordsig) t =
   ∃unused. FullSubtractorN n (dataa t,datab t,result t,unused)`;

val HalfAdder_def = Define`
  HalfAdder (a,b,s,c) = XORGate (a,b,s) ∧ ANDGate (a,b,c)`;

val FullAdder_def = Define`
  FullAdder (a,b,cin,s,cout) =
    ∃s1 c1 c2. HalfSubtractor (a,b,s1,c1) ∧
               HalfSubtractor (cin,s1,s,c2) ∧
               ORGate (c1,c2,cout)`;

val FullAdderN_def = Define`
  FullAdderN n (a,b,s,cout) =
    if n = 0 then cout = F else
    ∃x. FullAdderN (n-1) (a,b,s,x) ∧
        FullSubtractor ((a (n-1)),(b (n-1)),x,(s (n-1)),cout)`;

val acc_def = Define`
  acc n (clken:boolsig,data:wordsig,result:wordsig) t =
    ∀i. i < n ⇒
      if ¬(clken t) then result (t+1) = result t else
      (* passed t to clken *)
      FullAdderN n (data t, result t, result (t+1), result (t+1) n)`;

val SRS_def = Define`
  SRS n (clken:boolsig,shiftin:wordsig,RSlower:wordsig,RSupper:wordsig) t =
  (* added t to arguments, and passed it along to all calls below *)
    ∃data1x taps1x taps0x accin1x accin0x.
    (* existentially quantified data1x *)
      altshift_taps n (clken,data1x,taps1x,taps0x) t ∧
      A_minus_B n (data1x,taps1x,accin1x) t ∧
      A_minus_B n (data1x,taps0x,accin0x) t ∧
      acc n (clken,accin1x,RSupper) t ∧
      acc n (clken,accin0x,RSlower) t`;

val SRDelay_def = Define`
  SRDelay m clken t = (clken t = ∃q. t = ((q+1) * (pwr (2,m) * tapDistance)))`

val RSDesign_def = Define`
  RSDesign (datain, RSum00, RSum01, RSum02, RSum03, RSum04, RSum05,
                    RSum06, RSum07, RSum08, RSum09, RSum10, RSum11) =
  ∃shiftin clken1 clken2 clken3 clken4 clken5 tmp.
  (* added existentially quantified shiftin *)
  ∀t.
    (∀i. i < 20 ⇒ (RSum00 i = datain t)) ∧
    (* removed t argument from RSum00 *)
    (* added t argument to datain *)
    (∀i. i < 20 ⇒ (tmp (t+1) = datain t)) ∧
    (* change I to i, changed and to AND *)
    (FullAdderN 21 (datain t, tmp t, RSum01 t, RSum01 t 21)) ∧
    (* added parenthesis, changed RSSum01 to RSum01 t *)
    SRDelay 1 clken1 t ∧
    SRS 22 (clken1,shiftin,RSum02,RSum03) t ∧
    SRDelay 2 clken2 t ∧
    SRS 26 (clken2,RSum03,RSum04,RSum05) t ∧
    SRDelay 3 clken3 t ∧
    SRS 32 (clken3,RSum05,RSum06,RSum07) t ∧
    SRDelay 4 clken4 t ∧
    SRS 36 (clken4,RSum07,RSum08,RSum09) t ∧
    SRDelay 5 clken5 t ∧
    SRS 40 (clken5,RSum09,RSum10,RSum11) t
    (* added clken argument to each SRS above *)
    (* added t argument to all the above *)`

val _ = export_theory()
