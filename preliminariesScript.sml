open HolKernel bossLib Parse

val _ = new_theory "preliminaries"

val _ = type_abbrev("time",``:num``)
val _ = type_abbrev("word",``:num->bool``)
val _ = type_abbrev("boolsig",``:time->bool``)
val _ = type_abbrev("wordsig",``:time->word``)

val NOTGate_def = Define`
  NOTGate (i,out) = (out = ¬i)`;

val ORGate_def = Define`
  ORGate (i1,i2,out) = (out = i1 ∨ i2)`;

val ANDGate_def = Define`
  ANDGate (i1,i2,out) = (out = i1 ∧ i2)`;

val XORGate_def = Define`
  XORGate (i1,i2,out) = (out = (i1 ∧ ¬i2) ∨ (¬i1 ∧ i2))`;

val _ = export_theory ()
