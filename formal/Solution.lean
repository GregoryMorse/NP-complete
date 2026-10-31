module

public import ZP

public section

/-!
# Proof

Comparator checks that this declaration has exactly the statement in
`Challenge.lean` and uses only the permitted axioms. It currently depends on the
open bridge `ZP.zp_quasihalts_iff_abstract` (`ZP/Bridge.lean`).
-/

theorem ZP.zp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpMachine ↔ ZP.Sentence :=
  ZP.zp_quasihalts_iff_abstract.trans ZP.abstractQuasihalts_iff_sentence
