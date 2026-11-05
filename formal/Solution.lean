module

public import ZP

public section

/-!
# Proof

Comparator checks that this declaration has exactly the statement in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem ZP.zp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpMachine ↔ ZP.Sentence :=
  ZP.zp_quasihalts_iff_abstract.trans ZP.abstractQuasihalts_iff_sentence

theorem ZP.zpp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zppMachine ↔ ZP.SentencePP :=
  ZP.zppQuasihalts_iff_sentence

theorem ZP.zps_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpsMachine ↔ ZP.SentencePS :=
  ZP.zpsQuasihalts_iff_sentence

theorem ZP.zfac_quasihalts_iff_sentence : ZP.Quasihalts ZP.zfacMachine ↔ ZP.SentenceF :=
  ZP.zfacQuasihalts_iff_sentence

theorem ZP.zdl_quasihalts_iff_sentence : ZP.Quasihalts ZP.zdlMachine ↔ ZP.SentenceD :=
  ZP.zdlQuasihalts_iff_sentence
