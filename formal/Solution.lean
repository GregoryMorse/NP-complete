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

theorem ZP.zgi_quasihalts_iff_sentence : ZP.Quasihalts ZP.zgiMachine ↔ ZP.SentenceG :=
  ZP.zgiQuasihalts_iff_sentence

theorem ZP.zntt_quasihalts_iff_sentence :
    ZP.Quasihalts ZP.znttMachine ↔ ZP.SentenceN ZP.primeN :=
  ZP.NTT.znttQuasihalts_iff_sentence

theorem ZP.zconp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zconpMachine ↔ ZP.SentenceConp :=
  ZP.zconpQuasihalts_iff_sentence

theorem ZP.twin_quasihalts_iff : ZP.Quasihalts ZP.twinMachine ↔ ¬ ZP.TwinPrimes :=
  ZP.twinQuasihalts_iff

theorem ZP.zbpp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zbppMachine ↔ ZP.SentenceBPP :=
  ZP.zbppQuasihalts_iff_sentence

theorem ZP.zppoly_quasihalts_iff_sentence : ZP.Quasihalts ZP.zppolyMachine ↔ ZP.SentencePoly :=
  ZP.zppolyQuasihalts_iff_sentence

theorem ZP.zmm_quasihalts_iff_sentence : ZP.Quasihalts ZP.zmmMachine ↔ ZP.SentenceMM :=
  ZP.zmmQuasihalts_iff_sentence

theorem ZP.zlp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zlpMachine ↔ ZP.SentenceLP :=
  ZP.zlpQuasihalts_iff_sentence

theorem ZP.zlnl_quasihalts_iff_sentence : ZP.Quasihalts ZP.zlnlMachine ↔ ZP.SentenceLNL :=
  ZP.zlnlQuasihalts_iff_sentence
