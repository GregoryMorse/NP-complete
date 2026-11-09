module

public import ZP.Compile
public import ZP.LogicPP
public import ZP.TablePP

@[expose] public section

/-! The certificate of the P = PP machine: the table simulates `zppLogic` gadget by gadget. -/

namespace ZP

def zppCert : Cert := ⟨zppLogic, zppMachine, zppEntry, zppSide, zppGlen⟩

theorem zppChk0 : Cert.allFrom 0 32 (Cert.checkQ zppCert) = true := by decide +kernel
theorem zppChk1 : Cert.allFrom 32 32 (Cert.checkQ zppCert) = true := by decide +kernel
theorem zppChk2 : Cert.allFrom 64 32 (Cert.checkQ zppCert) = true := by decide +kernel
theorem zppChk3 : Cert.allFrom 96 32 (Cert.checkQ zppCert) = true := by decide +kernel
theorem zppChk4 : Cert.allFrom 128 10 (Cert.checkQ zppCert) = true := by decide +kernel

theorem zppLogic_len : zppLogic.table.length = 138 := by decide +kernel

def zppBeepOK : Bool :=
  Cert.allFrom 0 138 fun q =>
    decide ((Cert.cEntry zppCert q = zppMachine.beep) ↔ (q = zppLogic.beep))

theorem zppBeepOK_true : zppBeepOK = true := by decide +kernel

theorem zppCert_ok : zppCert.OK where
  chk q hq := by
    have hq' : q < 138 := by
      have : zppCert.L.table.length = 138 := zppLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zppChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zppChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zppChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zppChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zppChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 138 := by
      have : zppCert.L.table.length = 138 := zppLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zppBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zppLogic` gives one by the table. -/
def zppMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zppLogic) : MacroSimC C zppMachine :=
  Cert.macroSimC_of_logic zppCert zppCert_ok S

end ZP
