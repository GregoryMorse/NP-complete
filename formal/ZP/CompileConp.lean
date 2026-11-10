module

public import ZP.Compile
public import ZP.LogicConp
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the NP = coNP machine: the table simulates `zconpLogic` gadget by gadget. -/

namespace ZP

def zconpCert : Cert := ⟨zconpLogic, zconpMachine, zconpEntry, zconpSide, zconpGlen⟩

theorem zconpChk0 : Cert.allFrom 0 32 (Cert.checkQ zconpCert) = true := by decide +kernel
theorem zconpChk1 : Cert.allFrom 32 32 (Cert.checkQ zconpCert) = true := by decide +kernel
theorem zconpChk2 : Cert.allFrom 64 32 (Cert.checkQ zconpCert) = true := by decide +kernel
theorem zconpChk3 : Cert.allFrom 96 32 (Cert.checkQ zconpCert) = true := by decide +kernel
theorem zconpChk4 : Cert.allFrom 128 23 (Cert.checkQ zconpCert) = true := by decide +kernel

theorem zconpLogic_len : zconpLogic.table.length = 151 := by decide +kernel

def zconpBeepOK : Bool :=
  Cert.allFrom 0 151 fun q =>
    decide ((Cert.cEntry zconpCert q = zconpMachine.beep) ↔ (q = zconpLogic.beep))

theorem zconpBeepOK_true : zconpBeepOK = true := by decide +kernel

theorem zconpCert_ok : zconpCert.OK where
  chk q hq := by
    have hq' : q < 151 := by
      have : zconpCert.L.table.length = 151 := zconpLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zconpChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zconpChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zconpChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zconpChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zconpChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 151 := by
      have : zconpCert.L.table.length = 151 := zconpLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zconpBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zconpLogic` gives one by the table. -/
def zconpMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zconpLogic) : MacroSimC C zconpMachine :=
  Cert.macroSimC_of_logic zconpCert zconpCert_ok S

end ZP
