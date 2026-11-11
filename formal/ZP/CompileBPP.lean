module

public import ZP.Compile
public import ZP.LogicBPP
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the promise-BPP machine: the table simulates `zbppLogic` gadget by gadget. -/

namespace ZP

def zbppCert : Cert := ⟨zbppLogic, zbppMachine, zbppEntry, zbppSide, zbppGlen⟩

theorem zbppChk0 : Cert.allFrom 0 32 (Cert.checkQ zbppCert) = true := by decide +kernel
theorem zbppChk1 : Cert.allFrom 32 32 (Cert.checkQ zbppCert) = true := by decide +kernel
theorem zbppChk2 : Cert.allFrom 64 32 (Cert.checkQ zbppCert) = true := by decide +kernel
theorem zbppChk3 : Cert.allFrom 96 32 (Cert.checkQ zbppCert) = true := by decide +kernel
theorem zbppChk4 : Cert.allFrom 128 24 (Cert.checkQ zbppCert) = true := by decide +kernel

theorem zbppLogic_len : zbppLogic.table.length = 152 := by decide +kernel

def zbppBeepOK : Bool :=
  Cert.allFrom 0 152 fun q =>
    decide ((Cert.cEntry zbppCert q = zbppMachine.beep) ↔ (q = zbppLogic.beep))

theorem zbppBeepOK_true : zbppBeepOK = true := by decide +kernel

theorem zbppCert_ok : zbppCert.OK where
  chk q hq := by
    have hq' : q < 152 := by
      have : zbppCert.L.table.length = 152 := zbppLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zbppChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zbppChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zbppChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zbppChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zbppChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 152 := by
      have : zbppCert.L.table.length = 152 := zbppLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zbppBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zbppLogic` gives one by the table. -/
def zbppMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zbppLogic) : MacroSimC C zbppMachine :=
  Cert.macroSimC_of_logic zbppCert zbppCert_ok S

end ZP
