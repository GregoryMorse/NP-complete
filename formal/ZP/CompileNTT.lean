module

public import ZP.Compile
public import ZP.LogicNTT
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the P = NTT machine: the table simulates `znttLogic` gadget by gadget. -/

namespace ZP

def znttCert : Cert := ⟨znttLogic, znttMachine, znttEntry, znttSide, znttGlen⟩

theorem znttChk0 : Cert.allFrom 0 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk1 : Cert.allFrom 32 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk2 : Cert.allFrom 64 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk3 : Cert.allFrom 96 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk4 : Cert.allFrom 128 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk5 : Cert.allFrom 160 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk6 : Cert.allFrom 192 32 (Cert.checkQ znttCert) = true := by decide +kernel
theorem znttChk7 : Cert.allFrom 224 30 (Cert.checkQ znttCert) = true := by decide +kernel

theorem znttLogic_len : znttLogic.table.length = 254 := by decide +kernel

def znttBeepOK : Bool :=
  Cert.allFrom 0 254 fun q =>
    decide ((Cert.cEntry znttCert q = znttMachine.beep) ↔ (q = znttLogic.beep))

theorem znttBeepOK_true : znttBeepOK = true := by decide +kernel

theorem znttCert_ok : znttCert.OK where
  chk q hq := by
    have hq' : q < 254 := by
      have : znttCert.L.table.length = 254 := znttLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q znttChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q znttChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q znttChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q znttChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q znttChk4 (by omega) (by omega)
            · by_cases h5 : q < 192
              · exact Cert.allFrom_spec _ _ 160 q znttChk5 (by omega) (by omega)
              · by_cases h6 : q < 224
                · exact Cert.allFrom_spec _ _ 192 q znttChk6 (by omega) (by omega)
                · exact Cert.allFrom_spec _ _ 224 q znttChk7 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 254 := by
      have : znttCert.L.table.length = 254 := znttLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q znttBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `znttLogic` gives one by the table. -/
def znttMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C znttLogic) : MacroSimC C znttMachine :=
  Cert.macroSimC_of_logic znttCert znttCert_ok S

end ZP
