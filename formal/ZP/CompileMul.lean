module

public import ZP.Compile
public import ZP.LogicMul
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the multiplication machine: the table simulates `zmulLogic` gadget by gadget. -/

namespace ZP

def zmulCert : Cert := ⟨zmulLogic, zmulMachine, zmulEntry, zmulSide, zmulGlen⟩

theorem zmulChk0 : Cert.allFrom 0 32 (Cert.checkQ zmulCert) = true := by decide +kernel
theorem zmulChk1 : Cert.allFrom 32 32 (Cert.checkQ zmulCert) = true := by decide +kernel
theorem zmulChk2 : Cert.allFrom 64 32 (Cert.checkQ zmulCert) = true := by decide +kernel
theorem zmulChk3 : Cert.allFrom 96 32 (Cert.checkQ zmulCert) = true := by decide +kernel
theorem zmulChk4 : Cert.allFrom 128 32 (Cert.checkQ zmulCert) = true := by decide +kernel
theorem zmulChk5 : Cert.allFrom 160 31 (Cert.checkQ zmulCert) = true := by decide +kernel

theorem zmulLogic_len : zmulLogic.table.length = 191 := by decide +kernel

def zmulBeepOK : Bool :=
  Cert.allFrom 0 191 fun q =>
    decide ((Cert.cEntry zmulCert q = zmulMachine.beep) ↔ (q = zmulLogic.beep))

theorem zmulBeepOK_true : zmulBeepOK = true := by decide +kernel

theorem zmulCert_ok : zmulCert.OK where
  chk q hq := by
    have hq' : q < 191 := by
      have : zmulCert.L.table.length = 191 := zmulLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zmulChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zmulChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zmulChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zmulChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zmulChk4 (by omega) (by omega)
            · exact Cert.allFrom_spec _ _ 160 q zmulChk5 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 191 := by
      have : zmulCert.L.table.length = 191 := zmulLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zmulBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zmulLogic` gives one by the table. -/
def zmulMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zmulLogic) : MacroSimC C zmulMachine :=
  Cert.macroSimC_of_logic zmulCert zmulCert_ok S

end ZP
