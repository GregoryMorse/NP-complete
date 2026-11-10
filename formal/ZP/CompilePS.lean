module

public import ZP.Compile
public import ZP.LogicPS
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the P = PSPACE machine: the table simulates `zpsLogic` gadget by gadget. -/

namespace ZP

def zpsCert : Cert := ⟨zpsLogic, zpsMachine, zpsEntry, zpsSide, zpsGlen⟩

theorem zpsChk0 : Cert.allFrom 0 32 (Cert.checkQ zpsCert) = true := by decide +kernel
theorem zpsChk1 : Cert.allFrom 32 32 (Cert.checkQ zpsCert) = true := by decide +kernel
theorem zpsChk2 : Cert.allFrom 64 32 (Cert.checkQ zpsCert) = true := by decide +kernel
theorem zpsChk3 : Cert.allFrom 96 32 (Cert.checkQ zpsCert) = true := by decide +kernel
theorem zpsChk4 : Cert.allFrom 128 8 (Cert.checkQ zpsCert) = true := by decide +kernel

theorem zpsLogic_len : zpsLogic.table.length = 136 := by decide +kernel

def zpsBeepOK : Bool :=
  Cert.allFrom 0 136 fun q =>
    decide ((Cert.cEntry zpsCert q = zpsMachine.beep) ↔ (q = zpsLogic.beep))

theorem zpsBeepOK_true : zpsBeepOK = true := by decide +kernel

theorem zpsCert_ok : zpsCert.OK where
  chk q hq := by
    have hq' : q < 136 := by
      have : zpsCert.L.table.length = 136 := zpsLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zpsChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zpsChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zpsChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zpsChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zpsChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 136 := by
      have : zpsCert.L.table.length = 136 := zpsLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zpsBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zpsLogic` gives one by the table. -/
def zpsMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zpsLogic) : MacroSimC C zpsMachine :=
  Cert.macroSimC_of_logic zpsCert zpsCert_ok S

end ZP
