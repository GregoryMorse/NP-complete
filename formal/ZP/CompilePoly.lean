module

public import ZP.Compile
public import ZP.LogicPoly
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the Z_PPOLY machine: the table simulates `zppolyLogic` gadget by gadget. -/

namespace ZP

def zppolyCert : Cert := ⟨zppolyLogic, zppolyMachine, zppolyEntry, zppolySide, zppolyGlen⟩

theorem zppolyChk0 : Cert.allFrom 0 32 (Cert.checkQ zppolyCert) = true := by decide +kernel
theorem zppolyChk1 : Cert.allFrom 32 32 (Cert.checkQ zppolyCert) = true := by decide +kernel
theorem zppolyChk2 : Cert.allFrom 64 32 (Cert.checkQ zppolyCert) = true := by decide +kernel
theorem zppolyChk3 : Cert.allFrom 96 32 (Cert.checkQ zppolyCert) = true := by decide +kernel
theorem zppolyChk4 : Cert.allFrom 128 26 (Cert.checkQ zppolyCert) = true := by decide +kernel

theorem zppolyLogic_len : zppolyLogic.table.length = 154 := by decide +kernel

def zppolyBeepOK : Bool :=
  Cert.allFrom 0 154 fun q =>
    decide ((Cert.cEntry zppolyCert q = zppolyMachine.beep) ↔ (q = zppolyLogic.beep))

theorem zppolyBeepOK_true : zppolyBeepOK = true := by decide +kernel

theorem zppolyCert_ok : zppolyCert.OK where
  chk q hq := by
    have hq' : q < 154 := by
      have : zppolyCert.L.table.length = 154 := zppolyLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zppolyChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zppolyChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zppolyChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zppolyChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zppolyChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 154 := by
      have : zppolyCert.L.table.length = 154 := zppolyLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zppolyBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zppolyLogic` gives one by the table. -/
def zppolyMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zppolyLogic) : MacroSimC C zppolyMachine :=
  Cert.macroSimC_of_logic zppolyCert zppolyCert_ok S

end ZP
