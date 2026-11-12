module

public import ZP.Compile
public import ZP.LogicLNL
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the Z_LNL machine: the table simulates `zlnlLogic` gadget by gadget. -/

namespace ZP

def zlnlCert : Cert := ⟨zlnlLogic, zlnlMachine, zlnlEntry, zlnlSide, zlnlGlen⟩

theorem zlnlChk0 : Cert.allFrom 0 32 (Cert.checkQ zlnlCert) = true := by decide +kernel
theorem zlnlChk1 : Cert.allFrom 32 32 (Cert.checkQ zlnlCert) = true := by decide +kernel
theorem zlnlChk2 : Cert.allFrom 64 32 (Cert.checkQ zlnlCert) = true := by decide +kernel
theorem zlnlChk3 : Cert.allFrom 96 32 (Cert.checkQ zlnlCert) = true := by decide +kernel
theorem zlnlChk4 : Cert.allFrom 128 32 (Cert.checkQ zlnlCert) = true := by decide +kernel
theorem zlnlChk5 : Cert.allFrom 160 28 (Cert.checkQ zlnlCert) = true := by decide +kernel

theorem zlnlLogic_len : zlnlLogic.table.length = 188 := by decide +kernel

def zlnlBeepOK : Bool :=
  Cert.allFrom 0 188 fun q =>
    decide ((Cert.cEntry zlnlCert q = zlnlMachine.beep) ↔ (q = zlnlLogic.beep))

theorem zlnlBeepOK_true : zlnlBeepOK = true := by decide +kernel

theorem zlnlCert_ok : zlnlCert.OK where
  chk q hq := by
    have hq' : q < 188 := by
      have : zlnlCert.L.table.length = 188 := zlnlLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zlnlChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zlnlChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zlnlChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zlnlChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zlnlChk4 (by omega) (by omega)
            · exact Cert.allFrom_spec _ _ 160 q zlnlChk5 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 188 := by
      have : zlnlCert.L.table.length = 188 := zlnlLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zlnlBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zlnlLogic` gives one by the table. -/
def zlnlMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zlnlLogic) : MacroSimC C zlnlMachine :=
  Cert.macroSimC_of_logic zlnlCert zlnlCert_ok S

end ZP
