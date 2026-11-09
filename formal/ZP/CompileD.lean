module

public import ZP.Compile
public import ZP.LogicD
public import ZP.TableD

@[expose] public section

/-! The certificate of the P = DLOG machine: the table simulates `zdlLogic` gadget by gadget. -/

namespace ZP

def zdlCert : Cert := ⟨zdlLogic, zdlMachine, zdlEntry, zdlSide, zdlGlen⟩

theorem zdlChk0 : Cert.allFrom 0 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk1 : Cert.allFrom 32 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk2 : Cert.allFrom 64 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk3 : Cert.allFrom 96 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk4 : Cert.allFrom 128 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk5 : Cert.allFrom 160 32 (Cert.checkQ zdlCert) = true := by decide +kernel
theorem zdlChk6 : Cert.allFrom 192 19 (Cert.checkQ zdlCert) = true := by decide +kernel

theorem zdlLogic_len : zdlLogic.table.length = 211 := by decide +kernel

def zdlBeepOK : Bool :=
  Cert.allFrom 0 211 fun q =>
    decide ((Cert.cEntry zdlCert q = zdlMachine.beep) ↔ (q = zdlLogic.beep))

theorem zdlBeepOK_true : zdlBeepOK = true := by decide +kernel

theorem zdlCert_ok : zdlCert.OK where
  chk q hq := by
    have hq' : q < 211 := by
      have : zdlCert.L.table.length = 211 := zdlLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zdlChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zdlChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zdlChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zdlChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zdlChk4 (by omega) (by omega)
            · by_cases h5 : q < 192
              · exact Cert.allFrom_spec _ _ 160 q zdlChk5 (by omega) (by omega)
              · exact Cert.allFrom_spec _ _ 192 q zdlChk6 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 211 := by
      have : zdlCert.L.table.length = 211 := zdlLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zdlBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zdlLogic` gives one by the table. -/
def zdlMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zdlLogic) : MacroSimC C zdlMachine :=
  Cert.macroSimC_of_logic zdlCert zdlCert_ok S

end ZP
