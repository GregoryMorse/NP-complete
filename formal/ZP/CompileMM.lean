module

public import ZP.Compile
public import ZP.LogicMM
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the GF(2) matrix product machine: the table simulates `zmmLogic` gadget by gadget. -/

namespace ZP

def zmmCert : Cert := ⟨zmmLogic, zmmMachine, zmmEntry, zmmSide, zmmGlen⟩

theorem zmmChk0 : Cert.allFrom 0 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk1 : Cert.allFrom 32 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk2 : Cert.allFrom 64 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk3 : Cert.allFrom 96 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk4 : Cert.allFrom 128 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk5 : Cert.allFrom 160 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk6 : Cert.allFrom 192 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk7 : Cert.allFrom 224 32 (Cert.checkQ zmmCert) = true := by decide +kernel
theorem zmmChk8 : Cert.allFrom 256 4 (Cert.checkQ zmmCert) = true := by decide +kernel

theorem zmmLogic_len : zmmLogic.table.length = 260 := by decide +kernel

def zmmBeepOK : Bool :=
  Cert.allFrom 0 260 fun q =>
    decide ((Cert.cEntry zmmCert q = zmmMachine.beep) ↔ (q = zmmLogic.beep))

theorem zmmBeepOK_true : zmmBeepOK = true := by decide +kernel

theorem zmmCert_ok : zmmCert.OK where
  chk q hq := by
    have hq' : q < 260 := by
      have : zmmCert.L.table.length = 260 := zmmLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zmmChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zmmChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zmmChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zmmChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zmmChk4 (by omega) (by omega)
            · by_cases h5 : q < 192
              · exact Cert.allFrom_spec _ _ 160 q zmmChk5 (by omega) (by omega)
              · by_cases h6 : q < 224
                · exact Cert.allFrom_spec _ _ 192 q zmmChk6 (by omega) (by omega)
                · by_cases h7 : q < 256
                  · exact Cert.allFrom_spec _ _ 224 q zmmChk7 (by omega) (by omega)
                  · exact Cert.allFrom_spec _ _ 256 q zmmChk8 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 260 := by
      have : zmmCert.L.table.length = 260 := zmmLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zmmBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zmmLogic` gives one by the table. -/
def zmmMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zmmLogic) : MacroSimC C zmmMachine :=
  Cert.macroSimC_of_logic zmmCert zmmCert_ok S

end ZP
