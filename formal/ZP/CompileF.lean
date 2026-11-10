module

public import ZP.Compile
public import ZP.LogicF
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the P = FACTOR machine: the table simulates `zfacLogic` gadget by gadget. -/

namespace ZP

def zfacCert : Cert := ⟨zfacLogic, zfacMachine, zfacEntry, zfacSide, zfacGlen⟩

theorem zfacChk0 : Cert.allFrom 0 32 (Cert.checkQ zfacCert) = true := by decide +kernel
theorem zfacChk1 : Cert.allFrom 32 32 (Cert.checkQ zfacCert) = true := by decide +kernel
theorem zfacChk2 : Cert.allFrom 64 32 (Cert.checkQ zfacCert) = true := by decide +kernel
theorem zfacChk3 : Cert.allFrom 96 32 (Cert.checkQ zfacCert) = true := by decide +kernel
theorem zfacChk4 : Cert.allFrom 128 32 (Cert.checkQ zfacCert) = true := by decide +kernel

theorem zfacLogic_len : zfacLogic.table.length = 160 := by decide +kernel

def zfacBeepOK : Bool :=
  Cert.allFrom 0 160 fun q =>
    decide ((Cert.cEntry zfacCert q = zfacMachine.beep) ↔ (q = zfacLogic.beep))

theorem zfacBeepOK_true : zfacBeepOK = true := by decide +kernel

theorem zfacCert_ok : zfacCert.OK where
  chk q hq := by
    have hq' : q < 160 := by
      have : zfacCert.L.table.length = 160 := zfacLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zfacChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zfacChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zfacChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zfacChk3 (by omega) (by omega)
          · exact Cert.allFrom_spec _ _ 128 q zfacChk4 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 160 := by
      have : zfacCert.L.table.length = 160 := zfacLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zfacBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zfacLogic` gives one by the table. -/
def zfacMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zfacLogic) : MacroSimC C zfacMachine :=
  Cert.macroSimC_of_logic zfacCert zfacCert_ok S

end ZP
