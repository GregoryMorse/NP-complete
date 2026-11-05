module

public import ZP.Compile
public import ZP.LogicG
public import ZP.TableG

@[expose] public section

/-! The certificate of the P = GI machine: the table simulates `zgiLogic` gadget by gadget. -/

namespace ZP

def zgiCert : Cert := ⟨zgiLogic, zgiMachine, zgiEntry, zgiSide, zgiGlen⟩

theorem zgiChk0 : Cert.allFrom 0 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk1 : Cert.allFrom 32 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk2 : Cert.allFrom 64 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk3 : Cert.allFrom 96 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk4 : Cert.allFrom 128 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk5 : Cert.allFrom 160 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk6 : Cert.allFrom 192 32 (Cert.checkQ zgiCert) = true := by decide +kernel
theorem zgiChk7 : Cert.allFrom 224 5 (Cert.checkQ zgiCert) = true := by decide +kernel

theorem zgiLogic_len : zgiLogic.table.length = 229 := by decide +kernel

def zgiBeepOK : Bool :=
  Cert.allFrom 0 229 fun q =>
    decide ((Cert.cEntry zgiCert q = zgiMachine.beep) ↔ (q = zgiLogic.beep))

theorem zgiBeepOK_true : zgiBeepOK = true := by decide +kernel

theorem zgiCert_ok : zgiCert.OK where
  chk q hq := by
    have hq' : q < 229 := by
      have : zgiCert.L.table.length = 229 := zgiLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zgiChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zgiChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zgiChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zgiChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zgiChk4 (by omega) (by omega)
            · by_cases h5 : q < 192
              · exact Cert.allFrom_spec _ _ 160 q zgiChk5 (by omega) (by omega)
              · by_cases h6 : q < 224
                · exact Cert.allFrom_spec _ _ 192 q zgiChk6 (by omega) (by omega)
                · exact Cert.allFrom_spec _ _ 224 q zgiChk7 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 229 := by
      have : zgiCert.L.table.length = 229 := zgiLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zgiBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zgiLogic` gives one by the table. -/
def zgiMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zgiLogic) : MacroSimC C zgiMachine :=
  Cert.macroSimC_of_logic zgiCert zgiCert_ok S

end ZP
