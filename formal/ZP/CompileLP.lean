module

public import ZP.Compile
public import ZP.LogicLP
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the L = P machine: the table simulates `zlpLogic` gadget by gadget. -/

namespace ZP

def zlpCert : Cert := ⟨zlpLogic, zlpMachine, zlpEntry, zlpSide, zlpGlen⟩

theorem zlpChk0 : Cert.allFrom 0 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk1 : Cert.allFrom 32 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk2 : Cert.allFrom 64 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk3 : Cert.allFrom 96 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk4 : Cert.allFrom 128 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk5 : Cert.allFrom 160 32 (Cert.checkQ zlpCert) = true := by decide +kernel
theorem zlpChk6 : Cert.allFrom 192 21 (Cert.checkQ zlpCert) = true := by decide +kernel

theorem zlpLogic_len : zlpLogic.table.length = 213 := by decide +kernel

def zlpBeepOK : Bool :=
  Cert.allFrom 0 213 fun q =>
    decide ((Cert.cEntry zlpCert q = zlpMachine.beep) ↔ (q = zlpLogic.beep))

theorem zlpBeepOK_true : zlpBeepOK = true := by decide +kernel

theorem zlpCert_ok : zlpCert.OK where
  chk q hq := by
    have hq' : q < 213 := by
      have : zlpCert.L.table.length = 213 := zlpLogic_len
      omega
    by_cases h0 : q < 32
    · exact Cert.allFrom_spec _ _ 0 q zlpChk0 (by omega) (by omega)
    · by_cases h1 : q < 64
      · exact Cert.allFrom_spec _ _ 32 q zlpChk1 (by omega) (by omega)
      · by_cases h2 : q < 96
        · exact Cert.allFrom_spec _ _ 64 q zlpChk2 (by omega) (by omega)
        · by_cases h3 : q < 128
          · exact Cert.allFrom_spec _ _ 96 q zlpChk3 (by omega) (by omega)
          · by_cases h4 : q < 160
            · exact Cert.allFrom_spec _ _ 128 q zlpChk4 (by omega) (by omega)
            · by_cases h5 : q < 192
              · exact Cert.allFrom_spec _ _ 160 q zlpChk5 (by omega) (by omega)
              · exact Cert.allFrom_spec _ _ 192 q zlpChk6 (by omega) (by omega)
  beep q hq := by
    have hq' : q < 213 := by
      have : zlpCert.L.table.length = 213 := zlpLogic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q zlpBeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `zlpLogic` gives one by the table. -/
def zlpMacroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C zlpLogic) : MacroSimC C zlpMachine :=
  Cert.macroSimC_of_logic zlpCert zlpCert_ok S

end ZP
