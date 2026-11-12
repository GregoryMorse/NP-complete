module

public import ZP.PairLPV
public import ZP.CompileLP
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The L = P machine quasihalts iff `SentenceLP`
-/

namespace ZP.MH

open ZP

theorem pair_mainLP (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectLP J S → zlpLogic.zrun n (lay J S) = some (lay (absStepC CorrectLP (J, S)).1 (absStepC CorrectLP (J, S)).2)) ∧
       (¬ CorrectLP J S → ∃ a c1 c2, a < n ∧ zlpLogic.zrun a (lay J S) = some c1 ∧ c1.q = zlpLogic.beep ∧
          zlpLogic.zstep c1 = some c2 ∧
          zlpLogic.zrun (n - a - 1) c2 = some (lay (absStepC CorrectLP (J, S)).1 (absStepC CorrectLP (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have hA0 := vStartLP J S
  have hV := verPhase (str S) (bitsOf (str J)) hj
  have ht : ∀ a ∈ tflag (inLP (str S)), a ∈ T3 := by cases inLP (str S) <;> simp [tflag, T3]
  obtain ⟨Fu, hEr, hFu, hD⟩ := dPhaseLP (str J) (str S) (tflag (inLP (str S))) ht
  have hA := hA0.trans (hV.trans hD)
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectLP J S
  · have e : absStepC CorrectLP (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : runMH (str J) (str S) (clock (str J) (str S)) = inLP (str S) := hc
    rw [ho] at hA
    have hok : zlpLogic.Reach
        (hdR (dpOf (bn (inLP (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: 1 :: (tflag (inLP (str S)) ++ 1 :: Fu))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inLP (str S)
      · exact ((dOk0 _ _ Fu hj hs hFu).ofEq (by simp [dpOf, bn, tflag]) rfl).trans
          (eraseOk _ _ _ hj hs (Eras.nb one_nb hEr))
      · exact ((dOk1 _ _ Fu hj hs hFu).ofEq (by simp [dpOf, bn, tflag]) rfl).trans
          (eraseOk _ _ _ hj hs (Eras.nb (by simp [NB]) (Eras.nb one_nb hEr)))
    have hinc := ZP.MH.sincL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.of_eq (c4 := lay J (S + 1)) (by rw [eS]; rfl)
      (by rw [lay_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectLP (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : runMH (str J) (str S) (clock (str J) (str S)) = !inLP (str S) := by
      have h' : runMH (str J) (str S) (clock (str J) (str S)) ≠ inLP (str S) := hc
      revert h'
      cases runMH (str J) (str S) (clock (str J) (str S)) <;> cases inLP (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zlpLogic.Reach
        (hdR (dpOf (bn (!inLP (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: 1 :: (tflag (inLP (str S)) ++ 1 :: Fu))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zlpLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inLP (str S)
      · refine ⟨1 :: Fu, (dBad1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) (by simp), ?_⟩
        exact (eraseBad _ _ _ hj hs (Eras.nb one_nb hEr)).ofEq (hdR_eq (by simp) rfl) rfl
      · refine ⟨3 :: 1 :: Fu, (dBad0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) (by simp), ?_⟩
        exact (eraseBad _ _ _ hj hs (Eras.nb (by simp [NB]) (Eras.nb one_nb hEr))).ofEq
          (hdR_eq (by simp) rfl) rfl
    obtain ⟨n1, hn1⟩ := hA.trans h1
    obtain ⟨n2, hn2⟩ := h3.trans ((ZP.MH.jincL rJ 0).of_eq (c4 := lay (J + 1) 1) (by rw [eJ]; rfl)
      (by rw [lay_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, ZP.MH.beepStep _ _ Y, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2

end ZP.MH

namespace ZP

theorem zlpConf_two : zlpLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zlpLogic`: `pair_mainLP` is the one lemma. -/
def zlpPairData : PairData zlpLogic CorrectLP where
  lay := lay
  k0 := 2
  h0 := zlpConf_two
  step := MH.pair_mainLP

theorem zlpLogic_macroSim : Nonempty (LMacroSimC CorrectLP zlpLogic) := zlpPairData.macroSim

theorem zlpQuasihalts_iff_sentence : Quasihalts zlpMachine ↔ SentenceLP :=
  match zlpLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zlpMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectLP))

end ZP
