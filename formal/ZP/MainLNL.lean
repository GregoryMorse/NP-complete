module

public import ZP.PairLNLD
public import ZP.CompileLNL
public import ZP.GenericP
public import ZP.LogicalG

@[expose] public section

/-!
# The L = P machine quasihalts iff `SentenceLNL`
-/

namespace ZP.MH

open ZP

theorem pair_mainLNL (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectLNL J S → zlnlLogic.zrun n (lay J S) = some (lay (absStepC CorrectLNL (J, S)).1 (absStepC CorrectLNL (J, S)).2)) ∧
       (¬ CorrectLNL J S → ∃ a c1 c2, a < n ∧ zlnlLogic.zrun a (lay J S) = some c1 ∧ c1.q = zlnlLogic.beep ∧
          zlnlLogic.zstep c1 = some c2 ∧
          zlnlLogic.zrun (n - a - 1) c2 = some (lay (absStepC CorrectLNL (J, S)).1 (absStepC CorrectLNL (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have hA0 := vStartL J S
  have hV := vFullL (bitsOf (str J)) hj (str S)
  have ht : ∀ a ∈ tflag (inLNL (str S)), a ∈ T3 := by cases inLNL (str S) <;> simp [tflag, T3]
  obtain ⟨Fu, hEr, hFu, hD⟩ := dPhaseL (str J) (str S) (tflag (inLNL (str S))) ht
  have hA := hA0.trans (hV.trans hD)
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectLNL J S
  · have e : absStepC CorrectLNL (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : runMH (str J) (str S) (clock (str J) (str S)) = inLNL (str S) := hc
    rw [ho] at hA
    have hok : zlnlLogic.Reach
        (hdR (dpOf (bn (inLNL (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: 1 :: (tflag (inLNL (str S)) ++ 1 :: Fu))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inLNL (str S)
      · exact ((dOk0L _ hj _ hs Fu hFu).ofEq (by simp [dpOf, bn, tflag]) rfl).trans
          (eraseOkL _ _ _ hj hs (Eras.nb one_nb hEr))
      · exact ((dOk1L _ hj _ hs Fu hFu).ofEq (by simp [dpOf, bn, tflag]) rfl).trans
          (eraseOkL _ _ _ hj hs (Eras.nb (by simp [NB]) (Eras.nb one_nb hEr)))
    have hinc := ZP.MH.sincLL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.ofEq (c4 := lay J (S + 1)) (by rw [eS]; rfl)
      (by rw [lay_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectLNL (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : runMH (str J) (str S) (clock (str J) (str S)) = !inLNL (str S) := by
      have h' : runMH (str J) (str S) (clock (str J) (str S)) ≠ inLNL (str S) := hc
      revert h'
      cases runMH (str J) (str S) (clock (str J) (str S)) <;> cases inLNL (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zlnlLogic.Reach
        (hdR (dpOf (bn (!inLNL (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: 1 :: (tflag (inLNL (str S)) ++ 1 :: Fu))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zlnlLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inLNL (str S)
      · refine ⟨1 :: Fu, (dBad1L _ hj _ hs Fu hFu).ofEq (by simp [dpOf, bn, tflag]) (by simp), ?_⟩
        exact (eraseBadL _ _ _ hj hs (Eras.nb one_nb hEr)).ofEq (hdR_eq (by simp) rfl) rfl
      · refine ⟨3 :: 1 :: Fu, (dBad0L _ hj _ hs Fu hFu).ofEq (by simp [dpOf, bn, tflag]) (by simp), ?_⟩
        exact (eraseBadL _ _ _ hj hs (Eras.nb (by simp [NB]) (Eras.nb one_nb hEr))).ofEq
          (hdR_eq (by simp) rfl) rfl
    obtain ⟨n1, hn1⟩ := hA.trans h1
    obtain ⟨n2, hn2⟩ := h3.trans ((ZP.MH.jincLL rJ 0).ofEq (c4 := lay (J + 1) 1) (by rw [eJ]; rfl)
      (by rw [lay_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, ZP.MH.beepStepL _ _ Y, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2

end ZP.MH

namespace ZP

theorem zlnlConf_two : zlnlLogic.zconf 2 = some (lay 1 1) := rfl

/-- The pair data of `zlnlLogic`: `pair_mainLNL` is the one lemma. -/
def zlnlPairData : PairData zlnlLogic CorrectLNL where
  lay := lay
  k0 := 2
  h0 := zlnlConf_two
  step := MH.pair_mainLNL

theorem zlnlLogic_macroSim : Nonempty (LMacroSimC CorrectLNL zlnlLogic) := zlnlPairData.macroSim

theorem zlnlQuasihalts_iff_sentence : Quasihalts zlnlMachine ↔ SentenceLNL :=
  match zlnlLogic_macroSim with
  | ⟨S⟩ => (quasihalts_iff_of_macroSimC (zlnlMacroSimC S)).trans (abstractQuasihaltsC_iff (C := CorrectLNL))

end ZP
