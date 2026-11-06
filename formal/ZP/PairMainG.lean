module

public import ZP.CheckG12

@[expose] public section

/-! # The pair lemma for the GI machine -/

namespace ZP.G

open ZP

theorem newInstG (J S : Nat) :
    zgiLogic.Reach1 (F.layF J S) (TR (bitsOf (str J)) (str S) (inLG (str S))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  rw [F.layF_hdR]
  have h0 := ni0 (bitsOf (str J)) (bitsOf (str S)) hj hs
  have h1 := gcLoop [1] (bitsOf (str J)) [] (NoB.cons one_nb NoB.nil) hj Sym4.nil (bitsOf (str S)) []
    Bits.nil hs
  have h2 := ni2a (bitsOf (str S)).reverse (bitsOf (str J)) (bitsOf (str S)) (Bits.ofB _).rev hj hs
  have hR : Sym4 (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1]))) :=
    Sym4.cons (by simp [ALL]) (hj.sym4.app (Sym4.cons (by simp [ALL]) ((Bits.ofB _).sym4.app
      (Sym4.cons (by simp [ALL]) Sym4.nil))))
  have h3 := gtcLoop _ hR (bitsOf (str S)).reverse [1] (Bits.ofB _).rev (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h4 := truthPhaseG (str J) (str S)
  have hall := (h0.trans ((h1.of_eq (by simp) rfl).trans (h2.of_eq (by simp) rfl))).trans
    ((h3.of_eq (by simp) rfl).trans h4)
  refine F.Reach_pos hall ?_
  show ((atR QF.NI).den _).q ≠ ((atR Q.GRB).den _).q
  rw [SC.den_q, SC.den_q]
  show QF.NI ≠ Q.GRB
  decide


theorem pair_mainG (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectG J S → zgiLogic.zrun n (F.layF J S) = some (F.layF (absStepC CorrectG (J, S)).1 (absStepC CorrectG (J, S)).2)) ∧
       (¬ CorrectG J S → ∃ a c1 c2, a < n ∧ zgiLogic.zrun a (F.layF J S) = some c1 ∧ c1.q = zgiLogic.beep ∧
          zgiLogic.zstep c1 = some c2 ∧
          zgiLogic.zrun (n - a - 1) c2 = some (F.layF (absStepC CorrectG (J, S)).1 (absStepC CorrectG (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨Fu, hFu, hD⟩ := dPhase (str J) (str S) (inLG (str S))
  have hA := (newInstG J S).trans hD
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectG J S
  · have e : absStepC CorrectG (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = inLG (str S) := hc
    rw [ho] at hA
    have hok : zgiLogic.Reach
        (hdR (dpOf (bn (inLG (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inLG (str S)) ++ 1 :: Fu)))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inLG (str S)
      · exact (dOk0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
      · exact (dOk1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
    have hinc := sincL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.of_eq (c4 := F.layF J (S + 1)) (by rw [eS]; rfl) (by rw [F.layF_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectG (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = !inLG (str S) := by
      have h' : run (str J) (str S) (clock (str J) (str S)) ≠ inLG (str S) := hc
      revert h'
      cases run (str J) (str S) (clock (str J) (str S)) <;> cases inLG (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zgiLogic.Reach
        (hdR (dpOf (bn (!inLG (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inLG (str S)) ++ 1 :: Fu)))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zgiLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inLG (str S)
      · exact ⟨1 :: Fu, (dBad1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad1E _ _ Fu hj hs hFu⟩
      · exact ⟨3 :: 1 :: Fu, (dBad0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad0E _ _ Fu hj hs hFu⟩
    obtain ⟨n1, hn1⟩ := hA.trans h1
    obtain ⟨n2, hn2⟩ := h3.trans ((jincL rJ 0).of_eq (c4 := F.layF (J + 1) 1) (by rw [eJ]; rfl) (by rw [F.layF_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, beepStep _ _ Y, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2

end ZP.G
