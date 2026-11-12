module

public import ZP.MMPhase
public import ZP.MMPair
public import ZP.MulCheck

@[expose] public section

/-!
# Z_MATMUL: the halting dispatch, the main phase, and one pair
-/

namespace ZP.Mul.MM

open ZP

/-- The outcome of a finished run, as the dispatch sees it. -/
def okBM (r : Option (List Bool)) (Xb : List Bool) : Bool :=
  match r with
  | none => false
  | some out => checkMM out Xb

theorem haltPhaseMM (Pb Xb : List Bool) (r : Option (List Bool)) (Fy ST : List Nat)
    (hF : NoB (1 :: Fy)) (hST : NoB ST) :
    ∃ q, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ okBM r Xb = true) ∧
      zmmLogic.Reach (REm r (bitsOf Pb ++ 1 :: bitsOf Xb) (1 :: Fy) ST)
        (hdR q (1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ [1]))) (1 :: (Fy ++ 0 :: ST))) := by
  have hY : Sym4 (Fy ++ 0 :: ST) :=
    (NoB.sym4 (by intro a ha; exact hF a (List.mem_cons_of_mem _ ha))).app
      (Sym4.cons (by simp [ALL]) hST.sym4)
  have hj : Bits (bitsOf Pb) := Bits.ofB Pb
  cases r with
  | none =>
    refine ⟨Q.DP30, Or.inr rfl, by simp [okBM, Q.DP31, Q.DP30], ?_⟩
    have h := dHalt0 (bitsOf Pb) (bitsOf Xb) (Fy ++ 0 :: ST) hj (Bits.ofB Xb) hY
    exact (h.of_eq (by simp [REm, REn, dpOf]) rfl)
  | some out =>
    obtain ⟨q, hq, hqiff, h⟩ := mmPhase out Xb (bitsOf Pb) (Fy ++ 0 :: ST) hj hY
    refine ⟨q, hq, by simp [okBM, hqiff], ?_⟩
    exact h.of_eq (by simp [REm, REn]) rfl

theorem full_fzM (n k : Nat) : full (fz n k) = fz n k := by
  simp [full, fz, List.map_replicate]

theorem mainPhaseMM (J S : Nat) :
    ∃ q Fy ST, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ CorrectMM J S) ∧ NoB Fy ∧ NoB ST ∧
      zmmLogic.Reach (hdR QMul.NI (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [])
        (hdR q (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1]))) (1 :: (Fy ++ 0 :: ST))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h0 := decFuelM (bitsOf (str S)) hs (bitsOf (str J)) hj
  have hdig := fz_dig (bitsOf (str S)).length (bitsOf (str J)).length
  have hne : fz (bitsOf (str S)).length (bitsOf (str J)).length ≠ [] := by simp [fz]
  obtain ⟨ds', ST', hds', hmap, hST', h1⟩ := runFromM (str J) (str S) _ hdig hne
  have hne' : ds' ≠ [] := by
    intro h
    rw [h] at hmap
    simp [fz] at hmap
  obtain ⟨Fy, hFy⟩ := FWr_one ds' hne'
  rw [hFy] at h1
  have hFnb : NoB (1 :: Fy) := by rw [← hFy]; exact FWr_noB _
  have hv : valr (fz (bitsOf (str S)).length (bitsOf (str J)).length) = clockMul (str J) (str S) := by
    have := fz_valr (bitsOf (str S)).length (bitsOf (str J)).length
    rw [full_fzM] at this
    simp only [bitsOf_len] at this ⊢
    unfold clockMul
    omega
  rw [hv] at h1
  obtain ⟨q, hq, hqok, h2⟩ := haltPhaseMM (str J) (str S)
    (runMulAux (clockMul (str J) (str S)) (rot ((str J).reverse ++ [false])) (str S) 0
      (List.replicate (str J).length [])) Fy ST' hFnb hST'
  refine ⟨q, Fy, ST', hq, ?_, fun a ha => hFnb a (List.mem_cons_of_mem _ ha), hST', ?_⟩
  · rw [hqok]
    unfold CorrectMM correctMMB runMul
    cases hr : runMulAux (clockMul (str J) (str S)) (rot ((str J).reverse ++ [false])) (str S) 0
      (List.replicate (str J).length []) <;> simp [okBM]
  · refine h0.trans ((h1.of_eq (by simp [bitsOf_len]) rfl).trans h2)

theorem pair_mainMM (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectMM J S → zmmLogic.zrun n (ZP.Mul.layMul J S) =
          some (ZP.Mul.layMul (absStepC CorrectMM (J, S)).1 (absStepC CorrectMM (J, S)).2)) ∧
       (¬ CorrectMM J S → ∃ a c1 c2, a < n ∧ zmmLogic.zrun a (ZP.Mul.layMul J S) = some c1 ∧
          c1.q = zmmLogic.beep ∧ zmmLogic.zstep c1 = some c2 ∧
          zmmLogic.zrun (n - a - 1) c2 =
            some (ZP.Mul.layMul (absStepC CorrectMM (J, S)).1 (absStepC CorrectMM (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨q, Fy, ST, hq, hqiff, hFy, hST, hA⟩ := mainPhaseMM J S
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  have hA1 : zmmLogic.Reach1 (ZP.Mul.layMul J S) (hdR q (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1])))
      (1 :: (Fy ++ 0 :: ST))) := by
    rw [ZP.Mul.layMul_hdR]
    refine ZP.F.Reach_pos hA ?_
    rw [ZP.F.hdR_eq', ZP.F.hdR_eq']
    show QMul.NI ≠ q
    rcases hq with rfl | rfl <;> decide
  by_cases hc : CorrectMM J S
  · have e : absStepC CorrectMM (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have hq1 : q = Q.DP31 := hqiff.mpr hc
    subst hq1
    have hok := okTailM (bitsOf (str J)) (bitsOf (str S)) Fy ST hj hs hFy hST
    have hinc := sincLM (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA1.trans (hok.trans (hinc.of_eq (c4 := ZP.Mul.layMul J (S + 1))
      (by rw [eS]; rfl) (by rw [ZP.Mul.layMul_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectMM (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have hq0 : q = Q.DP30 := by
      rcases hq with rfl | rfl
      · exact absurd (hqiff.mp rfl) hc
      · rfl
    subst hq0
    have h3 := badTailM (bitsOf (str J)) (bitsOf (str S)) Fy ST hj hs hFy hST
    obtain ⟨n1, hn1⟩ := hA1
    obtain ⟨n2, hn2⟩ := h3.trans ((jincLM rJ 0).of_eq (c4 := ZP.Mul.layMul (J + 1) 1)
      (by rw [eJ]; rfl) (by rw [ZP.Mul.layMul_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, beepStepM _ _ _, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2


end ZP.Mul.MM
