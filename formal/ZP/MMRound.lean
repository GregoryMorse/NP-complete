module

public import ZP.MMVerdict3
public import ZP.MMBRow
public import ZP.MMRSLoop
public import ZP.MMFetch3

@[expose] public section

/-! One round of the check: rewind the hole (`rsLoop`), return to `FA` (`toFA`), fetch the next bit `a` of `A`
(`fetchA0/1`) and process one B row (`bRow`).  The accumulator `Xt.reverse ++ [x]` is updated by `jc a`. -/

namespace ZP.Mul.MM

open ZP

theorem roundA (s a : Nat) (hsa : (s = 2 ∧ a = 1) ∨ (s = 3 ∧ a = 0))
    (Au' Be Vt Xt Bd R0 : List Nat) (q : Nat) (v x : Nat)
    (hAu : Bits Au') (hBe : Bits Be) (hVt : Bits Vt) (hXt : Bits Xt) (hBd : Bits Bd)
    (hv : v ∈ bits) (hx : x ∈ bits) (hlen : Vt.length = Xt.length) (hR : Sym4 R0) :
    zmmLogic.Reach
      (hdR QMM.RS1 (Au' ++ s :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])) ++ 0 :: Bd ++ [1])
        (0 :: (Xt.reverse ++ [x]) ++ 1 :: R0))
      (hdR QMM.RS1 (Au' ++ 1 :: (List.replicate q 1 ++ 1 :: Be) ++ 0 :: (Vt.reverse ++ v :: Bd ++ [1]))
        (0 :: ((List.zipWith (jc a) (v :: Vt) (x :: Xt)).reverse ++ [] ++ 1 :: R0))) := by
  have hAu4 := hAu.sym4
  have hBe4 := hBe.sym4
  have hVt4 := hVt.sym4
  have hBd4 := hBd.sym4
  have hXb : Bits (Xt.reverse ++ [x]) := fun c hc => by
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hXt c hc
    · exact hx
  have hVr : Bits Vt.reverse := fun c hc => hVt c (List.mem_reverse.mp hc)
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hq : Sym4 (List.replicate q 1) := sym4_rep q 1 h1
  have hs4 : s ∈ ALL := by rcases hsa with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [ALL]
  have hBr : Bits (Be ++ Vt.reverse) := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact hBe c hc
    · exact hVr c hc
  have hBr4 := hBr.sym4
  have hVr4 := hVr.sym4
  have hXb4 := hXb.sym4
  have hv4 : v ∈ ALL := by rcases mem_bits hv with rfl | rfl <;> simp [ALL]
  have hF0 : Sym4 (Au' ++ s :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v]))) := by
    simp [sym4_app_iff, sym4_cons_iff, *]
  have t0 := rsLoop (Xt.reverse ++ [x]) hXb
    (Au' ++ s :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])) ++ 0 :: Bd ++ [1])
    (by simp [sym4_app_iff, sym4_cons_iff, *]) R0 hR
  have t1 := toFA (Au' ++ s :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v]))) Bd
    (Xt.reverse ++ [x]) R0 hF0 hBd hXb hR
  have t2 : zmmLogic.Reach
      (hd QMM.FA (Au' ++ s :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])))
        (0 :: Bd ++ 1 :: (Xt.reverse ++ [x]) ++ 0 :: 1 :: R0))
      (hd QMM.J1 (Au' ++ 1 :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])))
        (0 :: Bd ++ a :: (Xt.reverse ++ [x]) ++ 0 :: 1 :: R0)) := by
    rcases hsa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fetchA0 Au' (Be ++ Vt.reverse) Bd (Xt.reverse ++ [x]) R0 v q hAu hBr hv hBd hXb hR
    · exact fetchA1 Au' (Be ++ Vt.reverse) Bd (Xt.reverse ++ [x]) R0 v q hAu hBr hv hBd hXb hR
  have e2 : Au' ++ 1 :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse ++ [v])) =
      (Au' ++ 1 :: (List.replicate q 1 ++ 1 :: (Be ++ Vt.reverse))) ++ [v] := by simp
  rw [e2, hd_snoc] at t2
  have t3 := bRow a (by rcases hsa with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]) R0 hR Vt Xt hlen hVt hXt v x hv hx
    (Au' ++ 1 :: (List.replicate q 1 ++ 1 :: Be)) Bd [] (by simp [sym4_app_iff, sym4_cons_iff, *]) hBd Bits.nil
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 t3 ⊢
  exact t0.trans (t1.trans (t2.trans t3))

end ZP.Mul.MM
