module

public import ZP.MMExit

@[expose] public section

/-! Verdict glue: from `VW1` with a blank prefix `Z` to the dispatch entry states `DP31` (outcome 1) / `DP30`
(outcome 0), with all blank prefixes dropped (`hdR_rep0`). -/

namespace ZP.Mul.MM

open ZP

theorem hdR_rep0 (q n : Nat) (A R : List Nat) : hdR q (List.replicate n 0 ++ A) R = hdR q A R := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, hdR_cons0, ih]

theorem zeros_pad (Z outr Cb : List Nat) (hZ : ∀ a ∈ Z, a = 0) (h2 : 2 ≤ Z.length) :
    ∃ n, Z = List.replicate (n + 2) 0 := by
  refine ⟨Z.length - 2, ?_⟩
  apply List.eq_replicate_iff.mpr
  exact ⟨by omega, hZ⟩

theorem zsum (n a b : Nat) :
    [0] ++ List.replicate n 0 ++ [0, 0, 0] ++ List.replicate a 0 ++ List.replicate b 0 = List.replicate (n + 4 + a + b) 0 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp; omega, ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton, List.mem_cons] at hx
  rcases hx with ((((h | h) | h) | h) | h)
  · simpa using h
  · exact List.eq_of_mem_replicate h
  · rcases h with h | h | h <;> simpa using h
  · exact List.eq_of_mem_replicate h
  · exact List.eq_of_mem_replicate h

theorem vw1Ok (Z outr Cb J sv Y2 : List Nat) (hZ : ∀ a ∈ Z, a = 0) (h2 : 2 ≤ Z.length)
    (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.VW1 [0] (Z ++ 3 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  obtain ⟨n, rfl⟩ := zeros_pad Z outr Cb hZ h2
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have t := verdictTail1 [0] (List.replicate n 0) outr Cb J sv Y2 (Sym4.cons h0 Sym4.nil)
    (sym4_rep n 0 h0) houtr hCb hJ hsv hY2
  have e : [0] ++ (List.replicate (List.replicate n 0).length 0 ++ (0 :: 0 :: 0 :: (List.replicate outr.length 0 ++
      (List.replicate Cb.length 0 ++ (1 :: (J ++ (1 :: (sv ++ [1])))))))) =
      List.replicate (n + 4 + outr.length + Cb.length) 0 ++ (1 :: (J ++ (1 :: (sv ++ [1])))) := by
    have := congrArg (· ++ (1 :: (J ++ (1 :: (sv ++ [1]))))) (zsum n outr.length Cb.length)
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.length_replicate] at this ⊢
    exact this
  have es : List.replicate (n + 2) 0 ++ 3 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2 =
      List.replicate (List.replicate n 0).length 0 ++ (0 :: 0 :: 3 :: (outr ++ (Cb ++ (1 :: (J ++ (1 :: (sv ++ (0 :: 1 :: Y2)))))))) := by
    have h22 : List.replicate (n + 2) 0 = List.replicate n 0 ++ [0, 0] := by
      rw [← List.replicate_append_replicate]; rfl
    rw [h22]
    simp
  rw [es]
  rw [e, hdR_rep0] at t
  exact t

theorem vw1Bad (Z outr Cb J sv Y2 : List Nat) (hZ : ∀ a ∈ Z, a = 0) (h2 : 2 ≤ Z.length)
    (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach (hdR QMM.VW1 [0] (Z ++ 2 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))
      (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  obtain ⟨n, rfl⟩ := zeros_pad Z outr Cb hZ h2
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have t := verdictTail0 [0] (List.replicate n 0) outr Cb J sv Y2 (Sym4.cons h0 Sym4.nil)
    (sym4_rep n 0 h0) houtr hCb hJ hsv hY2
  have e : [0] ++ (List.replicate (List.replicate n 0).length 0 ++ (0 :: 0 :: 0 :: (List.replicate outr.length 0 ++
      (List.replicate Cb.length 0 ++ (1 :: (J ++ (1 :: (sv ++ [1])))))))) =
      List.replicate (n + 4 + outr.length + Cb.length) 0 ++ (1 :: (J ++ (1 :: (sv ++ [1])))) := by
    have := congrArg (· ++ (1 :: (J ++ (1 :: (sv ++ [1]))))) (zsum n outr.length Cb.length)
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.length_replicate] at this ⊢
    exact this
  have es : List.replicate (n + 2) 0 ++ 2 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2 =
      List.replicate (List.replicate n 0).length 0 ++ (0 :: 0 :: 2 :: (outr ++ (Cb ++ (1 :: (J ++ (1 :: (sv ++ (0 :: 1 :: Y2)))))))) := by
    have h22 : List.replicate (n + 2) 0 = List.replicate n 0 ++ [0, 0] := by
      rw [← List.replicate_append_replicate]; rfl
    rw [h22]
    simp
  rw [es]
  rw [e, hdR_rep0] at t
  exact t

end ZP.Mul.MM
