module

public import ZP.MMQ2

@[expose] public section

/-! The Q pass: `k` iterations.  Invariant at `Q2` (head on the last of `U = replicate k 2`):
`hd Q2 (A ++ U) (0 :: Wl ++ 1 :: (Os ++ e :: Rest))`.  After the pass the loaded bits are
`((Os.reverse ++ replicate k 2).take k).reverse ++ Wl` (out cells taken from the top, missing ones read 0),
and the taken out cells are blanked. -/

namespace ZP.Mul.MM

open ZP

theorem reach_hd_cong {q q' : Nat} {A A' R R' B B' S S' : List Nat}
    (h : zmmLogic.Reach (hd q A R) (hd q' B S)) (h1 : A = A') (h2 : R = R') (h3 : B = B') (h4 : S = S') :
    zmmLogic.Reach (hd q A' R') (hd q' B' S') := by
  subst h1 h2 h3 h4; exact h

theorem take_pad (k : Nat) (u : List Nat) (c : Nat) :
    List.take k (u ++ List.replicate (k + 1) c) = List.take k (u ++ List.replicate k c) := by
  rw [List.take_append, List.take_append, List.take_replicate, List.take_replicate]
  have : min (k - u.length) (k + 1) = min (k - u.length) k := by omega
  rw [this]

theorem qPass (A : List Nat) (hA : Sym4 A) :
    ∀ (k : Nat) (Wl Os Rest : List Nat) (e : Nat), (e = 0 ∨ e = 1) → Bits Wl → Bits Os → Sym4 Rest →
      zmmLogic.Reach (hd QMM.Q2 (A ++ List.replicate k 2) (0 :: Wl ++ 1 :: (Os ++ e :: Rest)))
        (hd QMM.Q2 A (0 :: ((Os.reverse ++ List.replicate k 2).take k).reverse ++ Wl ++
          1 :: (Os.take (Os.length - k) ++ List.replicate (min k Os.length) 0 ++ e :: Rest))) := by
  intro k
  induction k with
  | zero =>
    intro Wl Os Rest e _ _ _ _
    simp only [List.replicate_zero, List.append_nil, List.take_zero, List.reverse_nil, List.nil_append,
      Nat.sub_zero, List.take_length, List.append_assoc]
    simp
    exact LTM.Reach.refl _ _
  | succ k ih =>
    intro Wl Os Rest e he hWl hOs hRest
    have hU : ∀ a ∈ List.replicate k 2, a = 2 := fun a ha => List.eq_of_mem_replicate ha
    have e1 : A ++ List.replicate (k + 1) 2 = A ++ List.replicate k 2 ++ [2] := by
      simp [List.replicate_succ']
    rw [e1]
    rcases List.eq_nil_or_concat Os with rfl | ⟨Os', y, rfl⟩
    · have s1 := qIter0 A (List.replicate k 2) Wl Rest e he hA hU hWl hRest
      have s2 := ih (2 :: Wl) [] Rest e he (Bits.cons (by simp [bits]) hWl) (fun a ha => by simp at ha) hRest
      have := s1.trans s2
      refine reach_hd_cong this rfl ?_ rfl ?_
      · simp
      · simp only [List.reverse_nil, List.nil_append, List.take_replicate, List.length_nil, Nat.zero_sub,
          List.take_nil, List.replicate_zero, Nat.min_zero, List.append_nil, List.reverse_replicate,
          Nat.min_self, List.append_assoc, List.cons_append]
        rw [List.replicate_succ', List.append_assoc]
        simp
    · simp only [List.concat_eq_append] at hOs ⊢
      have hOs' : Bits Os' := fun a ha => hOs a (by simp [ha])
      have hy := hOs y (by simp)
      have hWl' : Bits (y :: Wl) := Bits.cons hy hWl
      have hR' : Sym4 (e :: Rest) := Sym4.cons (by rcases he with rfl | rfl <;> simp [ALL]) hRest
      have s2 := ih (y :: Wl) Os' (e :: Rest) 0 (Or.inl rfl) hWl' hOs' hR'
      have s1 : zmmLogic.Reach (hd QMM.Q2 (A ++ List.replicate k 2 ++ [2]) (0 :: Wl ++ 1 :: (Os' ++ y :: e :: Rest)))
          (hd QMM.Q2 (A ++ List.replicate k 2) (0 :: y :: Wl ++ 1 :: (Os' ++ 0 :: e :: Rest))) := by
        rcases mem_bits hy with rfl | rfl
        · exact qIter2 A (List.replicate k 2) Wl Os' Rest e he hA hU hWl hOs' hRest
        · exact qIter3 A (List.replicate k 2) Wl Os' Rest e he hA hU hWl hOs' hRest
      have := s1.trans s2
      refine reach_hd_cong this rfl ?_ rfl ?_
      · simp
      · have F1 : (List.take (k + 1) ((Os' ++ [y]).reverse ++ List.replicate (k + 1) 2)).reverse =
            (List.take k (Os'.reverse ++ List.replicate k 2)).reverse ++ [y] := by
          have : (Os' ++ [y]).reverse ++ List.replicate (k + 1) 2 = y :: (Os'.reverse ++ List.replicate (k + 1) 2) := by
            simp
          rw [this, List.take_succ_cons, List.reverse_cons, take_pad]
        have F2 : List.take ((Os' ++ [y]).length - (k + 1)) (Os' ++ [y]) = List.take (Os'.length - k) Os' := by
          have : (Os' ++ [y]).length - (k + 1) = Os'.length - k := by simp
          rw [this, List.take_append_of_le_length (by omega)]
        have F3 : List.replicate (min (k + 1) (Os' ++ [y]).length) 0 ++ e :: Rest =
            List.replicate (min k Os'.length) 0 ++ 0 :: e :: Rest := by
          have : min (k + 1) (Os' ++ [y]).length = min k Os'.length + 1 := by simp
          rw [this, List.replicate_succ', List.append_assoc]; rfl
        rw [F1, F2]
        simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at F3 ⊢
        rw [F3]

end ZP.Mul.MM
