module

public import ZP.RulerNTT

@[expose] public section

/-! # NTT machine: the primality test (part 1): copying `P` into `D` -/

namespace ZP.NTT

open ZP ZP.G

theorem repSet (k c : Nat) : ∀ x ∈ List.replicate k c, x ∈ [c] := by
  intro x hx; simp [List.mem_replicate] at hx; simp [hx]

/-- `DC1`: skip the marked cells of `P`, mark the next one, turn back. -/
theorem dc1Mark (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DC1 A (List.replicate m 2 ++ 3 :: R))
      (hd QNTT.DC2 (A ++ List.replicate m 2) (2 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dc2Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.DC2 L R) (hdR QNTT.DC3 [3] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dc3Walk (d : Nat) (X : List Nat) (hX : Sym4 X) :
    znttLogic.Reach (hdR QNTT.DC3 [3] (List.replicate d 3 ++ 1 :: X))
      (hdR QNTT.DC1 (3 :: List.replicate d 3 ++ [1]) X) := by
  have hV : Valid [[3], ALL] [List.replicate d 3, X] :=
    Valid.cons (repSet d 3) (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [List.replicate d 3, X]) (E := []) (k := 4) hV trivial
    (ls := [.sym 3]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 3, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dcCycle (d m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.DC1 (List.replicate (d + 1) 3 ++ [1]) (List.replicate (m + 1) 2 ++ R)) := by
  have sA : Sym4 (List.replicate d 3 ++ [1]) :=
    (Sym4.rep d 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h1 := dc1Mark _ m R sA hR
  have nL : NoB (List.replicate d 3 ++ [1] ++ List.replicate m 2) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_rep_iff, NoB_nil_iff]; simp [NB]
  have h2 := dc2Scan _ (2 :: R) nL (Sym4.cons (by simp [ALL]) hR)
  have h3 := dc3Walk d (List.replicate m 2 ++ 2 :: R)
    ((Sym4.rep m 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR))
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 h3
  have e2 : List.replicate (m + 1) 2 ++ R = List.replicate m 2 ++ 2 :: R := by
    simp [List.replicate_succ']
  have e1 : List.replicate (d + 1) 3 ++ [1] = 3 :: (List.replicate d 3 ++ [1]) := by
    simp [List.replicate_succ]
  rw [e1, e2]
  exact h1.trans (h2.trans h3)

theorem dcLoop (rest : List Nat) (hr : Sym4 rest) :
    ∀ (k d m : Nat),
    znttLogic.Reach
      (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ List.replicate k 3 ++ 1 :: rest))
      (hdR QNTT.DC1 (List.replicate (d + k) 3 ++ [1]) (List.replicate (m + k) 2 ++ 1 :: rest)) := by
  intro k
  induction k with
  | zero => intro d m; simpa using LTM.Reach.refl znttLogic _
  | succ k ih =>
    intro d m
    have h1 := dcCycle d m (List.replicate k 3 ++ 1 :: rest)
      ((Sym4.rep k 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr))
    have h2 := ih (d + 1) (m + 1)
    have e1 : List.replicate m 2 ++ List.replicate (k + 1) 3 ++ 1 :: rest =
        List.replicate m 2 ++ 3 :: (List.replicate k 3 ++ 1 :: rest) := by
      simp [List.replicate_succ]
    rw [e1]
    have := h1.trans (h2.of_eq (by simp [List.append_assoc]) rfl)
    have e2 : d + 1 + k = d + (k + 1) := by omega
    have e3 : m + 1 + k = m + (k + 1) := by omega
    rw [e2, e3] at this
    exact this

/-- `P` exhausted: `DC1` hits `M`, `DCU` unmarks `P`, crosses the separator. -/
theorem dcEnd (d m : Nat) (rest : List Nat) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate d 3) (1 :: (List.replicate m 3 ++ 1 :: rest))) := by
  have sA : Sym4 (List.replicate d 3 ++ [1]) :=
    (Sym4.rep d 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have sD : Sym4 (List.replicate d 3) := Sym4.rep d 3 (by simp [ALL])
  have hV : Valid [ALL, [2], ALL] [List.replicate d 3 ++ [1], List.replicate m 2, rest] :=
    Valid.cons sA (Valid.cons (repSet m 2) (Valid.cons hr (Valid.nil _)))
  have h1 : znttLogic.Reach (hdR QNTT.DC1 (List.replicate d 3 ++ [1]) (List.replicate m 2 ++ 1 :: rest))
      (hd QNTT.DCU (List.replicate d 3 ++ [1] ++ List.replicate m 2) (1 :: rest)) :=
    checkFT (env := [List.replicate d 3 ++ [1], List.replicate m 2, rest]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV2 : Valid [ALL, [2], ALL] [List.replicate d 3 ++ [1], List.replicate m 2, 1 :: rest] :=
    Valid.cons sA (Valid.cons (repSet m 2) (Valid.cons (Sym4.cons (by simp [ALL]) hr) (Valid.nil _)))
  have h2 : znttLogic.Reach (hd QNTT.DCU (List.replicate d 3 ++ [1] ++ List.replicate m 2) (1 :: rest))
      (hd QNTT.DCU (List.replicate d 3 ++ [1]) (List.replicate m 3 ++ 1 :: rest)) :=
    checkTT (env := [List.replicate d 3 ++ [1], List.replicate m 2, 1 :: rest]) (E := []) (k := 4) hV2 trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  have hV3 : Valid [ALL, ALL] [List.replicate d 3, List.replicate m 3 ++ 1 :: rest] :=
    Valid.cons sD (Valid.cons ((Sym4.rep m 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hr)) (Valid.nil _))
  have h3 : znttLogic.Reach (hd QNTT.DCU (List.replicate d 3 ++ [1]) (List.replicate m 3 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate d 3) (1 :: (List.replicate m 3 ++ 1 :: rest))) :=
    checkTT (env := [List.replicate d 3, List.replicate m 3 ++ 1 :: rest]) (E := []) (k := 4) hV3 trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact h1.trans (h2.trans h3)

/-- Whole copy phase: `D M P rest` with `D` empty becomes `D = 1^p`, `P` unmarked, at `XS1`. -/
theorem dcAll (p : Nat) (rest : List Nat) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.DC1 [1] (List.replicate p 3 ++ 1 :: rest))
      (hd QNTT.XS1 (List.replicate p 3) (1 :: (List.replicate p 3 ++ 1 :: rest))) := by
  have h1 := dcLoop rest hr p 0 0
  have h2 := dcEnd (0 + p) (0 + p) rest hr
  simp only [Nat.zero_add, List.replicate_zero, List.nil_append] at h1 h2
  exact h1.trans h2

end ZP.NTT
