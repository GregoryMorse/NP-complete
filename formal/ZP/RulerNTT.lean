module

public import ZP.CompileNTT
public import ZP.PairG

@[expose] public section

/-! # NTT machine: the `P += n` ruler (part 1) -/

namespace ZP.NTT

open ZP ZP.G

/-- `PA0` scans right to the end of the tape (blank), turns back to `PA1`. -/
theorem pa0Scan (A X Z : List Nat) (hA : Sym4 A) (hX : NoB X) (hZ : Sym4 Z) :
    znttLogic.Reach (hdR QNTT.PA0 A (X ++ 0 :: Z)) (hd QNTT.PA1 (A ++ X) (0 :: Z)) := by
  have hV : Valid [ALL, NB, ALL] [A, X, Z] :=
    Valid.cons hA (Valid.cons hX (Valid.cons hZ (Valid.nil _)))
  exact checkFT (env := [A, X, Z]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PA1` over marked cells of `Nn`. -/
theorem pa1Walk (a : Nat) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PA1 (L ++ List.replicate a 2) R) (hd QNTT.PA1 L (List.replicate a 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [L, List.replicate a 2, R] :=
    Valid.cons hL (Valid.cons (by intro x hx; simp [List.mem_replicate] at hx; simp [hx]) (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [L, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PA1` marks the last unmarked cell. -/
theorem pa1Mark (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PA1 (L ++ [3]) R) (hd QNTT.PA2 L (2 :: R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PA2` runs to the left end and writes a `1`. -/
theorem pa2Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PA2 L R) (hdR QNTT.PA0 [3] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PA1` crosses the `M` before `Nn`. -/
theorem pa1M (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PA1 (L ++ [1]) R) (hdR QNTT.PAU (L ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PAU` unmarks `Nn` and turns at the blank. -/
theorem pauSweep (A : List Nat) (a : Nat) (Z : List Nat) (hA : Sym4 A) (hZ : Sym4 Z) :
    znttLogic.Reach (hdR QNTT.PAU A (List.replicate a 2 ++ 0 :: Z))
      (hd QNTT.PT0 (A ++ List.replicate a 3) (0 :: Z)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, Z] :=
    Valid.cons hA (Valid.cons (by intro x hx; simp [List.mem_replicate] at hx; simp [hx]) (Valid.cons hZ (Valid.nil _)))
  exact checkFT (env := [A, List.replicate a 2, Z]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3)]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `PT0` runs to the left end and writes `M`. -/
theorem pt0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PT0 L R) (hdR QNTT.DC1 [1] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sym4_rep (k c : Nat) (hc : c ∈ ALL) : Sym4 (List.replicate k c) := Sym4.rep k c hc

/-- Tape of the ruler at `PA1`: `P M Mid M (1^r 0^a)`; one round marks one more cell of `Nn`. -/
theorem paLoop (Mid Z : List Nat) (hM : NoB Mid) (hZ : Sym4 Z) :
    ∀ (r p a : Nat),
    znttLogic.Reach
      (hd QNTT.PA1 (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: (List.replicate r 3 ++ List.replicate a 2))) (0 :: Z))
      (hd QNTT.PA1 (List.replicate (p + r) 3 ++ 1 :: (Mid ++ 1 :: (List.replicate 0 3 ++ List.replicate (a + r) 2))) (0 :: Z)) := by
  intro r
  induction r with
  | zero => intro p a; simpa using LTM.Reach.refl znttLogic _
  | succ r ih =>
    intro p a
    have sP := sym4_rep p 3 (by simp [ALL])
    have sM : Sym4 Mid := hM.sym4
    obtain ⟨L0, hL0⟩ : ∃ L0, L0 = List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate r 3) := ⟨_, rfl⟩
    have sL0 : Sym4 L0 := by
      simp only [hL0]
      exact sP.app (Sym4.cons (by simp [ALL]) (sM.app (Sym4.cons (by simp [ALL]) (sym4_rep r 3 (by simp [ALL])))))
    have sRa : Sym4 (List.replicate a 2 ++ 0 :: Z) :=
      (sym4_rep a 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hZ)
    have h1 := pa1Walk a (L0 ++ [3]) (0 :: Z) (sL0.app (Sym4.cons (by simp [ALL]) Sym4.nil)) (Sym4.cons (by simp [ALL]) hZ)
    have h2 := pa1Mark L0 (List.replicate a 2 ++ 0 :: Z) sL0 sRa
    have h3 := pa2Scan L0 (2 :: (List.replicate a 2 ++ 0 :: Z)) (by
      simp only [hL0, NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB, hM]) (Sym4.cons (by simp [ALL]) sRa)
    have h4 := pa0Scan [3] (L0 ++ List.replicate (a + 1) 2) Z (Sym4.cons (by simp [ALL]) Sym4.nil)
      (by simp only [hL0, NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB, hM]) hZ
    have h5 := ih (p + 1) (a + 1)
    have e1 : List.replicate p 3 ++ 1 :: (Mid ++ 1 :: (List.replicate (r + 1) 3 ++ List.replicate a 2)) =
        L0 ++ [3] ++ List.replicate a 2 := by
      simp [hL0, List.replicate_succ', List.append_assoc]
    refine (h1.of_eq (by rw [e1]) rfl).trans (h2.trans (h3.trans ((h4.of_eq (by simp [List.replicate_succ]) rfl).trans
      (h5.of_eq ?_ ?_))))
    · subst hL0; simp [List.replicate_succ, List.append_assoc]
    · have : p + 1 + r = p + (r + 1) := by omega
      have h' : a + 1 + r = a + (r + 1) := by omega
      rw [this, h']
/-- All of `Nn` marked: unmark it, write the separator `M` at the left end. -/
theorem paEnd (Mid Z : List Nat) (hM : NoB Mid) (hZ : Sym4 Z) (p a : Nat) :
    znttLogic.Reach
      (hd QNTT.PA1 (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: (List.replicate 0 3 ++ List.replicate a 2))) (0 :: Z))
      (hdR QNTT.DC1 [1] (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate a 3) ++ 0 :: Z)) := by
  have sP := sym4_rep p 3 (by simp [ALL])
  have sL : Sym4 (List.replicate p 3 ++ 1 :: (Mid ++ [1])) :=
    sP.app (Sym4.cons (by simp [ALL]) (hM.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)))
  have sRa : Sym4 (List.replicate a 2 ++ 0 :: Z) :=
    (sym4_rep a 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hZ)
  have s0Z : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  have nL : NoB (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate a 3)) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB, hM]
  have h1 := pa1Walk a (List.replicate p 3 ++ 1 :: (Mid ++ [1])) (0 :: Z) sL s0Z
  have h2 := pa1M (List.replicate p 3 ++ 1 :: Mid) (List.replicate a 2 ++ 0 :: Z)
    (sP.app (Sym4.cons (by simp [ALL]) hM.sym4)) sRa
  have h3 := pauSweep (List.replicate p 3 ++ 1 :: Mid ++ [1]) a Z
    (by simpa using sL) hZ
  have h4 := pt0Scan (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate a 3)) (0 :: Z) nL s0Z
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

/-- The ruler `P += n`: from `P M Mid M Nn` with `P = 3^(j+p)`, `Nn = 3^n`, to `DC1`
with `P` advanced by `n` and the separator `M` written at the left. -/
theorem padd (Mid Z : List Nat) (hM : NoB Mid) (hZ : Sym4 Z) (j p n : Nat) :
    znttLogic.Reach
      (hdR QNTT.PA0 (List.replicate j 3) (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z))
      (hdR QNTT.DC1 [1] (List.replicate (j + p + n) 3 ++ 1 :: (Mid ++ 1 :: List.replicate n 3) ++ 0 :: Z)) := by
  have h1 := pa0Scan (List.replicate j 3) (List.replicate p 3 ++ 1 :: (Mid ++ 1 :: List.replicate n 3)) Z
    (sym4_rep j 3 (by simp [ALL])) (by simp only [NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB, hM]) hZ
  have h2 := paLoop Mid Z hM hZ n (j + p) 0
  simp only [Nat.zero_add] at h2
  have h3 := paEnd Mid Z hM hZ (j + p + n) n
  refine (h1.of_eq (by simp) rfl).trans (((h2.of_eq ?_ rfl)).trans h3)
  simp [← List.append_assoc, List.replicate_append_replicate]

end ZP.NTT
