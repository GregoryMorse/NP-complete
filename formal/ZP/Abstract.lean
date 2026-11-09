module

public import ZP.Defs

@[expose] public section

/-!
# Layer L4: the abstract program beeps finitely often iff `Sentence`

The abstract program of docs/spec.md §1.5 walks through pairs `(J, S)`, starting at
`(1, 1)`. If `J` is correct on `S` it moves to `(J, S + 1)`. Otherwise it beeps and
moves to `(J + 1, 1)`.
-/

namespace ZP

/-- `C J S`: candidate `J` is correct on instance `S`. -/
def SentenceC (C : Nat → Nat → Prop) : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → C J S


def absStepC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] (p : Nat × Nat) : Nat × Nat :=
  if C p.1 p.2 then (p.1, p.2 + 1) else (p.1 + 1, 1)

def absStateC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] : Nat → Nat × Nat
  | 0 => (1, 1)
  | k + 1 => absStepC C (absStateC C k)

/-- The abstract program beeps at step `k` iff `¬ C (absStateC C k)`. -/
def AbstractQuasihaltsC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] : Prop :=
  ∃ N, ∀ k, N ≤ k → C (absStateC C k).1 (absStateC C k).2

variable {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)]

theorem absStepC_pos {p : Nat × Nat} (h : C p.1 p.2) : absStepC C p = (p.1, p.2 + 1) := by
  simp [absStepC, h]

theorem absStepC_neg {p : Nat × Nat} (h : ¬ C p.1 p.2) : absStepC C p = (p.1 + 1, 1) := by
  simp [absStepC, h]

/-- Invariant: `J, S ≥ 1`, and the current `J` is correct on every earlier instance. -/
theorem absStateC_inv (k : Nat) :
    1 ≤ (absStateC C k).1 ∧ 1 ≤ (absStateC C k).2 ∧
      ∀ S', 1 ≤ S' → S' < (absStateC C k).2 → C (absStateC C k).1 S' := by
  induction k with
  | zero => exact ⟨Nat.le_refl 1, Nat.le_refl 1, fun S' h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl 1)⟩
  | succ k ih =>
    obtain ⟨hJ, hS, hc⟩ := ih
    show 1 ≤ (absStepC C (absStateC C k)).1 ∧ 1 ≤ (absStepC C (absStateC C k)).2 ∧
      ∀ S', 1 ≤ S' → S' < (absStepC C (absStateC C k)).2 → C (absStepC C (absStateC C k)).1 S'
    by_cases h : C (absStateC C k).1 (absStateC C k).2
    · rw [absStepC_pos h]
      refine ⟨hJ, Nat.le_succ_of_le hS, fun S' h1 h2 => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h3 | h3
      · exact hc S' h1 h3
      · rw [h3]; exact h
    · rw [absStepC_neg h]
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.le_refl 1,
        fun S' h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl 1)⟩

theorem absStateC_fst_mono (k m : Nat) : (absStateC C k).1 ≤ (absStateC C (k + m)).1 := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    show (absStateC C k).1 ≤ (absStepC C (absStateC C (k + m))).1
    by_cases h : C (absStateC C (k + m)).1 (absStateC C (k + m)).2
    · rw [absStepC_pos h]; exact ih
    · rw [absStepC_neg h]; exact Nat.le_succ_of_le ih

/-- The abstract program quasihalts iff the Σ₂ sentence holds. -/
theorem abstractQuasihaltsC_iff : AbstractQuasihaltsC C ↔ SentenceC C := by
  constructor
  · rintro ⟨N, hN⟩
    -- from step N on, J is fixed and S counts up
    have hrun : ∀ m, absStateC C (N + m) = ((absStateC C N).1, (absStateC C N).2 + m) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        show absStepC C (absStateC C (N + m)) = _
        have hc := hN (N + m) (Nat.le_add_right N m)
        rw [absStepC_pos hc, ih]
        rfl
    obtain ⟨hJ, hS, hc⟩ := absStateC_inv (C := C) N
    refine ⟨(absStateC C N).1, hJ, fun S h1 => ?_⟩
    by_cases hlt : S < (absStateC C N).2
    · exact hc S h1 hlt
    · have hm : S = (absStateC C N).2 + (S - (absStateC C N).2) := by omega
      have := hN (N + (S - (absStateC C N).2)) (Nat.le_add_right _ _)
      rw [hrun] at this
      rw [hm]
      exact this
  · rintro ⟨Js, hJs1, hJs⟩
    -- J never passes the correct candidate Js
    have hle : ∀ k, (absStateC C k).1 ≤ Js := by
      intro k
      induction k with
      | zero => exact hJs1
      | succ k ih =>
        show (absStepC C (absStateC C k)).1 ≤ Js
        by_cases h : C (absStateC C k).1 (absStateC C k).2
        · rw [absStepC_pos h]; exact ih
        · rw [absStepC_neg h]
          have hne : (absStateC C k).1 ≠ Js := by
            intro he
            apply h
            rw [he]
            exact hJs _ (absStateC_inv (C := C) k).2.1
          show (absStateC C k).1 + 1 ≤ Js
          omega
    -- induction on the gap Js - J
    have key : ∀ g k, Js - (absStateC C k).1 ≤ g →
        ∃ N, ∀ k', N ≤ k' → C (absStateC C k').1 (absStateC C k').2 := by
      intro g
      induction g with
      | zero =>
        intro k hk
        refine ⟨k, fun k' hk' => Classical.byContradiction fun hbad => ?_⟩
        have h1 := absStateC_fst_mono (C := C) k (k' - k)
        have h2 : k + (k' - k) = k' := by omega
        rw [h2] at h1
        have h3 : (absStateC C (k' + 1)).1 = (absStateC C k').1 + 1 := by
          show (absStepC C (absStateC C k')).1 = _
          rw [absStepC_neg hbad]
        have h4 := hle (k' + 1)
        omega
      | succ g ih =>
        intro k hk
        by_cases hex : ∃ k', k ≤ k' ∧ ¬ C (absStateC C k').1 (absStateC C k').2
        · obtain ⟨k', hk', hbad⟩ := hex
          apply ih (k' + 1)
          have h1 := absStateC_fst_mono (C := C) k (k' - k)
          have h2 : k + (k' - k) = k' := by omega
          rw [h2] at h1
          have h3 : (absStateC C (k' + 1)).1 = (absStateC C k').1 + 1 := by
            show (absStepC C (absStateC C k')).1 = _
            rw [absStepC_neg hbad]
          have h4 := hle (k' + 1)
          omega
        · exact ⟨k, fun k' hk' => Classical.byContradiction fun hbad => hex ⟨k', hk', hbad⟩⟩
    exact key Js 0 (Nat.sub_le _ _)


/-! ## The original instance -/

abbrev absStep : Nat × Nat → Nat × Nat := absStepC Correct
abbrev absState : Nat → Nat × Nat := absStateC Correct
abbrev AbstractQuasihalts : Prop := AbstractQuasihaltsC Correct

theorem absStep_pos {p : Nat × Nat} (h : Correct p.1 p.2) : absStep p = (p.1, p.2 + 1) :=
  absStepC_pos h
theorem absStep_neg {p : Nat × Nat} (h : ¬ Correct p.1 p.2) : absStep p = (p.1 + 1, 1) :=
  absStepC_neg h
theorem absState_inv (k : Nat) :
    1 ≤ (absState k).1 ∧ 1 ≤ (absState k).2 ∧
      ∀ S', 1 ≤ S' → S' < (absState k).2 → Correct (absState k).1 S' := absStateC_inv k
theorem absState_fst_mono (k m : Nat) : (absState k).1 ≤ (absState (k + m)).1 :=
  absStateC_fst_mono k m
theorem abstractQuasihalts_iff_sentence : AbstractQuasihalts ↔ Sentence :=
  abstractQuasihaltsC_iff

end ZP
