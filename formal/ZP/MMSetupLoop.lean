module

public import ZP.MMSetup

@[expose] public section

/-! The SM loop of the setup: `w` shifts by one cell and `M` (`Mr`) is written in front. -/

namespace ZP.Mul.MM

open ZP

theorem smLoop (L : List Nat) (hL : Sym4 L) :
    ∀ (w : List Nat), Bits w → ∀ (R : List Nat), Sym4 R → ∀ (q x : Nat),
      ((q = QMM.SM0 ∧ x = 2) ∨ (q = QMM.SM1 ∧ x = 3)) →
      zmmLogic.Reach (hd q (L ++ 0 :: w) R) (hd QMM.RB1 L (w ++ x :: R)) := by
  suffices H : ∀ n (w : List Nat), w.length = n → Bits w → ∀ (R : List Nat), Sym4 R → ∀ (q x : Nat),
      ((q = QMM.SM0 ∧ x = 2) ∨ (q = QMM.SM1 ∧ x = 3)) →
      zmmLogic.Reach (hd q (L ++ 0 :: w) R) (hd QMM.RB1 L (w ++ x :: R)) from fun w => H _ w rfl
  intro n
  induction n with
  | zero =>
    intro w hn _ R hR q x hq
    have : w = [] := List.length_eq_zero_iff.mp hn
    subst this
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact smEnd0 L R hL hR
    · exact smEnd1 L R hL hR
  | succ n ih =>
    intro w hn hw R hR q x hq
    rcases List.eq_nil_or_concat w with rfl | ⟨w', y, rfl⟩
    · simp at hn
    simp only [List.concat_eq_append] at hn hw ⊢
    have hw' : Bits w' := fun a ha => hw a (by simp [ha])
    have hy : y = 2 ∨ y = 3 := mem_bits (hw y (by simp))
    have hL' : Sym4 (L ++ 0 :: w') :=
      Sym4.app hL (Sym4.cons (by simp [ALL]) hw'.sym4)
    have hx : x = 2 ∨ x = 3 := by rcases hq with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have hR' : Sym4 (x :: R) :=
      Sym4.cons (by rcases hx with h | h <;> simp [h, ALL]) hR
    have e : L ++ 0 :: (w' ++ [y]) = (L ++ 0 :: w') ++ [y] := by simp
    rw [e]
    have e2 : (w' ++ [y]) ++ x :: R = w' ++ y :: x :: R := by simp
    rw [e2]
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hy with rfl | rfl
    · exact (smStep00 _ _ hL' hR).trans (ih w' (by simpa using hn) hw' _ hR' _ _ (Or.inl ⟨rfl, rfl⟩))
    · exact (smStep01 _ _ hL' hR).trans (ih w' (by simpa using hn) hw' _ hR' _ _ (Or.inr ⟨rfl, rfl⟩))
    · exact (smStep10 _ _ hL' hR).trans (ih w' (by simpa using hn) hw' _ hR' _ _ (Or.inl ⟨rfl, rfl⟩))
    · exact (smStep11 _ _ hL' hR).trans (ih w' (by simpa using hn) hw' _ hR' _ _ (Or.inr ⟨rfl, rfl⟩))

end ZP.Mul.MM
