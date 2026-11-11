module

public import ZP.MMRB

@[expose] public section

/-! The RB loop: the hole slides through the bits of `B`; `M` is written at the end. -/

namespace ZP.Mul.MM

open ZP

theorem hdR_eq'' (q : Nat) (A R : List Nat) :
    hdR q A R = ⟨q, sapp A.reverse blank, sapp R blank⟩ := by
  show (⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem hd_snoc (q : Nat) (A R : List Nat) (b : Nat) :
    hd q (A ++ [b]) R = hdR q A (b :: R) := by
  rw [hd_eq', hdR_eq'']
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rfl

theorem rbLoop (L : List Nat) (hL : Sym4 L) :
    ∀ (X : List Nat), Bits X → ∀ (R : List Nat), Sym4 R →
      zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (X ++ 0 :: 1 :: R))
        (hdR QMM.RS1 (L ++ (X ++ [1, 0, 1])) R) := by
  intro X
  induction X generalizing L with
  | nil =>
    intro _ R hR
    exact rbEnd L R hL hR
  | cons x X ih =>
    intro hX R hR
    have hx : x = 2 ∨ x = 3 := mem_bits (hX x (by simp))
    have hX' : Bits X := fun a ha => hX a (by simp [ha])
    have hL' : Sym4 (L ++ [x]) :=
      Sym4.app hL (Sym4.cons (by rcases hx with rfl | rfl <;> simp [ALL]) Sym4.nil)
    have hs : zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (x :: (X ++ 0 :: 1 :: R)))
        (hd QMM.RB1 (L ++ [x] ++ [0]) (X ++ 0 :: 1 :: R)) := by
      rw [hd_snoc QMM.RB1 (L ++ [x]) (X ++ 0 :: 1 :: R) 0]
      rcases hx with rfl | rfl
      · exact rbStep0 L _ hL (Sym4.app hX'.sym4 (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hR)))
      · exact rbStep1 L _ hL (Sym4.app hX'.sym4 (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hR)))
    refine hs.trans ?_
    have := ih (L ++ [x]) hL' hX' R hR
    simpa using this

end ZP.Mul.MM
