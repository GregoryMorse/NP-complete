module

public import ZP.MMFetch
public import ZP.MMRBLoop

@[expose] public section

/-! Generic pass loops (F: toward lower indices, K: toward higher) and their instances. -/

namespace ZP.Mul.MM

open ZP

theorem fLoopRev (q : Nat) (S : Nat → Prop) (hS : ∀ c, S c → c ∈ ALL)
    (step : ∀ L R c, Sym4 L → Sym4 R → S c → zmmLogic.Reach (hd q (L ++ [c]) R) (hd q L (c :: R))) :
    ∀ (Y : List Nat), (∀ a ∈ Y, S a) → ∀ L R, Sym4 L → Sym4 R →
      zmmLogic.Reach (hd q (L ++ Y.reverse) R) (hd q L (Y.reverse ++ R)) := by
  intro Y
  induction Y with
  | nil =>
    intro _ L R _ _
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | cons y Y ih =>
    intro hY L R hL hR
    have hy : S y := hY y (by simp)
    have hY' : ∀ a ∈ Y, S a := fun a ha => hY a (by simp [ha])
    have hL' : Sym4 (L ++ Y.reverse) :=
      Sym4.app hL (fun b hb => hS b (hY' b (by simpa using hb)))
    have h1 := step (L ++ Y.reverse) R y hL' hR hy
    have h2 := ih hY' L (y :: R) hL (Sym4.cons (hS y hy) hR)
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

theorem fLoop (q : Nat) (S : Nat → Prop) (hS : ∀ c, S c → c ∈ ALL)
    (step : ∀ L R c, Sym4 L → Sym4 R → S c → zmmLogic.Reach (hd q (L ++ [c]) R) (hd q L (c :: R)))
    (X : List Nat) (hX : ∀ a ∈ X, S a) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd q (L ++ X) R) (hd q L (X ++ R)) := by
  have := fLoopRev q S hS step X.reverse (fun a ha => hX a (by simpa using ha)) L R hL hR
  simpa using this

theorem kLoop (q : Nat) (S : Nat → Prop) (hS : ∀ c, S c → c ∈ ALL)
    (step : ∀ L R c, Sym4 L → Sym4 R → S c → zmmLogic.Reach (hd q (L ++ [c]) R) (hdR q (L ++ [c]) R)) :
    ∀ (X : List Nat), (∀ a ∈ X, S a) → ∀ L R, Sym4 L → Sym4 R →
      zmmLogic.Reach (hdR q L (X ++ R)) (hdR q (L ++ X) R) := by
  intro X
  induction X with
  | nil =>
    intro _ L R _ _
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | cons x X ih =>
    intro hX L R hL hR
    have hx : S x := hX x (by simp)
    have hX' : ∀ a ∈ X, S a := fun a ha => hX a (by simp [ha])
    have hL' : Sym4 (L ++ [x]) := Sym4.app hL (Sym4.cons (hS x hx) Sym4.nil)
    have hR' : Sym4 (X ++ R) := Sym4.app (fun b hb => hS b (hX' b hb)) hR
    have h1 := step L (X ++ R) x hL hR' hx
    have e : hdR q L ((x :: X) ++ R) = hd q (L ++ [x]) (X ++ R) := (hd_snoc q L (X ++ R) x).symm
    rw [e]
    have h2 := ih hX' (L ++ [x]) R hL' hR
    simp only [List.cons_append, List.append_assoc, List.nil_append, List.singleton_append] at h2 ⊢
    exact h1.trans h2

end ZP.Mul.MM
