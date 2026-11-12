module

public import ZP.MMJ
public import ZP.MMRBLoop

@[expose] public section

/-! The rewind loop RS: the hole slides through the bits up to `Ms`, then `G1`. -/

namespace ZP.Mul.MM

open ZP

theorem rsLoop :
    ∀ (X : List Nat), Bits X → ∀ (Lq : List Nat), Sym4 Lq → ∀ (R : List Nat), Sym4 R →
      zmmLogic.Reach (hdR QMM.RS1 Lq (0 :: (X ++ 1 :: R)))
        (hd QMM.G1 (Lq ++ X ++ [0]) (1 :: R)) := by
  intro X
  induction X with
  | nil =>
    intro _ Lq hL R hR
    simpa using rsEnd Lq R hL hR
  | cons x X ih =>
    intro hX Lq hL R hR
    have hx : x ∈ bits := hX x (by simp)
    have hX' : Bits X := fun a ha => hX a (by simp [ha])
    have hL' : Sym4 (Lq ++ [x]) :=
      Sym4.app hL (Sym4.cons (by rcases mem_bits hx with rfl | rfl <;> simp [ALL]) Sym4.nil)
    have hs := rsStep Lq (X ++ 1 :: R) x hL (Sym4.app hX'.sym4 (Sym4.cons (by simp [ALL]) hR)) hx
    refine hs.trans ?_
    simpa using ih hX' (Lq ++ [x]) hL' R hR

end ZP.Mul.MM
