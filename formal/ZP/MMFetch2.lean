module

public import ZP.MMLoops

@[expose] public section

/-! Fetch after a B row: `toFA` (G1, GA), and the cases of FA.

Ascending (Lean) layout at `G1` after `rsLoop`:
`F0 ++ 0 :: Bd ++ [1]` (below: A side, boundary, rest of B, `P`, done part of B, `Mr`),
then the accumulator `X ++ [0]` (the hole at the top), then `Ms = 1`, then `out`. -/

namespace ZP.Mul.MM

open ZP

theorem g1Loop (X : List Nat) (hX : ∀ a ∈ X, a = 0 ∨ a = 2 ∨ a = 3) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.G1 (L ++ X) R) (hd QMM.G1 L (X ++ R)) :=
  fLoop QMM.G1 (fun c => c = 0 ∨ c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl | rfl
      · exact g1Step0 L R hL hR
      · exact g1Step2 L R hL hR
      · exact g1Step3 L R hL hR)
    X hX L R hL hR

theorem gaLoop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.GA (L ++ X) R) (hd QMM.GA L (X ++ R)) :=
  fLoop QMM.GA (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact gaStep2 L R hL hR
      · exact gaStep3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

theorem g2Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.G2 (L ++ X) R) (hd QMM.G2 L (X ++ R)) :=
  fLoop QMM.G2 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact g2Step2 L R hL hR
      · exact g2Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

/-- From the end of `rsLoop` to `FA` (the cell below `P`). -/
theorem toFA (F0 Bd X R0 : List Nat) (hF : Sym4 F0) (hBd : Bits Bd) (hX : Bits X) (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.G1 (F0 ++ 0 :: Bd ++ [1] ++ X ++ [0]) (1 :: R0))
      (hd QMM.FA F0 (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0)) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hL1 : Sym4 (F0 ++ 0 :: Bd ++ [1]) :=
    Sym4.app (Sym4.app hF (Sym4.cons h0 hBd.sym4)) (Sym4.cons h1 Sym4.nil)
  have hXa : ∀ a ∈ X ++ [0], a = 0 ∨ a = 2 ∨ a = 3 := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · rcases mem_bits (hX a ha) with rfl | rfl <;> simp
    · simp [ha]
  have hXs : Sym4 (X ++ [0]) := Sym4.app hX.sym4 (Sym4.cons h0 Sym4.nil)
  have hR1 : Sym4 (1 :: R0) := Sym4.cons h1 hR
  have s1 := g1Loop (X ++ [0]) hXa (F0 ++ 0 :: Bd ++ [1]) (1 :: R0) hL1 hR1
  have hL2 : Sym4 (F0 ++ 0 :: Bd) := Sym4.app hF (Sym4.cons h0 hBd.sym4)
  have hR2 : Sym4 ((X ++ [0]) ++ 1 :: R0) := Sym4.app hXs hR1
  have s2 := g1End (F0 ++ 0 :: Bd) ((X ++ [0]) ++ 1 :: R0) hL2 hR2
  have hL3 : Sym4 (F0 ++ [0]) := Sym4.app hF (Sym4.cons h0 Sym4.nil)
  have hR3 : Sym4 (1 :: ((X ++ [0]) ++ 1 :: R0)) := Sym4.cons h1 hR2
  have s3 := gaLoop Bd hBd (F0 ++ [0]) _ hL3 hR3
  have s4 := gaEnd F0 (Bd ++ 1 :: ((X ++ [0]) ++ 1 :: R0)) hF (Sym4.app hBd.sym4 hR3)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s1 s2 s3 s4 ⊢
  exact s1.trans (s2.trans (s3.trans s4))

end ZP.Mul.MM
