module

public import ZP.PairPolyDec

@[expose] public section

/-!
# Successors of a pair

The beep (`K + 1`), the wrong answer (`a + 1`, `s := 0^n`) and the correct answer (`s + 1`, or `n + 1`
with `a := ''`).
-/

namespace ZP.Poly

open ZP

/-! ## `K + 1` after a beep -/

/-- K + 1 (a `0` became `1`): skip to `M_1`, erase everything right of it, write `M_a`. -/
theorem j2End (Z : List Nat) (Kr : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hKr : Bits Kr) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.J2 (Z) (Kr ++ (1 :: (b :: (X))))) (hdR Q.GRB (Z ++ (Kr ++ (1 :: ([1])))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, Kr, X] := Valid.cons hZ (Valid.cons hKr (Valid.cons hX (Valid.nil _)))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1 (carry out): `M_1` moves right, erase the rest, write `M_a`. -/
theorem jov2End (Z : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR Q.JOV2 (Z) (b :: (X))) (hdR Q.GRB (Z ++ (1 :: ([1]))) ([])) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 7) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: a `0` becomes `1`. -/
theorem kinc0 (Z : List Nat) (Kr : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hKr : Bits Kr) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (2 :: (Kr ++ (1 :: (b :: (X)))))) (hdR Q.GRB (Z ++ (3 :: (Kr ++ (1 :: ([1]))))) ([])) := by
  have hV : Valid [ALL, bits, NB] [Z, Kr, X] := Valid.cons hZ (Valid.cons hKr (Valid.cons hX (Valid.nil _)))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, Kr, X]) (E := []) (k := 10) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
          (ls' := [.blk 0 .id, .sym 3, .blk 1 .id, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: the carry leaves `K`. -/
theorem kincOv (Z : List Nat) (X : List Nat) (b : Nat) (hZ : Sym4 Z) (hX : NoB X) (hb : b ∈ NB) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (1 :: (b :: (X)))) (hdR Q.GRB (Z ++ (2 :: (1 :: ([1])))) ([])) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  rcases (show b = 1 ∨ b = 2 ∨ b = 3 by simpa [NB] using hb) with rfl | rfl | rfl
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 2, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Z, X]) (E := []) (k := 8) hV trivial
          (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 3, .blk 1 .id])
          (ls' := [.blk 0 .id, .sym 2, .sym 1, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- K + 1: a `1` becomes `0`, carry. -/
theorem kinc1 (Z : List Nat) (R : List Nat) (hZ : Sym4 Z) (hR : Sym4 R) :
    zppolyLogic.Reach (hdR QPoly.KINC (Z) (3 :: (R))) (hdR QPoly.KINC (Z ++ ([2])) (R)) := by
  have hV : Valid [ALL, ALL] [Z, R] := Valid.cons hZ (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [Z, R]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
        (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem beepStep3 (Z R : List Nat) :
    zppolyLogic.zstep (hdR QPoly.BEEPX Z (3 :: R)) = some (hdR QPoly.KINC (Z ++ [2]) R) := by
  have e1 : (⟨QPoly.BEEPX, [Item.blk 0 .id].reverse, [.sym 3, .blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR QPoly.BEEPX Z (3 :: R) := den_tapeR (by osimp) (by osimp)
  have e2 : (⟨QPoly.KINC, [Item.blk 0 .id, .sym 2].reverse, [.blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR QPoly.KINC (Z ++ [2]) R := den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

theorem beepStep2 (Z R : List Nat) :
    zppolyLogic.zstep (hdR QPoly.BEEPX Z (2 :: R)) = some (hdR QPoly.J2 (Z ++ [3]) R) := by
  have e1 : (⟨QPoly.BEEPX, [Item.blk 0 .id].reverse, [.sym 2, .blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR QPoly.BEEPX Z (2 :: R) := den_tapeR (by osimp) (by osimp)
  have e2 : (⟨QPoly.J2, [Item.blk 0 .id, .sym 3].reverse, [.blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR QPoly.J2 (Z ++ [3]) R := den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

theorem beepStep1 (Z R : List Nat) :
    zppolyLogic.zstep (hdR QPoly.BEEPX Z (1 :: R)) = some (hdR Q.JOV2 (Z ++ [2]) R) := by
  have e1 : (⟨QPoly.BEEPX, [Item.blk 0 .id].reverse, [.sym 1, .blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR QPoly.BEEPX Z (1 :: R) := den_tapeR (by osimp) (by osimp)
  have e2 : (⟨Q.JOV2, [Item.blk 0 .id, .sym 2].reverse, [.blk 1 .id], false⟩ : SC).den [Z, R] =
      hdR Q.JOV2 (Z ++ [2]) R := den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

/-- The carry loop of `K + 1`. -/
theorem kincL (Y : List Nat) (hY : NoB Y) (hYne : Y ≠ []) : ∀ (r : List Bool) (Z : List Nat), Sym4 Z →
    zppolyLogic.Reach (hdR QPoly.KINC Z (bitsOf r ++ 1 :: Y))
      (hdR Q.GRB (Z ++ (bitsOf (incR r) ++ [1, 1])) [])
  | r, Z, hZ => by
    obtain ⟨b, X, rfl⟩ : ∃ b X, Y = b :: X := by
      cases Y with
      | nil => exact absurd rfl hYne
      | cons b X => exact ⟨b, X, rfl⟩
    have hb : b ∈ NB := hY b (List.mem_cons_self ..)
    have hX : NoB X := fun x hx => hY x (List.mem_cons_of_mem _ hx)
    induction r generalizing Z with
    | nil => simpa [bitsOf, incR] using kincOv Z X b hZ hX hb
    | cons c r ih =>
      cases c with
      | false =>
        have := kinc0 Z (bitsOf r) X b hZ (Bits.ofB r) hX hb
        simpa [bitsOf, incR] using this
      | true =>
        have h1 := kinc1 Z (bitsOf r ++ 1 :: b :: X) hZ (Sym4.app (Bits.ofB r).sym4
          (Sym4.cons (by simp [ALL]) (NoB.sym4 hY)))
        have h2 := ih (Z ++ [2]) (Sym4.app hZ (Sym4.cons (by simp [ALL]) Sym4.nil))
        simp only [bitsOf, List.map_cons, if_true] at h1 h2 ⊢
        simpa [incR] using h1.trans h2

/-- After a beep: one step, then `K + 1`, `a = ''`, `s = ''`. -/
theorem beepK (r : List Bool) (Z Y : List Nat) (hZ : Sym4 Z) (hY : NoB Y) (hYne : Y ≠ []) :
    ∃ c2, zppolyLogic.zstep (hdR QPoly.BEEPX Z (bitsOf r ++ 1 :: Y)) = some c2 ∧
      zppolyLogic.Reach c2 (hdR Q.GRB (Z ++ (bitsOf (incR r) ++ [1, 1])) []) := by
  obtain ⟨b, X, rfl⟩ : ∃ b X, Y = b :: X := by
    cases Y with
    | nil => exact absurd rfl hYne
    | cons b X => exact ⟨b, X, rfl⟩
  have hb : b ∈ NB := hY b (List.mem_cons_self ..)
  have hX : NoB X := fun x hx => hY x (List.mem_cons_of_mem _ hx)
  cases r with
  | nil =>
    refine ⟨_, beepStep1 Z (b :: X), ?_⟩
    simpa [bitsOf, incR] using jov2End (Z ++ [2]) X b (Sym4.app hZ (Sym4.cons (by simp [ALL]) Sym4.nil)) hX hb
  | cons c r =>
    cases c with
    | false =>
      refine ⟨_, beepStep2 Z (bitsOf r ++ 1 :: b :: X), ?_⟩
      simpa [bitsOf, incR] using j2End (Z ++ [3]) (bitsOf r) X b
        (Sym4.app hZ (Sym4.cons (by simp [ALL]) Sym4.nil)) (Bits.ofB r) hX hb
    | true =>
      refine ⟨_, beepStep3 Z (bitsOf r ++ 1 :: b :: X), ?_⟩
      have := kincL (b :: X) hY (by simp) r (Z ++ [2])
        (Sym4.app hZ (Sym4.cons (by simp [ALL]) Sym4.nil))
      simpa [bitsOf, incR] using this

end ZP.Poly
