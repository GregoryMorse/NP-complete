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


/-! ## Incrementing `s` and `a` -/

/-- Wrong answer: `s := 0^n`, back to the last cell of `a`. -/
theorem zsSweep (Z : List Nat) (s : List Nat) (hZ : Sym4 Z) (hs : Bits s) :
    zppolyLogic.Reach (hd QPoly.ZS (Z ++ (1 :: (s))) ([])) (hd Q.SINC (Z) (1 :: (List.replicate s.length 2))) := by
  have hV : Valid [ALL, bits] [Z, s] := Valid.cons hZ (Valid.cons hs (Valid.nil _))
  exact checkTT (env := [Z, s]) (E := []) (k := 2) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
        (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 2)])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Correct, `s` all ones: the carry reaches `M_a`, a `0` is appended, back to `a`. -/
theorem cOvA (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N)) (hd QPoly.DL1 (Z) (1 :: (N ++ ([2])))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTT (env := [Z, N]) (E := []) (k := 5) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
        (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .sym 2])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Overflow: one cell of `a` moves to `s`. -/
theorem dlStep (Z : List Nat) (N : List Nat) (b : Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) (hb : b ∈ bits) :
    zppolyLogic.Reach (hd QPoly.DL1 (Z ++ ([b])) (1 :: (N ++ ([2])))) (hd QPoly.DL1 (Z) (1 :: (2 :: (N)))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Z, N]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .sym 2]) (rs := [.sym 1, .blk 1 .id, .sym 2])
          (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 2, .blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Z, N]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id, .sym 2])
          (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 2, .blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Overflow: `a` is empty. -/
theorem dlEnd (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd QPoly.DL1 (Z ++ ([1])) (1 :: (N ++ ([2])))) (hdR Q.GRB (Z ++ ([1])) (1 :: (N ++ ([2])))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTF (env := [Z, N]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 1, .blk 1 .id, .sym 2])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 2])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Wrong, `a` all ones: `a` grows, `s` empty. -/
theorem wOv0 (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N ++ ([1]))) (hdR Q.GRB (Z ++ (1 :: (N ++ (2 :: ([1]))))) ([])) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTF (env := [Z, N]) (E := []) (k := 4) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 1]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Wrong, `a` all ones: `a` grows, `s` is kept at length `n`. -/
theorem wOv1 (Z : List Nat) (N : List Nat) (S : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) (hS : ∀ a ∈ S, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N ++ (1 :: (2 :: (S))))) (hdR Q.GRB (Z ++ (1 :: (N ++ (2 :: (1 :: (S ++ ([2]))))))) ([])) := by
  have hV : Valid [ALL, Z2, Z2] [Z, N, S] := Valid.cons hZ (Valid.cons hN (Valid.cons hS (Valid.nil _)))
  exact checkTF (env := [Z, N, S]) (E := []) (k := 6) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 1, .blk 2 .id, .sym 2]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- The carry loop of `SINC` when a `0` is met. -/
theorem sincNo (A T : List Nat) (hA : NoB A) (hT : NoB T) : ∀ (r : List Bool) (k : Nat), false ∈ r →
    zppolyLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2 ++ T))
      (hdR Q.GRB (A ++ 1 :: (bitsOf (incR r).reverse ++ (List.replicate k 2 ++ T))) [])
  | [], _, h => by simp at h
  | c :: r, k, h => by
    have hZ : NoB (List.replicate k 2 ++ T) :=
      (z2_noB (rep_z2 k)).app hT
    cases c with
    | false =>
      have h1 := sinc0 A (bitsOf r.reverse) (List.replicate k 2 ++ T) hA (Bits.ofB _) hZ
      have h2 := grbWalk (A ++ 1 :: (bitsOf r.reverse ++ [3])) (List.replicate k 2 ++ T) []
        (Sym4.app hA.sym4 (Sym4.cons (by simp [ALL]) (Sym4.app (Bits.ofB _).sym4
          (Sym4.cons (by simp [ALL]) Sym4.nil)))) hZ Sym4.nil
      simp only [List.append_nil] at h2
      have h3 := h1.trans h2
      exact h3.of_eq (by simp [bitsOf]) (by simp [incR, bitsOf])
    | true =>
      have h1 := sinc1 A (bitsOf r.reverse) (List.replicate k 2 ++ T) hA (Bits.ofB _) hZ
      have hr : false ∈ r := by
        rcases List.mem_cons.mp h with h | h
        · simp at h
        · exact h
      have h2 := sincNo A T hA hT r (k + 1) hr
      refine (h1.of_eq (by simp [bitsOf]) rfl).trans (h2.of_eq (by simp [List.replicate_succ]) ?_)
      simp [incR, bitsOf, List.replicate_succ]

/-- The carry loop of `SINC` on `s` when it overflows: `M_a` is reached, back at `a`. -/
theorem sincOvC (A : List Nat) (hA : NoB A) : ∀ (r : List Bool) (k : Nat), (∀ x ∈ r, x = true) →
    zppolyLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
      (hd QPoly.DL1 A (1 :: (List.replicate (r.length + k) 2 ++ [2])))
  | [], k, _ => by
    simpa [bitsOf] using cOvA A (List.replicate k 2) hA.sym4 (rep_z2 k)
  | c :: r, k, h => by
    have hc : c = true := h c (List.mem_cons_self ..)
    subst hc
    have h1 := sinc1 A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (z2_noB (rep_z2 k))
    have h2 := sincOvC A hA r (k + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have e : r.length + 1 + k = r.length + (k + 1) := by omega
    refine (h1.of_eq (by simp [bitsOf]) rfl).trans (h2.of_eq (by simp [List.replicate_succ]) ?_)
    simp [e]

theorem rep2_snoc (m : Nat) : List.replicate m 2 ++ [2] = List.replicate (m + 1) 2 :=
  (List.replicate_succ' ..).symm

/-- Overflow: all cells of `a` move to `s`. -/
theorem dlLoop (m : Nat) : ∀ (ar Z : List Nat), Bits ar → Sym4 Z →
    zppolyLogic.Reach (hd QPoly.DL1 (Z ++ ar.reverse) (1 :: (List.replicate m 2 ++ [2])))
      (hd QPoly.DL1 Z (1 :: (List.replicate m 2 ++ [2])))
  | [], Z, _, _ => by simpa using LTM.Reach.refl _ _
  | b :: ar, Z, hb, hZ => by
    have hZ' : Sym4 (Z ++ ar.reverse) := hZ.app (hb.tail.rev.sym4)
    have h1 := dlStep (Z ++ ar.reverse) (List.replicate m 2) b hZ' (rep_z2 m) hb.head
    have h2 := dlLoop m ar Z hb.tail hZ
    refine (h1.of_eq (by simp) ?_).trans h2
    rw [rep_snoc_eq]

theorem dlDone (Kr a : List Nat) (m : Nat) (hKr : Bits Kr) (ha : Bits a) :
    zppolyLogic.Reach (hd QPoly.DL1 (1 :: (Kr ++ 1 :: a)) (1 :: (List.replicate m 2 ++ [2])))
      (layP Kr [] (List.replicate (m + 1) 2)) := by
  have hZ0 : Sym4 (1 :: (Kr ++ [1])) :=
    Sym4.cons (by simp [ALL]) (Sym4.app hKr.sym4 (Sym4.cons (by simp [ALL]) Sym4.nil))
  have h1 := dlLoop m a.reverse (1 :: (Kr ++ [1])) ha.rev hZ0
  have h2 := dlEnd (1 :: Kr) (List.replicate m 2) (Sym4.cons (by simp [ALL]) hKr.sym4) (rep_z2 m)
  have hR : NoB (1 :: (List.replicate m 2 ++ [2])) :=
    NoB.cons one_nb ((z2_noB (rep_z2 m)).app (NoB.cons (by simp [NB]) NoB.nil))
  have h3 := grbWalk (1 :: Kr ++ [1]) (1 :: (List.replicate m 2 ++ [2])) []
    (Sym4.app (Sym4.cons (by simp [ALL]) hKr.sym4) (Sym4.cons (by simp [ALL]) Sym4.nil)) hR Sym4.nil
  simp only [List.append_nil, List.reverse_reverse] at h1 h3
  refine (h1.of_eq (by simp) rfl).trans (h2.trans (h3.of_eq rfl ?_))
  unfold layP
  rw [rep2_snoc]
  simp

/-- The carry loop of `SINC` on `a` when it overflows: back at `M_1`, `a` is all `0`. -/
theorem sincOvW (A T : List Nat) (hA : NoB A) (hT : NoB T) : ∀ (r : List Bool) (k : Nat),
    (∀ x ∈ r, x = true) →
    zppolyLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2 ++ T))
      (hd Q.SINC (A ++ [1]) (List.replicate (r.length + k) 2 ++ T))
  | [], k, _ => by simpa [bitsOf] using LTM.Reach.refl _ _
  | c :: r, k, h => by
    have hc : c = true := h c (List.mem_cons_self ..)
    subst hc
    have hZ : NoB (List.replicate k 2 ++ T) := (z2_noB (rep_z2 k)).app hT
    have h1 := sinc1 A (bitsOf r.reverse) (List.replicate k 2 ++ T) hA (Bits.ofB _) hZ
    have h2 := sincOvW A T hA hT r (k + 1) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have e : r.length + 1 + k = r.length + (k + 1) := by omega
    refine (h1.of_eq (by simp [bitsOf]) rfl).trans (h2.of_eq (by simp [List.replicate_succ]) ?_)
    simp [e]

/-- Wrong answer with `a` all ones: `a` grows by one cell, `s` keeps its length. -/
theorem wrongOv (Kr : List Nat) (hKr : Bits Kr) (r : List Bool) (hr : ∀ x ∈ r, x = true) (n : Nat) :
    zppolyLogic.Reach (hd Q.SINC (1 :: (Kr ++ 1 :: bitsOf r.reverse)) (1 :: List.replicate n 2))
      (layP Kr (List.replicate (r.length + 1) 2) (List.replicate n 2)) := by
  have hA : NoB (1 :: Kr) := NoB.cons one_nb hKr.noB
  have hT : NoB (1 :: List.replicate n 2) := NoB.cons one_nb (z2_noB (rep_z2 n))
  have h1 := sincOvW (1 :: Kr) (1 :: List.replicate n 2) hA hT r 0 hr
  have hZ : Sym4 (1 :: Kr) := hA.sym4
  have h1' : zppolyLogic.Reach (hd Q.SINC (1 :: (Kr ++ 1 :: bitsOf r.reverse)) (1 :: List.replicate n 2))
      (hd Q.SINC (1 :: (Kr ++ [1])) (List.replicate r.length 2 ++ 1 :: List.replicate n 2)) := by
    simpa using h1
  cases n with
  | zero =>
    have h2 := wOv0 (1 :: Kr) (List.replicate r.length 2) hZ (rep_z2 _)
    have h2' : zppolyLogic.Reach
        (hd Q.SINC (1 :: (Kr ++ [1])) (List.replicate r.length 2 ++ 1 :: List.replicate 0 2))
        (layP Kr (List.replicate (r.length + 1) 2) (List.replicate 0 2)) :=
      h2.of_eq (by simp) (by unfold layP; rw [← rep2_snoc]; simp)
    exact h1'.trans h2'
  | succ n =>
    have h2 := wOv1 (1 :: Kr) (List.replicate r.length 2) (List.replicate n 2) hZ (rep_z2 _) (rep_z2 _)
    have h2' : zppolyLogic.Reach
        (hd Q.SINC (1 :: (Kr ++ [1])) (List.replicate r.length 2 ++ 1 :: List.replicate (n + 1) 2))
        (layP Kr (List.replicate (r.length + 1) 2) (List.replicate (n + 1) 2)) :=
      h2.of_eq (by simp [List.replicate_succ])
        (by unfold layP; rw [← rep2_snoc, ← rep2_snoc n]; simp)
    exact h1'.trans h2'

end ZP.Poly
