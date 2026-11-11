module

public import ZP.PairPolySucc

@[expose] public section

/-!
# One pair, at the level of lists

`layP (bitsOf rK) (bitsOf Pb) (bitsOf Sb)` goes to the next configuration: after a beep `K + 1`,
after a wrong answer `a + 1`, after a correct one `s + 1` or `n + 1`.
-/

namespace ZP.Poly

open ZP

/-- Wrong answer (truth flag `1`): erase the fuel, back to `s`. -/
theorem dBad0E (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.EAs (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: ([2])))))))) (3 :: (1 :: (Fu)))) (hd QPoly.ZS (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 9) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem incR_ones : ∀ r : List Bool, (∀ x ∈ r, x = true) → incR r = List.replicate (r.length + 1) false
  | [], _ => rfl
  | c :: r, h => by
    have hc : c = true := h c (List.mem_cons_self ..)
    subst hc
    have := incR_ones r (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [incR, this, List.replicate_succ]

theorem bitsOf_rep_false (k : Nat) : bitsOf (List.replicate k false).reverse = List.replicate k 2 := by
  simp [bitsOf, List.map_replicate]

/-- Wrong answer: `a + 1`. -/
theorem wrongStep (Kr : List Nat) (hKr : Bits Kr) (r : List Bool) (n : Nat) :
    zppolyLogic.Reach (hd Q.SINC (1 :: (Kr ++ 1 :: bitsOf r.reverse)) (1 :: List.replicate n 2))
      (layP Kr (bitsOf (incR r).reverse) (List.replicate n 2)) := by
  by_cases h : false ∈ r
  · have hA : NoB (1 :: Kr) := NoB.cons one_nb hKr.noB
    have hT : NoB (1 :: List.replicate n 2) := NoB.cons one_nb (z2_noB (rep_z2 n))
    have h1 := sincNo (1 :: Kr) (1 :: List.replicate n 2) hA hT r 0 h
    refine (h1.of_eq (by simp) ?_)
    unfold layP
    simp
  · have hr : ∀ x ∈ r, x = true := by
      intro x hx
      cases x with
      | false => exact absurd hx h
      | true => rfl
    have h1 := wrongOv Kr hKr r hr n
    rw [incR_ones r hr, bitsOf_rep_false]
    exact h1

/-- Correct answer, `s + 1` without overflow. -/
theorem correctNext (Kr a : List Nat) (hKr : Bits Kr) (ha : Bits a) (r : List Bool) (h : false ∈ r) :
    zppolyLogic.Reach (hd Q.SINC (1 :: (Kr ++ 1 :: (a ++ 1 :: bitsOf r.reverse))) [])
      (layP Kr a (bitsOf (incR r).reverse)) := by
  have hA : NoB (1 :: (Kr ++ 1 :: a)) :=
    NoB.cons one_nb (hKr.noB.app (NoB.cons one_nb ha.noB))
  have h1 := sincNo (1 :: (Kr ++ 1 :: a)) [] hA NoB.nil r 0 h
  exact h1.of_eq (by simp) (by unfold layP; simp)

/-- Correct answer, `s` all ones: `n + 1` and `a := ''`. -/
theorem correctCarry (Kr a : List Nat) (hKr : Bits Kr) (ha : Bits a) (r : List Bool)
    (h : ∀ x ∈ r, x = true) :
    zppolyLogic.Reach (hd Q.SINC (1 :: (Kr ++ 1 :: (a ++ 1 :: bitsOf r.reverse))) [])
      (layP Kr [] (List.replicate (r.length + 1) 2)) := by
  have hA : NoB (1 :: (Kr ++ 1 :: a)) :=
    NoB.cons one_nb (hKr.noB.app (NoB.cons one_nb ha.noB))
  have h1 := sincOvC (1 :: (Kr ++ 1 :: a)) hA r 0 h
  have h2 := dlDone Kr a r.length hKr ha
  exact (h1.of_eq (by simp) (by simp)).trans h2

theorem beepStepP (Kr a s Y : List Nat) :
    zppolyLogic.zstep (hd Q.BEEP (1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: [1])))) Y) =
      some (hdR Q.EAs (1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: [2])))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1].reverse,
      [.blk 3 .id], true⟩ : SC).den [Kr, a, s, Y] =
      hd Q.BEEP (1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: [1])))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2].reverse,
      [.blk 3 .id], false⟩ : SC).den [Kr, a, s, Y] =
      hdR Q.EAs (1 :: (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: [2])))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

/-- A wrong answer: from the decider's outcome back to `ZS`. -/
theorem dispWrong (Kr a s Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu)
    (b : Bool) :
    zppolyLogic.Reach
      (hdR (dpOf (bn (!b))) [1] (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (tflag b ++ 1 :: Fu)))))
      (hd QPoly.ZS (1 :: (Kr ++ 1 :: (a ++ 1 :: s))) []) := by
  cases b
  · have h2 := LTM.Reach.step (M := zppolyLogic) (by show Q.BEEP ≠ zppolyLogic.beep; decide +kernel) (beepStepP Kr a s (1 :: Fu)) (LTM.Reach.refl _ _)
    refine ((dBad1 Kr a s Fu hKr ha hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl).trans
      (h2.trans (dBad1E Kr a s Fu hKr ha hs hFu))
  · have h2 := LTM.Reach.step (M := zppolyLogic) (by show Q.BEEP ≠ zppolyLogic.beep; decide +kernel) (beepStepP Kr a s (3 :: 1 :: Fu)) (LTM.Reach.refl _ _)
    refine ((dBad0 Kr a s Fu hKr ha hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl).trans
      (h2.trans (dBad0E Kr a s Fu hKr ha hs hFu))

/-- A correct answer: from the decider's outcome to `SINC` on `s`. -/
theorem dispOk (Kr a s Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu)
    (b : Bool) :
    zppolyLogic.Reach
      (hdR (dpOf (bn b)) [1] (Kr ++ 1 :: (a ++ 1 :: (s ++ 1 :: 1 :: (tflag b ++ 1 :: Fu)))))
      (hd Q.SINC (1 :: (Kr ++ 1 :: (a ++ 1 :: s))) []) := by
  cases b
  · exact (dOk0 Kr a s Fu hKr ha hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
  · exact (dOk1 Kr a s Fu hKr ha hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl

end ZP.Poly
