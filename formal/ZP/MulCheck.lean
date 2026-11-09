module

public import ZP.PairMul
public import ZP.PairF

@[expose] public section

/-!
# Z_MUL: the output check (conversion of the output to unary numbers, then `z = x y`)
-/

namespace ZP.Mul

open ZP
open ZP.F (lyt lay1 lay1_eq lyt_noB crev crev_noB parseState crev_cons2 crev_false lay1_sym4
  numbers_eq lay1_last2 LeftEnd rep2_ext)

/-- Conversion: a pair `1 1` is consumed; the target gets its marked cell. -/
theorem dig3M (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zmulLogic.Reach (hd QMul.HPF (T ++ (1 :: (L ++ (3 :: ([3]))))) (Rt))
      (hdR QMul.DR ([2]) (T ++ (1 :: (L ++ (0 :: (0 :: (Rt))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.sym 2]) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a pair `1 0` is consumed. -/
theorem dig2M (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zmulLogic.Reach (hd QMul.HPF (T ++ (1 :: (L ++ (2 :: ([3]))))) (Rt))
      (hdR QMul.DR ([]) (T ++ (1 :: (L ++ (0 :: (0 :: (Rt))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 3]) (rs := [.blk 2 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling: one unmarked `1` is marked and a marked cell appended. -/
theorem dstepM (Z : List Nat) (X : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hX : Sym4 X) :
    zmulLogic.Reach (hdR QMul.DR (Z) (3 :: (X)))
      (hdR QMul.DR (2 :: (Z ++ ([2]))) (X)) := by
  have hV : Valid [Z2, ALL] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.sym 2, .blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling is done: unmark, back to the copy. -/
theorem dEndM (Z : List Nat) (Y : List Nat) (R : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hY : NoB Y) (hR : Sym4 R) :
    zmulLogic.Reach (hdR QMul.DR (Z) (1 :: (Y ++ (0 :: (R)))))
      (hd QMul.HPF (List.replicate Z.length 3 ++ (1 :: (Y))) (0 :: (R))) := by
  have hV : Valid [Z2, NB, ALL] [Z, Y, R] := Valid.cons hZ (Valid.cons hY (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [Z, Y, R]) (E := []) (k := 7) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 (.const 3), .sym 1, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a `0` ends the number; a new separator opens the next target. -/
theorem sepStepM (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zmulLogic.Reach (hd QMul.HPF (T ++ (1 :: (L ++ ([2])))) (Rt))
      (hd QMul.HPF (1 :: (T ++ (1 :: (L)))) (0 :: (Rt))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTT (env := [T, L, Rt]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done (the copy is used up). -/
theorem endMM (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zmulLogic.Reach (hd QMul.HPF (Lp ++ ([1])) (Rt))
      (hd QMul.mP1 (Lp) (1 :: (Rt))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done after a trailing lone `1`. -/
theorem endLoneM (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zmulLogic.Reach (hd QMul.HPF (Lp ++ (1 :: ([3]))) (Rt))
      (hd QMul.mP1 (Lp) (1 :: (0 :: (Rt)))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## The conversion loop -/

theorem dloopM (X : List Nat) (hX : Sym4 X) : ∀ u m : Nat,
    zmulLogic.Reach (hdR QMul.DR (List.replicate m 2) (List.replicate u 3 ++ X))
      (hdR QMul.DR (List.replicate (m + 2 * u) 2) X)
  | 0, m => by simpa using LTM.Reach.refl _ _
  | u + 1, m => by
    have hX' : Sym4 (List.replicate u 3 ++ X) := (Sym4.rep u 3 (by simp [ALL])).app hX
    have h1 := dstepM (List.replicate m 2) (List.replicate u 3 ++ X) (rep_z2 m) hX'
    have h2 := dloopM X hX u (m + 2)
    refine (h1.of_eq (by simp [List.replicate_succ]) (by rw [rep2_ext])).trans (h2.of_eq rfl ?_)
    congr 2
    omega

theorem digitStepM (t : Nat) (L Rt : List Nat) (hL : NoB L) (hRt : Sym4 Rt) (b : Bool) :
    zmulLogic.Reach (hd QMul.HPF (List.replicate t 3 ++ 1 :: (L ++ [ZP.bn b, 3])) Rt)
      (hd QMul.HPF (List.replicate (bitN b + 2 * t) 3 ++ 1 :: L) (0 :: 0 :: Rt)) := by
  have hX : Sym4 (1 :: (L ++ 0 :: (0 :: Rt))) :=
    Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hRt)))
  have hR2 : Sym4 (0 :: Rt) := Sym4.cons (by simp [ALL]) hRt
  cases b
  · have h1 := dig2M (List.replicate t 3) L Rt (rep_t3 t) hL hRt
    have h2 := dloopM (1 :: (L ++ 0 :: (0 :: Rt))) hX t 0
    have h3 := dEndM (List.replicate (0 + 2 * t) 2) L (0 :: Rt) (rep_z2 _) hL hR2
    refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq rfl ?_))
    simp [bitN]
  · have h1 := dig3M (List.replicate t 3) L Rt (rep_t3 t) hL hRt
    have h2 := dloopM (1 :: (L ++ 0 :: (0 :: Rt))) hX t 1
    have h3 := dEndM (List.replicate (1 + 2 * t) 2) L (0 :: Rt) (rep_z2 _) hL hR2
    refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq rfl ?_))
    simp [bitN]

theorem rep0_cons (n : Nat) (Rt : List Nat) :
    List.replicate n 0 ++ 0 :: Rt = 0 :: (List.replicate n 0 ++ Rt) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem convLoopM : ∀ (f : Nat) (r : List Bool) (cur : Nat)
    (fr : List Nat) (Rt : List Nat), Sym4 Rt → r.length ≤ f →
    zmulLogic.Reach (hd QMul.HPF (List.replicate cur 3 ++ 1 :: (lyt fr ++ crev r)) Rt)
      (hd QMul.mP1 (lay1 (parseState f r cur fr).1 (parseState f r cur fr).2)
        (1 :: (List.replicate r.length 0 ++ Rt))) := by
  intro f
  induction f with
  | zero =>
    intro r cur fr Rt hRt hf
    have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have h := endMM (lay1 cur fr) Rt (lay1_sym4 _ _) hRt
    refine h.of_eq ?_ ?_
    · simp [crev, bitsOf, lay1_eq]
    · simp [parseState]
  | succ f ih =>
    intro r cur fr Rt hRt hf
    cases r with
    | nil =>
      have h := endMM (lay1 cur fr) Rt (lay1_sym4 _ _) hRt
      refine h.of_eq ?_ ?_
      · simp [crev, bitsOf, lay1_eq]
      · simp [parseState]
    | cons x r1 =>
      cases x with
      | true =>
        cases r1 with
        | nil =>
          have h := endLoneM (lay1 cur fr) Rt (lay1_sym4 _ _) hRt
          refine h.of_eq ?_ ?_
          · have e := lay1_eq cur fr
            have e2 : List.replicate cur 3 ++ 1 :: (lyt fr ++ crev [true]) = lay1 cur fr ++ [1, 3] :=
              calc List.replicate cur 3 ++ 1 :: (lyt fr ++ crev [true])
                  = (List.replicate cur 3 ++ 1 :: lyt fr) ++ [3] := by simp [crev, bitsOf]
                _ = lay1 cur fr ++ [1, 3] := by rw [e]; simp
            rw [e2]
          · simp [parseState]
        | cons b r' =>
          have hL : NoB (lyt fr ++ crev r') := (lyt_noB fr).app (crev_noB r')
          have h1 := digitStepM cur (lyt fr ++ crev r') Rt hL hRt b
          have hR2 : Sym4 (0 :: 0 :: Rt) := Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hRt)
          have h2 := ih r' (bitN b + 2 * cur) fr (0 :: 0 :: Rt) hR2 (by simp at hf; omega)
          refine (h1.of_eq ?_ rfl).trans (h2.of_eq ?_ ?_)
          · rw [crev_cons2, List.append_assoc]
          · rfl
          · simp only [parseState, List.length_cons, List.replicate_succ, List.cons_append]
            rw [rep0_cons, rep0_cons]
      | false =>
        have hL : NoB (lyt fr ++ crev r1) := (lyt_noB fr).app (crev_noB r1)
        have h1 := sepStepM (List.replicate cur 3) (lyt fr ++ crev r1) Rt (rep_t3 cur) hL hRt
        have hR2 : Sym4 (0 :: Rt) := Sym4.cons (by simp [ALL]) hRt
        have h2 := ih r1 0 (cur :: fr) (0 :: Rt) hR2 (by simp at hf; omega)
        refine (h1.of_eq ?_ rfl).trans (h2.of_eq ?_ ?_)
        · rw [crev_false]
          simp
        · simp [lyt]
        · simp only [parseState, List.length_cons, List.replicate_succ, List.cons_append]
          rw [rep0_cons]

/-! ## The multiplication check: segments (generated) -/

/-- Skip `z` and `x`, to the last cell of `y`. -/
theorem mpToYS (W : List Nat) (Xu : List Nat) (Zu : List Nat) (R : List Nat) (hW : Sym4 W) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZu : ∀ a ∈ Zu, a ∈ T3) (hR : Sym4 R) :
    zmulLogic.Reach (hd QMul.mP1 (W ++ (1 :: (Xu ++ (1 :: (Zu))))) (R))
      (hd QMul.mYS (W) (1 :: (Xu ++ (1 :: (Zu ++ (R)))))) := by
  have hV : Valid [ALL, T3, T3, ALL] [W, Xu, Zu, R] := Valid.cons hW (Valid.cons hXu (Valid.cons hZu (Valid.cons hR (Valid.nil _))))
  exact checkTT (env := [W, Xu, Zu, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.blk 3 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Mark the next cell of `y`, go to the start of `x`. -/
theorem ysMark (W : List Nat) (Ym : List Nat) (T : List Nat) (hW : Sym4 W) (hYm : ∀ a ∈ Ym, a ∈ Z2) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mYS (W ++ (3 :: (Ym))) (1 :: (T)))
      (hdR QMul.mXS (W ++ (2 :: (Ym ++ ([1])))) (T)) := by
  have hV : Valid [ALL, Z2, ALL] [W, Ym, T] := Valid.cons hW (Valid.cons hYm (Valid.cons hT (Valid.nil _)))
  exact checkTF (env := [W, Ym, T]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One step of the inner loop: a cell of `x` and a cell of `z` are marked. -/
theorem xIter (W : List Nat) (Xm : List Nat) (Xu : List Nat) (Zm : List Nat) (Zu : List Nat) (T : List Nat) (hW : Sym4 W) (hXm : ∀ a ∈ Xm, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hZu : ∀ a ∈ Zu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hdR QMul.mXS (W ++ (1 :: (Xm))) (3 :: (Xu ++ (1 :: (Zm ++ (3 :: (Zu ++ (1 :: (T)))))))))
      (hdR QMul.mXS (W ++ (1 :: (Xm ++ ([2])))) (Xu ++ (1 :: (Zm ++ (2 :: (Zu ++ (1 :: (T)))))))) := by
  have hV : Valid [ALL, Z2, T3, Z2, T3, ALL] [W, Xm, Xu, Zm, Zu, T] := Valid.cons hW (Valid.cons hXm (Valid.cons hXu (Valid.cons hZm (Valid.cons hZu (Valid.cons hT (Valid.nil _))))))
  exact checkFF (env := [W, Xm, Xu, Zm, Zu, T]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `z` is too small. -/
theorem xSmall (W : List Nat) (Xm : List Nat) (Xu : List Nat) (Zm : List Nat) (T : List Nat) (hW : Sym4 W) (hXm : ∀ a ∈ Xm, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hT : Sym4 T) :
    zmulLogic.Reach (hdR QMul.mXS (W ++ (1 :: (Xm))) (3 :: (Xu ++ (1 :: (Zm ++ (1 :: (T)))))))
      (hdR QMul.FR0 (W ++ (1 :: (Xm ++ (2 :: (Xu ++ (1 :: (Zm ++ ([1])))))))) (T)) := by
  have hV : Valid [ALL, Z2, T3, Z2, ALL] [W, Xm, Xu, Zm, T] := Valid.cons hW (Valid.cons hXm (Valid.cons hXu (Valid.cons hZm (Valid.cons hT (Valid.nil _)))))
  exact checkFF (env := [W, Xm, Xu, Zm, T]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1]) (rs' := [.blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `x` is used up: unmark it, back to `y`. -/
theorem xDone (W : List Nat) (Xm : List Nat) (Z : List Nat) (hW : Sym4 W) (hXm : ∀ a ∈ Xm, a ∈ Z2) (hZ : Sym4 Z) :
    zmulLogic.Reach (hdR QMul.mXS (W ++ (1 :: (Xm))) (1 :: (Z)))
      (hd QMul.mYS (W) (1 :: (List.replicate Xm.length 3 ++ (1 :: (Z))))) := by
  have hV : Valid [ALL, Z2, ALL] [W, Xm, Z] := Valid.cons hW (Valid.cons hXm (Valid.cons hZ (Valid.nil _)))
  exact checkFT (env := [W, Xm, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 3), .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `y` is used up (nothing before it), `z` is exact. -/
theorem y1o (Ym : List Nat) (Xu : List Nat) (Zm : List Nat) (T : List Nat) (hYm : ∀ a ∈ Ym, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mYS (Ym) (1 :: (Xu ++ (1 :: (Zm ++ (1 :: (T)))))))
      (hdR QMul.FR1 (Ym ++ (1 :: (Xu ++ (1 :: (Zm ++ ([1])))))) (T)) := by
  have hV : Valid [Z2, T3, Z2, ALL] [Ym, Xu, Zm, T] := Valid.cons hYm (Valid.cons hXu (Valid.cons hZm (Valid.cons hT (Valid.nil _))))
  exact checkTF (env := [Ym, Xu, Zm, T]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `y` is used up (nothing before it), `z` is too large. -/
theorem y1z (Ym : List Nat) (Xu : List Nat) (Zm : List Nat) (Zu : List Nat) (T : List Nat) (hYm : ∀ a ∈ Ym, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hZu : ∀ a ∈ Zu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mYS (Ym) (1 :: (Xu ++ (1 :: (Zm ++ (3 :: (Zu ++ (1 :: (T)))))))))
      (hdR QMul.FR0 (Ym ++ (1 :: (Xu ++ (1 :: (Zm ++ ([3])))))) (Zu ++ (1 :: (T)))) := by
  have hV : Valid [Z2, T3, Z2, T3, ALL] [Ym, Xu, Zm, Zu, T] := Valid.cons hYm (Valid.cons hXu (Valid.cons hZm (Valid.cons hZu (Valid.cons hT (Valid.nil _)))))
  exact checkTF (env := [Ym, Xu, Zm, Zu, T]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 3]) (rs' := [.blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `y` is used up, `z` is exact. -/
theorem y2o (X : List Nat) (Ym : List Nat) (Xu : List Nat) (Zm : List Nat) (T : List Nat) (hX : Sym4 X) (hYm : ∀ a ∈ Ym, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mYS (X ++ (1 :: (Ym))) (1 :: (Xu ++ (1 :: (Zm ++ (1 :: (T)))))))
      (hdR QMul.FR1 (X ++ (1 :: (Ym ++ (1 :: (Xu ++ (1 :: (Zm ++ ([1])))))))) (T)) := by
  have hV : Valid [ALL, Z2, T3, Z2, ALL] [X, Ym, Xu, Zm, T] := Valid.cons hX (Valid.cons hYm (Valid.cons hXu (Valid.cons hZm (Valid.cons hT (Valid.nil _)))))
  exact checkTF (env := [X, Ym, Xu, Zm, T]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1]) (rs' := [.blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `y` is used up, `z` is too large. -/
theorem y2z (X : List Nat) (Ym : List Nat) (Xu : List Nat) (Zm : List Nat) (Zu : List Nat) (T : List Nat) (hX : Sym4 X) (hYm : ∀ a ∈ Ym, a ∈ Z2) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZm : ∀ a ∈ Zm, a ∈ Z2) (hZu : ∀ a ∈ Zu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mYS (X ++ (1 :: (Ym))) (1 :: (Xu ++ (1 :: (Zm ++ (3 :: (Zu ++ (1 :: (T)))))))))
      (hdR QMul.FR0 (X ++ (1 :: (Ym ++ (1 :: (Xu ++ (1 :: (Zm ++ ([3])))))))) (Zu ++ (1 :: (T)))) := by
  have hV : Valid [ALL, Z2, T3, Z2, T3, ALL] [X, Ym, Xu, Zm, Zu, T] := Valid.cons hX (Valid.cons hYm (Valid.cons hXu (Valid.cons hZm (Valid.cons hZu (Valid.cons hT (Valid.nil _))))))
  exact checkTF (env := [X, Ym, Xu, Zm, Zu, T]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3]) (rs' := [.blk 4 .id, .sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `z` is the only number, and nonzero. -/
theorem lone0 (Zu : List Nat) (T : List Nat) (hZu : ∀ a ∈ Zu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mP1 (3 :: (Zu)) (1 :: (T)))
      (hdR QMul.FR0 ([3]) (Zu ++ (1 :: (T)))) := by
  have hV : Valid [T3, ALL] [Zu, T] := Valid.cons hZu (Valid.cons hT (Valid.nil _))
  exact checkTF (env := [Zu, T]) (E := []) (k := 4) hV trivial
    (ls := [.sym 3, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `z` is the only number, and zero. -/
theorem lone1 (T : List Nat) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mP1 ([]) (1 :: (T)))
      (hdR QMul.FR1 ([1]) (T)) := by
  have hV : Valid [ALL] [T] := Valid.cons hT (Valid.nil _)
  exact checkTF (env := [T]) (E := []) (k := 2) hV trivial
    (ls := []) (rs := [.sym 1, .blk 0 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Two numbers, `z` zero. -/
theorem two1 (Xu : List Nat) (T : List Nat) (hXu : ∀ a ∈ Xu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mP1 (Xu ++ ([1])) (1 :: (T)))
      (hdR QMul.FR1 (Xu ++ (1 :: ([1]))) (T)) := by
  have hV : Valid [T3, ALL] [Xu, T] := Valid.cons hXu (Valid.cons hT (Valid.nil _))
  exact checkTF (env := [Xu, T]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Two numbers, `z` nonzero. -/
theorem two0 (Xu : List Nat) (Zu : List Nat) (T : List Nat) (hXu : ∀ a ∈ Xu, a ∈ T3) (hZu : ∀ a ∈ Zu, a ∈ T3) (hT : Sym4 T) :
    zmulLogic.Reach (hd QMul.mP1 (Xu ++ (1 :: (3 :: (Zu)))) (1 :: (T)))
      (hdR QMul.FR0 (Xu ++ (1 :: ([3]))) (Zu ++ (1 :: (T)))) := by
  have hV : Valid [T3, T3, ALL] [Xu, Zu, T] := Valid.cons hXu (Valid.cons hZu (Valid.cons hT (Valid.nil _)))
  exact checkTF (env := [Xu, Zu, T]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .sym 3]) (rs' := [.blk 1 .id, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-! ## Result report (generated) -/

/-- The result 0 is reported and the left side erased. -/
theorem frPath0M (Lc : List Nat) (Mr : List Nat) (Gp : List Nat) (j : List Nat) (s : List Nat) (Y : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hGp : ∀ a ∈ Gp, a ∈ B0) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmulLogic.Reach (hdR QMul.FR0 (Lc) (Mr ++ (0 :: (Gp ++ (1 :: (j ++ (1 :: (s ++ (0 :: (1 :: (Y)))))))))))
      (hdR Q.DP30 (Gp ++ (1 :: (j ++ (1 :: (s ++ ([1])))))) (1 :: (Y))) := by
  have hV : Valid [NB, NB, B0, bits, bits, ALL] [Lc, Mr, Gp, j, s, Y] := Valid.cons hLc (Valid.cons hMr (Valid.cons hGp (Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _))))))
  exact checkFF (env := [Lc, Mr, Gp, j, s, Y]) (E := []) (k := 14) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 0, .sym 1, .blk 5 .id])
    (ls' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1]) (rs' := [.sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The result 1 is reported and the left side erased. -/
theorem frPath1M (Lc : List Nat) (Mr : List Nat) (Gp : List Nat) (j : List Nat) (s : List Nat) (Y : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hGp : ∀ a ∈ Gp, a ∈ B0) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmulLogic.Reach (hdR QMul.FR1 (Lc) (Mr ++ (0 :: (Gp ++ (1 :: (j ++ (1 :: (s ++ (0 :: (1 :: (Y)))))))))))
      (hdR Q.DP31 (Gp ++ (1 :: (j ++ (1 :: (s ++ ([1])))))) (1 :: (Y))) := by
  have hV : Valid [NB, NB, B0, bits, bits, ALL] [Lc, Mr, Gp, j, s, Y] := Valid.cons hLc (Valid.cons hMr (Valid.cons hGp (Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _))))))
  exact checkFF (env := [Lc, Mr, Gp, j, s, Y]) (E := []) (k := 14) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 0, .sym 1, .blk 5 .id])
    (ls' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1]) (rs' := [.sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-! ## The multiplication loops -/

theorem rep3_nb (n : Nat) : NoB (List.replicate n 3) := t3_noB (rep_t3 n)
theorem rep2_nb (n : Nat) : NoB (List.replicate n 2) := z2_noB (rep_z2 n)
theorem nb1 : NoB [1] := NoB.cons one_nb NoB.nil

theorem zt4 (q r : Nat) (T : List Nat) (hT : Sym4 T) :
    Sym4 (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T) :=
  ((Sym4.rep q 2 (by simp [ALL])).app (Sym4.rep r 3 (by simp [ALL]))).app
    (Sym4.cons (by simp [ALL]) hT)

theorem xLoopOk (W : List Nat) (hW : NoB W) (T : List Nat) (hT : Sym4 T) : ∀ (u p q r : Nat), u ≤ r →
    zmulLogic.Reach (hdR QMul.mXS (W ++ 1 :: List.replicate p 2)
        (List.replicate u 3 ++ 1 :: (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T)))
      (hd QMul.mYS W (1 :: (List.replicate (p + u) 3 ++
        1 :: (List.replicate (q + u) 2 ++ List.replicate (r - u) 3 ++ 1 :: T))))
  | 0, p, q, r, _ => by
    have h := xDone W (List.replicate p 2) (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T)
      hW.sym4 (rep_z2 p) (zt4 q r T hT)
    refine h.of_eq (by simp) ?_
    simp
  | u + 1, p, q, r, hu => by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have h1 := xIter W (List.replicate p 2) (List.replicate u 3) (List.replicate q 2) (List.replicate r' 3) T
      hW.sym4 (rep_z2 p) (rep_t3 u) (rep_z2 q) (rep_t3 r') hT
    have h2 := xLoopOk W hW T hT u (p + 1) (q + 1) r' (by omega)
    refine (h1.of_eq (by simp [List.replicate_succ]) rfl).trans (h2.of_eq (by simp [List.replicate_succ']) ?_)
    have e1 : p + 1 + u = p + (u + 1) := by omega
    have e2 : q + 1 + u = q + (u + 1) := by omega
    have e3 : r' + 1 - (u + 1) = r' - u := by omega
    rw [e1, e2, e3]

theorem xLoopBad (W : List Nat) (hW : NoB W) (T : List Nat) (hT : Sym4 T) : ∀ (u p q r : Nat), r < u →
    ∃ Lc, NoB Lc ∧ zmulLogic.Reach (hdR QMul.mXS (W ++ 1 :: List.replicate p 2)
        (List.replicate u 3 ++ 1 :: (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T)))
      (hdR QMul.FR0 Lc T)
  | 0, p, q, r, hu => by omega
  | u + 1, p, q, 0, hu => by
    have h := xSmall W (List.replicate p 2) (List.replicate u 3) (List.replicate q 2) T
      hW.sym4 (rep_z2 p) (rep_t3 u) (rep_z2 q) hT
    have hn : NoB (W ++ 1 :: (List.replicate p 2 ++ 2 :: (List.replicate u 3 ++ 1 :: (List.replicate q 2 ++ [1])))) :=
      (hW.app (NoB.cons one_nb ((rep2_nb p).app (NoB.cons (by simp [NB]) ((rep3_nb u).app
        (NoB.cons one_nb ((rep2_nb q).app nb1)))))))
    exact ⟨_, hn, h.of_eq (by simp [List.replicate_succ]) rfl⟩
  | u + 1, p, q, r + 1, hu => by
    have h1 := xIter W (List.replicate p 2) (List.replicate u 3) (List.replicate q 2) (List.replicate r 3) T
      hW.sym4 (rep_z2 p) (rep_t3 u) (rep_z2 q) (rep_t3 r) hT
    obtain ⟨Lc, hLc, h2⟩ := xLoopBad W hW T hT u (p + 1) (q + 1) r (by omega)
    exact ⟨Lc, hLc, (h1.of_eq (by simp [List.replicate_succ]) rfl).trans
      (h2.of_eq (by simp [List.replicate_succ']) rfl)⟩

theorem _root_.ZP.F.LeftEnd.noB {Pre : List Nat} (h : LeftEnd Pre) : NoB Pre := by
  rcases h with rfl | ⟨X, hX, rfl⟩
  · exact NoB.nil
  · exact hX.app nb1

theorem yLoop (Pre : List Nat) (hPre : LeftEnd Pre) (T : List Nat) (hT : Sym4 T) (a : Nat) :
    ∀ (c m q r : Nat), ∃ Lc Mr, NoB Lc ∧ NoB Mr ∧
      zmulLogic.Reach (hd QMul.mYS (Pre ++ List.replicate c 3 ++ List.replicate m 2)
        (1 :: (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T))))
      (hdR (if r = a * c then QMul.FR1 else QMul.FR0) Lc (Mr ++ T))
  | 0, m, q, r => by
    rcases hPre with rfl | ⟨X, hX, rfl⟩
    · cases r with
      | zero =>
        have h := y1o (List.replicate m 2) (List.replicate a 3) (List.replicate q 2) T
          (rep_z2 m) (rep_t3 a) (rep_z2 q) hT
        have hn : NoB (List.replicate m 2 ++ 1 :: (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ [1]))) :=
          (rep2_nb m).app (NoB.cons one_nb ((rep3_nb a).app (NoB.cons one_nb ((rep2_nb q).app nb1))))
        exact ⟨_, [], hn, NoB.nil, h.of_eq (by simp) (by simp)⟩
      | succ r =>
        have h := y1z (List.replicate m 2) (List.replicate a 3) (List.replicate q 2) (List.replicate r 3) T
          (rep_z2 m) (rep_t3 a) (rep_z2 q) (rep_t3 r) hT
        have hn : NoB (List.replicate m 2 ++ 1 :: (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ [3]))) :=
          (rep2_nb m).app (NoB.cons one_nb ((rep3_nb a).app (NoB.cons one_nb
            ((rep2_nb q).app (NoB.cons (by simp [NB]) NoB.nil)))))
        exact ⟨_, List.replicate r 3 ++ [1], hn, (rep3_nb r).app nb1,
          h.of_eq (by simp [List.replicate_succ]) (by simp)⟩
    · cases r with
      | zero =>
        have h := y2o X (List.replicate m 2) (List.replicate a 3) (List.replicate q 2) T
          hX.sym4 (rep_z2 m) (rep_t3 a) (rep_z2 q) hT
        have hn : NoB (X ++ 1 :: (List.replicate m 2 ++ 1 :: (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ [1])))) :=
          hX.app (NoB.cons one_nb ((rep2_nb m).app (NoB.cons one_nb ((rep3_nb a).app
            (NoB.cons one_nb ((rep2_nb q).app nb1))))))
        exact ⟨_, [], hn, NoB.nil, h.of_eq (by simp) (by simp)⟩
      | succ r =>
        have h := y2z X (List.replicate m 2) (List.replicate a 3) (List.replicate q 2) (List.replicate r 3) T
          hX.sym4 (rep_z2 m) (rep_t3 a) (rep_z2 q) (rep_t3 r) hT
        have hn : NoB (X ++ 1 :: (List.replicate m 2 ++ 1 :: (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ [3])))) :=
          hX.app (NoB.cons one_nb ((rep2_nb m).app (NoB.cons one_nb ((rep3_nb a).app
            (NoB.cons one_nb ((rep2_nb q).app (NoB.cons (by simp [NB]) NoB.nil)))))))
        exact ⟨_, List.replicate r 3 ++ [1], hn, (rep3_nb r).app nb1,
          h.of_eq (by simp [List.replicate_succ]) (by simp)⟩
  | c + 1, m, q, r => by
    have hP := hPre.noB
    have hT' : Sym4 (List.replicate a 3 ++ 1 :: (List.replicate q 2 ++ List.replicate r 3 ++ 1 :: T)) :=
      (Sym4.rep a 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) (zt4 q r T hT))
    have h1 := ysMark (Pre ++ List.replicate c 3) (List.replicate m 2) _ (hP.app (rep3_nb c)).sym4
      (rep_z2 m) hT'
    have hW : NoB (Pre ++ List.replicate c 3 ++ 2 :: List.replicate m 2) :=
      (hP.app (rep3_nb c)).app (NoB.cons (by simp [NB]) (rep2_nb m))
    have hr : a ≤ r ∨ r < a := by omega
    rcases hr with hr | hr
    · have h2 := xLoopOk _ hW T hT a 0 q r hr
      obtain ⟨Lc, Mr, hLc, hMr, h3⟩ := yLoop Pre hPre T hT a c (m + 1) (q + a) (r - a)
      refine ⟨Lc, Mr, hLc, hMr, (h1.of_eq (by simp [List.replicate_succ']) rfl).trans
        ((h2.of_eq (by simp) rfl).trans (h3.of_eq (by simp [List.replicate_succ]) ?_))⟩
      have e : (r - a = a * c) ↔ (r = a * (c + 1)) := by rw [Nat.mul_succ]; omega
      simp only [e]
    · obtain ⟨Lc, hLc, h2⟩ := xLoopBad _ hW T hT a 0 q r hr
      refine ⟨Lc, [], hLc, NoB.nil, (h1.of_eq (by simp [List.replicate_succ']) rfl).trans
        (h2.of_eq (by simp) ?_)⟩
      have : ¬ r = a * (c + 1) := by rw [Nat.mul_succ]; omega
      simp [this]

/-! ## The check phase -/

theorem lay1_last3 : ∀ (fr : List Nat) (c k a b : Nat) (rest : List Nat),
    fr.reverse ++ [c] = k :: a :: b :: rest →
    ∃ Pre, lay1 c fr = Pre ++ (List.replicate b 3 ++ 1 :: (List.replicate a 3 ++ 1 :: List.replicate k 3)) ∧
      LeftEnd Pre ∧ Sym4 Pre
  | [], c, k, a, b, rest, h => by simp at h
  | [n], c, k, a, b, rest, h => by simp at h
  | [n, n'], c, k, a, b, rest, h => by
    simp at h
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    exact ⟨[], by simp [lay1], Or.inl rfl, Sym4.nil⟩
  | n :: n' :: n'' :: fr3, c, k, a, b, rest, h => by
    have h2 : (n' :: n'' :: fr3).reverse ++ [n] ++ [c] = k :: a :: b :: rest := by simpa using h
    have hlen : 3 ≤ ((n' :: n'' :: fr3).reverse ++ [n]).length := by simp
    obtain ⟨rest', hL1⟩ : ∃ rest', (n' :: n'' :: fr3).reverse ++ [n] = k :: a :: b :: rest' := by
      generalize (n' :: n'' :: fr3).reverse ++ [n] = L at h2 hlen
      match L, hlen, h2 with
      | x :: y :: z :: L'', _, h2 =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl, rfl, -⟩ := h2
        exact ⟨L'', rfl⟩
    obtain ⟨Pre, hP, hLE, hS⟩ := lay1_last3 (n' :: n'' :: fr3) n k a b rest' hL1
    refine ⟨List.replicate c 3 ++ 1 :: Pre, ?_, ?_, ?_⟩
    · rw [show lay1 c (n :: n' :: n'' :: fr3) = List.replicate c 3 ++ 1 :: lay1 n (n' :: n'' :: fr3) from rfl, hP]
      simp
    · rcases hLE with rfl | ⟨X, hX, rfl⟩
      · exact Or.inr ⟨List.replicate c 3, rep3_nb c, by simp⟩
      · exact Or.inr ⟨List.replicate c 3 ++ 1 :: X, (rep3_nb c).app (NoB.cons one_nb hX), by simp⟩
    · exact (Sym4.rep c 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hS)

def chkB (Sb : List Bool) : Bool :=
  let N := numbers Sb ++ [0, 0]
  N.getD 0 0 == N.getD 1 0 * N.getD 2 0

theorem checkMul_eq (out s : List Bool) : checkMul out s = chkB (out ++ false :: s) := rfl

theorem mulPhase (Sb : List Bool) (Rt : List Nat) (hRt : Sym4 Rt) :
    ∃ Lc Mr, NoB Lc ∧ NoB Mr ∧
      zmulLogic.Reach (hd QMul.HPF (1 :: crev Sb) Rt)
        (hdR (if chkB Sb then QMul.FR1 else QMul.FR0) Lc (Mr ++ (List.replicate Sb.length 0 ++ Rt))) := by
  have hconv := convLoopM Sb.length Sb 0 [] Rt hRt (Nat.le_refl _)
  have hnum := numbers_eq Sb.length Sb 0 []
  simp only [List.reverse_nil, List.nil_append] at hnum
  have hT : Sym4 (List.replicate Sb.length 0 ++ Rt) := (zeros4 _).app hRt
  generalize parseState Sb.length Sb 0 [] = ps at hconv hnum
  obtain ⟨c, fr⟩ := ps
  simp only at hconv hnum
  have hc : zmulLogic.Reach (hd QMul.HPF (1 :: crev Sb) Rt)
      (hd QMul.mP1 (lay1 c fr) (1 :: (List.replicate Sb.length 0 ++ Rt))) :=
    hconv.of_eq (by simp [lyt]) rfl
  have hnum' : numbers Sb = fr.reverse ++ [c] := hnum
  generalize List.replicate Sb.length 0 ++ Rt = T at hc hT ⊢
  have e3 : ∀ L : List Nat, 3 ≤ L.length → ∃ k a b rest, L = k :: a :: b :: rest := by
    intro L h
    match L, h with
    | k :: a :: b :: rest, _ => exact ⟨k, a, b, rest, rfl⟩
  match fr, hc, hnum' with
  | [], hc, hnum' =>
    have hchk : chkB Sb = true ↔ c = 0 := by
      unfold chkB; rw [hnum']; simp
    cases c with
    | zero =>
      have h := lone1 T hT
      refine ⟨[1], [], nb1, NoB.nil, ?_⟩
      simp only [hchk]
      exact hc.trans (h.of_eq (by simp [lay1]) (by simp))
    | succ c' =>
      have h := lone0 (List.replicate c' 3) T (rep_t3 c') hT
      refine ⟨[3], List.replicate c' 3 ++ [1], NoB.cons (by simp [NB]) NoB.nil, (rep3_nb c').app nb1, ?_⟩
      simp only [hchk]
      exact hc.trans (h.of_eq (by simp [lay1, List.replicate_succ]) (by simp))
  | [n], hc, hnum' =>
    have hchk : chkB Sb = true ↔ n = 0 := by
      unfold chkB; rw [hnum']; simp
    cases n with
    | zero =>
      have h := two1 (List.replicate c 3) T (rep_t3 c) hT
      refine ⟨List.replicate c 3 ++ [1, 1], [], (rep3_nb c).app (NoB.cons one_nb nb1), NoB.nil, ?_⟩
      simp only [hchk]
      exact hc.trans (h.of_eq (by simp [lay1]) (by simp))
    | succ n' =>
      have h := two0 (List.replicate c 3) (List.replicate n' 3) T (rep_t3 c) (rep_t3 n') hT
      refine ⟨List.replicate c 3 ++ [1, 3], List.replicate n' 3 ++ [1],
        (rep3_nb c).app (NoB.cons one_nb (NoB.cons (by simp [NB]) NoB.nil)), (rep3_nb n').app nb1, ?_⟩
      simp only [hchk]
      exact hc.trans (h.of_eq (by simp [lay1, List.replicate_succ]) (by simp))
  | n :: n' :: fr'', hc, hnum' =>
    obtain ⟨k, a, b, rest, hN⟩ := e3 ((n :: n' :: fr'').reverse ++ [c]) (by simp)
    obtain ⟨Pre, hlay, hLE, hS⟩ := lay1_last3 (n :: n' :: fr'') c k a b rest hN
    have hchk : chkB Sb = true ↔ k = a * b := by
      unfold chkB; rw [hnum', hN]; simp
    have h1 := mpToYS (Pre ++ List.replicate b 3) (List.replicate a 3) (List.replicate k 3) (1 :: T)
      (hS.app (Sym4.rep b 3 (by simp [ALL]))) (rep_t3 a) (rep_t3 k) (Sym4.cons (by simp [ALL]) hT)
    obtain ⟨Lc, Mr, hLc, hMr, h2⟩ := yLoop Pre hLE T hT a b 0 0 k
    refine ⟨Lc, Mr, hLc, hMr, ?_⟩
    have e : (if chkB Sb = true then QMul.FR1 else QMul.FR0) = (if k = a * b then QMul.FR1 else QMul.FR0) := by
      simp only [hchk]
    rw [e]
    rw [hlay] at hc
    exact hc.trans ((h1.of_eq (by simp) rfl).trans (h2.of_eq (by simp) rfl))

/-! ## The check: set-up (generated) -/

/-- The check begins: over the output, `J` and `s`, back to the start of `s`. -/
theorem mkChain (Rw : List Nat) (j : List Nat) (s : List Nat) (Y : List Nat) (hRw : Bits Rw) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmulLogic.Reach (hdR QMul.mK1 ([2]) (Rw ++ (1 :: (j ++ (1 :: (s ++ (1 :: (Y))))))))
      (hdR Q.GC (2 :: (Rw ++ (1 :: (j ++ ([1]))))) (s ++ (0 :: (Y)))) := by
  have hV : Valid [bits, bits, bits, ALL] [Rw, j, s, Y] := Valid.cons hRw (Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _))))
  exact checkFF (env := [Rw, j, s, Y]) (E := []) (k := 8) hV trivial
    (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy one bit of `s` to the far left. -/
theorem gcBodyC (Ur : List Nat) (V : List Nat) (u : List Nat) (v : List Nat) (Y : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hu : Bits u) (hv : Bits v) (hY : Sym4 Y) (hb : b ∈ bits) :
    zmulLogic.Reach (hdR Q.GC (Ur ++ (V ++ (u))) (b :: (v ++ (0 :: (Y)))))
      (hdR Q.GC (b :: (Ur ++ (V ++ (u ++ ([b]))))) (v ++ (0 :: (Y)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Ur, V, u, v, Y] := Valid.cons hUr (Valid.cons hV (Valid.cons hu (Valid.cons hv (Valid.cons hY (Valid.nil _)))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Ur, V, u, v, Y]) (E := []) (k := 9) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .blk 2 .id]) (rs := [.sym 2, .blk 3 .id, .sym 0, .blk 4 .id])
      (ls' := [.sym 2, .blk 0 .id, .blk 1 .id, .blk 2 .id, .sym 2]) (rs' := [.blk 3 .id, .sym 0, .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Ur, V, u, v, Y]) (E := []) (k := 9) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .blk 2 .id]) (rs := [.sym 3, .blk 3 .id, .sym 0, .blk 4 .id])
      (ls' := [.sym 3, .blk 0 .id, .blk 1 .id, .blk 2 .id, .sym 3]) (rs' := [.blk 3 .id, .sym 0, .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The copy is done: the marker, then back to the end of the output. -/
theorem tsEnd (Ur : List Nat) (Rw : List Nat) (j : List Nat) (u : List Nat) (Y : List Nat) (hUr : Bits Ur) (hRw : Bits Rw) (hj : Bits j) (hu : Bits u) (hY : Sym4 Y) :
    zmulLogic.Reach (hdR Q.GC (Ur ++ (2 :: (Rw ++ (1 :: (j ++ (1 :: (u))))))) (0 :: (Y)))
      (hd QMul.HPF (1 :: (Ur ++ (2 :: (Rw)))) (1 :: (j ++ (1 :: (u ++ (0 :: (Y))))))) := by
  have hV : Valid [bits, bits, bits, bits, ALL] [Ur, Rw, j, u, Y] := Valid.cons hUr (Valid.cons hRw (Valid.cons hj (Valid.cons hu (Valid.cons hY (Valid.nil _)))))
  exact checkFT (env := [Ur, Rw, j, u, Y]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 0, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 0, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem gcLoopC (V Y : List Nat) (hV : NoB V) (hY : Sym4 Y) :
    ∀ v u, Bits u → Bits v →
      zmulLogic.Reach (hdR Q.GC (u.reverse ++ (V ++ u)) (v ++ 0 :: Y))
        (hdR Q.GC ((u ++ v).reverse ++ (V ++ (u ++ v))) (0 :: Y))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := gcBodyC u.reverse V u v Y b hu.rev hV hu hv.tail hY hv.head
    have h2 := gcLoopC V Y hV hY v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.of_eq (by simp) (by simp only [List.append_assoc, List.singleton_append]))

theorem checkPre (Rw J s Y : List Nat) (hRw : Bits Rw) (hJ : Bits J) (hs : Bits s) (hY : Sym4 Y) :
    zmulLogic.Reach (hdR QMul.mK1 [2] (Rw ++ 1 :: (J ++ 1 :: (s ++ 1 :: Y))))
      (hd QMul.HPF (1 :: (s.reverse ++ 2 :: Rw)) (1 :: (J ++ 1 :: (s ++ 0 :: Y)))) := by
  have h1 := mkChain Rw J s Y hRw hJ hs hY
  have hV : NoB (2 :: (Rw ++ 1 :: (J ++ [1]))) :=
    NoB.cons (by simp [NB]) (hRw.noB.app (NoB.cons one_nb (hJ.noB.app nb1)))
  have h2 := gcLoopC (2 :: (Rw ++ 1 :: (J ++ [1]))) Y hV hY s [] Bits.nil hs
  have h3 := tsEnd s.reverse Rw J s Y hs.rev hRw hJ hs hY
  have h2' := h2.of_eq (show _ = hdR Q.GC (2 :: (Rw ++ 1 :: (J ++ [1]))) (s ++ 0 :: Y) by simp) (show _ = hdR Q.GC (s.reverse ++ 2 :: (Rw ++ 1 :: (J ++ 1 :: s))) (0 :: Y) by simp)
  exact h1.trans (h2'.trans h3)

theorem hdR_rep0 (q n : Nat) (A R : List Nat) : hdR q (List.replicate n 0 ++ A) R = hdR q A R :=
  ZP.F.hdR_zeros q (List.replicate n 0) A R (fun a ha => by
    have := List.eq_of_mem_replicate ha
    subst this
    simp [ZP.F.B0])

/-- The outcome of a finished run, as the dispatch sees it. -/
def okB (r : Option (List Bool)) (Xb : List Bool) : Bool :=
  match r with
  | none => false
  | some out => checkMul out Xb

theorem haltPhase (Pb Xb : List Bool) (r : Option (List Bool)) (Fy ST : List Nat)
    (hF : NoB (1 :: Fy)) (hST : NoB ST) :
    ∃ q, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ okB r Xb = true) ∧
      zmulLogic.Reach (REm r (bitsOf Pb ++ 1 :: bitsOf Xb) (1 :: Fy) ST)
        (hdR q (1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ [1]))) (1 :: (Fy ++ 0 :: ST))) := by
  have hY : Sym4 (Fy ++ 0 :: ST) :=
    (NoB.sym4 (by intro a ha; exact hF a (List.mem_cons_of_mem _ ha))).app
      (Sym4.cons (by simp [ALL]) hST.sym4)
  have hj : Bits (bitsOf Pb) := Bits.ofB Pb
  have hs : Bits (bitsOf Xb) := Bits.ofB Xb
  cases r with
  | none =>
    refine ⟨Q.DP30, Or.inr rfl, by simp [okB, Q.DP31, Q.DP30], ?_⟩
    have h := dHalt0 (bitsOf Pb) (bitsOf Xb) (Fy ++ 0 :: ST) hj hs hY
    exact (h.of_eq (by simp [REm, REn, dpOf]) rfl)
  | some out =>
    have h1 := checkPre (bitsOf out.reverse) (bitsOf Pb) (bitsOf Xb) (1 :: (Fy ++ 0 :: ST))
      (Bits.ofB _) hj hs (Sym4.cons (by simp [ALL]) hY)
    have hT : Sym4 (1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 0 :: (1 :: (Fy ++ 0 :: ST))))) :=
      Sym4.cons (by simp [ALL]) (hj.sym4.app (Sym4.cons (by simp [ALL]) (hs.sym4.app
        (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hY)))))
    obtain ⟨Lc, Mr, hLc, hMr, h2⟩ := mulPhase (out ++ false :: Xb) _ hT
    have hcr : crev (out ++ false :: Xb) = (bitsOf Xb).reverse ++ 2 :: bitsOf out.reverse := by
      simp [crev, bitsOf, List.reverse_append]
    rw [hcr] at h2
    have hlen : (out ++ false :: Xb).length = (out.length + Xb.length) + 1 := by simp; omega
    rw [hlen, List.replicate_succ] at h2
    have hREm : REm (some out) (bitsOf Pb ++ 1 :: bitsOf Xb) (1 :: Fy) ST =
        hdR QMul.mK1 [2] (bitsOf out.reverse ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: (1 :: (Fy ++ 0 :: ST))))) := by
      simp [REm, REn]
    by_cases hc : chkB (out ++ false :: Xb) = true
    · have hc' : checkMul out Xb = true := hc
      refine ⟨Q.DP31, Or.inl rfl, by simp [okB, hc'], ?_⟩
      have h3 := frPath1M Lc Mr (List.replicate (out.length + Xb.length) 0) (bitsOf Pb) (bitsOf Xb)
        (Fy ++ 0 :: ST) hLc hMr (rep_b0 _) hj hs hY
      rw [hREm]
      simp only [hc, ite_true] at h2
      have h2' := h2.of_eq rfl (show _ = hdR QMul.FR1 Lc (Mr ++ 0 :: (List.replicate (out.length + Xb.length) 0 ++
        1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 0 :: 1 :: (Fy ++ 0 :: ST))))) by simp)
      exact (h1.trans (h2'.trans h3)).of_eq rfl (hdR_rep0 _ _ _ _)
    · have hc' : ¬ checkMul out Xb = true := hc
      refine ⟨Q.DP30, Or.inr rfl, by simp [okB, hc', Q.DP31, Q.DP30], ?_⟩
      have h3 := frPath0M Lc Mr (List.replicate (out.length + Xb.length) 0) (bitsOf Pb) (bitsOf Xb)
        (Fy ++ 0 :: ST) hLc hMr (rep_b0 _) hj hs hY
      rw [hREm]
      simp only [hc, ite_false] at h2
      have h2' := h2.of_eq rfl (show _ = hdR QMul.FR0 Lc (Mr ++ 0 :: (List.replicate (out.length + Xb.length) 0 ++
        1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 0 :: 1 :: (Fy ++ 0 :: ST))))) by simp)
      exact (h1.trans (h2'.trans h3)).of_eq rfl (hdR_rep0 _ _ _ _)

/-! ## One pair -/

def layMul (J S : Nat) : ZC := ⟨QMul.NI, sapp (layWord J S).reverse blank, blank⟩

theorem layMul_hdR (J S : Nat) :
    layMul J S = hdR QMul.NI (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [] := by
  rw [ZP.F.hdR_eq']
  simp only [layMul, layWord, sapp]

theorem FWr_one : ∀ (ds : List Dg), ds ≠ [] → ∃ Fy, FWr ds = 1 :: Fy
  | [], h => absurd rfl h
  | (n, d) :: ds, _ => by
    by_cases hds : ds = []
    · subst hds
      exact ⟨List.replicate d 3 ++ List.replicate (n + 1 - d) 2, by simp [FWr, blkW]⟩
    · obtain ⟨Fy, hF⟩ := FWr_one ds hds
      exact ⟨Fy ++ blkW n d, by simp [FWr, hF]⟩

theorem full_fz (n k : Nat) : full (fz n k) = fz n k := by
  simp [full, fz, List.map_replicate]

theorem mainPhase (J S : Nat) :
    ∃ q Fy ST, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ CorrectMul J S) ∧ NoB Fy ∧ NoB ST ∧
      zmulLogic.Reach (hdR QMul.NI (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [])
        (hdR q (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1]))) (1 :: (Fy ++ 0 :: ST))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h0 := decFuelM (bitsOf (str S)) hs (bitsOf (str J)) hj
  have hdig := fz_dig (bitsOf (str S)).length (bitsOf (str J)).length
  have hne : fz (bitsOf (str S)).length (bitsOf (str J)).length ≠ [] := by simp [fz]
  obtain ⟨ds', ST', hds', hmap, hST', h1⟩ := runFromM (str J) (str S) _ hdig hne
  have hne' : ds' ≠ [] := by
    intro h
    rw [h] at hmap
    simp [fz] at hmap
  obtain ⟨Fy, hFy⟩ := FWr_one ds' hne'
  rw [hFy] at h1
  have hFnb : NoB (1 :: Fy) := by rw [← hFy]; exact FWr_noB _
  have hv : valr (fz (bitsOf (str S)).length (bitsOf (str J)).length) = clockMul (str J) (str S) := by
    have := fz_valr (bitsOf (str S)).length (bitsOf (str J)).length
    rw [full_fz] at this
    simp only [bitsOf_len] at this ⊢
    unfold clockMul
    omega
  rw [hv] at h1
  obtain ⟨q, hq, hqok, h2⟩ := haltPhase (str J) (str S)
    (runMulAux (clockMul (str J) (str S)) (rot ((str J).reverse ++ [false])) (str S) 0
      (List.replicate (str J).length [])) Fy ST' hFnb hST'
  refine ⟨q, Fy, ST', hq, ?_, fun a ha => hFnb a (List.mem_cons_of_mem _ ha), hST', ?_⟩
  · rw [hqok]
    unfold CorrectMul correctMulB runMul
    cases hr : runMulAux (clockMul (str J) (str S)) (rot ((str J).reverse ++ [false])) (str S) 0
      (List.replicate (str J).length []) <;> simp [okB]
  · refine h0.trans ((h1.of_eq (by simp [bitsOf_len]) rfl).trans h2)

theorem pair_mainMul (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectMul J S → zmulLogic.zrun n (layMul J S) =
          some (layMul (absStepC CorrectMul (J, S)).1 (absStepC CorrectMul (J, S)).2)) ∧
       (¬ CorrectMul J S → ∃ a c1 c2, a < n ∧ zmulLogic.zrun a (layMul J S) = some c1 ∧
          c1.q = zmulLogic.beep ∧ zmulLogic.zstep c1 = some c2 ∧
          zmulLogic.zrun (n - a - 1) c2 =
            some (layMul (absStepC CorrectMul (J, S)).1 (absStepC CorrectMul (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨q, Fy, ST, hq, hqiff, hFy, hST, hA⟩ := mainPhase J S
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  have hA1 : zmulLogic.Reach1 (layMul J S) (hdR q (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1])))
      (1 :: (Fy ++ 0 :: ST))) := by
    rw [layMul_hdR]
    refine ZP.F.Reach_pos hA ?_
    rw [ZP.F.hdR_eq', ZP.F.hdR_eq']
    show QMul.NI ≠ q
    rcases hq with rfl | rfl <;> decide
  by_cases hc : CorrectMul J S
  · have e : absStepC CorrectMul (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have hq1 : q = Q.DP31 := hqiff.mpr hc
    subst hq1
    have hok := okTailM (bitsOf (str J)) (bitsOf (str S)) Fy ST hj hs hFy hST
    have hinc := sincLM (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA1.trans (hok.trans (hinc.of_eq (c4 := layMul J (S + 1))
      (by rw [eS]; rfl) (by rw [layMul_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectMul (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have hq0 : q = Q.DP30 := by
      rcases hq with rfl | rfl
      · exact absurd (hqiff.mp rfl) hc
      · rfl
    subst hq0
    have h3 := badTailM (bitsOf (str J)) (bitsOf (str S)) Fy ST hj hs hFy hST
    obtain ⟨n1, hn1⟩ := hA1
    obtain ⟨n2, hn2⟩ := h3.trans ((jincLM rJ 0).of_eq (c4 := layMul (J + 1) 1)
      (by rw [eJ]; rfl) (by rw [layMul_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, beepStepM _ _ _, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2

end ZP.Mul
