module

public import ZP.PrimeNTT

@[expose] public section

/-! # NTT machine: building the records (part 1): the field copy engine -/

namespace ZP.NTT

open ZP ZP.G

/-- Cells that are not marked: `M` or `'1'`. -/
def Un (w : List Nat) : Prop := ∀ x ∈ w, x ∈ [1, 3]

theorem Un.sym4 {w : List Nat} (h : Un w) : Sym4 w := by
  intro x hx; have := h x hx; simp at this; rcases this with rfl | rfl <;> simp [ALL]

theorem Un.noB {w : List Nat} (h : Un w) : NoB w := by
  intro x hx; have := h x hx; simp at this; rcases this with rfl | rfl <;> simp [NB]

theorem Un.rep (k c : Nat) (hc : c ∈ [1, 3]) : Un (List.replicate k c) := by
  intro x hx; simp [List.mem_replicate] at hx; rw [hx.2]; exact hc

theorem Un.app {u v : List Nat} (hu : Un u) (hv : Un v) : Un (u ++ v) := by
  intro x hx; simp at hx; rcases hx with h | h
  · exact hu x h
  · exact hv x h

theorem noBapp {u v : List Nat} (hu : NoB u) (hv : NoB v) : NoB (u ++ v) := NoB.app hu hv

theorem noBcons {a : Nat} {v : List Nat} (ha : a ∈ NB) (hv : NoB v) : NoB (a :: v) := NoB.cons ha hv

/-- `CL0`: scan left to the blank. -/
theorem cl0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CL0 L R) (hdR QNTT.CL1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CL1`: cross the unmarked cells to the first marked one. -/
theorem cl1Sweep (Lc : List Nat) (k : Nat) (R : List Nat) (hLc : Un Lc) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CL1 [] (Lc ++ 2 :: R)) (hdR QNTT.CL2 (Lc ++ [2]) R) := by
  have hV : Valid [[1, 3], ALL] [Lc, R] := Valid.cons hLc (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [Lc, R]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.blk 0 .id, .sym 2, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CL2`: cross the marked cells, mark the next one. -/
theorem cl2Mark (A : List Nat) (k : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CL2 A (List.replicate k 2 ++ 3 :: R))
      (hdR QNTT.CW0 (A ++ List.replicate (k + 1) 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate k 2, R] :=
    Valid.cons hA (Valid.cons (repSet k 2) (Valid.cons hR (Valid.nil _)))
  simpa [List.replicate_succ'] using checkFF (env := [A, List.replicate k 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CL2`: the source is used up. -/
theorem cl2End (A : List Nat) (k : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CL2 A (List.replicate k 2 ++ 1 :: R))
      (hd QNTT.CRs (A ++ List.replicate k 2) (1 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate k 2, R] :=
    Valid.cons hA (Valid.cons (repSet k 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate k 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CW0`: scan to the end of the tape and append a `'0'` to the copy. -/
theorem cw0Append (A X : List Nat) (hA : Sym4 A) (hX : NoB X) :
    znttLogic.Reach (hdR QNTT.CW0 A X) (hd QNTT.CL0 (A ++ X) [2]) := by
  have hV : Valid [ALL, NB] [A, X] := Valid.cons hA (Valid.cons hX (Valid.nil _))
  exact checkFT (env := [A, X]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 2])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem Un.noB' {w : List Nat} (h : Un w) : NoB w := h.noB

/-- One round of the copy: mark the next source cell, append a `'0'` to the copy. -/
theorem clStep (Lc Mid' : List Nat) (k j x : Nat) (hLc : Un Lc) (hMid : NoB Mid') (hx : x ∈ [2, 3]) :
    znttLogic.Reach
      (hd QNTT.CL0 (Lc ++ List.replicate (k + 1) 2 ++ List.replicate (j + 1) 3 ++ 1 :: Mid') [x])
      (hd QNTT.CL0 (Lc ++ List.replicate (k + 1 + 1) 2 ++ List.replicate j 3 ++ 1 :: (Mid' ++ [x])) [2]) := by
  have sx : Sym4 [x] := by
    intro y hy; simp at hy; subst hy; simp at hx; rcases hx with rfl | rfl <;> simp [ALL]
  have nx : NoB [x] := by
    intro y hy; simp at hy; subst hy; simp at hx; rcases hx with rfl | rfl <;> simp [NB]
  have nL : NoB (Lc ++ List.replicate (k + 1) 2 ++ List.replicate (j + 1) 3 ++ 1 :: Mid') := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]
    simp [NB, hMid, hLc.noB]
  have h1 := cl0Scan _ [x] nL sx
  have hxn : x = 1 ∨ x = 2 ∨ x = 3 := by simp at hx; omega
  have nR : NoB (List.replicate j 3 ++ 1 :: (Mid' ++ [x])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hMid, hxn]
  have sR3 : Sym4 (List.replicate j 3 ++ 1 :: (Mid' ++ [x])) := nR.sym4
  have sR2 : Sym4 (List.replicate k 2 ++ 3 :: (List.replicate j 3 ++ 1 :: (Mid' ++ [x]))) :=
    (s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sR3)
  have h2 := cl1Sweep Lc k _ hLc sR2
  have h3 := cl2Mark (Lc ++ [2]) k _ (hLc.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)) sR3
  have nA : NoB (Lc ++ [2] ++ List.replicate (k + 1) 2) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hLc.noB]
  have h4 := cw0Append (Lc ++ [2] ++ List.replicate (k + 1) 2) _
    (hLc.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil) |>.app (s4rep _ 2 (by simp [ALL]))) nR
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

/-- The last round: the source is exhausted. -/
theorem clEnd (Lc Mid' : List Nat) (k x : Nat) (hLc : Un Lc) (hMid : NoB Mid') (hx : x ∈ [2, 3]) :
    znttLogic.Reach
      (hd QNTT.CL0 (Lc ++ List.replicate (k + 1) 2 ++ 1 :: Mid') [x])
      (hd QNTT.CRs (Lc ++ List.replicate (k + 1) 2) (1 :: (Mid' ++ [x]))) := by
  have sx : Sym4 [x] := by
    intro y hy; simp at hy; subst hy; simp at hx; rcases hx with rfl | rfl <;> simp [ALL]
  have hxn : x = 1 ∨ x = 2 ∨ x = 3 := by simp at hx; omega
  have nL : NoB (Lc ++ List.replicate (k + 1) 2 ++ 1 :: Mid') := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]
    simp [NB, hMid, hLc.noB]
  have h1 := cl0Scan _ [x] nL sx
  have nR : NoB (List.replicate k 2 ++ 1 :: (Mid' ++ [x])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hMid, hxn]
  have h2 := cl1Sweep Lc k _ hLc nR.sym4
  have nR' : NoB (Mid' ++ [x]) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hMid, hxn]
  have h3 := cl2End (Lc ++ [2]) k _ (hLc.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)) nR'.sym4
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

theorem clLoop (Lc : List Nat) (hLc : Un Lc) :
    ∀ (j k : Nat) (Mid' : List Nat) (x : Nat), NoB Mid' → x ∈ [2, 3] →
    znttLogic.Reach
      (hd QNTT.CL0 (Lc ++ List.replicate (k + 1) 2 ++ List.replicate j 3 ++ 1 :: Mid') [x])
      (hd QNTT.CRs (Lc ++ List.replicate (k + 1 + j) 2) (1 :: (Mid' ++ x :: List.replicate j 2))) := by
  intro j
  induction j with
  | zero =>
    intro k Mid' x hM hx
    simpa using clEnd Lc Mid' k x hLc hM hx
  | succ j ih =>
    intro k Mid' x hM hx
    have h1 := clStep Lc Mid' k j x hLc hM hx
    have hxn : x = 1 ∨ x = 2 ∨ x = 3 := by simp at hx; omega
    have hM' : NoB (Mid' ++ [x]) := by
      simp only [NoB_app_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hM, hxn]
    have h2 := ih (k + 1) (Mid' ++ [x]) 2 hM' (by simp)
    have e : k + 1 + 1 + j = k + 1 + (j + 1) := by omega
    rw [e] at h2
    have := h1.trans h2
    simpa [List.replicate_succ, List.append_assoc] using this

/-- `SPR`: run to the end of the tape and append the separator `M`. -/
theorem sprScan (A R : List Nat) (hA : Sym4 A) (hR : NoB R) :
    znttLogic.Reach (hdR QNTT.SPR A R) (hd QNTT.SP1 (A ++ R) [1]) := by
  have hV : Valid [ALL, NB] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `SP1`: back to the left end. -/
theorem sp1Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SP1 L R) (hdR QNTT.SP2 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `SP2`: skip the first field (`W`). -/
theorem sp2Skip (W R : List Nat) (hW : BitsD W) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SP2 [] (W ++ 1 :: R)) (hdR QNTT.SP3 (W ++ [1]) R) := by
  have hV : Valid [[2, 3], ALL] [W, R] := Valid.cons hW (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [W, R]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `SP3`: mark the first cell of the source. -/
theorem sp3Mark (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SP3 A (3 :: R)) (hdR QNTT.SW3 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `SW3`: run to the end and write the first cell `'1'` of the copy. -/
theorem sw3Write (A X : List Nat) (hA : Sym4 A) (hX : NoB X) :
    znttLogic.Reach (hdR QNTT.SW3 A X) (hd QNTT.CL0 (A ++ X) [3]) := by
  have hV : Valid [ALL, NB] [A, X] := Valid.cons hA (Valid.cons hX (Valid.nil _))
  exact checkFT (env := [A, X]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CRs`: unmark the source, step right across the separator. -/
theorem crsP (Lc0 : List Nat) (s : Nat) (R : List Nat) (hLc : Sym4 Lc0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CRs (Lc0 ++ [1] ++ List.replicate s 2) R)
      (hdR QNTT.KX1 (Lc0 ++ [1]) (List.replicate s 3 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [Lc0, List.replicate s 2, R] :=
    Valid.cons hLc (Valid.cons (repSet s 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [Lc0, List.replicate s 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `CRs` at the left end of the tape (the copy of `W`): write the new `'1'` of `W`. -/
theorem crsW (s : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CRs (List.replicate s 2) R)
      (hdR QNTT.RN0 [3] (List.replicate s 3 ++ R)) := by
  have hV : Valid [[2], ALL] [List.replicate s 2, R] := Valid.cons (repSet s 2) (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [List.replicate s 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := [.sym 3]) (rs' := [.blk 0 (.const 3), .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy `P` (of `j + 1` cells) to the end of the tape, from `SPR`; `W = 3^w` is the first field. -/
theorem copyP (w j : Nat) (Mid1 Mid2 : List Nat) (hM1 : NoB Mid1) (hM2 : NoB Mid2) :
    znttLogic.Reach
      (hdR QNTT.SPR (List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: Mid1)) Mid2)
      (hdR QNTT.KX1 (List.replicate w 3 ++ [1])
        (List.replicate (j + 1) 3 ++ 1 :: (Mid1 ++ Mid2 ++ 1 :: 3 :: List.replicate j 2))) := by
  have sW : Sym4 (List.replicate w 3) := s4rep _ 3 (by simp [ALL])
  have unW : Un (List.replicate w 3 ++ [1]) := (Un.rep _ _ (by simp)).app (by intro x hx; simp at hx; simp [hx])
  have nA : NoB (List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: Mid1)) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, hM1]
  have h1 := sprScan _ Mid2 nA.sym4 hM2
  have nL : NoB (List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: Mid1) ++ Mid2) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, hM1, hM2]
  have h2 := sp1Scan _ [1] nL (by intro y hy; simp at hy; subst hy; simp [ALL])
  have nR2 : NoB (List.replicate (j + 1) 3 ++ 1 :: (Mid1 ++ Mid2 ++ [1])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hM1, hM2]
  have h3 := sp2Skip (List.replicate w 3) _ (BitsD.rep _ _ (by simp)) nR2.sym4
  have nR3 : NoB (List.replicate j 3 ++ 1 :: (Mid1 ++ Mid2 ++ [1])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hM1, hM2]
  have h4 := sp3Mark (List.replicate w 3 ++ [1]) _ (unW.sym4) nR3.sym4
  have h5 := sw3Write (List.replicate w 3 ++ [1] ++ [2]) _
    (unW.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)) nR3
  have nM' : NoB (Mid1 ++ Mid2 ++ [1]) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, hM1, hM2]
  have h6 := clLoop (List.replicate w 3 ++ [1]) unW j 0 (Mid1 ++ Mid2 ++ [1]) 3 nM' (by simp)
  have h7 := crsP (List.replicate w 3) (j + 1) (1 :: ((Mid1 ++ Mid2 ++ [1]) ++ 3 :: List.replicate j 2)) sW
    (Sym4.cons (by simp [ALL]) (nM'.sym4.app (Sym4.cons (by simp [ALL]) (s4rep _ 2 (by simp [ALL])))))
  have e : 0 + 1 + j = j + 1 := by omega
  rw [e] at h6
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

theorem kx1Skip (A : List Nat) (s : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.KX1 A (List.replicate s 3 ++ 1 :: R))
      (hdR QNTT.KX2 (A ++ List.replicate s 3 ++ [1]) R) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate s 3, R] :=
    Valid.cons hA (Valid.cons (repSet s 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate s 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem kx2Mark (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.KX2 A (List.replicate a 2 ++ 3 :: R))
      (hdR QNTT.SPR (A ++ List.replicate (a + 1) 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  simpa [List.replicate_succ'] using checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem kx2End (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.KX2 A (List.replicate a 2 ++ 1 :: R))
      (hd QNTT.KR (A ++ List.replicate a 2) (1 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem krSweep (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.KR (A ++ [1] ++ List.replicate a 2) R)
      (hdR QNTT.SWR (A ++ [1]) (List.replicate a 3 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem swrScan (A R : List Nat) (hA : Sym4 A) (hR : NoB R) :
    znttLogic.Reach (hdR QNTT.SWR A R) (hd QNTT.SW1 (A ++ R) [1]) := by
  have hV : Valid [ALL, NB] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sw1Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SW1 L R) (hdR QNTT.SW2 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sw2Mark (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SW2 [] (3 :: R)) (hdR QNTT.SW3 [2] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkFF (env := [R]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.sym 3, .blk 0 .id]) (ls' := [.sym 2]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy `W` (of `j + 1` cells, at the left edge) to the end; `W` grows by a cell. -/
theorem copyW (j : Nat) (Rest1 Rest2 : List Nat) (h1 : NoB Rest1) (h2 : NoB Rest2) :
    znttLogic.Reach
      (hdR QNTT.SWR (List.replicate (j + 1) 3 ++ 1 :: Rest1) Rest2)
      (hdR QNTT.RN0 [3] (List.replicate (j + 1) 3 ++ 1 :: (Rest1 ++ Rest2 ++ 1 :: 3 :: List.replicate j 2))) := by
  have nA : NoB (List.replicate (j + 1) 3 ++ 1 :: Rest1) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, h1]
  have g1 := swrScan _ Rest2 nA.sym4 h2
  have nL : NoB (List.replicate (j + 1) 3 ++ 1 :: Rest1 ++ Rest2) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, h1, h2]
  have g2 := sw1Scan _ [1] nL (by intro y hy; simp at hy; subst hy; simp [ALL])
  have nR : NoB (List.replicate j 3 ++ 1 :: (Rest1 ++ Rest2 ++ [1])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2]
  have g3 : znttLogic.Reach (hdR QNTT.SW2 [] (List.replicate (j + 1) 3 ++ 1 :: Rest1 ++ Rest2 ++ [1]))
      (hdR QNTT.SW3 [2] (List.replicate j 3 ++ 1 :: (Rest1 ++ Rest2 ++ [1]))) :=
    (sw2Mark _ nR.sym4).of_eq (by simp [List.replicate_succ]) rfl
  have g4 := sw3Write [2] _ (by intro y hy; simp at hy; subst hy; simp [ALL]) nR
  have nM' : NoB (Rest1 ++ Rest2 ++ [1]) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2]
  have g5 := clLoop [] (by intro x hx; simp at hx) j 0 (Rest1 ++ Rest2 ++ [1]) 3 nM' (by simp)
  have g6 := crsW (0 + 1 + j) (1 :: ((Rest1 ++ Rest2 ++ [1]) ++ 3 :: List.replicate j 2))
    (Sym4.cons (by simp [ALL]) (nM'.sym4.app (Sym4.cons (by simp [ALL]) (s4rep _ 2 (by simp [ALL])))))
  have e : 0 + 1 + j = j + 1 := by omega
  rw [e] at g5 g6
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at g1 g2 g3 g4 g5 g6 ⊢
  exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans g6))))

theorem sym4_one : Sym4 [1] := by intro y hy; simp at hy; subst hy; simp [ALL]

/-- The copy `M 1 0^j` appended after one copy of `P`. -/
def Dcopy (j : Nat) : List Nat := 1 :: 3 :: List.replicate j 2

theorem Dcopy_noB (j : Nat) : NoB (Dcopy j) := by
  simp only [Dcopy, NoB_cons_iff, NoB_rep_iff]; simp [NB]

theorem noB_flat (j b : Nat) : NoB (List.replicate b (Dcopy j)).flatten := by
  induction b with
  | zero => exact NoB.nil
  | succ b ih => simp only [List.replicate_succ, List.flatten_cons, NoB_app_iff]; exact ⟨Dcopy_noB j, ih⟩

/-- One cell of `K`: copy `P` once. -/
theorem kIter (w j a : Nat) (Rest0 : List Nat) (hR : NoB Rest0) :
    znttLogic.Reach
      (hdR QNTT.KX1 (List.replicate w 3 ++ [1])
        (List.replicate (j + 1) 3 ++ 1 :: (List.replicate a 2 ++ 3 :: Rest0)))
      (hdR QNTT.KX1 (List.replicate w 3 ++ [1])
        (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (a + 1) 2 ++ (Rest0 ++ Dcopy j)))) := by
  have sW : Sym4 (List.replicate w 3 ++ [1]) :=
    (s4rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have nR : NoB (List.replicate a 2 ++ 3 :: Rest0) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, hR]
  have h1 := kx1Skip (List.replicate w 3 ++ [1]) (j + 1) _ sW nR.sym4
  have h2 := kx2Mark (List.replicate w 3 ++ [1] ++ List.replicate (j + 1) 3 ++ [1]) a Rest0
    (((sW.app (s4rep (j + 1) 3 (by simp [ALL]))).app sym4_one)) hR.sym4
  have nM1 : NoB (List.replicate (a + 1) 2) := by simp only [NoB_rep_iff]; simp [NB]
  have h3 := copyP w j (List.replicate (a + 1) 2) Rest0 nM1 hR
  simp only [List.append_assoc, List.cons_append, List.nil_append, Dcopy] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

theorem kLoop (w j : Nat) :
    ∀ (b a : Nat) (Rest : List Nat), NoB Rest →
    znttLogic.Reach
      (hdR QNTT.KX1 (List.replicate w 3 ++ [1])
        (List.replicate (j + 1) 3 ++ 1 :: (List.replicate a 2 ++ List.replicate b 3 ++ Rest)))
      (hdR QNTT.KX1 (List.replicate w 3 ++ [1])
        (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (a + b) 2 ++
          (Rest ++ (List.replicate b (Dcopy j)).flatten)))) := by
  intro b
  induction b with
  | zero => intro a Rest _; simpa using LTM.Reach.refl znttLogic _
  | succ b ih =>
    intro a Rest hR
    have e1 : List.replicate a 2 ++ List.replicate (b + 1) 3 ++ Rest =
        List.replicate a 2 ++ 3 :: (List.replicate b 3 ++ Rest) := by simp [List.replicate_succ]
    have nR : NoB (List.replicate b 3 ++ Rest) := by
      simp only [NoB_app_iff, NoB_rep_iff]; simp [NB, hR]
    have h1 := kIter w j a _ nR
    have nR' : NoB (Rest ++ Dcopy j) := by simp only [NoB_app_iff]; exact ⟨hR, Dcopy_noB j⟩
    have h2 := ih (a + 1) (Rest ++ Dcopy j) nR'
    rw [e1]
    have e2 : a + 1 + b = a + (b + 1) := by omega
    rw [e2] at h2
    have := h1.trans (h2.of_eq (by simp [List.append_assoc]) rfl)
    simpa [List.replicate_succ, List.append_assoc] using this

/-- `RSR`..`RS4`: write the record separator `MM` and the header `0 1 0`. -/
theorem rsHeader (A R : List Nat) (hA : Sym4 A) (hR : NoB R) :
    znttLogic.Reach (hdR QNTT.RSR A R) (hd QNTT.KS (A ++ R ++ [1, 1, 2, 3]) [2]) := by
  have hV : Valid [ALL, NB] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1, .sym 2, .sym 3]) (rs' := [.sym 2])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ksScan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.KS L R) (hdR QNTT.KS1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ks1Skip (W R : List Nat) (hW : BitsD W) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.KS1 [] (W ++ 1 :: R)) (hdR QNTT.KX1 (W ++ [1]) R) := by
  have hV : Valid [[2, 3], ALL] [W, R] := Valid.cons hW (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [W, R]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- What one record appends: `MM 0 1 0`, `kk` copies of `P`, one copy of `W`. -/
def recTail (j j' kk : Nat) : List Nat :=
  [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten ++ Dcopy j'

theorem recTail_noB (j j' kk : Nat) : NoB (recTail j j' kk) :=
  NoB.app (NoB.app (by intro x hx; simp at hx; simp [NB]; omega) (noB_flat j kk)) (Dcopy_noB j')

/-- One whole record: `W` has `j' + 1` cells, `P` has `j + 1` cells, `K` has `kk`. -/
theorem recordOne (j' j kk : Nat) (Mid1 Mid2 : List Nat) (h1 : NoB Mid1) (h2 : NoB Mid2) :
    znttLogic.Reach
      (hdR QNTT.RSR
        (List.replicate (j' + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate kk 3 ++ 1 :: Mid1)))
        Mid2)
      (hdR QNTT.RN0 [3]
        (List.replicate (j' + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate kk 3 ++ 1 ::
          (Mid1 ++ Mid2 ++ recTail j j' kk))))) := by
  have nA : NoB (List.replicate (j' + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate kk 3 ++ 1 :: Mid1))) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff]; simp [NB, h1]
  have g1 := rsHeader _ Mid2 nA.sym4 h2
  have nL : NoB (List.replicate (j' + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate kk 3 ++ 1 :: Mid1)) ++ Mid2 ++ [1, 1, 2, 3]) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2]
  have g2 := ksScan _ [2] nL (by intro y hy; simp at hy; subst hy; simp [ALL])
  have nRest : NoB (List.replicate (j + 1) 3 ++ 1 :: (List.replicate kk 3 ++ 1 :: Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2]
  have g3 := ks1Skip (List.replicate (j' + 1) 3) _ (BitsD.rep _ _ (by simp)) nRest.sym4
  have nK : NoB (1 :: (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2])) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2]
  have g4 := kLoop (j' + 1) j kk 0 _ nK
  have hf := noB_flat j kk
  have nX : NoB (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten) := by
    simp only [NoB_app_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2, hf]
  have g5 := kx1Skip (List.replicate (j' + 1) 3 ++ [1]) (j + 1)
    (List.replicate kk 2 ++ 1 :: (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten))
    ((s4rep _ 3 (by simp [ALL])).app sym4_one)
    ((s4rep _ 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) nX.sym4))
  have g6 := kx2End (List.replicate (j' + 1) 3 ++ [1] ++ List.replicate (j + 1) 3 ++ [1]) kk
    (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten)
    ((((s4rep _ 3 (by simp [ALL])).app sym4_one).app (s4rep _ 3 (by simp [ALL]))).app sym4_one) nX.sym4
  have g7 := krSweep (List.replicate (j' + 1) 3 ++ [1] ++ List.replicate (j + 1) 3) kk
    (1 :: (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten))
    (((s4rep _ 3 (by simp [ALL])).app sym4_one).app (s4rep _ 3 (by simp [ALL])))
    (Sym4.cons (by simp [ALL]) nX.sym4)
  have nR1 : NoB (List.replicate (j + 1) 3 ++ [1]) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_nil_iff]; simp [NB]
  have nR2 : NoB (List.replicate kk 3 ++ 1 :: (Mid1 ++ Mid2 ++ [1, 1, 2, 3, 2] ++ (List.replicate kk (Dcopy j)).flatten)) := by
    simp only [NoB_app_iff, NoB_rep_iff, NoB_cons_iff, NoB_nil_iff]; simp [NB, h1, h2, hf]
  have g8 := copyW j' _ _ nR1 nR2
  simp only [recTail, List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 g6 g7 g8 ⊢
  simp only [Nat.zero_add] at g4
  exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans g8))))))

end ZP.NTT
