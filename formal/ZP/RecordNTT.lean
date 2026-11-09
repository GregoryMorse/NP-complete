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

/-- `RN0`/`RN1`: cross a field and the single separator `M`, and the first cell of the next field. -/
theorem rnField (A f : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hf : BitsD f)
    (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RN0 A (f ++ 1 :: b :: rest)) (hdR QNTT.RN0 (A ++ f ++ [1, b]) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RN0`: the record separator `MM` is reached; step back onto the last cell of `Nn`. -/
theorem rnMM (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RN0 A (f ++ 1 :: 1 :: rest)) (hd QNTT.RN2 (A ++ f) (1 :: 1 :: rest)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFT (env := [A, f, rest]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RN0`: the end of the tape is reached (no record yet). -/
theorem rnEnd (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.RN0 A f) (hd QNTT.RN2 (A ++ f) []) := by
  have hV : Valid [ALL, [2, 3]] [A, f] := Valid.cons hA (Valid.cons hf (Valid.nil _))
  exact checkFT (env := [A, f]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RN2`: mark the last unmarked cell of `Nn` and start a record. -/
theorem rn2Mark (A0 : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RN2 (A0 ++ [3] ++ List.replicate m 2) R)
      (hdR QNTT.RSR (A0 ++ [2]) (List.replicate m 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A0, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A0, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RN2`: `Nn` is used up (all marked); `RNU` unmarks it. -/
theorem rn2End (A0 : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RN2 (A0 ++ [1] ++ List.replicate m 2) R)
      (hdR QNTT.RNU (A0 ++ [1]) (List.replicate m 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A0, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A0, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rnuSweep (A : List Nat) (m : Nat) (rest : List Nat) (hA : Sym4 A) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RNU A (List.replicate m 2 ++ 1 :: rest))
      (hd QNTT.RC0 (A ++ List.replicate m 3) (1 :: rest)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, rest] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hr (Valid.nil _)))
  exact checkFT (env := [A, List.replicate m 2, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3)]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rnuSweepB (A : List Nat) (m : Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.RNU A (List.replicate m 2)) (hd QNTT.RC0 (A ++ List.replicate m 3) []) := by
  have hV : Valid [ALL, [2]] [A, List.replicate m 2] := Valid.cons hA (Valid.cons (repSet m 2) (Valid.nil _))
  exact checkFT (env := [A, List.replicate m 2]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3)]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rc0Walk (A1 : List Nat) (n : Nat) (R : List Nat) (hA : Sym4 A1) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RC0 (A1 ++ [1] ++ List.replicate n 3) R)
      (hd QNTT.RC1 A1 (1 :: (List.replicate n 3 ++ R))) := by
  have hV : Valid [ALL, [3], ALL] [A1, List.replicate n 3, R] :=
    Valid.cons hA (Valid.cons (repSet n 3) (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [A1, List.replicate n 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rc1Mark (A0 : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RC1 (A0 ++ [3] ++ List.replicate m 2) R)
      (hdR QNTT.RO0 (A0 ++ [2]) (List.replicate m 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A0, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A0, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rc1End (A0 : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RC1 (A0 ++ [1] ++ List.replicate m 2) R)
      (hdR QNTT.RCU (A0 ++ [1]) (List.replicate m 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A0, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A0, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rcuSweep (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RCU A (List.replicate m 2 ++ 1 :: R))
      (hd QNTT.WI0 (A ++ List.replicate m 3) (1 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3)]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RO0`/`RO1`: cross a field, the separator `M` and the first cell of the next field. -/
theorem roField (A f : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hf : BitsD f)
    (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RO0 A (f ++ 1 :: b :: rest)) (hdR QNTT.RO0 (A ++ f ++ [1, b]) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RO0`: a bit block. -/
theorem roBlock (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RO0 A (f ++ rest)) (hdR QNTT.RO0 (A ++ f) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFF (env := [A, f, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RO0`: at a record `MM h0 h1 ...`, set `h1 := '0'`. -/
theorem roRec (A f : List Nat) (h0 h1 : Nat) (rest : List Nat) (hA : Sym4 A) (hf : BitsD f)
    (h0b : h0 ∈ [2, 3]) (h1b : h1 ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RO0 A (f ++ 1 :: 1 :: h0 :: h1 :: rest))
      (hdR QNTT.RO0 (A ++ f ++ [1, 1, h0, 2]) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  simp at h0b h1b
  rcases h0b with rfl | rfl <;> rcases h1b with rfl | rfl
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 8) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .sym 2, .sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1, .sym 2, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 8) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .sym 2, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1, .sym 2, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 8) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 8) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RO0`: the end of the tape; `RNL` runs back to the left end, into `RN0`. -/
theorem roEnd (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.RO0 A f) (hd QNTT.RNL (A ++ f) []) := by
  have hV : Valid [ALL, [2, 3]] [A, f] := Valid.cons hA (Valid.cons hf (Valid.nil _))
  exact checkFT (env := [A, f]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rnlScan (L : List Nat) (hL : NoB L) :
    znttLogic.Reach (hd QNTT.RNL L []) (hdR QNTT.RN0 [] L) := by
  have hV : Valid [NB] [L] := Valid.cons hL (Valid.nil _)
  simpa using checkTF (env := [L]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := []) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `RN0` across the five fields `W M P M K M C M Nn`, up to the record separator `MM`. -/
theorem rnWalkMM (A f1 r2 r3 r4 r5 rest : List Nat) (a2 a3 a4 a5 : Nat) (hA : Sym4 A)
    (h1 : BitsD f1) (h2 : BitsD r2) (h3 : BitsD r3) (h4 : BitsD r4) (h5 : BitsD r5)
    (b2 : a2 ∈ [2, 3]) (b3 : a3 ∈ [2, 3]) (b4 : a4 ∈ [2, 3]) (b5 : a5 ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach
      (hdR QNTT.RN0 A (f1 ++ 1 :: a2 :: (r2 ++ 1 :: a3 :: (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: (r5 ++ 1 :: 1 :: rest))))))
      (hd QNTT.RN2 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4] ++ r4 ++ [1, a5] ++ r5)
        (1 :: 1 :: rest)) := by
  have sr : ∀ {l : List Nat}, BitsD l → Sym4 l := fun h => h.sym4
  have sb : ∀ {a : Nat}, a ∈ [2, 3] → Sym4 [a] := by
    intro a ha y hy; simp at hy; subst hy; simp at ha; rcases ha with rfl | rfl <;> simp [ALL]
  have s5 : Sym4 (1 :: 1 :: rest) := Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hr)
  have t5 : Sym4 (r5 ++ 1 :: 1 :: rest) := (sr h5).app s5
  have t4 : Sym4 (r4 ++ 1 :: a5 :: (r5 ++ 1 :: 1 :: rest)) :=
    (sr h4).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b5; rcases b5 with rfl | rfl <;> simp [ALL]) t5))
  have t3 : Sym4 (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: (r5 ++ 1 :: 1 :: rest))) :=
    (sr h3).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b4; rcases b4 with rfl | rfl <;> simp [ALL]) t4))
  have t2 : Sym4 (r2 ++ 1 :: a3 :: (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: (r5 ++ 1 :: 1 :: rest)))) :=
    (sr h2).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b3; rcases b3 with rfl | rfl <;> simp [ALL]) t3))
  have sA1 : Sym4 (A ++ f1 ++ [1, a2]) :=
    (hA.app (sr h1)).app (Sym4.cons (by simp [ALL]) (sb b2))
  have sA2 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3]) :=
    (sA1.app (sr h2)).app (Sym4.cons (by simp [ALL]) (sb b3))
  have sA3 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4]) :=
    (sA2.app (sr h3)).app (Sym4.cons (by simp [ALL]) (sb b4))
  have sA4 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4] ++ r4 ++ [1, a5]) :=
    (sA3.app (sr h4)).app (Sym4.cons (by simp [ALL]) (sb b5))
  have g1 := rnField A f1 a2 _ hA h1 b2 t2
  have g2 := rnField _ r2 a3 _ sA1 h2 b3 t3
  have g3 := rnField _ r3 a4 _ sA2 h3 b4 t4
  have g4 := rnField _ r4 a5 _ sA3 h4 b5 t5
  have g5 := rnMM _ r5 rest sA4 h5 hr
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 ⊢
  exact g1.trans (g2.trans (g3.trans (g4.trans g5)))

/-- Same, when there is no record yet (the tape ends after `Nn`). -/
theorem rnWalkEnd (A f1 r2 r3 r4 r5 : List Nat) (a2 a3 a4 a5 : Nat) (hA : Sym4 A)
    (h1 : BitsD f1) (h2 : BitsD r2) (h3 : BitsD r3) (h4 : BitsD r4) (h5 : BitsD r5)
    (b2 : a2 ∈ [2, 3]) (b3 : a3 ∈ [2, 3]) (b4 : a4 ∈ [2, 3]) (b5 : a5 ∈ [2, 3]) :
    znttLogic.Reach
      (hdR QNTT.RN0 A (f1 ++ 1 :: a2 :: (r2 ++ 1 :: a3 :: (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: r5)))))
      (hd QNTT.RN2 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4] ++ r4 ++ [1, a5] ++ r5) []) := by
  have sr : ∀ {l : List Nat}, BitsD l → Sym4 l := fun h => h.sym4
  have sb : ∀ {a : Nat}, a ∈ [2, 3] → Sym4 [a] := by
    intro a ha y hy; simp at hy; subst hy; simp at ha; rcases ha with rfl | rfl <;> simp [ALL]
  have t5 : Sym4 r5 := sr h5
  have t4 : Sym4 (r4 ++ 1 :: a5 :: r5) :=
    (sr h4).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b5; rcases b5 with rfl | rfl <;> simp [ALL]) t5))
  have t3 : Sym4 (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: r5)) :=
    (sr h3).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b4; rcases b4 with rfl | rfl <;> simp [ALL]) t4))
  have t2 : Sym4 (r2 ++ 1 :: a3 :: (r3 ++ 1 :: a4 :: (r4 ++ 1 :: a5 :: r5))) :=
    (sr h2).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at b3; rcases b3 with rfl | rfl <;> simp [ALL]) t3))
  have sA1 : Sym4 (A ++ f1 ++ [1, a2]) :=
    (hA.app (sr h1)).app (Sym4.cons (by simp [ALL]) (sb b2))
  have sA2 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3]) :=
    (sA1.app (sr h2)).app (Sym4.cons (by simp [ALL]) (sb b3))
  have sA3 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4]) :=
    (sA2.app (sr h3)).app (Sym4.cons (by simp [ALL]) (sb b4))
  have sA4 : Sym4 (A ++ f1 ++ [1, a2] ++ r2 ++ [1, a3] ++ r3 ++ [1, a4] ++ r4 ++ [1, a5]) :=
    (sA3.app (sr h4)).app (Sym4.cons (by simp [ALL]) (sb b5))
  have g1 := rnField A f1 a2 _ hA h1 b2 t2
  have g2 := rnField _ r2 a3 _ sA1 h2 b3 t3
  have g3 := rnField _ r3 a4 _ sA2 h3 b4 t4
  have g4 := rnField _ r4 a5 _ sA3 h4 b5 t5
  have g5 := rnEnd _ r5 sA4 h5
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 ⊢
  exact g1.trans (g2.trans (g3.trans (g4.trans g5)))

/-- Words that `RO0` crosses completely (isolated separators `M`, each followed by a bit). -/
inductive GoodW : List Nat → Prop
  | nil : GoodW []
  | bit {b : Nat} {u : List Nat} : b ∈ [2, 3] → GoodW u → GoodW (b :: u)
  | mb {b : Nat} {u : List Nat} : b ∈ [2, 3] → GoodW u → GoodW (1 :: b :: u)

theorem GoodW.app {u v : List Nat} (hu : GoodW u) (hv : GoodW v) : GoodW (u ++ v) := by
  induction hu with
  | nil => simpa using hv
  | bit hb _ ih => exact GoodW.bit hb ih
  | mb hb _ ih => exact GoodW.mb hb ih

theorem GoodW.rep (j c : Nat) (hc : c ∈ [2, 3]) : GoodW (List.replicate j c) := by
  induction j with
  | zero => exact GoodW.nil
  | succ j ih => exact GoodW.bit hc ih

theorem GoodW.bits {u : List Nat} (h : BitsD u) : GoodW u := by
  induction u with
  | nil => exact GoodW.nil
  | cons a u ih => exact GoodW.bit (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem GoodW.sym4 {u : List Nat} (h : GoodW u) : Sym4 u := by
  induction h with
  | nil => exact Sym4.nil
  | bit hb _ ih =>
    exact Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) ih
  | mb hb _ ih =>
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) ih)

theorem roGood {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.RO0 A (u ++ rest)) (hdR QNTT.RO0 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := roBlock A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb)
      (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have h1 := roField A [] b (u ++ rest) hA (by intro x hx; simp at hx) hb (hu'.sym4.app hr)
    have h2 := ih (A ++ [] ++ [1, b]) rest (by simpa using hA.app sb) hr
    simpa using h1.trans h2

/-- A record with header second cell `h1`. -/
def recH (h1 j j' kk : Nat) : List Nat :=
  [1, 1, 2, h1, 2] ++ (List.replicate kk (Dcopy j)).flatten ++ Dcopy j'

theorem recTail_eq (j j' kk : Nat) : recTail j j' kk = recH 3 j j' kk := rfl

/-- The record list `(h1, j')` as a tape word. -/
def recsFlat (j kk : Nat) (ps : List (Nat × Nat)) : List Nat :=
  (ps.map fun q => recH q.1 j q.2 kk).flatten

/-- The `RO` pass resets every header's second cell. -/
def resetO (ps : List (Nat × Nat)) : List (Nat × Nat) := ps.map fun q => (2, q.2)

theorem goodW_Dcopy (j : Nat) : GoodW (Dcopy j) :=
  GoodW.mb (by simp) (GoodW.rep _ _ (by simp))

theorem goodW_flat (j : Nat) : ∀ kk, GoodW (List.replicate kk (Dcopy j)).flatten := by
  intro kk
  induction kk with
  | zero => exact GoodW.nil
  | succ kk ih => simp only [List.replicate_succ, List.flatten_cons]; exact (goodW_Dcopy j).app ih

theorem goodW_body (j j' kk : Nat) : GoodW (2 :: ((List.replicate kk (Dcopy j)).flatten ++ Dcopy j')) :=
  GoodW.bit (by simp) ((goodW_flat j kk).app (goodW_Dcopy j'))

theorem recsFlat_noB (j kk : Nat) : ∀ ps : List (Nat × Nat), (∀ q ∈ ps, q.1 ∈ [2, 3]) → NoB (recsFlat j kk ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact NoB.nil
  | cons q ps ih =>
    intro h
    simp only [recsFlat, List.map_cons, List.flatten_cons] at ih ⊢
    refine NoB.app ?_ (ih (fun x hx => h x (by simp [hx])))
    have hq := h q (by simp)
    simp only [recH, List.append_assoc, List.cons_append, List.nil_append]
    refine NoB.cons (by simp [NB]) (NoB.cons (by simp [NB]) (NoB.cons (by simp [NB]) (NoB.cons ?_ (NoB.cons (by simp [NB]) (NoB.app (noB_flat j kk) (Dcopy_noB q.2))))))
    simp at hq; rcases hq with h | h <;> simp [NB, h]

/-- The `RO` pass: from the start of a `GoodW` word followed by the records, to the end of the tape. -/
theorem roAll (j kk : Nat) :
    ∀ (ps : List (Nat × Nat)) (A u : List Nat), (∀ q ∈ ps, q.1 ∈ [2, 3]) → Sym4 A → GoodW u →
    znttLogic.Reach (hdR QNTT.RO0 A (u ++ recsFlat j kk ps))
      (hd QNTT.RNL (A ++ u ++ recsFlat j kk (resetO ps)) []) := by
  intro ps
  induction ps with
  | nil =>
    intro A u _ hA hu
    have h1 := roGood hu A [] hA Sym4.nil
    have h2 := roEnd (A ++ u) [] (hA.app hu.sym4) (by intro x hx; simp at hx)
    simpa [recsFlat, resetO] using h1.trans h2
  | cons q ps ih =>
    intro A u hq hA hu
    have hq1 := hq q (by simp)
    have hq' : ∀ x ∈ ps, x.1 ∈ [2, 3] := fun x hx => hq x (by simp [hx])
    have sB := (goodW_body j q.2 kk).sym4
    have sPs := (recsFlat_noB j kk ps hq').sym4
    have sRest : Sym4 ((2 :: ((List.replicate kk (Dcopy j)).flatten ++ Dcopy q.2)) ++ recsFlat j kk ps) := sB.app sPs
    have sAll : Sym4 (recsFlat j kk (q :: ps)) := (recsFlat_noB j kk (q :: ps) hq).sym4
    have sA' : Sym4 (A ++ u) := hA.app hu.sym4
    have h1 := roGood hu A (recsFlat j kk (q :: ps)) hA sAll
    have h2 := roRec (A ++ u) [] 2 q.1 ((List.replicate kk (Dcopy j)).flatten ++ Dcopy q.2 ++ recsFlat j kk ps |> fun r => 2 :: r)
      sA' (by intro x hx; simp at hx) (by simp) hq1 sRest
    have sA'' : Sym4 (A ++ u ++ [] ++ [1, 1, 2, 2]) := by
      simpa using sA'.app (show Sym4 [1, 1, 2, 2] by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [ALL])
    have h3 := ih (A ++ u ++ [] ++ [1, 1, 2, 2]) (2 :: ((List.replicate kk (Dcopy j)).flatten ++ Dcopy q.2)) hq' sA''
      (goodW_body j q.2 kk)
    simp only [recsFlat, resetO, List.map_cons, List.flatten_cons, recH, List.append_assoc, List.cons_append,
      List.nil_append, List.map_map] at h1 h2 h3 ⊢
    exact h1.trans (h2.trans h3)

/-- The tape word before the records: `W M P M K M C M`. -/
def PreT (w j k1 : Nat) (Cf : List Nat) : List Nat :=
  List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ 1 :: (Cf ++ [1])))

theorem rnWalkS (A : List Nat) (w j k1 : Nat) (c0 : Nat) (cr : List Nat) (n0 : Nat) (nr Tl : List Nat)
    (hA : Sym4 A) (hC : BitsD (c0 :: cr)) (hN : BitsD (n0 :: nr))
    (hT : Tl = [] ∨ ∃ rest, Tl = 1 :: 1 :: rest ∧ Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RN0 A (PreT w j k1 (c0 :: cr) ++ (n0 :: nr) ++ Tl))
      (hd QNTT.RN2 (A ++ PreT w j k1 (c0 :: cr) ++ (n0 :: nr)) Tl) := by
  have hc0 := hC c0 (by simp)
  have hn0 := hN n0 (by simp)
  have hcr : BitsD cr := fun x hx => hC x (by simp [hx])
  have hnr : BitsD nr := fun x hx => hN x (by simp [hx])
  have e1 : PreT w j k1 (c0 :: cr) ++ (n0 :: nr) ++ Tl =
      List.replicate w 3 ++ 1 :: 3 :: (List.replicate j 3 ++ 1 :: 3 :: (List.replicate k1 3 ++ 1 :: c0 ::
        (cr ++ 1 :: n0 :: (nr ++ Tl)))) := by
    simp [PreT, List.replicate_succ, List.append_assoc]
  rcases hT with rfl | ⟨rest, rfl, hr⟩
  · have := rnWalkEnd A (List.replicate w 3) (List.replicate j 3) (List.replicate k1 3) cr nr 3 3 c0 n0 hA
      (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) hcr hnr (by simp) (by simp) hc0 hn0
    simp only [List.append_nil] at e1 ⊢
    rw [e1]
    simpa [PreT, List.replicate_succ, List.append_assoc] using this
  · have := rnWalkMM A (List.replicate w 3) (List.replicate j 3) (List.replicate k1 3) cr nr rest 3 3 c0 n0 hA
      (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) hcr hnr (by simp) (by simp) hc0 hn0 hr
    rw [e1]
    simpa [PreT, List.replicate_succ, List.append_assoc] using this

theorem rnWalkS' (A : List Nat) (w j k1 : Nat) (Cf Nn Tl : List Nat)
    (hA : Sym4 A) (hC : BitsD Cf) (hCne : Cf ≠ []) (hN : BitsD Nn) (hNne : Nn ≠ [])
    (hT : Tl = [] ∨ ∃ rest, Tl = 1 :: 1 :: rest ∧ Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RN0 A (PreT w j k1 Cf ++ Nn ++ Tl))
      (hd QNTT.RN2 (A ++ PreT w j k1 Cf ++ Nn) Tl) := by
  obtain ⟨c0, cr, rfl⟩ := List.exists_cons_of_ne_nil hCne
  obtain ⟨n0, nr, rfl⟩ := List.exists_cons_of_ne_nil hNne
  exact rnWalkS A w j k1 c0 cr n0 nr Tl hA hC hN hT

/-- The new records of a round: header `(3, j')` for `W` sizes `j' + 1, j' + 2, ...`. -/
def newRecs : Nat → Nat → List (Nat × Nat)
  | _, 0 => []
  | w, u + 1 => (3, w) :: newRecs (w + 1) u

theorem recsFlat_cases (j kk : Nat) (ps : List (Nat × Nat)) (hq : ∀ q ∈ ps, q.1 ∈ [2, 3]) :
    recsFlat j kk ps = [] ∨ ∃ rest, recsFlat j kk ps = 1 :: 1 :: rest ∧ Sym4 rest := by
  cases ps with
  | nil => exact Or.inl rfl
  | cons q ps =>
    have hs := (recsFlat_noB j kk (q :: ps) hq).sym4
    refine Or.inr ⟨2 :: q.1 :: 2 :: ((List.replicate kk (Dcopy j)).flatten ++ Dcopy q.2 ++ recsFlat j kk ps), ?_, ?_⟩
    · simp [recsFlat, recH, List.append_assoc]
    · have e : recsFlat j kk (q :: ps) =
          1 :: 1 :: (2 :: q.1 :: 2 :: ((List.replicate kk (Dcopy j)).flatten ++ Dcopy q.2 ++ recsFlat j kk ps)) := by
        simp [recsFlat, recH, List.append_assoc]
      rw [e] at hs
      intro x hx; exact hs x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

theorem preT_noB (w j k1 : Nat) (Cf : List Nat) (hC : NoB Cf) : NoB (PreT w j k1 Cf) := by
  simp only [PreT, NoB_app_iff, NoB_cons_iff, NoB_rep_iff, NoB_nil_iff]; simp [NB, hC]

theorem PreT_cons (w j k1 : Nat) (Cf : List Nat) : 3 :: PreT w j k1 Cf = PreT (w + 1) j k1 Cf := by
  simp [PreT, List.replicate_succ]

theorem recsFlat_append (j kk : Nat) (ps qs : List (Nat × Nat)) :
    recsFlat j kk (ps ++ qs) = recsFlat j kk ps ++ recsFlat j kk qs := by
  simp [recsFlat]

theorem recsFlat_single (j kk j' : Nat) : recsFlat j kk [(3, j')] = recTail j j' kk := by
  simp [recsFlat, recTail_eq]

theorem nnLoop (j k1 : Nat) (Cf : List Nat) (hC : BitsD Cf) (hCne : Cf ≠ []) :
    ∀ (u m w' : Nat) (ps : List (Nat × Nat)), (∀ q ∈ ps, q.1 ∈ [2, 3]) →
    znttLogic.Reach
      (hd QNTT.RN2 (PreT (w' + 1) j k1 Cf ++ (List.replicate u 3 ++ List.replicate m 2)) (recsFlat j (k1 + 1) ps))
      (hd QNTT.RN2 (PreT (w' + 1 + u) j k1 Cf ++ List.replicate (m + u) 2)
        (recsFlat j (k1 + 1) (ps ++ newRecs w' u))) := by
  intro u
  induction u with
  | zero => intro m w' ps _; simpa [newRecs] using LTM.Reach.refl znttLogic _
  | succ u ih =>
    intro m w' ps hq
    have hqs : ∀ q ∈ ps ++ [(3, w')], q.1 ∈ [2, 3] := by
      intro q hq'; simp at hq'; rcases hq' with h | h
      · exact hq q h
      · subst h; simp
    have sC : Sym4 Cf := hC.sym4
    have nC : NoB Cf := hC.noB
    have sTl : Sym4 (recsFlat j (k1 + 1) ps) := (recsFlat_noB j (k1 + 1) ps hq).sym4
    have sPre : Sym4 (PreT (w' + 1) j k1 Cf ++ List.replicate u 3) :=
      (NoB.app (preT_noB _ _ _ _ nC) (noBrep u 3 (by simp [NB]))).sym4
    have h1 := rn2Mark (PreT (w' + 1) j k1 Cf ++ List.replicate u 3) m (recsFlat j (k1 + 1) ps) sPre sTl
    have nM1 : NoB (Cf ++ 1 :: (List.replicate u 3 ++ [2])) := by
      simp only [NoB_app_iff, NoB_cons_iff, NoB_rep_iff, NoB_nil_iff]; simp [NB, nC]
    have nM2 : NoB (List.replicate m 2 ++ recsFlat j (k1 + 1) ps) := by
      simp only [NoB_app_iff, NoB_rep_iff]; simp [NB, recsFlat_noB j (k1 + 1) ps hq]
    have h2 := recordOne w' j (k1 + 1) (Cf ++ 1 :: (List.replicate u 3 ++ [2])) _ nM1 nM2
    have e12 : PreT (w' + 1) j k1 Cf ++ List.replicate u 3 ++ [2] =
        List.replicate (w' + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ 1 ::
          (Cf ++ 1 :: (List.replicate u 3 ++ [2])))) := by
      simp [PreT, List.append_assoc]
    rw [e12] at h1
    have hNe : List.replicate u 3 ++ List.replicate (m + 1) 2 ≠ [] := by
      simp [List.replicate_succ']
    have hNb : BitsD (List.replicate u 3 ++ List.replicate (m + 1) 2) := by
      intro x hx; simp [List.mem_replicate] at hx; rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    have hT := recsFlat_cases j (k1 + 1) (ps ++ [(3, w')]) hqs
    rw [recsFlat_append, recsFlat_single] at hT
    have h3 := rnWalkS' [3] (w' + 1) j k1 Cf (List.replicate u 3 ++ List.replicate (m + 1) 2)
      (recsFlat j (k1 + 1) ps ++ recTail j w' (k1 + 1)) (Sym4.cons (by simp [ALL]) Sym4.nil) hC hCne hNb hNe hT
    have h4 := ih (m + 1) (w' + 1) (ps ++ [(3, w')]) hqs
    have e34 : [3] ++ PreT (w' + 1) j k1 Cf = PreT (w' + 1 + 1) j k1 Cf := PreT_cons ..
    rw [e34] at h3
    have e1 : w' + 1 + 1 + u = w' + 1 + (u + 1) := by omega
    have e2 : m + 1 + u = m + (u + 1) := by omega
    rw [e1, e2] at h4
    have e5 : ps ++ [(3, w')] ++ newRecs (w' + 1) u = ps ++ newRecs w' (u + 1) := by
      simp [newRecs]
    rw [e5] at h4
    simp only [recsFlat_append, recsFlat_single] at h4 ⊢
    have e0 : hd QNTT.RN2 (PreT (w' + 1) j k1 Cf ++ (List.replicate (u + 1) 3 ++ List.replicate m 2)) (recsFlat j (k1 + 1) ps) =
        hd QNTT.RN2 (PreT (w' + 1) j k1 Cf ++ List.replicate u 3 ++ [3] ++ List.replicate m 2) (recsFlat j (k1 + 1) ps) := by
      simp [List.replicate_succ', List.append_assoc]
    rw [e0]
    refine h1.trans (h2.trans ((h3.of_eq (by simp [PreT, List.replicate_succ, List.append_assoc]) rfl).trans (h4.of_eq ?_ rfl)))
    simp [List.append_assoc]

/-! ### One round -/

def Pfx (w j k1 : Nat) : List Nat :=
  List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ [1]))

theorem Pfx_un (w j k1 : Nat) : Un (Pfx w j k1) := by
  intro x hx
  simp [Pfx, List.mem_replicate] at hx
  simp; omega

theorem PreT_eq (w j k1 : Nat) (Cf : List Nat) : PreT w j k1 Cf = Pfx w j k1 ++ Cf ++ [1] := by
  simp [PreT, Pfx, List.append_assoc]

theorem recsFlat_ne (j kk : Nat) (ps qs : List (Nat × Nat)) (q : Nat × Nat) (hq : ∀ x ∈ ps ++ q :: qs, x.1 ∈ [2, 3]) :
    ∃ rest, recsFlat j kk (ps ++ q :: qs) = 1 :: rest ∧ Sym4 rest := by
  rcases recsFlat_cases j kk (ps ++ q :: qs) hq with h | ⟨rest, h, hs⟩
  · exfalso
    cases ps with
    | nil => simp [recsFlat, recH] at h
    | cons a ps => simp [recsFlat, recH] at h
  · refine ⟨1 :: rest, h, ?_⟩
    have := (recsFlat_noB j kk _ hq).sym4
    rw [h] at this
    intro x hx; exact this x (List.mem_cons_of_mem _ hx)

theorem resetO_snd (ps : List (Nat × Nat)) : ∀ q ∈ resetO ps, q.1 ∈ [2, 3] := by
  intro q hq; simp [resetO] at hq; obtain ⟨a, b, _, rfl⟩ := hq; simp

theorem roundStep (w0 j k1 c m n : Nat) (ps : List (Nat × Nat)) (hq : ∀ q ∈ ps, q.1 ∈ [2, 3]) :
    znttLogic.Reach
      (hd QNTT.RC1 (Pfx (w0 + 1) j k1 ++ (List.replicate (c + 1) 3 ++ List.replicate m 2))
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)))
      (hd QNTT.RC1 (Pfx (w0 + 1 + (n + 1)) j k1 ++ (List.replicate c 3 ++ List.replicate (m + 1) 2))
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) (resetO ps ++ newRecs w0 (n + 1))))) := by
  have sP : Sym4 (Pfx (w0 + 1) j k1) := (Pfx_un _ _ _).sym4
  have hCf : BitsD (List.replicate c 3 ++ List.replicate (m + 1) 2) := by
    intro x hx; simp [List.mem_replicate] at hx; simp; omega
  have hCne : (List.replicate c 3 ++ List.replicate (m + 1) 2) ≠ [] := by simp [List.replicate_succ']
  have sR0 : Sym4 (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)) := by
    have : NoB (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)) := by
      simp only [NoB_cons_iff, NoB_app_iff, NoB_rep_iff]
      simp [NB, recsFlat_noB j (k1 + 1) ps hq]
    exact this.sym4
  have sCr : Sym4 (Pfx (w0 + 1) j k1 ++ List.replicate c 3) :=
    (Pfx_un _ _ _).sym4.app (Un.rep _ _ (by simp)).sym4
  have h1 := rc1Mark (Pfx (w0 + 1) j k1 ++ List.replicate c 3) m _ sCr sR0
  have hu : GoodW (List.replicate m 2 ++ 1 :: 3 :: List.replicate n 3) := by
    refine GoodW.app (GoodW.rep _ _ (by simp)) (GoodW.mb (by simp) (GoodW.rep _ _ (by simp)))
  have sA2 : Sym4 (Pfx (w0 + 1) j k1 ++ List.replicate c 3 ++ [2]) :=
    sCr.app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h2 := roAll j (k1 + 1) ps _ _ hq sA2 hu
  have hq1 := resetO_snd ps
  have eL : Pfx (w0 + 1) j k1 ++ List.replicate c 3 ++ [2] ++ (List.replicate m 2 ++ 1 :: 3 :: List.replicate n 3) ++
      recsFlat j (k1 + 1) (resetO ps) = PreT (w0 + 1) j k1 (List.replicate c 3 ++ List.replicate (m + 1) 2) ++ List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) (resetO ps) := by
    simp [PreT_eq, List.replicate_succ, List.replicate_succ', List.append_assoc]
  have nL : NoB (Pfx (w0 + 1) j k1 ++ List.replicate c 3 ++ [2] ++ (List.replicate m 2 ++ 1 :: 3 :: List.replicate n 3) ++
      recsFlat j (k1 + 1) (resetO ps)) := by
    rw [eL]
    exact NoB.app (NoB.app (preT_noB _ _ _ _ hCf.noB) (noBrep _ 3 (by simp [NB]))) (recsFlat_noB _ _ _ hq1)
  have h3 := rnlScan _ nL
  have h4 := rnWalkS' [] (w0 + 1) j k1 (List.replicate c 3 ++ List.replicate (m + 1) 2) (List.replicate (n + 1) 3) (recsFlat j (k1 + 1) (resetO ps)) Sym4.nil hCf hCne
    (BitsD.rep _ _ (by simp)) (by simp) (recsFlat_cases j (k1 + 1) (resetO ps) hq1)
  have h5 := nnLoop j k1 (List.replicate c 3 ++ List.replicate (m + 1) 2) hCf hCne (n + 1) 0 w0 (resetO ps) hq1
  have hq2 : ∀ q ∈ (resetO ps) ++ newRecs w0 (n + 1), q.1 ∈ [2, 3] := by
    intro q hq'
    have hn : ∀ w u, ∀ q ∈ newRecs w u, q.1 ∈ [2, 3] := by
      intro w u; induction u generalizing w with
      | zero => simp [newRecs]
      | succ u ih =>
        intro q hq''; simp [newRecs] at hq''
        rcases hq'' with h | h
        · subst h; simp
        · exact ih _ q h
    simp at hq'; rcases hq' with h | h
    · exact hq1 q h
    · exact hn _ _ q h
  obtain ⟨rest, hrest, hsrest⟩ : ∃ rest, recsFlat j (k1 + 1) ((resetO ps) ++ newRecs w0 (n + 1)) = 1 :: rest ∧ Sym4 rest := by
    have : newRecs w0 (n + 1) = (3, w0) :: newRecs (w0 + 1) n := rfl
    rw [this] at hq2 ⊢
    exact recsFlat_ne j (k1 + 1) (resetO ps) _ _ hq2
  have sC2 : Sym4 (Pfx (w0 + 1 + (n + 1)) j k1 ++ (List.replicate c 3 ++ List.replicate (m + 1) 2)) := (Pfx_un _ _ _).sym4.app hCf.sym4
  have h6 := rn2End (Pfx (w0 + 1 + (n + 1)) j k1 ++ (List.replicate c 3 ++ List.replicate (m + 1) 2)) (n + 1) (recsFlat j (k1 + 1) ((resetO ps) ++ newRecs w0 (n + 1)))
    sC2 (recsFlat_noB _ _ _ hq2).sym4
  have h7 := rnuSweep (Pfx (w0 + 1 + (n + 1)) j k1 ++ (List.replicate c 3 ++ List.replicate (m + 1) 2) ++ [1]) (n + 1) rest
    (sC2.app (by intro y hy; simp at hy; subst hy; simp [ALL])) hsrest
  have h8 := rc0Walk (Pfx (w0 + 1 + (n + 1)) j k1 ++ (List.replicate c 3 ++ List.replicate (m + 1) 2)) (n + 1) (1 :: rest) sC2 (by
    intro x hx; simp at hx; rcases hx with rfl | hx
    · simp [ALL]
    · exact hsrest x hx)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  have e1 := h1.of_eq (c3 := hd QNTT.RC1 (Pfx (w0 + 1) j k1 ++ (List.replicate (c + 1) 3 ++ List.replicate m 2))
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps))) (by simp [List.replicate_succ']) rfl
  refine e1.trans ((h2.of_eq (by simp [List.replicate_succ]) rfl).trans (h3.trans ((h4.of_eq ?_ rfl).trans
    ((h5.of_eq ?_ rfl).trans ((h6.of_eq ?_ rfl).trans ((h7.of_eq ?_ rfl).trans (h8.of_eq rfl ?_)))))))
  all_goals simp [PreT_eq, List.replicate_succ, List.replicate_succ', List.append_assoc, hrest]

/-! ### The loop over the cells of `C` -/

/-- Records after `c` rounds. -/
def roundsPs (n : Nat) : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, ps => ps
  | c + 1, w0, ps => roundsPs n c (w0 + (n + 1)) (resetO ps ++ newRecs w0 (n + 1))

/-- `W` offset after `c` rounds. -/
def wEnd (n : Nat) : Nat → Nat → Nat
  | 0, w0 => w0
  | c + 1, w0 => wEnd n c (w0 + (n + 1))

theorem roundsPs_ok (n : Nat) : ∀ c w0 ps, (∀ q ∈ ps, q.1 ∈ [2, 3]) → ∀ q ∈ roundsPs n c w0 ps, q.1 ∈ [2, 3] := by
  intro c
  induction c with
  | zero => intro w0 ps h; simpa [roundsPs] using h
  | succ c ih =>
    intro w0 ps h
    refine ih _ _ ?_
    have hn : ∀ w u, ∀ q ∈ newRecs w u, q.1 ∈ [2, 3] := by
      intro w u; induction u generalizing w with
      | zero => simp [newRecs]
      | succ u ih =>
        intro q hq''; simp [newRecs] at hq''
        rcases hq'' with h | h
        · subst h; simp
        · exact ih _ q h
    intro q hq'
    simp at hq'; rcases hq' with h' | h'
    · exact resetO_snd ps q h'
    · exact hn _ _ q h'

theorem Pfx_eq (w j k1 : Nat) :
    Pfx w j k1 = (List.replicate w 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: List.replicate (k1 + 1) 3)) ++ [1] := by
  simp [Pfx, List.append_assoc]

theorem roundLoop (j k1 n : Nat) :
    ∀ (c m w0 : Nat) (ps : List (Nat × Nat)), (∀ q ∈ ps, q.1 ∈ [2, 3]) → 0 < c + m →
    znttLogic.Reach
      (hd QNTT.RC1 (Pfx (w0 + 1) j k1 ++ (List.replicate c 3 ++ List.replicate m 2))
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)))
      (hd QNTT.WI0 (Pfx (wEnd n c w0 + 1) j k1 ++ List.replicate (m + c) 3)
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) (roundsPs n c w0 ps)))) := by
  intro c
  induction c with
  | zero =>
    intro m w0 ps hq hm
    have sA : Sym4 (List.replicate (w0 + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: List.replicate (k1 + 1) 3)) := by
      have := (Pfx_un (w0 + 1) j k1).sym4
      rw [Pfx_eq] at this
      intro x hx; exact this x (by simp at hx ⊢; omega)
    have sR : Sym4 (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)) := by
      have : NoB (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)) := by
        simp only [NoB_cons_iff, NoB_app_iff, NoB_rep_iff]
        simp [NB, recsFlat_noB j (k1 + 1) ps hq]
      exact this.sym4
    have h1 := rc1End _ m _ sA sR
    have h2 := rcuSweep (List.replicate (w0 + 1) 3 ++ 1 :: (List.replicate (j + 1) 3 ++ 1 :: List.replicate (k1 + 1) 3) ++ [1])
      m (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps)
      (sA.app (by intro y hy; simp at hy; subst hy; simp [ALL]))
      (by
        have : NoB (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) ps) := by
          simp only [NoB_app_iff, NoB_rep_iff]
          simp [NB, recsFlat_noB j (k1 + 1) ps hq]
        exact this.sym4)
    rw [Pfx_eq]
    simp only [wEnd, roundsPs, Nat.add_zero]
    refine (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl ?_)
    simp [Pfx_eq]
  | succ c ih =>
    intro m w0 ps hq hm
    have hr := roundStep w0 j k1 c m n ps hq
    have e : w0 + 1 + (n + 1) = (w0 + (n + 1)) + 1 := by omega
    rw [e] at hr
    have hq' : ∀ q ∈ resetO ps ++ newRecs w0 (n + 1), q.1 ∈ [2, 3] := by
      have := roundsPs_ok n 1 w0 ps hq
      simpa [roundsPs] using this
    have h2 := ih (m + 1) (w0 + (n + 1)) _ hq' (by omega)
    have e2 : m + 1 + c = m + (c + 1) := by omega
    rw [e2] at h2
    simp only [wEnd, roundsPs]
    exact (hr.of_eq (by simp [List.replicate_succ']) rfl).trans h2

/-! ### Setup: `WX` .. `RC1` -/

theorem wxStep (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WX [0, 3] R) (hd QNTT.WX2 [0] (3 :: R)) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTT (env := [R]) (E := []) (k := 4) hV trivial
    (ls := [.sym 0, .sym 3]) (rs := [.blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 3, .blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wx2Step (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WX2 [0] R) (hdR QNTT.WSR [3] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTF (env := [R]) (E := []) (k := 4) hV trivial
    (ls := [.sym 0]) (rs := [.blk 0 .id]) (ls' := [.sym 3]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsrScan (A R : List Nat) (hA : Sym4 A) (hR : NoB R) :
    znttLogic.Reach (hdR QNTT.WSR A R) (hd QNTT.WC0 (A ++ R) []) := by
  have hV : Valid [ALL, NB] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wc0Walk (A1 : List Nat) (n : Nat) (R : List Nat) (hA : Sym4 A1) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WC0 (A1 ++ [1] ++ List.replicate n 3) R)
      (hd QNTT.RC1 A1 (1 :: (List.replicate n 3 ++ R))) := by
  have hV : Valid [ALL, [3], ALL] [A1, List.replicate n 3, R] :=
    Valid.cons hA (Valid.cons (repSet n 3) (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [A1, List.replicate n 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The whole record build, from `WX` to `WI0`. -/
theorem recordBuild (j k1 c n : Nat) (hc : 0 < c) :
    znttLogic.Reach
      (hd QNTT.WX [0, 3] (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (n + 1) 3)))))
      (hd QNTT.WI0 (Pfx (wEnd n c 1 + 1) j k1 ++ List.replicate (0 + c) 3)
        (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (k1 + 1) (roundsPs n c 1 [])))) := by
  have sR : Sym4 (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (n + 1) 3)))) := by
    intro x hx; simp [List.mem_replicate] at hx; simp [ALL]; omega
  have h1 := wxStep _ sR
  have h2 := wx2Step (3 :: _) (Sym4.cons (by simp [ALL]) sR)
  have nR : NoB (3 :: 1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (k1 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (n + 1) 3)))) := by
    intro x hx; simp [List.mem_replicate, NB] at hx; simp [NB]; omega
  have h3 := wsrScan [3] _ (by intro y hy; simp at hy; subst hy; simp [ALL]) nR
  have sA1 : Sym4 (Pfx 2 j k1 ++ List.replicate c 3) := (Pfx_un _ _ _).sym4.app (Un.rep _ _ (by simp)).sym4
  have h4 := wc0Walk (Pfx 2 j k1 ++ List.replicate c 3) (n + 1) [] sA1 Sym4.nil
  have h5 := roundLoop j k1 n c 0 1 [] (by simp) (by omega)
  refine h1.trans (h2.trans (h3.trans ((h4.of_eq ?_ rfl).trans (h5.of_eq ?_ rfl))))
  · simp [Pfx, List.replicate_succ, List.append_assoc]
  · simp [recsFlat]

end ZP.NTT
