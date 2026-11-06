import ZP.CheckG6

namespace ZP.G

open ZP

theorem lpEndZ (b : Bool) (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (LP b) P (0 :: R)) (hd (LDone b) P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  cases b
  · exact checkFT (env := [P, R]) (E := []) (k := 3) (q := QG.gLPe) (q' := QG.gM1) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [P, R]) (E := []) (k := 3) (q := QG.gLPo) (q' := QG.gIL0) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lpEndAny (b : Bool) (P : List Nat) (c : Nat) (R : List Nat) (hc : c = 0 ∨ c = 1) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (LP b) P (c :: R)) (hd (LDone b) P (c :: R)) := by
  rcases hc with rfl | rfl
  · exact lpEndZ b P R hP hR
  · exact lpEndB b P R hP hR

theorem labelIterY (b : Bool) (ms ws' : List Nat) (v m : Nat) (d : List Nat) (j r' : Nat) (Xrest : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws', 1 ≤ e) (hX : Sym4 Xrest) :
    zgiLogic.Reach
      (hdR (LP b) (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2)
        (3 :: (List.replicate r' 3 ++ Xrest)))
      (hdR QG.gY1e (MEnc (ms ++ [v + 1]) ++ Enc ws' ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate (j + 1) 2 ++ 3 :: (List.replicate r' 3 ++ Xrest))) := by
  have hcs := Enc_entries ws' hws
  have hEnc : Enc ws' = MEs (ws'.map fun e => List.replicate e 3) := Enc_MEs ws'
  have hRt : Sym4 (3 :: (List.replicate r' 3 ++ Xrest)) := by simp [ALL, hX]
  have hP0 : Sym4 (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [ALL]
  have hP0n : NoB (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [NB]
  have hA := lpMoreB b _ (List.replicate r' 3 ++ Xrest) hP0 (by simp [ALL, hX])
  have hB := lw1Walk _ _ hP0n hRt
  have hRest : Sym4 (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ Xrest))) := by
    simp [ALL, hX]
  have hRest2 : Sym4 (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ Xrest)))) := by
    simp [ALL, hRest, hX]
  have hT : Sym4 (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ Xrest))))) := by
    simp [ALL, hRest2, hX]
  have hC1 := lw2bSkipList (List.replicate (v + 1) 3 ++ 1 :: (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ Xrest))))))
    (by simp [ALL, hT, hX]) ms [0] hms (by simp [ALL])
  have hC2 := lw2bMark ([0] ++ MEnc ms) (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ Xrest))))) v (by simp [ALL]) hT
  have hD := cxWalk (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ Xrest))))
    hRest2 (ws'.map fun e => List.replicate e 3) ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1])) hcs (by simp [ALL])
  have hE := xmCells (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ Xrest))) hRest
    (List.replicate m 3) ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1]) ++ MEs (ws'.map fun e => List.replicate e 3) ++ [1])
    (bits_rep3 m) (by rw [← hEnc]; simp [ALL])
  rw [← hEnc] at hD hE
  have hAll := hA.trans (hB.trans ((hC1.of_eq (by simp [Enc, U, MEnc, List.append_assoc]) rfl).trans
    ((hC2.of_eq rfl rfl).trans ((hD.of_eq (by simp [List.append_assoc]) rfl).trans (hE.of_eq (by simp [List.append_assoc]) rfl)))))
  refine hAll.of_eq rfl ?_
  rw [unm_rep3] at *
  rw [show ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1]) ++ Enc ws' ++ [1] ++ List.replicate m 3 ++ [1]) =
    0 :: (MEnc (ms ++ [v + 1]) ++ Enc ws' ++ [1] ++ (List.replicate m 3 ++ [1])) by
      simp [MEnc_append, MEnc, List.append_assoc]]
  rw [hdR_z0]


theorem labelFindY (m : Nat) (d : List Nat) (Xrest : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hX : Sym4 Xrest) (hY : ∃ c R', (c = 0 ∨ c = 1) ∧ Xrest = c :: R' ∧ Sym4 R') :
    ∀ (r : Nat) (ms ws : List Nat) (j : Nat), (∀ e ∈ ms, 1 ≤ e) → (∀ e ∈ ws, 1 ≤ e) → r ≤ ws.length →
    zgiLogic.Reach
      (hdR QG.gY1e (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate j 2 ++ List.replicate (r + 1) 3 ++ Xrest))
      (hd (LDone (decide (d.length % 2 = 1)))
        (MEnc (ms ++ ws.take r) ++ Enc (ws.drop r) ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++
          List.replicate (j + r + 1) 2) (Xrest)) := by
  intro r
  induction r with
  | zero =>
    intro ms ws j hms hws hr
    obtain ⟨c, R', hc, hXr, hR'⟩ := hY
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (0 + 1) 3 ++ Xrest) (by simp [ALL, hX]) d false
      (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (Xrest) j (by simp [ALL]) (by simp [ALL, hX])
    have hE := lpEndAny (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++
      List.replicate (j + 1) 2) c R' hc (by simp [ALL]) hR'
    rw [← hXr] at hE
    simp only [Bool.false_xor] at hL
    refine (hL.of_eq (by simp [List.append_assoc]) rfl).trans ((hM.of_eq (by simp [List.append_assoc]) rfl).trans
      (hE.of_eq rfl ?_))
    simp [List.append_assoc]
  | succ r ih =>
    intro ms ws j hms hws hr
    obtain ⟨w1, ws', hw⟩ : ∃ w1 ws', ws = w1 :: ws' := by
      cases ws with
      | nil => simp at hr
      | cons a l => exact ⟨a, l, rfl⟩
    subst hw
    obtain ⟨v, rfl⟩ : ∃ v, w1 = v + 1 := ⟨w1 - 1, by have := hws w1 (List.mem_cons_self ..); omega⟩
    have hws' : ∀ e ∈ ws', 1 ≤ e := fun e he => hws e (List.mem_cons_of_mem _ he)
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (r + 1 + 1) 3 ++ Xrest) (by simp [ALL, hX]) d false
      (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (List.replicate (r + 1) 3 ++ Xrest) j (by simp [ALL]) (by simp [ALL, hX])
    have hI := labelIterY (decide (d.length % 2 = 1)) ms ws' v m d j r Xrest hms hws' hX
    have hF := ih (ms ++ [v + 1]) ws' (j + 1) (by
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hms e he
        · simp at he; omega) hws' (by simp at hr; omega)
    simp only [Bool.false_xor] at hL
    refine (hL.of_eq (by simp [List.append_assoc]) rfl).trans ((hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
      ((hI.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans (hF.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_)))
    simp [List.append_assoc, MEnc_append, Nat.add_assoc, Nat.add_comm 1 r]


theorem labelIterFY (b : Bool) (ms : List Nat) (m : Nat) (d : List Nat) (j r' : Nat) (X0 Zt : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hX : NoB X0) (hZ : Sym4 Zt) :
    FailsTo
      (hdR (LP b) (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2)
        (3 :: (List.replicate r' 3 ++ (X0 ++ 0 :: Zt))))
      (unm (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2 ++
        3 :: (List.replicate r' 3 ++ X0))) Zt := by
  have hX' := hX.sym4
  have hRt : Sym4 (3 :: (List.replicate r' 3 ++ (X0 ++ 0 :: Zt))) := by simp [ALL, hX', hZ]
  have hP0 : Sym4 (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [ALL]
  have hP0n : NoB (MEnc ms ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [NB]
  have hA := lpMoreB b _ (List.replicate r' 3 ++ (X0 ++ 0 :: Zt)) hP0 (by simp [ALL, hX', hZ])
  have hB := lw1Walk _ _ hP0n hRt
  have hR1 : Sym4 (1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ (X0 ++ 0 :: Zt))))) := by
    simp [ALL, hX', hZ]
  have hC := lw2bSkipList (1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ (X0 ++ 0 :: Zt))))) hR1 ms [0] hms (by simp [ALL])
  have hRest : Sym4 (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      3 :: (List.replicate r' 3 ++ (X0 ++ 0 :: Zt)))) := by
    simp [ALL, hX', hZ]
  have hD := lw2bFail ([0] ++ MEnc ms) _ (by simp [ALL]) hRest
  have hAll := hA.trans (hB.trans ((hC.of_eq (by simp [MEnc, List.append_assoc]) rfl).trans (hD.of_eq rfl rfl)))
  refine FailsTo.mk' (A := MEnc ms ++ [1])
    (R1 := List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ 3 :: (List.replicate r' 3 ++ X0)))
    (by simp [NB]) (by simp [NB, hX]) (by simp [List.append_assoc]) ?_
  refine hAll.of_eq (by simp [List.append_assoc]) ?_
  rw [show [0] ++ MEnc ms ++ [1] = 0 :: (MEnc ms ++ [1]) by simp]
  rw [hdR_z0]; simp [List.append_assoc]


theorem labelFindFY (m : Nat) (d : List Nat) (X0 Zt : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e)
    (hX : NoB X0) (hZ : Sym4 Zt) :
    ∀ (r : Nat) (ms ws : List Nat) (j : Nat), (∀ e ∈ ms, 1 ≤ e) → (∀ e ∈ ws, 1 ≤ e) → ws.length < r →
    FailsTo
      (hdR QG.gY1e (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate j 2 ++ List.replicate (r + 1) 3 ++ (X0 ++ 0 :: Zt)))
      (unm (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate j 2 ++
        List.replicate (r + 1) 3 ++ X0)) Zt := by
  have hX' := hX.sym4
  intro r
  induction r with
  | zero => intro ms ws j _ _ hr; simp at hr
  | succ r ih =>
    intro ms ws j hms hws hr
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (r + 1 + 1) 3 ++ (X0 ++ 0 :: Zt))
      (by simp [ALL, hX', hZ]) d false (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    simp only [Bool.false_xor] at hL
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (List.replicate (r + 1) 3 ++ (X0 ++ 0 :: Zt)) j (by simp [ALL]) (by simp [ALL, hX', hZ])
    cases ws with
    | nil =>
      have hI := labelIterFY (decide (d.length % 2 = 1)) ms m d j r X0 Zt hms hX hZ
      refine FailsTo.pre ((hL.of_eq (by simp [List.append_assoc]) rfl).trans
        (hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl))
        (FailsTo.ofCfg ?_ (FailsTo.cast ?_ hI))
      · simp [Enc, List.replicate_succ, List.append_assoc]
      · simp [Enc, unm_append, unm_rep2, unm_rep3, unm1, List.replicate_succ, rep3_cons, List.append_assoc]
    | cons w1 ws' =>
      obtain ⟨v, rfl⟩ : ∃ v, w1 = v + 1 := ⟨w1 - 1, by have := hws w1 (List.mem_cons_self ..); omega⟩
      have hws' : ∀ e ∈ ws', 1 ≤ e := fun e he => hws e (List.mem_cons_of_mem _ he)
      have hI := labelIterY (decide (d.length % 2 = 1)) ms ws' v m d j r (X0 ++ 0 :: Zt) hms hws' (by simp [ALL, hX', hZ])
      have hF := ih (ms ++ [v + 1]) ws' (j + 1) (by
          intro e he
          rcases List.mem_append.1 he with he | he
          · exact hms e he
          · simp at he; omega) hws' (by simp at hr; omega)
      refine FailsTo.pre ((hL.of_eq (by simp [List.append_assoc]) rfl).trans
        ((hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
          (hI.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl)))
        (FailsTo.ofCfg ?_ (FailsTo.cast ?_ hF))
      · simp [List.replicate_succ, List.append_assoc]
      · simp [unm_append, unm_rep2, unm_rep3, unm1, MEnc_append, Enc, MEnc, U, ME, List.replicate_succ, rep3_cons, List.append_assoc]


end ZP.G
