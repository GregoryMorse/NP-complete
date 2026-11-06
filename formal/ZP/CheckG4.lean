import ZP.CheckG3

namespace ZP.G

open ZP

/-- The first label fails: it points beyond `w`, or its row part overruns `H`. -/
theorem firstFail (F : HFam) (W d X' : List Nat) (p x c : Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX' : ∀ e ∈ X', 1 ≤ e) (hdl : d.length % 2 = 0)
    (hx : 1 ≤ x) (hc : c ≤ F.N)
    (hbad : W.length < x ∨ ∃ n Wr, W.drop (x - 1) = (n + 1) :: Wr ∧ F.N < c + (p + 1) * n) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc X' ++ (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ x :: X') F.Hu) F.Zt := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  have hXs : Sym4 (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (F.sym c hc)
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  have hnb := F.nb c hc
  have hX'n : NoB (Enc X') := by
    intro a ha; have := Enc_o13 X' a ha; simp [O13, NB] at this ⊢; omega
  rcases Nat.lt_or_ge W.length (r + 1) with hlt | hge
  · rcases Nat.lt_or_ge W.length r with hlt2 | hge2
    · -- label two or more beyond `w`
      have hF := labelFindF (p + 1) d (Enc X' ++ F.Hc c) F.Zt hdd
        (by simp only [NoB_app_iff, NoB_cons_iff]; simp [NB, hnb, hX'n]) F.hZ r [] W 0 (by simp) hW hlt2
      refine FailsTo.ofCfg (by simp [MEnc]) (FailsTo.cast ?_ hF)
      simp [Ufull, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, F.un c hc, List.append_assoc, unm1, Enc_append, Enc, U,
        List.replicate_succ']
    · -- the label is exactly one beyond `w`
      have hr : r = W.length := by omega
      subst hr
      have hL := labelFind (p + 1) d (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) hdd hXs W.length [] W 0 (by simp) hW (by omega)
      rw [hdf] at hL
      have hLd : (LDone false) = QG.gM1 := rfl
      rw [hLd] at hL
      have hN := rowNoTarget F W d X' p (W.length + 1) c hW hdd hX' hc
      exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc, Enc])) hN
  · obtain ⟨n, Wr, hr, hov⟩ : ∃ n Wr, W.drop r = (n + 1) :: Wr ∧ F.N < c + (p + 1) * n := by
      rcases hbad with h | ⟨n, Wr, h1, h2⟩
      · omega
      · exact ⟨n, Wr, by simpa using h1, h2⟩
    have hrl : r ≤ W.length := by omega
    have hWr : ∀ e ∈ Wr, 1 ≤ e := by
      intro e he
      have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
      exact hW e (List.mem_of_mem_drop this)
    have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
    have hL := labelFind (p + 1) d (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0 (by simp) hW hrl
    rw [hdf] at hL
    have hLd : (LDone false) = QG.gM1 := rfl
    rw [hLd, hr] at hL
    have hN := rowFail F (W.take r) Wr d X' n (r + 1) p c hms hWr hdd hX' (by omega) hc hov
    have hW' : W.take r ++ (n + 1) :: Wr = W := by rw [← hr, List.take_append_drop]
    rw [hW'] at hN
    exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc])) hN

/-- The second label fails: it points beyond `w`, or its column part fails. -/
theorem secondFail (F : HFam) (W d X' : List Nat) (p y c : Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX' : ∀ e ∈ X', 1 ≤ e) (hdl : d.length % 2 = 1)
    (hy : 1 ≤ y) (hc : c ≤ F.N)
    (hbad : W.length < y ∨ ∃ n Wr, W.drop (y - 1) = (n + 1) :: Wr ∧
      (F.N < c + n ∨ (c + n ≤ F.N ∧ F.Hc (c + n) = []) ∨ ∃ (T : List (List Nat)) (R0 : List Nat), c + n ≤ F.N ∧ (∀ t ∈ T, Bits t) ∧
        F.Hc (c + n) ++ 0 :: F.Zt = 1 :: (MP T ++ (R0 ++ 0 :: F.Zt)) ∧
        (R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
          (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)))) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate y 3 ++ 1 :: (Enc X' ++ (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ y :: X') F.Hu) F.Zt := by
  obtain ⟨r, rfl⟩ : ∃ r, y = r + 1 := ⟨y - 1, by omega⟩
  have hXs : Sym4 (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (F.sym c hc)
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hdf : decide (d.length % 2 = 1) = true := by simp [hdl]
  have hnb := F.nb c hc
  have hX'n : NoB (Enc X') := by
    intro a ha; have := Enc_o13 X' a ha; simp [O13, NB] at this ⊢; omega
  rcases Nat.lt_or_ge W.length (r + 1) with hlt | hge
  · rcases Nat.lt_or_ge W.length r with hlt2 | hge2
    · have hF := labelFindF (p + 1) d (Enc X' ++ F.Hc c) F.Zt hdd
        (by simp only [NoB_app_iff, NoB_cons_iff]; simp [NB, hnb, hX'n]) F.hZ r [] W 0 (by simp) hW hlt2
      refine FailsTo.ofCfg (by simp [MEnc]) (FailsTo.cast ?_ hF)
      simp [Ufull, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, F.un c hc, List.append_assoc, unm1, Enc_append, Enc, U,
        List.replicate_succ']
    · have hr : r = W.length := by omega
      subst hr
      have hL := labelFind (p + 1) d (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) hdd hXs W.length [] W 0 (by simp) hW (by omega)
      rw [hdf] at hL
      have hLd : (LDone true) = QG.gIL0 := rfl
      rw [hLd] at hL
      have hN := colNoTarget F W d X' p (W.length + 1) c hW hdd hX' hc
      exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc, Enc])) hN
  · obtain ⟨n, Wr, hr, hcb⟩ : ∃ n Wr, W.drop r = (n + 1) :: Wr ∧
        (F.N < c + n ∨ (c + n ≤ F.N ∧ F.Hc (c + n) = []) ∨ ∃ (T : List (List Nat)) (R0 : List Nat), c + n ≤ F.N ∧ (∀ t ∈ T, Bits t) ∧
        F.Hc (c + n) ++ 0 :: F.Zt = 1 :: (MP T ++ (R0 ++ 0 :: F.Zt)) ∧
        (R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
          (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q))) := by
      rcases hbad with h | ⟨n, Wr, h1, h2⟩
      · omega
      · exact ⟨n, Wr, by simpa using h1, h2⟩
    have hrl : r ≤ W.length := by omega
    have hWr : ∀ e ∈ Wr, 1 ≤ e := by
      intro e he
      have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
      exact hW e (List.mem_of_mem_drop this)
    have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
    have hL := labelFind (p + 1) d (Enc X' ++ (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0 (by simp) hW hrl
    rw [hdf] at hL
    have hLd : (LDone true) = QG.gIL0 := rfl
    rw [hLd, hr] at hL
    obtain ⟨e, d', hdeq⟩ : ∃ e d', d = e :: d' := by
      cases d with
      | nil => simp at hdl
      | cons e d' => exact ⟨e, d', rfl⟩
    have hde : 1 ≤ e := hdd e (by simp [hdeq])
    have hd' : ∀ x ∈ d', 1 ≤ x := fun x hx => hdd x (by simp [hdeq, hx])
    have hnA : NoB (MEnc (W.take r) ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++
        List.replicate (0 + r + 1) 2) := by simp [NB]
    have hIL := il0Walk' _ (1 :: (Enc X' ++ (F.Hc c ++ 0 :: F.Zt))) hnA (Sym4.cons (by simp [ALL]) hXs)
    have hws := Enc_entries Wr hWr
    have hxs0 : ∀ x ∈ (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
        X'.map fun e => List.replicate e 3)), Bits x ∧ x ≠ [] := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
      · exact ⟨bits_rep2 e, by intro h; have := congrArg List.length h; simp at this; omega⟩
      · exact ⟨bits_rep2 v, by have := hd' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
      · exact ⟨bits_rep2 _, by intro h; have := congrArg List.length h; simp at this⟩
      · exact ⟨bits_rep3 v, by have := hX' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    have hwsb : ∀ x ∈ Wr.map (fun e => List.replicate e 3), Bits x ∧ x ≠ [] := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    have hF : FailsTo
        (hdR QG.gIL1b [] (MEnc (W.take r) ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
          (MEs (Wr.map fun e => List.replicate e 3) ++ 1 :: (List.replicate (p + 1) 3 ++ 1 ::
            (MEs (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
              X'.map fun e => List.replicate e 3)) ++ (F.Hc c ++ 0 :: F.Zt))))))
        (UG (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++
          List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)) n (p + 1) F.Hu) F.Zt := by
      rcases hcb with hov | ⟨hcn0, hT0⟩ | ⟨T, R0, hcn, hTb, hT, hR⟩
      · exact colPartF1 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
          ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)
          hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
          (p + 1) n c hc hov
      · exact colPartF3 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
          ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)
          hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
          (p + 1) n c hcn0 hT0
      · exact colPartF2 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
          ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)
          hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
          (p + 1) n c hcn T R0 hTb hT hR
    refine FailsTo.pre (hL.of_eq (by simp [MEnc]) rfl) (FailsTo.pre (hIL.of_eq rfl ?_) (FailsTo.cast ?_ hF))
    · subst hdeq
      simp [Enc, U, MEnc, Enc_MEs, MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
    have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = Enc Wr := by
      rw [← Enc_MEs, unm_Enc]
    have e4 : MEs (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
        X'.map fun e => List.replicate e 3)) = MEnc (e :: d') ++ List.replicate (r + 1) 2 ++ 1 :: Enc X' := by
      simp [MEnc_MEs, Enc_MEs, MEs_append, MEs, ME, List.append_assoc]
    have u4 : unm (MEs (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 ::
        X'.map fun e => List.replicate e 3))) = Enc ((e :: d') ++ (r + 1) :: X') := by
      rw [e4]
      simp [unm_append, unm_MEnc, unm_rep2, unm_Enc, Enc_append, Enc, U, unm1, List.append_assoc]
    have eW : Enc W = Enc (W.take r) ++ Enc ((n + 1) :: Wr) := by
      rw [← Enc_append, ← hr, List.take_append_drop]
    subst hdeq
    simp only [UG, Ufull, u3, u4, eW, unm_Enc, unm_rep3, F.hu_unm]
    simp [Enc, U, List.replicate_succ, rep3_cons, List.append_assoc]

def RowBad (F : HFam) (W : List Nat) (p x c : Nat) : Prop :=
  W.length < x ∨ ∃ n Wr, W.drop (x - 1) = (n + 1) :: Wr ∧ F.N < c + (p + 1) * n

def ColBad (F : HFam) (W : List Nat) (y c : Nat) : Prop :=
  W.length < y ∨ ∃ n Wr, W.drop (y - 1) = (n + 1) :: Wr ∧
      (F.N < c + n ∨ (c + n ≤ F.N ∧ F.Hc (c + n) = []) ∨ ∃ (T : List (List Nat)) (R0 : List Nat), c + n ≤ F.N ∧ (∀ t ∈ T, Bits t) ∧
        F.Hc (c + n) ++ 0 :: F.Zt = 1 :: (MP T ++ (R0 ++ 0 :: F.Zt)) ∧
        (R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
          (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)))

/-- One edge `(x, y)` fails (at the `HFam` level). -/
theorem edgeFailF (F : HFam) (W d X'' : List Nat) (p x y c : Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hX'' : ∀ e ∈ X'', 1 ≤ e) (hdl : d.length % 2 = 0)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hc : c ≤ F.N)
    (hbad : RowBad F W p x c ∨ ∃ n Wr, W.drop (x - 1) = (n + 1) :: Wr ∧ c + (p + 1) * n ≤ F.N ∧
      ColBad F W y (c + (p + 1) * n)) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc (y :: X'') ++ (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ x :: y :: X'') F.Hu) F.Zt := by
  have hX' : ∀ e ∈ y :: X'', 1 ≤ e := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hy
    · exact hX'' e he
  rcases hbad with h | ⟨n, Wr, hr, hcn, hcol⟩
  · exact firstFail F W d (y :: X'') p x c hW hdd hX' hdl hx hc h
  · obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
    have hr' : W.drop r = (n + 1) :: Wr := by simpa using hr
    have hWr : ∀ e ∈ Wr, 1 ≤ e := by
      intro e he
      have : e ∈ W.drop r := by rw [hr']; exact List.mem_cons_of_mem _ he
      exact hW e (List.mem_of_mem_drop this)
    have hrow := rowHalf F W Wr d (y :: X'') r n p c hW hdd hX' hdl hr' hc hcn
    have hdd' : ∀ e ∈ d ++ [r + 1], 1 ≤ e := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hdd e he
      · simp at he; omega
    have hsec := secondFail F W (d ++ [r + 1]) X'' p y (c + (p + 1) * n) hW hdd' hX'' (by simp; omega) hy (by omega) hcol
    refine FailsTo.pre (hrow.of_eq rfl (by simp [Enc, U, List.append_assoc])) (FailsTo.cast ?_ hsec)
    simp [Ufull, List.append_assoc]

/-- Shapes at the point where the column part looks for its target (index `i`). -/
theorem hsBad (hs : List (List Nat)) (hb : ∀ t ∈ hs, Bits t) (hne : hs ≠ []) (J : List Nat) (hJ : JShape J)
    (Zt : List Nat) (i : Nat) (hi : i ≤ hs.length)
    (hbad : i = hs.length ∨ ∃ h : i < hs.length, hs[i] = [] ∨ ∃ Q, hs[i] = 2 :: Q) :
    ∃ (T : List (List Nat)) (R0 : List Nat), (∀ t ∈ T, Bits t) ∧
      HP hs i ++ J ++ 0 :: Zt = MP T ++ (R0 ++ 0 :: Zt) ∧
      (R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
        (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)) := by
  rcases hbad with rfl | ⟨hlt, ht⟩
  · obtain ⟨tl, h1, h2⟩ := HP_full hs hne
    obtain ⟨L, rfl⟩ : ∃ L, hs = L ++ [tl] := by
      have h3 := List.dropLast_concat_getLast hne
      rw [List.getLast?_eq_getLast hne] at h2
      have h4 : hs.getLast hne = tl := by simpa using h2
      exact ⟨hs.dropLast, by rw [← h4]; exact h3.symm⟩
    simp only [List.dropLast_concat] at h1
    have hbT : ∀ t ∈ L, Bits t := fun t ht => hb t (by simp [ht])
    have hbtl : Bits tl := hb tl (by simp)
    rcases hJ.2 with hJ0 | hJ1 | ⟨J', hJ'⟩
    · refine ⟨L, 2 :: tl, hbT, ?_, Or.inr (Or.inr (Or.inl ⟨tl, hbtl, rfl⟩))⟩
      rw [h1, hJ0]; simp
    · refine ⟨L ++ [tl], [], hb, ?_, Or.inl rfl⟩
      rw [h1, hJ1, MP_append]
      simp [MP]
    · refine ⟨L ++ [tl], 1 :: J', hb, ?_, Or.inr (Or.inl ⟨J', ?_, rfl⟩)⟩
      · rw [h1, hJ', MP_append]
        simp [MP]
      · have := hJ.1; rw [hJ'] at this
        intro a ha; exact this a (by simp [ha])
  · have hbt := hb _ (List.getElem_mem hlt)
    have e0 := List.take_append_drop i hs
    have h1 : hs.drop i = hs[i] :: hs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [h1] at e0
    obtain ⟨A, hA⟩ : ∃ A, A = hs.take i := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = hs.drop (i + 1) := ⟨_, rfl⟩
    rw [← hA, ← hB] at e0
    have hAl : A.length = i := by rw [hA]; simp; omega
    have hAb : ∀ t ∈ A, Bits t := fun t ht => hb t (List.mem_of_mem_take (hA ▸ ht))
    have hBb : ∀ t ∈ B, Bits t := fun t ht => hb t (List.mem_of_mem_drop (hB ▸ ht))
    generalize hs[i] = t at e0 ht hbt
    have hcut := (HP_cut t B A).1
    rw [e0, hAl] at hcut
    have sQB : NoB (Qof B ++ J) := by
      refine NoB.app ?_ hJ.1
      cases B with
      | nil => simp [Qof]
      | cons u ts => exact (NoB.cons (by simp [NB]) (HP_noB _ _ hBb))
    rcases ht with ht | ⟨Q, hQ⟩
    · refine ⟨A, 3 :: (Qof B ++ J), hAb, ?_, ?_⟩
      · rw [hcut, ht]; simp
      · cases B with
        | nil => rcases hJ.2 with hJ0 | hJ1 | ⟨J', hJ'⟩
                 · right; right; right; right; left; simp [Qof, hJ0]
                 · right; right; right; left; exact ⟨[], NoB.nil, by simp [Qof, hJ1]⟩
                 · right; right; right; left
                   refine ⟨1 :: J', ?_, by simp [Qof, hJ']⟩
                   have := hJ.1; rw [hJ'] at this
                   intro a ha; exact this a (by simp [ha])
        | cons u ts => right; right; right; left; exact ⟨HP (u :: ts) 0 ++ J, NoB.app (HP_noB _ _ hBb) hJ.1, by simp [Qof]⟩
    · have hbQ : Bits Q := by
        have := hbt; rw [hQ] at this
        intro a ha; exact this a (by simp [ha])
      refine ⟨A, 3 :: 2 :: (Q ++ Qof B ++ J), hAb, ?_, ?_⟩
      · rw [hcut, hQ]; simp
      · right; right; right; right; right
        have nQ : NoB (Qof B) := by
          cases B with
          | nil => simp [Qof]
          | cons u ts => exact NoB.cons (by simp [NB]) (HP_noB _ _ hBb)
        exact ⟨Q ++ Qof B ++ J, NoB.app (NoB.app hbQ.noB nQ) hJ.1, rfl⟩

/-- One edge fails in the reference semantics: the machine fails on the unmarked tape. -/
theorem edgeFail (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H used J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (hne : H ≠ []) (d X'' : List Nat) (x y : Nat)
    (hdd : ∀ e ∈ d, 1 ≤ e) (hX'' : ∀ e ∈ X'', 1 ≤ e) (hdl : d.length % 2 = 0) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hfail : x > W.length ∨ y > W.length ∨
      ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0 > H.length ∨
        H.getD ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0 - 1) 0 < 2 ∨
        ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) ∈ used)) (hHv : ∀ e ∈ W, 1 ≤ e) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc (y :: X'') ++ 1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt))))
      (Ufull W (p + 1) (d ++ x :: y :: X'') (unm (1 :: (HP (Hs H used) 0 ++ J)))) Zt := by
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  let F := HFam.ofHP (Hs H used) hhne (Hs_bits H used) J hJ Zt hZ
  have hFN : F.N = H.length := by simp [F, HFam.ofHP, Hs_length]
  have hFc : ∀ c, F.Hc c = 1 :: (HP (Hs H used) c ++ J) := fun c => rfl
  have hFH : F.Hu = unm (1 :: (HP (Hs H used) 0 ++ J)) := rfl
  have key : FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc (y :: X'') ++ (F.Hc 0 ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ x :: y :: X'') F.Hu) F.Zt := by
    refine edgeFailF F W d X'' p x y 0 hW hdd hX'' hdl hx hy (Nat.zero_le _) ?_
    by_cases hxW : x ≤ W.length
    · obtain ⟨n, Wr, hr, hgr⟩ := W_split W hW (x - 1) (by omega)
      by_cases hov : H.length < (p + 1) * n
      · exact Or.inl (Or.inr ⟨n, Wr, hr, by rw [hFN]; omega⟩)
      · refine Or.inr ⟨n, Wr, hr, by rw [hFN]; omega, ?_⟩
        by_cases hyW : y ≤ W.length
        · obtain ⟨n', Wr', hr', hgr'⟩ := W_split W hW (y - 1) (by omega)
          have hkn : (W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0 = n * (p + 1) + n' + 1 := by
            rw [hgr, hgr']; simp [Nat.add_assoc]
          rw [hkn] at hfail
          simp only [Nat.add_sub_cancel] at hfail
          have hmul : (p + 1) * n = n * (p + 1) := Nat.mul_comm _ _
          refine Or.inr ⟨n', Wr', hr', ?_⟩
          by_cases hbig : H.length < 0 + (p + 1) * n + n'
          · exact Or.inl (by rw [hFN]; exact hbig)
          · refine Or.inr (Or.inr ?_)
            have hcn : 0 + (p + 1) * n + n' ≤ H.length := by omega
            have hsh := hsBad (Hs H used) (Hs_bits H used) hhne J hJ Zt (0 + (p + 1) * n + n')
              (by rw [Hs_length]; exact hcn) ?_
            · obtain ⟨T, R0, hT, he, hR⟩ := hsh
              exact ⟨T, R0, by rw [hFN]; exact hcn, hT, by rw [hFc, List.cons_append, List.append_assoc]; exact congrArg (List.cons 1) (by simp only [List.append_assoc] at he ⊢; exact he), hR⟩
            · by_cases heq : 0 + (p + 1) * n + n' = H.length
              · exact Or.inl (by rw [Hs_length]; exact heq)
              · have hlt : 0 + (p + 1) * n + n' < H.length := by omega
                refine Or.inr ⟨by rw [Hs_length]; exact hlt, ?_⟩
                rw [Hs_get _ _ _ hlt]
                have hi : 0 + (p + 1) * n + n' = n * (p + 1) + n' := by omega
                rw [hi]
                rcases hfail with h | h | h | h | h
                · omega
                · omega
                · omega
                · left; simp [tl]; rw [List.getD_eq_getElem?_getD] at h; omega
                · by_cases hv : H.getD (n * (p + 1) + n') 0 ≤ 1
                  · left; simp [tl]; rw [List.getD_eq_getElem?_getD] at hv; omega
                  · right
                    refine ⟨List.replicate (H.getD (n * (p + 1) + n') 0 - 2) 3, ?_⟩
                    have hm : decide (n * (p + 1) + n' + 1 ∈ used) = true := by
                      simpa using h
                    rw [List.getD_eq_getElem?_getD] at hv
                    simp [tl, hm]; omega
        · exact Or.inl (by omega)
    · exact Or.inl (Or.inl (by omega))
  exact key

theorem Hu_used (H used used' J : List Nat) :
    unm (1 :: (HP (Hs H used) 0 ++ J)) = unm (1 :: (HP (Hs H used') 0 ++ J)) := by
  have h1 := HP_unm_map (Hs H used)
  have h2 := HP_unm_map (Hs H used')
  simp only [unm_cons, unm_append]
  rw [h1, h2, Hs_unm, Hs_unm]

theorem loopFail (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e)
    (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt) :
    ∀ (X d used : List Nat), (∀ e ∈ X, 1 ≤ e) → (∀ e ∈ d, 1 ≤ e) → d.length % 2 = 0 →
    checkEdges W (p + 1) H (pairsOf X) used = none →
    FailsTo (cfgE W p H J Zt d X used) (Ufull W (p + 1) (d ++ X) (unm (1 :: (HP (Hs H []) 0 ++ J)))) Zt
  | [], d, used, _, _, _, h => by simp [pairsOf, checkEdges] at h
  | [x], d, used, _, _, _, h => by simp [pairsOf, checkEdges] at h
  | x :: y :: rest, d, used, hX, hdd, hdl, h => by
    simp only [pairsOf, checkEdges] at h
    have hx1 : 1 ≤ x := hX x (by simp)
    have hy1 : 1 ≤ y := hX y (by simp)
    have hrest : ∀ e ∈ rest, 1 ≤ e := fun e he => hX e (by simp [he])
    by_cases h1 : x > W.length ∨ y > W.length
    · have := edgeFail W hW p H used J Zt hJ hZ hne d rest x y hdd hrest hdl hx1 hy1
        (by rcases h1 with h1 | h1 <;> simp [h1]) hW
      refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ this)
      · simp [cfgE, Enc, U, List.append_assoc]
      · rw [Hu_used H used []]
    rw [if_neg h1] at h
    by_cases h2 : ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) > H.length ∨
        H.getD (((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) - 1) 0 < 2 ∨
        ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) ∈ used
    · have := edgeFail W hW p H used J Zt hJ hZ hne d rest x y hdd hrest hdl hx1 hy1 (Or.inr (Or.inr h2)) hW
      refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ this)
      · simp [cfgE, Enc, U, List.append_assoc]
      · rw [Hu_used H used []]
    rw [if_neg h2] at h
    simp only [not_or] at h1 h2
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hk, hv, hu⟩ := h2
    have hstep := edgeStep W hW p H used J Zt hJ hZ hne hHv d rest (x - 1) (y - 1) hdd hrest hdl
      (by omega) (by omega) _ rfl (by omega) (by omega) hu
    have hdd' : ∀ e ∈ d ++ [x, y], 1 ≤ e := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hdd e he
      · simp at he; rcases he with rfl | rfl <;> omega
    have ih := loopFail W hW p H hne hHv J Zt hJ hZ rest (d ++ [x, y]) _ hrest hdd'
      (by simp; omega) h
    have hs2 : zgiLogic.Reach (cfgE W p H J Zt d (x :: y :: rest) used)
        (cfgE W p H J Zt (d ++ [x, y]) rest (((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) :: used)) := by
      refine hstep.of_eq ?_ ?_
      · simp [cfgE, Enc, U, show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega, List.append_assoc]
      · simp [cfgE, show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega]
    exact FailsTo.pre hs2 (FailsTo.cast (by simp [List.append_assoc]) ih)

theorem Hs_ok (H used : List Nat) (hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ used) :
    ∀ t ∈ Hs H used, t = [] ∨ ∃ t', Bits t' ∧ t = 2 :: t' := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
  have hi' : i < H.length := by simpa using hi
  have hall' := hall i hi'
  simp only [List.getD_eq_getElem?_getD] at hall' ⊢
  rcases hall' with h | h
  · left; simp [tl]; omega
  · by_cases hv : H[i]?.getD 0 ≤ 1
    · left; simp [tl, hv]
    · right
      refine ⟨List.replicate (H[i]?.getD 0 - 2) 3, ?_, ?_⟩
      · intro a ha; rw [List.eq_of_mem_replicate ha]; simp [bits]
      · simp [tl, hv, h]

/-- After all edges: the final check accepts when every entry `≥ 2` is used. -/
theorem finalAcc (W : List Nat) (p : Nat) (H : List Nat) (hne : H ≠ []) (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (d used : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0)
    (hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ used) :
    ∃ c', AccS c' ∧ zgiLogic.Reach (cfgE W p H J Zt d [] used) c' := by
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  have sH : Sym4 (HP (Hs H used) 0 ++ J ++ 0 :: Zt) :=
    ((HP_sym4 _ _ (Hs_bits H used)).app hJ.1.sym4).app (Sym4.cons (by simp [ALL]) hZ)
  have sP : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) := by
    refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
    have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
  have h1 := lblWalk (1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) sH) d false _ hdd sP
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  rw [hdf] at h1
  simp only [Bool.xor_false] at h1
  have sP2 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d) := sP.app (MEnc_sym4 d)
  have h2 := y1eEnd _ _ sP2 sH
  obtain ⟨c', hc, h3⟩ := finalOk J Zt hJ hZ (Hs H used) hhne (Hs_bits H used) (Hs_ok H used hall) _ (sP2.app (show Sym4 [1] from Sym4.cons (by simp [ALL]) Sym4.nil))
  exact ⟨c', hc, ((h1.of_eq (by simp [cfgE, Enc]) rfl).trans h2).trans h3⟩

theorem exists_min (P : Nat → Prop) (h : ∃ k, P k) : ∃ i, P i ∧ ∀ j < i, ¬ P j := by
  classical
  obtain ⟨k, hk⟩ := h
  have : ∀ n k, k ≤ n → P k → ∃ i, P i ∧ ∀ j < i, ¬ P j := by
    intro n
    induction n with
    | zero => intro k hk0 hPk; exact ⟨k, hPk, fun j hj => by omega⟩
    | succ n ih =>
      intro k hkn hPk
      by_cases hc : ∃ j < k, P j
      · obtain ⟨j, hj, hPj⟩ := hc
        exact ih j (by omega) hPj
      · exact ⟨k, hPk, fun j hj hP => hc ⟨j, hj, hP⟩⟩
  exact this k k (Nat.le_refl _) hk

theorem tl_ok (v : Nat) (b : Bool) (h : v < 2 ∨ b = true) : tl v b = [] ∨ ∃ t', Bits t' ∧ tl v b = 2 :: t' := by
  by_cases hv : v ≤ 1
  · left; simp [tl, hv]
  · right
    have hb : b = true := by
      rcases h with h | h
      · omega
      · exact h
    refine ⟨List.replicate (v - 2) 3, ?_, ?_⟩
    · intro a ha; rw [List.eq_of_mem_replicate ha]; simp [bits]
    · simp [tl, hv, hb]

theorem finalFail (W : List Nat) (p : Nat) (H : List Nat) (hne : H ≠ []) (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (d used : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0)
    (hbad : ∃ k, k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ used) :
    FailsTo (cfgE W p H J Zt d [] used) (Ufull W (p + 1) d (unm (1 :: (HP (Hs H used) 0 ++ J)))) Zt := by
  classical
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  have hex : ∃ k, k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ used := hbad
  obtain ⟨i, ⟨hi, hv, hu⟩, hmin⟩ := exists_min (fun k => k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ used) hex
  have hlt : i < (Hs H used).length := by rw [Hs_length]; exact hi
  have hget : (Hs H used)[i] = 3 :: List.replicate (H.getD i 0 - 2) 3 := by
    rw [Hs_get _ _ _ hi]
    have hv1 : ¬ (H.getD i 0 ≤ 1) := by omega
    have hd : decide (i + 1 ∈ used) = false := by simpa using hu
    rw [hd]
    simp only [tl, if_neg hv1, Bool.false_eq_true, if_false]
  have e0 := List.take_append_drop i (Hs H used)
  have h1 : (Hs H used).drop i = (Hs H used)[i] :: (Hs H used).drop (i + 1) := List.drop_eq_getElem_cons hlt
  rw [h1, hget] at e0
  obtain ⟨A, hA⟩ : ∃ A, A = (Hs H used).take i := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (Hs H used).drop (i + 1) := ⟨_, rfl⟩
  rw [← hA, ← hB] at e0
  have hAb : ∀ t ∈ A, Bits t := fun t ht => Hs_bits H used t (List.mem_of_mem_take (hA ▸ ht))
  have hBb : ∀ t ∈ B, Bits t := fun t ht => Hs_bits H used t (List.mem_of_mem_drop (hB ▸ ht))
  have hAok : ∀ t ∈ A, t = [] ∨ ∃ t', Bits t' ∧ t = 2 :: t' := by
    intro t ht
    rw [hA] at ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have hj' : j < i := by have := hj; simp [Hs_length] at this; omega
    have hjH : j < H.length := by omega
    simp only [List.getElem_take]
    rw [Hs_get _ _ _ hjH]
    apply tl_ok
    have := hmin j hj'
    by_cases h2 : 2 ≤ H.getD j 0
    · right; exact Classical.byContradiction fun hb => this ⟨hjH, h2, by simpa using hb⟩
    · left; omega
  have hr : Bits (List.replicate (H.getD i 0 - 2) 3) := by
    intro a ha; rw [List.eq_of_mem_replicate ha]; simp [bits]
  have sP : NoB (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ [1]) := by
    have := Enc_o13 W
    simp only [NoB_app_iff]
    refine ⟨⟨⟨⟨fun a ha => ?_, by simp [NB]⟩, by simp [NB]⟩, (fun a ha => by have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega)⟩, by simp [NB]⟩
    have := Enc_o13 W a ha; simp [O13, NB] at this ⊢; omega
  have hfin := finalBad J Zt hJ hZ _ hr B hBb A hAb hAok _ sP
  rw [e0] at hfin
  have sH : Sym4 (HP (Hs H used) 0 ++ J ++ 0 :: Zt) :=
    ((HP_sym4 _ _ (Hs_bits H used)).app hJ.1.sym4).app (Sym4.cons (by simp [ALL]) hZ)
  have sP' : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) := by
    refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
    have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
  have hw := lblWalk (1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) sH) d false _ hdd sP'
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  rw [hdf] at hw
  simp only [Bool.xor_false] at hw
  have sP2 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d) := sP'.app (MEnc_sym4 d)
  have h2 := y1eEnd _ _ sP2 sH
  refine FailsTo.pre ((hw.of_eq (by simp [cfgE, Enc]) rfl).trans h2) (FailsTo.cast ?_ hfin)
  simp [Ufull, unm_append, unm_MEnc, unm_Enc, unm_rep3, unm1, Enc, List.append_assoc]

theorem y1oEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1o P (1 :: R)) (hdR QG.gFG (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem y1oEndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1o P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem y1oFail (P Hc Z : List Nat) (hP : Sym4 P) (hPn : NoB P) (hPne : P ≠ [])
    (hH : Hc = [] ∨ ∃ t, Hc = 1 :: t) (hnb : NoB Hc) (hZ : Sym4 Z) :
    ∃ A R1 : List Nat, NoB A ∧ NoB R1 ∧ A ++ R1 = P ++ Hc ∧
      zgiLogic.Reach (hdR QG.gY1o P (Hc ++ 0 :: Z)) (hdR QG.gFG A (R1 ++ 0 :: Z)) := by
  rcases hH with rfl | ⟨t, rfl⟩
  · exact ⟨P, [], hPn, NoB.nil, by simp, (y1oEndB P Z hP hZ).trans (gfgR' _ _ hPn hPne (Sym4.cons (by simp [ALL]) hZ)) |>.of_eq rfl (by simp)⟩
  · have ht : NoB t := ((NoB_cons_iff).1 hnb).2
    refine ⟨P ++ [1], t, hPn.app (by simp [NB]), ht, by simp, ?_⟩
    exact (y1oEnd P (t ++ 0 :: Z) hP (ht.sym4.app (Sym4.cons (by simp [ALL]) hZ))).of_eq rfl rfl

/-- A lone last label: the second label is missing, so the check fails. -/
theorem oddFailF (F : HFam) (W d : List Nat) (p x c : Nat)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0) (hx : 1 ≤ x) (hc : c ≤ F.N) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc [] ++ (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ [x]) F.Hu) F.Zt := by
  by_cases hb : RowBad F W p x c
  · exact firstFail F W d [] p x c hW hdd (by simp) hdl hx hc hb
  · obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
    have hrl : r < W.length := by
      exact Classical.byContradiction fun h => hb (Or.inl (by omega))
    obtain ⟨n, Wr, hr, _⟩ := W_split W hW r hrl
    have hcn : c + (p + 1) * n ≤ F.N := by
      exact Classical.byContradiction fun h => hb (Or.inr ⟨n, Wr, by simpa using hr, by omega⟩)
    have hrow := rowHalf F W Wr d [] r n p c hW hdd (by simp) hdl hr hc hcn
    have hdd' : ∀ e ∈ d ++ [r + 1], 1 ≤ e := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hdd e he
      · simp at he; omega
    have sP : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) := by
      refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
      have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
    have sH : Sym4 (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt) := F.sym _ hcn
    have hw := lblWalk ((F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt)) sH (d ++ [r + 1]) false _ hdd' sP
    have hdf : decide ((d ++ [r + 1]).length % 2 = 1) = true := by simp; omega
    rw [hdf] at hw
    simp only [Bool.false_xor] at hw
    have sP2 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc (d ++ [r + 1])) := sP.app (MEnc_sym4 _)
    have hnb := F.nb _ hcn
    have nP2 : NoB (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc (d ++ [r + 1])) := by
      simp only [NoB_app_iff]
      refine ⟨⟨⟨fun a ha => ?_, by simp [NB]⟩, by simp [NB]⟩, fun a ha => ?_⟩
      · have := Enc_o13 W a ha; simp [O13, NB] at this ⊢; omega
      · have := MEnc_o12 (d ++ [r + 1]) a ha; simp [O12, NB] at this ⊢; omega
    have hne2 : (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc (d ++ [r + 1])) ≠ [] := by simp
    obtain ⟨A, R1, hA, hR1, hAR, h2⟩ := y1oFail _ _ F.Zt sP2 nP2 hne2 (F.shape _ hcn) hnb F.hZ
    refine ⟨A, R1, hA, hR1, ?_, ?_⟩
    · have hun := F.un _ hcn
      rw [hAR]
      simp [Ufull, unm_append, unm_MEnc, unm_Enc, unm_rep3, unm1, hun, Enc, U, List.append_assoc]
    · have hrow' : zgiLogic.Reach
          (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
            (MEnc d ++ List.replicate (r + 1) 3 ++ 1 :: (Enc [] ++ (F.Hc c ++ 0 :: F.Zt))))
          (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
            (MEnc (d ++ [r + 1]) ++ (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt))) :=
        hrow.of_eq rfl (by simp [Enc])
      have hw' : zgiLogic.Reach
          (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
            (MEnc (d ++ [r + 1]) ++ (F.Hc (c + (p + 1) * n) ++ 0 :: F.Zt)))
          (hdR QG.gFG A (R1 ++ 0 :: F.Zt)) :=
        (hw.of_eq rfl rfl).trans h2
      exact hrow'.trans hw'

theorem oddFail (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H used J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (hne : H ≠ []) (d : List Nat) (x : Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0) (hx : 1 ≤ x) :
    FailsTo (cfgE W p H J Zt d [x] used) (Ufull W (p + 1) (d ++ [x]) (unm (1 :: (HP (Hs H used) 0 ++ J)))) Zt := by
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  let F := HFam.ofHP (Hs H used) hhne (Hs_bits H used) J hJ Zt hZ
  have key := oddFailF F W d p x 0 hW hdd hdl hx (Nat.zero_le _)
  refine FailsTo.ofCfg ?_ key
  simp [cfgE, Enc, U, F, HFam.ofHP, List.append_assoc]

theorem loopOdd (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e)
    (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt) :
    ∀ (X d used used' : List Nat), (∀ e ∈ X, 1 ≤ e) → (∀ e ∈ d, 1 ≤ e) → d.length % 2 = 0 → X.length % 2 = 1 →
    checkEdges W (p + 1) H (pairsOf X) used = some used' →
    FailsTo (cfgE W p H J Zt d X used) (Ufull W (p + 1) (d ++ X) (unm (1 :: (HP (Hs H []) 0 ++ J)))) Zt
  | [], d, used, used', _, _, _, hl, _ => by simp at hl
  | [x], d, used, used', hX, hdd, hdl, _, _ => by
    have := oddFail W hW p H used J Zt hJ hZ hne d x hdd hdl (hX x (by simp))
    exact FailsTo.cast (by rw [Hu_used H used []]) this
  | x :: y :: rest, d, used, used', hX, hdd, hdl, hl, h => by
    simp only [pairsOf, checkEdges] at h
    by_cases h1 : x > W.length ∨ y > W.length
    · simp [h1] at h
    rw [if_neg h1] at h
    by_cases h2 : ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) > H.length ∨
        H.getD (((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) - 1) 0 < 2 ∨
        ((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) ∈ used
    · rw [if_pos h2] at h; simp at h
    rw [if_neg h2] at h
    simp only [not_or] at h1 h2
    obtain ⟨hx, hy⟩ := h1
    obtain ⟨hk, hv, hu⟩ := h2
    have hx1 : 1 ≤ x := hX x (by simp)
    have hy1 : 1 ≤ y := hX y (by simp)
    have hrest : ∀ e ∈ rest, 1 ≤ e := fun e he => hX e (by simp [he])
    have hstep := edgeStep W hW p H used J Zt hJ hZ hne hHv d rest (x - 1) (y - 1) hdd hrest hdl
      (by omega) (by omega) _ rfl (by omega) (by omega) hu
    have hdd' : ∀ e ∈ d ++ [x, y], 1 ≤ e := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hdd e he
      · simp at he; rcases he with rfl | rfl <;> omega
    have ih := loopOdd W hW p H hne hHv J Zt hJ hZ rest (d ++ [x, y]) _ used' hrest hdd'
      (by simp; omega) (by simp at hl; omega) h
    have hs2 : zgiLogic.Reach (cfgE W p H J Zt d (x :: y :: rest) used)
        (cfgE W p H J Zt (d ++ [x, y]) rest (((W.getD (x - 1) 0 - 1) * (p + 1) + W.getD (y - 1) 0) :: used)) := by
      refine hstep.of_eq ?_ ?_
      · simp [cfgE, Enc, U, show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega, List.append_assoc]
      · simp [cfgE, show x - 1 + 1 = x by omega, show y - 1 + 1 = y by omega]
    exact FailsTo.pre hs2 (FailsTo.cast (by simp [List.append_assoc]) ih)

/-- The whole check for a tape with a nonempty `H`: accepts iff `checkG`, else fails on the unmarked tape. -/
theorem checkAFull (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e)
    (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt) (X : List Nat) (hX : ∀ e ∈ X, 1 ≤ e) :
    (checkG W (p + 1) X H = true → ∃ c', AccS c' ∧ zgiLogic.Reach (cfgE W p H J Zt [] X []) c') ∧
    (checkG W (p + 1) X H = false →
      FailsTo (cfgE W p H J Zt [] X []) (Ufull W (p + 1) X (unm (1 :: (HP (Hs H []) 0 ++ J)))) Zt) := by
  have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
  constructor
  · intro hg
    simp only [checkG, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨hev, hg⟩ := hg
    cases hce : checkEdges W (p + 1) H (pairsOf X) [] with
    | none => rw [hce] at hg; simp at hg
    | some used' =>
      rw [hce] at hg
      have hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ used' := by
        intro k hk
        have := (List.all_eq_true.1 hg) k (List.mem_range.2 hk)
        simpa using this
      have hl := loopOk W hW p H hne hHv J Zt hJ hZ X [] [] used' hX hd0 (by simp) hev hce
      obtain ⟨c', hc, hr⟩ := finalAcc W p H hne J Zt hJ hZ ([] ++ X) used'
        (by simpa using hX) (by simpa using hev) hall
      exact ⟨c', hc, hl.trans hr⟩
  · intro hg
    by_cases hev : X.length % 2 = 0
    · cases hce : checkEdges W (p + 1) H (pairsOf X) [] with
      | none =>
        have := loopFail W hW p H hne hHv J Zt hJ hZ X [] [] hX hd0 (by simp) hce
        simpa using this
      | some used' =>
        have hl := loopOk W hW p H hne hHv J Zt hJ hZ X [] [] used' hX hd0 (by simp) hev hce
        have hbad : ∃ k, k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ used' := by
          refine Classical.byContradiction fun hno => ?_
          have hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ used' := by
            intro k hk
            by_cases h2 : 2 ≤ H.getD k 0
            · right; exact Classical.byContradiction fun hu => hno ⟨k, hk, h2, hu⟩
            · left; omega
          have : checkG W (p + 1) X H = true := by
            simp only [checkG, hev, hce]
            simp only [decide_true, Bool.true_and, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
            intro k hk
            rcases hall k hk with h | h
            · left; exact h
            · right; exact h
          rw [this] at hg; cases hg
        have hf := finalFail W p H hne J Zt hJ hZ ([] ++ X) used' (by simpa using hX) (by simpa using hev) hbad
        refine FailsTo.pre hl (FailsTo.cast ?_ hf)
        simp [Hu_used H used' []]
    · have hodd : X.length % 2 = 1 := by omega
      cases hce : checkEdges W (p + 1) H (pairsOf X) [] with
      | none =>
        have := loopFail W hW p H hne hHv J Zt hJ hZ X [] [] hX hd0 (by simp) hce
        simpa using this
      | some used' =>
        have := loopOdd W hW p H hne hHv J Zt hJ hZ X [] [] used' hX hd0 (by simp) hodd hce
        simpa using this

end ZP.G
