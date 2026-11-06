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
        (MEnc d ++ List.replicate x 3 ++ 1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ x :: X') F.Hu) F.Zt := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  have hXs : Sym4 (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (F.sym c hc))
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  have hnb := F.nb c hc
  have hX'n : NoB (Enc X') := by
    intro a ha; have := Enc_o13 X' a ha; simp [O13, NB] at this ⊢; omega
  rcases Nat.lt_or_ge W.length (r + 1) with hlt | hge
  · rcases Nat.lt_or_ge W.length r with hlt2 | hge2
    · -- label two or more beyond `w`
      have hF := labelFindF (p + 1) d (Enc X' ++ 1 :: F.Hc c) F.Zt hdd
        (by simp only [NoB_app_iff, NoB_cons_iff]; simp [NB, hnb, hX'n]) F.hZ r [] W 0 (by simp) hW hlt2
      refine FailsTo.ofCfg (by simp [MEnc]) (FailsTo.cast ?_ hF)
      simp [Ufull, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, F.un c hc, List.append_assoc, unm1, Enc_append, Enc, U,
        List.replicate_succ']
    · -- the label is exactly one beyond `w`
      have hr : r = W.length := by omega
      subst hr
      have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs W.length [] W 0 (by simp) hW (by omega)
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
    have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0 (by simp) hW hrl
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
      (F.N < c + n ∨ ∃ (T : List (List Nat)) (R0 : List Nat), c + n ≤ F.N ∧ (∀ t ∈ T, Bits t) ∧
        F.Hc (c + n) ++ 0 :: F.Zt = MP T ++ (R0 ++ 0 :: F.Zt) ∧
        (R0 = [] ∨ (∃ R1, NoB R1 ∧ R0 = 1 :: R1) ∨ (∃ tl, Bits tl ∧ R0 = 2 :: tl) ∨
          (∃ R1, NoB R1 ∧ R0 = 3 :: 1 :: R1) ∨ R0 = [3] ∨ (∃ Q, NoB Q ∧ R0 = 3 :: 2 :: Q)))) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate y 3 ++ 1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))
      (Ufull W (p + 1) (d ++ y :: X') F.Hu) F.Zt := by
  obtain ⟨r, rfl⟩ : ∃ r, y = r + 1 := ⟨y - 1, by omega⟩
  have hXs : Sym4 (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (F.sym c hc))
    have := Enc_o13 X' a ha; simp [O13, ALL] at this ⊢; omega
  have hdf : decide (d.length % 2 = 1) = true := by simp [hdl]
  have hnb := F.nb c hc
  have hX'n : NoB (Enc X') := by
    intro a ha; have := Enc_o13 X' a ha; simp [O13, NB] at this ⊢; omega
  rcases Nat.lt_or_ge W.length (r + 1) with hlt | hge
  · rcases Nat.lt_or_ge W.length r with hlt2 | hge2
    · have hF := labelFindF (p + 1) d (Enc X' ++ 1 :: F.Hc c) F.Zt hdd
        (by simp only [NoB_app_iff, NoB_cons_iff]; simp [NB, hnb, hX'n]) F.hZ r [] W 0 (by simp) hW hlt2
      refine FailsTo.ofCfg (by simp [MEnc]) (FailsTo.cast ?_ hF)
      simp [Ufull, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, F.un c hc, List.append_assoc, unm1, Enc_append, Enc, U,
        List.replicate_succ']
    · have hr : r = W.length := by omega
      subst hr
      have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs W.length [] W 0 (by simp) hW (by omega)
      rw [hdf] at hL
      have hLd : (LDone true) = QG.gIL0 := rfl
      rw [hLd] at hL
      have hN := colNoTarget F W d X' p (W.length + 1) c hW hdd hX' hc
      exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc, Enc])) hN
  · obtain ⟨n, Wr, hr, hcb⟩ : ∃ n Wr, W.drop r = (n + 1) :: Wr ∧
        (F.N < c + n ∨ ∃ (T : List (List Nat)) (R0 : List Nat), c + n ≤ F.N ∧ (∀ t ∈ T, Bits t) ∧
        F.Hc (c + n) ++ 0 :: F.Zt = MP T ++ (R0 ++ 0 :: F.Zt) ∧
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
    have hL := labelFind (p + 1) d (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt)) hdd hXs r [] W 0 (by simp) hW hrl
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
    have hIL := il0Walk' _ (1 :: (Enc X' ++ 1 :: (F.Hc c ++ 0 :: F.Zt))) hnA (Sym4.cons (by simp [ALL]) hXs)
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
              X'.map fun e => List.replicate e 3)) ++ 1 :: (F.Hc c ++ 0 :: F.Zt))))))
        (UG (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2 :: ((d'.map fun e => List.replicate e 2) ++
          List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)) n (p + 1) F.Hu) F.Zt := by
      rcases hcb with hov | ⟨T, R0, hcn, hTb, hT, hR⟩
      · exact colPartF1 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
          ((d'.map fun e => List.replicate e 2) ++ List.replicate (r + 1) 2 :: X'.map fun e => List.replicate e 3)
          hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
          (p + 1) n c hc hov
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

end ZP.G
