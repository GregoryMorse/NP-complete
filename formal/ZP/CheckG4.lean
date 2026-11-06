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

end ZP.G
