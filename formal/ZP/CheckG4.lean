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
      refine FailsTo.cast ?_ (FailsTo.pre (by exact LTM.Reach.refl _ _) hF)
      · simp [Ufull, unm_append, unm_MEnc, unm_rep3, unm_Enc, F.un c hc, List.append_assoc, unm1, Enc_append, Enc, U, MEnc,
          List.replicate_succ']
        sorry
    · sorry
  · sorry

end ZP.G
