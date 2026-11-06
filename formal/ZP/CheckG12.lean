import ZP.CheckG11

/-! # The GI machine: the truth phase (setup, search, check, report) -/

namespace ZP.G

open ZP

theorem flatR_shape (R : List Nat) : flatR R = [] ∨ ∃ t, flatR R = 1 :: t := by
  cases R with
  | nil => exact Or.inl (by simp [flatR])
  | cons r R' => exact Or.inr ⟨List.replicate r 3 ++ flatR R', by simp [flatR]⟩

theorem tc_o13 (sb : List Bool) : ∀ a ∈ fz (bitsOf sb).reverse, a ∈ O13 := by
  intro a ha
  rw [fz_bitsOf] at ha
  simp only [List.mem_map, List.mem_reverse] at ha
  obtain ⟨b, _, rfl⟩ := ha
  cases b <;> simp [O13]

/-- The environment of the search for the instance `sb`. -/
theorem genv_of (sb : List Bool) (Z : List Nat) (hZ : Sym4 Z) :
    ∃ E : GEnv, E.Tc = fz (bitsOf sb).reverse ∧ E.Z = Z ∧ E.m = (parseG sb).1 := by
  have hne : (runsAux sb 0).reverse ≠ [] := by simpa using runsAux_ne sb 0
  obtain ⟨m, R, hT⟩ := List.exists_cons_of_ne_nil hne
  have hTc2 : fz (bitsOf sb).reverse = List.replicate m 3 ++ flatR R := by
    have h := tc_runs sb 0
    rw [hT] at h
    rw [fz_bitsOf]
    simpa [tcOfList] using h
  have hp : (parseG sb).1 = m := by simp [parseG, hT]
  rw [hp]
  rcases flatR_shape R with h | ⟨t, h⟩
  · refine ⟨⟨m, fz (bitsOf sb).reverse, Z, 0, Z, ?_, Or.inl rfl, hZ, tc_o13 sb, hZ⟩, rfl, rfl, rfl⟩
    rw [hTc2, h]; simp
  · refine ⟨⟨m, fz (bitsOf sb).reverse, Z, 1, t ++ 0 :: Z, ?_, Or.inr rfl, ?_, tc_o13 sb, hZ⟩, rfl, rfl, rfl⟩
    · rw [hTc2, h]; simp
    · have h1 : ∀ a ∈ t, a ∈ O13 := by
        have := tc_o13 sb
        rw [hTc2] at this
        intro a ha
        exact this a (by simp [h, ha])
      exact (o13_sym4 h1).app (Sym4.cons (by simp [ALL]) hZ)

theorem truthPhaseG (jb sb : List Bool) :
    zgiLogic.Reach
      (hd QG.gUP ([1] ++ fz (bitsOf sb).reverse) (0 :: (1 :: (bitsOf jb ++ 1 :: (bitsOf sb ++ [1])))))
      (TR (bitsOf jb) sb (inLG sb)) := by
  have hj := Bits.ofB jb
  have hs := Bits.ofB sb
  have hZ : Sym4 (1 :: (bitsOf jb ++ 1 :: (bitsOf sb ++ [1]))) :=
    Sym4.cons (by simp [ALL]) (hj.sym4.app (Sym4.cons (by simp [ALL]) (hs.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil))))
  obtain ⟨E, hTc, hEZ, hEm⟩ := genv_of sb _ hZ
  have hC := csParse E sb hTc
  have hnb : NoB ([1] ++ E.Tc) := (NoB.cons one_nb NoB.nil).app (o13_noB E.hTc)
  have h1 := gupWalk ([1] ++ E.Tc) (0 :: E.Z) hnb (Sym4.cons (by simp [ALL]) E.hZ)
  have h2 := pushAll E.m [] E.Z' E.z E.hz (by simp) E.hZ'
  have hS : zgiLogic.Reach (hd QG.gUP ([1] ++ E.Tc) (0 :: E.Z)) (E.CfgS [] E.m) := by
    refine h1.trans (h2.of_eq ?_ ?_)
    · rw [unm_append, unm_o13 E.hTc]
      have := E.hT
      simp [Enc, unm1, ← this]
    · simp [GEnv.CfgS, GEnv.Rt, Enc, U, ← E.hT, List.append_assoc]
  rw [← hTc, ← hEZ]
  have hb0 := Rch_total (fun w => checkG w (parseG sb).1 (parseG sb).2.1 (parseG sb).2.2) (parseG sb).1 _ []
    (parseG sb).1 rfl ⟨List.nodup_nil, by simp⟩ (Nat.le_refl _)
  obtain ⟨b, hb⟩ := hb0
  have hsem := inLG_iff_Rch sb b hb
  have hb' : Rch (fun w => checkG w (parseG sb).1 (parseG sb).2.1 (parseG sb).2.2) E.m [] E.m b := by
    rw [hEm]; exact hb
  have hv : VStack E.m [] := ⟨List.nodup_nil, by simp⟩
  obtain ⟨hA, hB⟩ := GEnv.search_machine E _ (AccS E.Z) hC hb' hv (Nat.le_refl _)
  cases b with
  | true =>
    obtain ⟨c', ⟨L, Mr, hL, hMr, hc⟩, hr⟩ := hA rfl
    have hin : inLG sb = true := hsem.1 rfl
    rw [hin]
    rcases hc with rfl | rfl
    · have hf := fePathG L (bitsOf jb) (bitsOf sb) hL hj hs
      rw [hEZ] at hr
      refine (hS.trans hr).trans (hf.of_eq ?_ ?_)
      · simp
      · simp [TR, tflag]
    · have hf := frPath1G L Mr (bitsOf jb) (bitsOf sb) hL hMr hj hs
      rw [hEZ] at hr
      refine (hS.trans hr).trans (hf.of_eq ?_ ?_)
      · simp
      · simp [TR, tflag]
  | false =>
    have hin : inLG sb = false := by
      cases h : inLG sb
      · rfl
      · have := hsem.2 h; cases this
    rw [hin]
    have hdd := hB rfl
    have hg := gdcEmpty (E.Tc ++ 0 :: E.Z) (by
      have := o13_sym4 E.hTc
      exact this.app (Sym4.cons (by simp [ALL]) E.hZ))
    have hf := frPath0G [1] E.Tc (bitsOf jb) (bitsOf sb) (NoB.cons one_nb NoB.nil) (o13_noB E.hTc) hj hs
    refine (hS.trans hdd).trans ((hg.of_eq ?_ rfl).trans (hf.of_eq ?_ ?_))
    · simp [GEnv.CfgD, GEnv.Rt, Enc, hEZ]
    · simp [hEZ]
    · simp [TR, tflag]

end ZP.G
