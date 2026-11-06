import ZP.CheckG4

/-! # The check phase of the GI machine (part 5): the `CheckSpec` for a nonempty `H` -/

namespace ZP.G

open ZP

theorem Hs_nil (H : List Nat) : Hs H [] = H.map fun v => tl v false := by
  apply List.ext_getElem
  · simp [Hs_length]
  · intro i h1 h2
    have hi : i < H.length := by simpa [Hs_length] using h1
    rw [Hs_get _ _ _ hi]
    simp [List.getD_eq_getElem?_getD, hi]

theorem HP_Hs_o13 (H : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e) :
    ∀ a ∈ HP (Hs H []) 0, a ∈ O13 := by
  rw [Hs_nil, HP_Enc H hne hHv]
  intro a ha
  exact Enc_o13 H a (List.dropLast_subset _ ha)

theorem unmHu (H J : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e) (hJ : ∀ a ∈ J, a ∈ O13) :
    unm (HP (Hs H []) 0 ++ J) = HP (Hs H []) 0 ++ J := by
  apply unm_o13
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · exact HP_Hs_o13 H hne hHv a ha
  · exact hJ a ha

/-- The popped stack leads to the start of the edge loop. -/
theorem popE (E : GEnv) (rest : List Nat) (hrest : ∀ e ∈ rest, 1 ≤ e) (p : Nat) (hm : E.m = p + 1)
    (X H J : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e) (hJo : ∀ a ∈ J, a ∈ O13)
    (hTc : E.Tc = List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J))) :
    zgiLogic.Reach (E.CfgPop rest) (cfgE rest p H J E.Z [] X []) := by
  have sRt := E.Rt_sym4
  have hws := Enc_entries rest hrest
  have sZ := E.hZ
  have sEnc : Sym4 (Enc rest) := by
    intro a ha; have := Enc_o13 rest a ha; simp [O13, ALL] at this ⊢; omega
  have hlist : Enc rest ++ E.Rt = MEs (rest.map fun e => List.replicate e 3) ++ 1 ::
      (List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J ++ 0 :: E.Z))) := by
    rw [Enc_MEs]
    simp [GEnv.Rt, hTc, List.append_assoc]
  obtain ⟨a, X0, hax, ha⟩ : ∃ a X0, Enc rest ++ E.Rt = a :: X0 ∧ a ∈ NB := by
    cases rest with
    | nil => exact ⟨1, E.Tc ++ 0 :: E.Z, by simp [GEnv.Rt, Enc], by simp [NB]⟩
    | cons v r =>
      obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by have := hrest v (by simp); omega⟩
      exact ⟨3, List.replicate k 3 ++ 1 :: (Enc r ++ E.Rt), by simp [Enc, U, List.replicate_succ], by simp [NB]⟩
  have hX0 : Sym4 X0 := by
    have hs : Sym4 (a :: X0) := hax ▸ (sEnc.app sRt)
    exact fun x hx => hs x (by simp [hx])
  have h1 := gglStart X0 a ha hX0
  have sR : Sym4 (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J ++ 0 :: E.Z)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.cons (by simp [ALL]) (Sym4.app (Sym4.app ?_ ?_) (Sym4.cons (by simp [ALL]) sZ)))
    · have := Enc_o13 X a ha; simp [O13, ALL] at this ⊢; omega
    · exact o13_sym4 (HP_Hs_o13 H hne hHv)
    · exact o13_sym4 hJo
  have hp := phaseU (rest.map fun e => List.replicate e 3) (List.replicate (p + 1) 3)
    (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J ++ 0 :: E.Z)) [0] hws (bits_rep3 _) (by simp [ALL]) sR
  have hax2 := hax.symm.trans hlist
  have hstart : E.CfgPop rest = hdR QG.gGL [0] (a :: X0) := by
    simp only [GEnv.CfgPop]; rw [hax]
  rw [hstart]
  refine ((h1.trans (hp.of_eq (by rw [hax2]) rfl)).of_eq rfl ?_)
  simp only [cfgE, unm_append, unm_Enc, unm_rep3, MEnc, List.nil_append, ← Enc_MEs]
  rw [show [0] ++ Enc rest ++ [1] ++ List.replicate (p + 1) 3 ++ [1] = 0 :: (Enc rest ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) by
    simp [List.append_assoc], hdR_z0]

theorem checkSpecA (E : GEnv) (p : Nat) (hm : E.m = p + 1) (X H J : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e)
    (hJ : JShape J) (hJo : ∀ a ∈ J, a ∈ O13) (hX : ∀ e ∈ X, 1 ≤ e)
    (hTc : E.Tc = List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ 1 :: (HP (Hs H []) 0 ++ J))) :
    E.CheckSpec (fun w => checkG w (p + 1) X H) AccS := by
  intro rest hv
  have hW : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
  have hpop := popE E rest hW p hm X H J hne hHv hJo hTc
  have hfull := checkAFull rest hW p H hne hHv J E.Z hJ E.hZ X hX
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨c', hc, hr⟩ := hfull.1 hg
    exact ⟨c', hc, hpop.trans hr⟩
  · obtain ⟨A, R1, hA, hR1, hu, hr⟩ := hfull.2 hg
    have hf := failPath A R1 E.Z hA hR1 E.hZ
    refine (hpop.trans hr).trans (hf.of_eq rfl ?_)
    rw [hu, unmHu H J hne hHv hJo]
    simp [Ufull, GEnv.CfgD, GEnv.Rt, hTc, List.append_assoc]

end ZP.G
