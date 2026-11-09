module

public import ZP.CheckG9

@[expose] public section

/-! # The check phase of the GI machine (part 10): `m = 0` -/

namespace ZP.G

open ZP

def cfgM (W : List Nat) (m : Nat) (H J : List Nat) (Zt : List Nat) (d Xr used : List Nat) : ZC :=
  hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate m 3 ++ [1]))
    (MEnc d ++ Enc Xr ++ 1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt))

theorem popM (E : GEnv) (rest : List Nat) (hrest : ∀ e ∈ rest, 1 ≤ e) (m : Nat) (X Q : List Nat)
    (hQ : ∀ a ∈ Q, a ∈ O13)
    (hTc : E.Tc = List.replicate m 3 ++ 1 :: (Enc X ++ Q)) :
    zgiLogic.Reach (E.CfgPop rest)
      (hdR QG.gY1e (Enc rest ++ [1] ++ (List.replicate m 3 ++ [1])) (Enc X ++ (Q ++ 0 :: E.Z))) := by
  have sRt := E.Rt_sym4
  have hws := Enc_entries rest hrest
  have sZ := E.hZ
  have sEnc : Sym4 (Enc rest) := by
    intro a ha; have := Enc_o13 rest a ha; simp [O13, ALL] at this ⊢; omega
  have hlist : Enc rest ++ E.Rt = MEs (rest.map fun e => List.replicate e 3) ++ 1 ::
      (List.replicate m 3 ++ 1 :: (Enc X ++ (Q ++ 0 :: E.Z))) := by
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
  have sR : Sym4 (Enc X ++ (Q ++ 0 :: E.Z)) := by
    refine Sym4.app (fun a ha => ?_) (Sym4.app ?_ (Sym4.cons (by simp [ALL]) sZ))
    · have := Enc_o13 X a ha; simp [O13, ALL] at this ⊢; omega
    · exact o13_sym4 hQ
  have hp := phaseU (rest.map fun e => List.replicate e 3) (List.replicate m 3)
    (Enc X ++ (Q ++ 0 :: E.Z)) [0] hws (bits_rep3 _) (by simp [ALL]) sR
  have hax2 := hax.symm.trans hlist
  have hstart : E.CfgPop rest = hdR QG.gGL [0] (a :: X0) := by
    simp only [GEnv.CfgPop]; rw [hax]
  rw [hstart]
  refine ((h1.trans (hp.of_eq (by rw [hax2]) rfl)).of_eq rfl ?_)
  simp only [unm_append, unm_Enc, unm_rep3, ← Enc_MEs]
  rw [show [0] ++ Enc rest ++ [1] ++ List.replicate m 3 ++ [1] = 0 :: (Enc rest ++ [1] ++ (List.replicate m 3 ++ [1])) by
    simp [List.append_assoc], hdR_z0]


theorem finalAccM (W : List Nat) (m : Nat) (H : List Nat) (hne : H ≠ []) (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (d used : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0)
    (hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ used) :
    ∃ c', AccS Zt c' ∧ zgiLogic.Reach (cfgM W m H J Zt d [] used) c' := by
  have hhne : Hs H used ≠ [] := by
    intro h; have := Hs_length H used; rw [h] at this; simp at this; exact hne (List.length_eq_zero_iff.1 this.symm)
  have sH : Sym4 (HP (Hs H used) 0 ++ J ++ 0 :: Zt) :=
    ((HP_sym4 _ _ (Hs_bits H used)).app hJ.1.sym4).app (Sym4.cons (by simp [ALL]) hZ)
  have sP : Sym4 (Enc W ++ [1] ++ (List.replicate m 3 ++ [1])) := by
    refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
    have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
  have h1 := lblWalk (1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) sH) d false _ hdd sP
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  rw [hdf] at h1
  simp only [Bool.xor_false] at h1
  have sP2 : Sym4 (Enc W ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d) := sP.app (MEnc_sym4 d)
  have h2 := y1eEnd _ _ sP2 sH
  have nP2 : NoB (Enc W ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ [1]) := by
    simp only [NoB_app_iff]
    refine ⟨⟨⟨⟨fun a ha => ?_, by simp [NB]⟩, by simp [NB]⟩, fun a ha => ?_⟩, by simp [NB]⟩
    · have := Enc_o13 W a ha; simp [O13, NB] at this ⊢; omega
    · have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega
  obtain ⟨c', hc, h3⟩ := finalOk J Zt hJ hZ (Hs H used) hhne (Hs_bits H used) (Hs_ok H used hall) _ (sP2.app (show Sym4 [1] from Sym4.cons (by simp [ALL]) Sym4.nil)) nP2
  exact ⟨c', hc, ((h1.of_eq (by simp [cfgM, Enc]) rfl).trans h2).trans h3⟩


theorem finalFailM (W : List Nat) (m : Nat) (H : List Nat) (hne : H ≠ []) (J Zt : List Nat) (hJ : JShape J) (hZ : Sym4 Zt)
    (d used : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0)
    (hbad : ∃ k, k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ used) :
    FailsTo (cfgM W m H J Zt d [] used) (Ufull W m d (unm (1 :: (HP (Hs H used) 0 ++ J)))) Zt := by
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
  have sP : NoB (Enc W ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ [1]) := by
    have := Enc_o13 W
    simp only [NoB_app_iff]
    refine ⟨⟨⟨⟨fun a ha => ?_, by simp [NB]⟩, by simp [NB]⟩, (fun a ha => by have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega)⟩, by simp [NB]⟩
    have := Enc_o13 W a ha; simp [O13, NB] at this ⊢; omega
  have hfin := finalBad J Zt hJ hZ _ hr B hBb A hAb hAok _ sP
  rw [e0] at hfin
  have sH : Sym4 (HP (Hs H used) 0 ++ J ++ 0 :: Zt) :=
    ((HP_sym4 _ _ (Hs_bits H used)).app hJ.1.sym4).app (Sym4.cons (by simp [ALL]) hZ)
  have sP' : Sym4 (Enc W ++ [1] ++ (List.replicate m 3 ++ [1])) := by
    refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
    have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
  have hw := lblWalk (1 :: (HP (Hs H used) 0 ++ J ++ 0 :: Zt)) (Sym4.cons (by simp [ALL]) sH) d false _ hdd sP'
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  rw [hdf] at hw
  simp only [Bool.xor_false] at hw
  have sP2 : Sym4 (Enc W ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d) := sP'.app (MEnc_sym4 d)
  have h2 := y1eEnd _ _ sP2 sH
  refine FailsTo.pre ((hw.of_eq (by simp [cfgM, Enc]) rfl).trans h2) (FailsTo.cast ?_ hfin)
  simp [Ufull, unm_append, unm_MEnc, unm_Enc, unm_rep3, unm1, Enc, List.append_assoc]


theorem hd_nil0 (q : Nat) (R : List Nat) : hd q [0] R = hd q [] R := rfl

theorem gm1End (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gM1 [0] R) (hdR QG.gFG [0] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTF (env := [R]) (E := []) (k := 3) hV trivial
    (ls := [.sym 0]) (rs := [.blk 0 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gm1Walk0 : ∀ (n : Nat) (L R : List Nat), L.length = n → Sym4 R →
    (∀ a ∈ L, a = 1 ∨ a = 2) →
    zgiLogic.Reach (hd QG.gM1 L R) (hdR QG.gFG [] (L ++ R)) := by
  intro n
  induction n with
  | zero =>
    intro L R hl hR _
    have : L = [] := List.length_eq_zero_iff.1 hl
    subst this
    have h := gm1End R hR
    rw [hd_nil0, hdR_z0] at h
    simpa using h
  | succ n ih =>
    intro L R hl hR hL
    obtain ⟨L0, a, hLa⟩ := (List.eq_nil_or_concat L).resolve_left (by rintro rfl; simp at hl)
    rw [List.concat_eq_append] at hLa
    subst hLa
    have ha := hL a (by simp)
    have hL0 : ∀ b ∈ L0, b = 1 ∨ b = 2 := fun b hb => hL b (by simp [hb])
    have sL0 : Sym4 L0 := by
      intro b hb; rcases hL0 b hb with rfl | rfl <;> simp [ALL]
    have sR : Sym4 (a :: R) := Sym4.cons (by rcases ha with rfl | rfl <;> simp [ALL]) hR
    have h1 := gm1Pass L0 R a ha sL0 hR
    have h2 := ih L0 (a :: R) (by simpa using hl) sR hL0
    exact h1.trans (h2.of_eq rfl (by simp))


/-- `m = 0`, the first label (terminated) fails: it points beyond the empty `w`. -/
theorem firstFailM0T (x : Nat) (hx : 1 ≤ x) (X0 Z : List Nat) (hX0 : NoB X0) (hZ : Sym4 Z) :
    FailsTo
      (hdR QG.gY1e [1, 1] (List.replicate x 3 ++ 1 :: (X0 ++ 0 :: Z)))
      (unm ([1, 1] ++ List.replicate x 3 ++ 1 :: X0)) Z := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have sX : Sym4 (X0 ++ 0 :: Z) := hX0.sym4.app (Sym4.cons (by simp [ALL]) hZ)
    have hL := labelFind 0 [] (X0 ++ 0 :: Z) hd0 sX 0 [] [] 0 (by simp) (by simp) (by simp)
    have hLd : (LDone (decide (([] : List Nat).length % 2 = 1))) = QG.gM1 := rfl
    rw [hLd] at hL
    have sR : Sym4 (1 :: (X0 ++ 0 :: Z)) := Sym4.cons (by simp [ALL]) sX
    have hw := gm1Walk0 _ [1, 1, 2] _ rfl sR (by simp)
    have hnb : NoB ([1, 1, 2] ++ 1 :: X0) := by
      simp only [NoB_app_iff, NoB_cons_iff]; simp [NB, hX0]
    refine ⟨[], [1, 1, 2] ++ 1 :: X0, NoB.nil, hnb, ?_, ?_⟩
    · simp [unm, unm1]
    · refine (hL.of_eq (by simp [MEnc, Enc]) (by simp [MEnc, Enc])).trans (hw.of_eq rfl ?_)
      simp
  · have hF := labelFindF 0 [] X0 Z hd0 hX0 hZ r [] [] 0 (by simp) (by simp) (by simpa using hr)
    refine FailsTo.ofCfg (by simp [MEnc, Enc]) (FailsTo.cast ?_ hF)
    simp [unm_append, unm_MEnc, unm_rep3, unm_rep2, Enc, List.replicate_succ']

/-- `m = 0`, the first label (unterminated) fails. -/
theorem firstFailM0U (x : Nat) (hx : 1 ≤ x) (Z : List Nat) (hZ : Sym4 Z) :
    FailsTo
      (hdR QG.gY1e [1, 1] (List.replicate x 3 ++ 0 :: Z))
      (unm ([1, 1] ++ List.replicate x 3)) Z := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hY : ∃ c R', (c = 0 ∨ c = 1) ∧ (0 :: Z) = c :: R' ∧ Sym4 R' := ⟨0, Z, Or.inl rfl, rfl, hZ⟩
    have hL := labelFindY 0 [] (0 :: Z) hd0 sZ0 hY 0 [] [] 0 (by simp) (by simp) (by simp)
    have hLd : (LDone (decide (([] : List Nat).length % 2 = 1))) = QG.gM1 := rfl
    rw [hLd] at hL
    have hw := gm1Walk0 _ [1, 1, 2] _ rfl sZ0 (by simp)
    refine ⟨[], [1, 1, 2], NoB.nil, by simp [NB], ?_, ?_⟩
    · simp [unm, unm1]
    · refine (hL.of_eq (by simp [MEnc, Enc]) (by simp [MEnc, Enc])).trans (hw.of_eq rfl ?_)
      simp
  · have hF := labelFindFY 0 [] [] Z hd0 NoB.nil hZ r [] [] 0 (by simp) (by simp) (by simpa using hr)
    refine FailsTo.ofCfg (by simp [MEnc, Enc]) (FailsTo.cast ?_ hF)
    simp [unm_append, unm_MEnc, unm_rep3, unm_rep2, Enc, List.replicate_succ']


/-- `T = [m]`: nothing but the cells of `m`; the machine accepts. -/
theorem checkSpecS0M (E : GEnv) (hTc : E.Tc = List.replicate m 3) (m' : Nat) :
    E.CheckSpec (fun w => checkG w m' [] []) (AccS E.Z) := by
  intro rest hv
  have hW : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
  refine ⟨fun _ => ?_, fun hg => absurd hg (by simp [checkG, pairsOf, checkEdges])⟩
  have sRt := E.Rt_sym4
  have hws := Enc_entries rest hW
  have sZ := E.hZ
  have sEnc : Sym4 (Enc rest) := by
    intro a ha; have := Enc_o13 rest a ha; simp [O13, ALL] at this ⊢; omega
  have hlist : Enc rest ++ E.Rt = MEs (rest.map fun e => List.replicate e 3) ++ 1 ::
      (List.replicate m 3 ++ 0 :: E.Z) := by
    rw [Enc_MEs]
    simp [GEnv.Rt, hTc, List.append_assoc]
  obtain ⟨a, X0, hax, ha⟩ : ∃ a X0, Enc rest ++ E.Rt = a :: X0 ∧ a ∈ NB := by
    cases rest with
    | nil => exact ⟨1, E.Tc ++ 0 :: E.Z, by simp [GEnv.Rt, Enc], by simp [NB]⟩
    | cons v r =>
      obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by have := hW v (by simp); omega⟩
      exact ⟨3, List.replicate k 3 ++ 1 :: (Enc r ++ E.Rt), by simp [Enc, U, List.replicate_succ], by simp [NB]⟩
  have hX0 : Sym4 X0 := by
    have hs : Sym4 (a :: X0) := hax ▸ (sEnc.app sRt)
    exact fun x hx => hs x (by simp [hx])
  have h1 := gglStart X0 a ha hX0
  have hR1 : Sym4 (1 :: (List.replicate m 3 ++ 0 :: E.Z)) :=
    Sym4.cons (by simp [ALL]) ((Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sZ))
  have hu := uwWalk (1 :: (List.replicate m 3 ++ 0 :: E.Z)) hR1 (rest.map fun e => List.replicate e 3) [0] hws (by simp [ALL])
  have hn := unm_nb (MEs_noB _ (fun e he => (hws e he).1))
  have hP1 : Sym4 ([0] ++ unm (MEs (rest.map fun e => List.replicate e 3))) := by simp [hn.sym4, ALL]
  have h2 := uw2End _ (List.replicate m 3 ++ 0 :: E.Z) hP1 (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (Sym4.cons (by simp [ALL]) sZ))
  have hP2 : Sym4 (unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1]) := by simp [hn.sym4, ALL]
  have h3 := xmCellsB E.Z sZ (List.replicate m 3) _ (bits_rep3 _) hP2
  have hLn : NoB (unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1] ++ unm (List.replicate m 3)) := by
    simp [NB, hn]
  have hz0 : hdR QG.gXm ([0] ++ unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1]) (List.replicate m 3 ++ 0 :: E.Z) =
      hdR QG.gXm (unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1]) (List.replicate m 3 ++ 0 :: E.Z) := by
    rw [show [0] ++ unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1] =
      0 :: (unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1]) by simp, hdR_z0]
  have hax2 := hax.symm.trans hlist
  have hstart : E.CfgPop rest = hdR QG.gGL [0] (a :: X0) := by
    simp only [GEnv.CfgPop]; rw [hax]
  rw [hstart]
  exact ⟨_, ⟨_, [], hLn, NoB.nil, Or.inl rfl⟩, h1.trans ((hu.of_eq (by rw [hax2]) rfl).trans ((h2.of_eq rfl hz0).trans (h3.of_eq rfl rfl)))⟩

theorem restNil0 (E : GEnv) (hm : E.m = 0) (rest : List Nat) (hv : VStack E.m rest) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons a r =>
    have := hv.2 a (by simp)
    omega

theorem checkG_nil0 (m : Nat) (X H : List Nat) (hX : ∀ e ∈ X, 1 ≤ e) (hne : X ≠ []) :
    checkG [] m X H = false := by
  match X, hne with
  | [x], _ => simp [checkG]
  | x :: y :: r, _ =>
    have hx := hX x (by simp)
    simp only [checkG, pairsOf, checkEdges]
    simp [show 0 < x by omega]


theorem checkG_nil_true (m : Nat) (H : List Nat) :
    checkG [] m [] H = true ↔ ∀ k < H.length, H.getD k 0 < 2 := by
  simp only [checkG, pairsOf, checkEdges]
  simp

/-- `m = 0`, `X` nonempty: the first label fails. -/
theorem checkSpecM0X (E : GEnv) (hm : E.m = 0) (chk : List Nat → Bool) (hchk : chk [] = false)
    (x : Nat) (X' Q : List Nat) (hQ : ∀ a ∈ Q, a ∈ O13) (hx : 1 ≤ x) (hX' : ∀ e ∈ X', 1 ≤ e)
    (hTc : E.Tc = 1 :: (Enc (x :: X') ++ Q)) :
    E.CheckSpec chk (AccS E.Z) := by
  intro rest hv
  have hr := restNil0 E hm rest hv
  subst hr
  refine ⟨(fun h => by rw [hchk] at h; cases h), fun _ => ?_⟩
  have hpop := popM E [] (by simp) 0 (x :: X') Q hQ (by simpa using hTc)
  have hX0 : NoB (Enc X' ++ Q) := by
    simp only [NoB_app_iff]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have := Enc_o13 X' a ha; simp [O13, NB] at this ⊢; omega
    · have := hQ a ha; simp [O13, NB] at this ⊢; omega
  obtain ⟨A, R1, hA, hR1, hu, hr⟩ := firstFailM0T x hx (Enc X' ++ Q) E.Z hX0 E.hZ
  have hf := failPath A R1 E.Z hA hR1 E.hZ
  refine (hpop.of_eq rfl (by simp [Enc, U, List.append_assoc])).trans (hr.trans (hf.of_eq rfl ?_))
  rw [hu]
  simp [unm_append, unm_Enc, unm_rep3, unm_o13 hQ, unm1, Enc, U, GEnv.CfgD, GEnv.Rt, hTc, List.append_assoc]

/-- `m = 0`, a single unterminated label. -/
theorem checkSpecM0U (E : GEnv) (hm : E.m = 0) (chk : List Nat → Bool) (hchk : chk [] = false)
    (y : Nat) (hy : 1 ≤ y) (hTc : E.Tc = 1 :: List.replicate y 3) :
    E.CheckSpec chk (AccS E.Z) := by
  intro rest hv
  have hr := restNil0 E hm rest hv
  subst hr
  refine ⟨(fun h => by rw [hchk] at h; cases h), fun _ => ?_⟩
  have hpop := popM E [] (by simp) 0 [] (List.replicate y 3) (fun a ha => by
      rw [List.eq_of_mem_replicate ha]; simp [O13]) (by simpa [Enc] using hTc)
  obtain ⟨A, R1, hA, hR1, hu, hr⟩ := firstFailM0U y hy E.Z E.hZ
  have hf := failPath A R1 E.Z hA hR1 E.hZ
  refine (hpop.of_eq rfl (by simp [Enc])).trans (hr.trans (hf.of_eq rfl ?_))
  rw [hu]
  simp [unm_append, unm_rep3, unm1, GEnv.CfgD, GEnv.Rt, hTc, Enc, List.append_assoc]

/-- `m = 0`, `X` and `H` empty. -/
theorem checkSpecM0E (E : GEnv) (hm : E.m = 0) (H0 : List Nat)
    (hH0 : H0 = [] ∨ H0 = [1] ∨ (∃ J', NoB J' ∧ H0 = 1 :: 1 :: J')) (hH0o : ∀ a ∈ H0, a ∈ O13)
    (hTc : E.Tc = 1 :: H0) :
    E.CheckSpec (fun w => checkG w 0 [] []) (AccS E.Z) := by
  intro rest hv
  have hr := restNil0 E hm rest hv
  subst hr
  refine ⟨fun _ => ?_, fun hg => absurd hg (by simp [checkG, pairsOf, checkEdges])⟩
  have hpop := popM E [] (by simp) 0 [] H0 hH0o (by simpa [Enc] using hTc)
  have hZ := E.hZ
  have sP : Sym4 (Enc [] ++ [1] ++ (List.replicate 0 3 ++ [1])) := by simp [Enc, ALL, Sym4]
  have nP : NoB (Enc [] ++ [1] ++ (List.replicate 0 3 ++ [1])) := by simp [Enc, NB, NoB]
  have sP1 : Sym4 (Enc [] ++ [1] ++ (List.replicate 0 3 ++ [1]) ++ [1]) := by simp [Enc, ALL, Sym4]
  rcases hH0 with rfl | rfl | ⟨J', hJ', rfl⟩
  · exact ⟨_, ⟨_, [], nP, NoB.nil, Or.inl rfl⟩, hpop.trans ((y1eEndB _ E.Z sP hZ).of_eq (by simp [Enc]) rfl)⟩
  · have h1 := y1eEnd _ (0 :: E.Z) sP (Sym4.cons (by simp [ALL]) hZ)
    have h2 := fn1_B _ E.Z sP1 hZ
    exact ⟨_, ⟨_, [], nP.app (NoB.cons one_nb NoB.nil), NoB.nil, Or.inl rfl⟩,
      hpop.trans (((h1.of_eq (by simp [Enc]) rfl).trans h2))⟩
  · have sR : Sym4 (1 :: (J' ++ 0 :: E.Z)) := Sym4.cons (by simp [ALL]) (hJ'.sym4.app (Sym4.cons (by simp [ALL]) hZ))
    have h1 := y1eEnd _ (1 :: (J' ++ 0 :: E.Z)) sP sR
    have h2 := fn1_M _ (J' ++ 0 :: E.Z) sP1 (hJ'.sym4.app (Sym4.cons (by simp [ALL]) hZ))
    exact ⟨_, ⟨_, J', (nP.app (NoB.cons one_nb NoB.nil)).app (NoB.cons one_nb NoB.nil), hJ', Or.inr rfl⟩,
      hpop.trans ((h1.of_eq (by simp [Enc]) rfl).trans h2)⟩

/-- `m = 0`, `X` empty and `H` nonempty. -/
theorem checkSpecM0A (E : GEnv) (hm : E.m = 0) (H J : List Nat) (hne : H ≠ []) (hHv : ∀ e ∈ H, 1 ≤ e)
    (hJ : JShape J) (hJo : ∀ a ∈ J, a ∈ O13)
    (hTc : E.Tc = 1 :: (1 :: (HP (Hs H []) 0 ++ J))) :
    E.CheckSpec (fun w => checkG w 0 [] H) (AccS E.Z) := by
  intro rest hv
  have hr := restNil0 E hm rest hv
  subst hr
  have hQ : ∀ a ∈ (1 :: (HP (Hs H []) 0 ++ J)), a ∈ O13 := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [O13]
    · rcases List.mem_append.1 ha with ha | ha
      · exact HP_Hs_o13 H hne hHv a ha
      · exact hJo a ha
  have hpop := popM E [] (by simp) 0 [] (1 :: (HP (Hs H []) 0 ++ J)) hQ (by simpa [Enc] using hTc)
  have hpop' : zgiLogic.Reach (E.CfgPop [])
      (cfgM [] 0 H J E.Z [] [] []) :=
    hpop.of_eq rfl (by simp [cfgM, Enc, MEnc, List.append_assoc])
  have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
  constructor
  · intro hg
    have hall : ∀ k < H.length, H.getD k 0 < 2 ∨ k + 1 ∈ ([] : List Nat) := fun k hk =>
      Or.inl ((checkG_nil_true 0 H).1 hg k hk)
    obtain ⟨c', hc, h⟩ := finalAccM [] 0 H hne J E.Z hJ E.hZ [] [] hd0 (by simp) hall
    exact ⟨c', hc, hpop'.trans h⟩
  · intro hg
    have hbad : ∃ k, k < H.length ∧ 2 ≤ H.getD k 0 ∧ k + 1 ∉ ([] : List Nat) := by
      refine Classical.byContradiction fun hno => ?_
      have hlt : ∀ k < H.length, H.getD k 0 < 2 := by
        intro k hk
        refine Classical.byContradiction fun h => ?_
        exact hno ⟨k, hk, by omega, by simp⟩
      have : checkG [] 0 [] H = true := (checkG_nil_true 0 H).2 hlt
      have hg' : checkG [] 0 [] H = false := hg
      rw [this] at hg'; cases hg'
    have hf := finalFailM [] 0 H hne J E.Z hJ E.hZ [] [] hd0 (by simp) hbad
    obtain ⟨A, R1, hA, hR1, hu, h⟩ := hf
    have hf2 := failPath A R1 E.Z hA hR1 E.hZ
    refine (hpop'.trans h).trans (hf2.of_eq rfl ?_)
    rw [hu]
    simp [Ufull, unm_cons, unmHu H J hne hHv hJo, unm1, GEnv.CfgD, GEnv.Rt, hTc, Enc, List.append_assoc]

end ZP.G
