import ZP.CheckG5

namespace ZP.G

open ZP

/-- The popped stack leads to the start of the edge loop, for an arbitrary tail `Q` after the separator. -/
theorem popG (E : GEnv) (rest : List Nat) (hrest : ∀ e ∈ rest, 1 ≤ e) (p : Nat) (X Q : List Nat)
    (hQ : ∀ a ∈ Q, a ∈ O13)
    (hTc : E.Tc = List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ Q)) :
    zgiLogic.Reach (E.CfgPop rest)
      (hdR QG.gY1e (Enc rest ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (Enc X ++ (Q ++ 0 :: E.Z))) := by
  have sRt := E.Rt_sym4
  have hws := Enc_entries rest hrest
  have sZ := E.hZ
  have sEnc : Sym4 (Enc rest) := by
    intro a ha; have := Enc_o13 rest a ha; simp [O13, ALL] at this ⊢; omega
  have hlist : Enc rest ++ E.Rt = MEs (rest.map fun e => List.replicate e 3) ++ 1 ::
      (List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ (Q ++ 0 :: E.Z))) := by
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
  have hp := phaseU (rest.map fun e => List.replicate e 3) (List.replicate (p + 1) 3)
    (Enc X ++ (Q ++ 0 :: E.Z)) [0] hws (bits_rep3 _) (by simp [ALL]) sR
  have hax2 := hax.symm.trans hlist
  have hstart : E.CfgPop rest = hdR QG.gGL [0] (a :: X0) := by
    simp only [GEnv.CfgPop]; rw [hax]
  rw [hstart]
  refine ((h1.trans (hp.of_eq (by rw [hax2]) rfl)).of_eq rfl ?_)
  simp only [unm_append, unm_Enc, unm_rep3, ← Enc_MEs]
  rw [show [0] ++ Enc rest ++ [1] ++ List.replicate (p + 1) 3 ++ [1] = 0 :: (Enc rest ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) by
    simp [List.append_assoc], hdR_z0]

/-- The `HFam` of an empty `H`: what follows `X` is `H0` (nothing, one separator, or the separator and more). -/
def HFam.ofEmpty (H0 : List Nat) (hH0 : H0 = [] ∨ H0 = [1] ∨ (∃ J', NoB J' ∧ H0 = 1 :: 1 :: J') ∨ (∃ t, Bits t ∧ t ≠ [] ∧ H0 = t)) (hnb : NoB H0)
    (Zt : List Nat) (hZ : Sym4 Zt) : HFam where
  Hc := fun _ => H0
  N := 0
  Zt := Zt
  Hu := unm H0
  hZ := hZ
  nb := fun _ _ => hnb
  un := fun _ _ => rfl
  step := fun c hc => absurd hc (Nat.not_lt_zero _)
  last := Or.inr ⟨rfl, hH0⟩

/-- With an empty `H` every edge fails. -/
theorem emptyBad (F : HFam) (hN : F.N = 0) (hH0 : F.Hc 0 = [] ∨ F.Hc 0 = [1] ∨ (∃ J', NoB J' ∧ F.Hc 0 = 1 :: 1 :: J') ∨ (∃ t, Bits t ∧ t ≠ [] ∧ F.Hc 0 = t))
    (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    RowBad F W p x 0 ∨ ∃ n Wr, W.drop (x - 1) = (n + 1) :: Wr ∧ 0 + (p + 1) * n ≤ F.N ∧
      ColBad F W y (0 + (p + 1) * n) := by
  by_cases hxW : x ≤ W.length
  · obtain ⟨n, Wr, hr, hgr⟩ := W_split W hW (x - 1) (by omega)
    by_cases hn : n = 0
    · subst hn
      refine Or.inr ⟨0, Wr, hr, by simp [hN], ?_⟩
      by_cases hyW : y ≤ W.length
      · by_cases hy1 : 1 ≤ y
        · obtain ⟨n', Wr', hr', hgr'⟩ := W_split W hW (y - 1) (by omega)
          refine Or.inr ⟨n', Wr', hr', ?_⟩
          by_cases hn' : n' = 0
          · subst hn'
            rcases hH0 with h | h | ⟨J', hJ', h⟩ | ⟨t, ht, htne, h⟩
            · exact Or.inr (Or.inl ⟨by simp [hN], by simp [h]⟩)
            · exact Or.inr (Or.inr (Or.inr ⟨[], [], by simp [hN], by simp, by simp [MP, h], Or.inl rfl⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨[], 1 :: J', by simp [hN], by simp, by simp [MP, h], Or.inr (Or.inl ⟨J', hJ', rfl⟩)⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨by simp [hN], t, ht, htne, h⟩))
          · exact Or.inl (by simp [hN]; omega)
        · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · exact Or.inl (Or.inr ⟨n, Wr, hr, by
        rw [hN]; have : 0 < (p + 1) * n := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hn); omega⟩)
  · exact Or.inl (Or.inl (by omega))

theorem y1eEndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1e P (0 :: R)) (hd QG.FE P (3 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem checkEmpty (W : List Nat) (hW : ∀ e ∈ W, 1 ≤ e) (p : Nat) (H0 : List Nat)
    (hH0 : H0 = [] ∨ H0 = [1] ∨ (∃ J', NoB J' ∧ H0 = 1 :: 1 :: J') ∨ (∃ t, Bits t ∧ t ≠ [] ∧ H0 = t)) (hnb : NoB H0) (Zt : List Nat) (hZ : Sym4 Zt)
    (X : List Nat) (hX : ∀ e ∈ X, 1 ≤ e) (hDlen : (∃ t, Bits t ∧ t ≠ [] ∧ H0 = t) → 2 ≤ X.length) :
    (X = [] → ∃ c', AccS c' ∧ zgiLogic.Reach
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (Enc X ++ (H0 ++ 0 :: Zt))) c') ∧
    (X ≠ [] → FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (Enc X ++ (H0 ++ 0 :: Zt)))
      (Ufull W (p + 1) X (unm H0)) Zt) := by
  let F := HFam.ofEmpty H0 hH0 hnb Zt hZ
  have sP : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) := by
    refine ((Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL])))
    have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
  constructor
  · rintro rfl
    have sP1 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ [1]) := by
      refine sP.app (show Sym4 [1] from Sym4.cons (by simp [ALL]) Sym4.nil)
    rcases hH0 with rfl | rfl | ⟨J', hJ', rfl⟩ | ⟨t, ht, htne, hh⟩
    · exact ⟨_, ⟨_, _, Or.inl rfl⟩, (y1eEndB _ Zt sP hZ).of_eq (by simp [Enc]) rfl⟩
    · have h1 := y1eEnd _ (0 :: Zt) sP (Sym4.cons (by simp [ALL]) hZ)
      have h2 := fn1_B _ Zt sP1 hZ
      exact ⟨_, ⟨_, _, Or.inl rfl⟩, (h1.of_eq (by simp [Enc]) rfl).trans h2⟩
    · have sR : Sym4 (1 :: (J' ++ 0 :: Zt)) := Sym4.cons (by simp [ALL]) (hJ'.sym4.app (Sym4.cons (by simp [ALL]) hZ))
      have h1 := y1eEnd _ (1 :: (J' ++ 0 :: Zt)) sP sR
      have h2 := fn1_M _ (J' ++ 0 :: Zt) sP1 (hJ'.sym4.app (Sym4.cons (by simp [ALL]) hZ))
      exact ⟨_, ⟨_, _, Or.inr rfl⟩, (h1.of_eq (by simp [Enc]) rfl).trans h2⟩
    · exact absurd (hDlen ⟨t, ht, htne, hh⟩) (by simp)
  · intro hne
    obtain ⟨x, X1, rfl⟩ : ∃ x X1, X = x :: X1 := by
      cases X with
      | nil => exact absurd rfl hne
      | cons x X1 => exact ⟨x, X1, rfl⟩
    have hx : 1 ≤ x := hX x (by simp)
    have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
    cases X1 with
    | nil =>
      have := oddFailF F W [] p x 0 hW hd0 (by simp) hx (Nat.zero_le _)
        (fun c' _ => by
          rcases hH0 with h | h | ⟨J', _, h⟩ | ⟨t, ht, htne, h⟩
          · simp [F, HFam.ofEmpty, h]
          · simp [F, HFam.ofEmpty, h]
          · simp [F, HFam.ofEmpty, h]
          · exact absurd (hDlen ⟨t, ht, htne, h⟩) (by simp))
      refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ this)
      · simp [Enc, U, MEnc, F, HFam.ofEmpty, List.append_assoc]
      · simp [Ufull, F, HFam.ofEmpty, Enc, U, List.append_assoc]
    | cons y X2 =>
      have hy : 1 ≤ y := hX y (by simp)
      have hX2 : ∀ e ∈ X2, 1 ≤ e := fun e he => hX e (by simp [he])
      have := edgeFailF F W [] X2 p x y 0 hW hd0 hX2 (by simp) hx hy (Nat.zero_le _)
        (emptyBad F rfl (by simpa [F, HFam.ofEmpty] using hH0) W hW p x y hx hy)
      refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ this)
      · simp [Enc, U, MEnc, F, HFam.ofEmpty, List.append_assoc]
      · simp [Ufull, F, HFam.ofEmpty, Enc, U, List.append_assoc]

theorem checkG_nil (w : List Nat) (m : Nat) (X : List Nat) : checkG w m X [] = decide (X = []) := by
  match X with
  | [] => simp [checkG, pairsOf, checkEdges]
  | [x] => simp [checkG]
  | x :: y :: r =>
    simp only [checkG, pairsOf, checkEdges]
    by_cases h1 : x > w.length ∨ y > w.length
    · simp [h1]
    · rw [if_neg h1]
      have : (w.getD (x - 1) 0 - 1) * m + w.getD (y - 1) 0 > ([] : List Nat).length ∨
          ([] : List Nat).getD (((w.getD (x - 1) 0 - 1) * m + w.getD (y - 1) 0) - 1) 0 < 2 ∨
          ((w.getD (x - 1) 0 - 1) * m + w.getD (y - 1) 0) ∈ ([] : List Nat) := by
        right; left; simp
      rw [if_pos this]
      simp

theorem checkSpecE (E : GEnv) (p : Nat) (X H0 : List Nat) (hH0 : H0 = [] ∨ H0 = [1] ∨ (∃ J', NoB J' ∧ H0 = 1 :: 1 :: J') ∨ (∃ t, Bits t ∧ t ≠ [] ∧ H0 = t))
    (hH0o : ∀ a ∈ H0, a ∈ O13) (hX : ∀ e ∈ X, 1 ≤ e) (hDlen : (∃ t, Bits t ∧ t ≠ [] ∧ H0 = t) → 2 ≤ X.length)
    (hTc : E.Tc = List.replicate (p + 1) 3 ++ 1 :: (Enc X ++ H0)) :
    E.CheckSpec (fun w => checkG w (p + 1) X []) AccS := by
  intro rest hv
  have hW : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
  have hpop := popG E rest hW p X H0 hH0o hTc
  have hnb : NoB H0 := fun a ha => by have := hH0o a ha; simp [O13, NB] at this ⊢; omega
  have hfull := checkEmpty rest hW p H0 hH0 hnb E.Z E.hZ X hX hDlen
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · simp only [checkG_nil] at hg
    have hX0 : X = [] := by simpa using hg
    obtain ⟨c', hc, hr⟩ := hfull.1 hX0
    exact ⟨c', hc, hpop.trans hr⟩
  · simp only [checkG_nil] at hg
    have hX0 : X ≠ [] := by simpa using hg
    obtain ⟨A, R1, hA, hR1, hu, hr⟩ := hfull.2 hX0
    have hf := failPath A R1 E.Z hA hR1 E.hZ
    refine (hpop.trans hr).trans (hf.of_eq rfl ?_)
    rw [hu, unm_o13 hH0o]
    simp [Ufull, GEnv.CfgD, GEnv.Rt, hTc, List.append_assoc]

theorem xmEndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gXm P (0 :: R)) (hd QG.FE P (3 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xmCellsB (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gXm P (c ++ 0 :: R)) (hd QG.FE (P ++ unm c) (3 :: R))
  | [], P, _, hP => (xmEndB P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := xmStep P (c ++ 0 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [unm1 b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [unm1, ALL, hP]
    have h2 := xmCellsB R hR c (P ++ [unm1 b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp [unm]))

/-- `T = [m]`: nothing but the cells of `m`; the machine accepts. -/
theorem checkSpecS0 (E : GEnv) (p : Nat) (hTc : E.Tc = List.replicate (p + 1) 3) (m' : Nat) :
    E.CheckSpec (fun w => checkG w m' [] []) AccS := by
  intro rest hv
  have hW : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
  refine ⟨fun _ => ?_, fun hg => absurd hg (by simp [checkG, pairsOf, checkEdges])⟩
  have sRt := E.Rt_sym4
  have hws := Enc_entries rest hW
  have sZ := E.hZ
  have sEnc : Sym4 (Enc rest) := by
    intro a ha; have := Enc_o13 rest a ha; simp [O13, ALL] at this ⊢; omega
  have hlist : Enc rest ++ E.Rt = MEs (rest.map fun e => List.replicate e 3) ++ 1 ::
      (List.replicate (p + 1) 3 ++ 0 :: E.Z) := by
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
  have hR1 : Sym4 (1 :: (List.replicate (p + 1) 3 ++ 0 :: E.Z)) :=
    Sym4.cons (by simp [ALL]) ((Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) sZ))
  have hu := uwWalk (1 :: (List.replicate (p + 1) 3 ++ 0 :: E.Z)) hR1 (rest.map fun e => List.replicate e 3) [0] hws (by simp [ALL])
  have hn := unm_nb (MEs_noB _ (fun e he => (hws e he).1))
  have hP1 : Sym4 ([0] ++ unm (MEs (rest.map fun e => List.replicate e 3))) := by simp [hn.sym4, ALL]
  have h2 := uw2End _ (List.replicate (p + 1) 3 ++ 0 :: E.Z) hP1 (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (Sym4.cons (by simp [ALL]) sZ))
  have hP2 : Sym4 ([0] ++ unm (MEs (rest.map fun e => List.replicate e 3)) ++ [1]) := by simp [hn.sym4, ALL]
  have h3 := xmCellsB E.Z sZ (List.replicate (p + 1) 3) _ (bits_rep3 _) hP2
  have hax2 := hax.symm.trans hlist
  have hstart : E.CfgPop rest = hdR QG.gGL [0] (a :: X0) := by
    simp only [GEnv.CfgPop]; rw [hax]
  rw [hstart]
  exact ⟨_, ⟨_, _, Or.inl rfl⟩, h1.trans ((hu.of_eq (by rw [hax2]) rfl).trans ((h2.of_eq rfl rfl).trans (h3.of_eq rfl rfl)))⟩

end ZP.G
