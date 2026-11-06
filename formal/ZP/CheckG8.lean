import ZP.CheckG7

namespace ZP.G

open ZP

theorem y1eTwo (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1e P (2 :: R)) (hdR QG.gY2e (P ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem y2Two (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY2e P (2 :: R)) (hdR QG.gY2e (P ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem y2EndB (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY2e P (0 :: R)) (hd QG.gFG P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem y2Run (R : List Nat) (hR : Sym4 R) : ∀ (k : Nat) (P : List Nat), Sym4 P →
    zgiLogic.Reach (hdR QG.gY2e P (List.replicate k 2 ++ 0 :: R)) (hd QG.gFG (P ++ List.replicate k 2) (0 :: R))
  | 0, P, hP => (y2EndB P R hP hR).of_eq (by simp) (by simp)
  | k + 1, P, hP => by
    have hR' : Sym4 (List.replicate k 2 ++ 0 :: R) := (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)
    have h1 := y2Two P (List.replicate k 2 ++ 0 :: R) hP hR'
    have h2 := y2Run R hR k (P ++ [2]) (hP.app (by simp [ALL]))
    exact (h1.of_eq (by simp [List.replicate_succ]) rfl).trans (h2.of_eq (by simp) (by simp [List.replicate_succ, List.append_assoc]))

/-- A marked run that is followed by the blank: the parity cannot be completed, so the check fails. -/
theorem y1eRunFail (P R : List Nat) (k : Nat) (hP : Sym4 P) (hPn : NoB P) (hR : Sym4 R) :
    ∃ A R1 : List Nat, NoB A ∧ NoB R1 ∧ A ++ R1 = P ++ List.replicate (k + 1) 2 ∧
      zgiLogic.Reach (hdR QG.gY1e P (List.replicate (k + 1) 2 ++ 0 :: R)) (hdR QG.gFG A (R1 ++ 0 :: R)) := by
  have hR' : Sym4 (List.replicate k 2 ++ 0 :: R) := (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)
  have h1 := y1eTwo P (List.replicate k 2 ++ 0 :: R) hP hR'
  have h2 := y2Run R hR k (P ++ [2]) (hP.app (by simp [ALL]))
  have nA : NoB (P ++ [2] ++ List.replicate k 2) := by simp [NB, hPn]
  have h3 := gfgR' (P ++ [2] ++ List.replicate k 2) (0 :: R) nA (by simp) (Sym4.cons (by simp [ALL]) hR)
  exact ⟨P ++ [2] ++ List.replicate k 2, [], nA, NoB.nil, by simp [List.replicate_succ, List.append_assoc],
    ((h1.of_eq (by simp [List.replicate_succ]) rfl).trans (h2.trans h3)).of_eq rfl (by simp)⟩


/-- The unmarked content for an unterminated last label `x`. -/
def UfullNS (W : List Nat) (m : Nat) (d : List Nat) (x : Nat) : List Nat :=
  Enc W ++ 1 :: (List.replicate m 3 ++ 1 :: (Enc d ++ List.replicate x 3))

/-- An `H` family for the marked unterminated label (a single bits-only entry). -/
def Fmark (x : Nat) (hx : 1 ≤ x) (Z : List Nat) (hZ : Sym4 Z) : HFam where
  Hc := fun _ => List.replicate x 2
  N := 0
  Zt := Z
  Hu := List.replicate x 3
  hZ := hZ
  nb := fun _ _ => by simp [NB]
  un := fun _ _ => unm_rep2 x
  step := fun c hc => absurd hc (Nat.not_lt_zero _)
  last := Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr ⟨List.replicate x 2, bits_rep2 x, by
    intro h; have := congrArg List.length h; simp at this; omega, rfl⟩))⟩

theorem rowNoTargetNS (W d Z : List Nat) (p x : Nat) (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hZ : Sym4 Z) :
    FailsTo
      (hd QG.gM1 (MEnc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2) (0 :: Z))
      (UfullNS W (p + 1) d x) Z := by
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  have sQ : Sym4 (MEnc W ++ [1] ++ List.replicate p 3) :=
    (((MEnc_sym4 W).app (by simp [ALL])).app (Sym4.rep _ _ (by simp [ALL])))
  have nQ : NoB (MEnc W ++ [1] ++ List.replicate p 3) := by simp [NB]
  have hZ' : ∀ a ∈ [1] ++ MEnc d ++ List.replicate x 2, a = 1 ∨ a = 2 := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at ha
    rcases ha with (rfl | ha) | ⟨_, rfl⟩
    · left; rfl
    · have := MEnc_o12 d a ha; simp [O12] at this; omega
    · right; rfl
  have h1 := gm1Walk (MEnc W ++ [1] ++ List.replicate p 3) sQ _ ([1] ++ MEnc d ++ List.replicate x 2)
    (0 :: Z) rfl hZ' sZ0
  have sR2 : Sym4 (2 :: ([1] ++ MEnc d ++ List.replicate x 2 ++ 0 :: Z)) := by
    refine Sym4.cons (by simp [ALL]) ((((Sym4.cons (by simp [ALL]) Sym4.nil).app (MEnc_sym4 d)).app (Sym4.rep _ _ (by simp [ALL]))).app sZ0)
  have h2 := trLeft _ _ nQ sR2
  have sR3 : Sym4 (1 :: (List.replicate p 3 ++ 2 :: ([1] ++ MEnc d ++ List.replicate x 2 ++ 0 :: Z))) := by
    refine Sym4.cons (by simp [ALL]) ((Sym4.rep _ _ (by simp [ALL])).app sR2)
  have h3 := trSkipList _ sR3 W [0] hW (by simp [ALL])
  have h4 := trNoTarget ([0] ++ MEnc W) (List.replicate p 3 ++ 2 :: ([1] ++ MEnc d ++ List.replicate x 2 ++ 0 :: Z))
    (by simp [ALL]) ((Sym4.rep _ _ (by simp [ALL])).app sR2)
  have hall := h1.trans ((h2.of_eq rfl (by simp [List.append_assoc])).trans ((h3.of_eq rfl (by simp)).trans (h4.of_eq rfl rfl)))
  refine ⟨MEnc W ++ [1], List.replicate p 3 ++ 2 :: ([1] ++ MEnc d ++ List.replicate x 2), by simp [NB], ?_, ?_, ?_⟩
  · have : NoB (MEnc d) := by
      intro a ha; have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega
    simp only [NoB_app_iff, NoB_cons_iff]
    simp [NB, this]
  · simp [UfullNS, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, List.append_assoc, unm1, List.replicate_succ', Enc_append, Enc, U]
  · refine hall.of_eq (by simp [List.replicate_succ', List.append_assoc]) ?_
    rw [show [0] ++ MEnc W ++ [1] = 0 :: (MEnc W ++ [1]) by simp, hdR_z0]
    simp [List.append_assoc]


theorem rowFailNS (ms Wr d Z : List Nat) (n x p : Nat) (hZ : Sym4 Z)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hWr : ∀ e ∈ Wr, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hx : 1 ≤ x) (hn : 0 < n) :
    FailsTo
      (hd QG.gM1 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (0 :: Z))
      (UfullNS (ms ++ (n + 1) :: Wr) (p + 1) d x) Z := by
  let F := Fmark x hx Z hZ
  have hws := Enc_entries Wr hWr
  have hxs : ∀ e ∈ d.map fun e => List.replicate e 2, Bits e ∧ e ≠ [] := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 he
    exact ⟨bits_rep2 v, by have := hdd v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  have sQ : Sym4 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ List.replicate p 3) := by
    refine (((MEnc_sym4 ms).app (fun a ha => ?_)).app (by simp [ALL])).app (Sym4.rep _ _ (by simp [ALL]))
    have := Enc_o13 ((n + 1) :: Wr) a ha; simp [O13, ALL] at this ⊢; omega
  have hZ' : ∀ a ∈ [1] ++ MEnc d ++ List.replicate x 2, a = 1 ∨ a = 2 := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at ha
    rcases ha with (rfl | ha) | ⟨_, rfl⟩
    · left; rfl
    · have := MEnc_o12 d a ha; simp [O12] at this; omega
    · right; rfl
  have h1 := gm1Walk (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ List.replicate p 3) sQ _ ([1] ++ MEnc d ++ List.replicate x 2)
    (0 :: Z) rfl hZ' sZ0
  have hov : F.N < 0 + (p + 1) * n := by
    show 0 < 0 + (p + 1) * n
    exact Nat.add_pos_right _ (Nat.mul_pos (Nat.succ_pos p) hn)
  have h2 := rowLoopF F ms (Wr.map fun e => List.replicate e 3) (d.map fun e => List.replicate e 2)
    hms hws hxs n p 0 n 0 0 (by omega) (Nat.le_refl _) hov
  have h1' : zgiLogic.Reach
      (hd QG.gM1 (MEnc ms ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (0 :: Z))
      (hd QG.gTR1 (MEnc ms ++ List.replicate 0 2 ++ 3 :: (List.replicate n 3 ++ 1 :: (MEs (Wr.map fun e => List.replicate e 3) ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate 0 2 ++ 1 :: (MEs (d.map fun e => List.replicate e 2) ++ (F.Hc 0 ++ 0 :: F.Zt))))) := by
    refine h1.of_eq (by simp [List.replicate_succ', List.append_assoc]) ?_
    simp [F, Fmark, Enc_MEs, MEnc_MEs, MEs_append, MEs, ME, List.append_assoc, List.replicate_succ]
  refine FailsTo.pre h1' (FailsTo.cast ?_ h2)
  have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = MEs (Wr.map fun e => List.replicate e 3) := by
    rw [← Enc_MEs, unm_Enc]
  have e2 : MEs (d.map fun e => List.replicate e 2) = MEnc d := (MEnc_MEs d).symm
  have e3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = Enc Wr := by
    rw [u3, ← Enc_MEs]
  have e4 : unm (MEs (d.map fun e => List.replicate e 2)) = Enc d := by rw [e2, unm_MEnc]
  simp [UG, UfullNS, F, Fmark, e4, e3, unm_append, unm_MEnc, unm_rep2, unm_Enc, Enc_append, Enc, U, unm1, List.append_assoc]


theorem rowOkNS (ms Wr d Z : List Nat) (x p : Nat) (hZ : Sym4 Z)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hWr : ∀ e ∈ Wr, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hx : 1 ≤ x) :
    zgiLogic.Reach
      (hd QG.gM1 (MEnc ms ++ Enc (1 :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (0 :: Z))
      (hdR QG.gY1e (Enc (ms ++ 1 :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
        (MEnc d ++ List.replicate x 2 ++ 0 :: Z)) := by
  let F := Fmark x hx Z hZ
  have hws := Enc_entries Wr hWr
  have hxs : ∀ e ∈ d.map fun e => List.replicate e 2, Bits e ∧ e ≠ [] := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 he
    exact ⟨bits_rep2 v, by have := hdd v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  have sQ : Sym4 (MEnc ms ++ Enc (1 :: Wr) ++ [1] ++ List.replicate p 3) := by
    refine (((MEnc_sym4 ms).app (fun a ha => ?_)).app (by simp [ALL])).app (Sym4.rep _ _ (by simp [ALL]))
    have := Enc_o13 (1 :: Wr) a ha; simp [O13, ALL] at this ⊢; omega
  have hZ' : ∀ a ∈ [1] ++ MEnc d ++ List.replicate x 2, a = 1 ∨ a = 2 := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at ha
    rcases ha with (rfl | ha) | ⟨_, rfl⟩
    · left; rfl
    · have := MEnc_o12 d a ha; simp [O12] at this; omega
    · right; rfl
  have h1 := gm1Walk (MEnc ms ++ Enc (1 :: Wr) ++ [1] ++ List.replicate p 3) sQ _ ([1] ++ MEnc d ++ List.replicate x 2)
    (0 :: Z) rfl hZ' sZ0
  have h2 := rowLoopU F ms (Wr.map fun e => List.replicate e 3) (d.map fun e => List.replicate e 2)
    hms hws hxs 0 p 0 0 0 0 (by omega) (by show 0 + (p + 1) * 0 ≤ 0; omega)
  have h1' : zgiLogic.Reach
      (hd QG.gM1 (MEnc ms ++ Enc (1 :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate x 2)
        (0 :: Z))
      (hd QG.gTR1 (MEnc ms ++ List.replicate 0 2 ++ 3 :: (List.replicate 0 3 ++ 1 :: (MEs (Wr.map fun e => List.replicate e 3) ++ 1 :: List.replicate p 3)))
        (2 :: (List.replicate 0 2 ++ 1 :: (MEs (d.map fun e => List.replicate e 2) ++ (F.Hc 0 ++ 0 :: F.Zt))))) := by
    refine h1.of_eq (by simp [List.replicate_succ', List.append_assoc]) ?_
    simp [F, Fmark, Enc_MEs, MEnc_MEs, MEs_append, MEs, ME, List.append_assoc, List.replicate_succ]
  have hWL : ∀ e ∈ ms.map (fun e => List.replicate e 2) ++ (List.replicate 0 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3),
      Bits e ∧ e ≠ [] := by
    intro e he
    simp only [List.mem_append, List.mem_cons, List.mem_map] at he
    rcases he with ⟨v, hv, rfl⟩ | rfl | ⟨v, hv, rfl⟩
    · exact ⟨bits_rep2 v, by have := hms v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
    · refine ⟨fun a ha => ?_, by simp⟩
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha]; simp [bits]
      · simp at ha; subst ha; simp [bits]
    · exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
  have hRr : Sym4 (MEs (d.map fun e => List.replicate e 2) ++ (F.Hc 0 ++ 0 :: F.Zt)) := by
    refine Sym4.app (MEs_sym4 _ ?_) ((Sym4.rep _ _ (by simp [ALL])).app sZ0)
    intro e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 he
    exact bits_rep2 v
  have hT := toY1 _ (List.replicate (p + 1) 2) _ hWL (bits_rep2 _) hRr
  refine (h1'.trans h2).trans (hT.of_eq ?_ ?_)
  · simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc, List.replicate_succ]
  · have e1 : MEs (ms.map (fun e => List.replicate e 2) ++ (List.replicate 0 2 ++ [3]) :: Wr.map (fun e => List.replicate e 3)) =
        MEnc ms ++ List.replicate 0 2 ++ 3 :: 1 :: MEs (Wr.map fun e => List.replicate e 3) := by
      simp [MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
    rw [e1, show Enc (ms ++ 1 :: Wr) = Enc ms ++ Enc (1 :: Wr) from Enc_append ..]
    have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = MEs (Wr.map fun e => List.replicate e 3) := by
      rw [← Enc_MEs, unm_Enc]
    have u4 : unm (MEs (ms.map fun e => List.replicate e 2)) = MEs (ms.map fun e => List.replicate e 3) := by
      rw [← MEnc_MEs, unm_MEnc, Enc_MEs]
    simp [F, Fmark, unm_append, unm_rep2, unm_rep3, unm1, unm_MEnc, u3, u4, Enc_MEs, rep3_cons, MEs, ME, MEnc, MEnc_append, Enc, U,
      MEnc_MEs, List.replicate_succ, List.append_assoc]
    done


/-- The first label is the unterminated last entry of `X`: the check fails. -/
theorem firstFailNS (W d Z : List Nat) (p x : Nat) (hZ : Sym4 Z)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 0) (hx : 1 ≤ x) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (MEnc d ++ List.replicate x 3 ++ 0 :: Z))
      (UfullNS W (p + 1) d x) Z := by
  obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
  have hdf : decide (d.length % 2 = 1) = false := by simp [hdl]
  have hY : ∃ c R', (c = 0 ∨ c = 1) ∧ (0 :: Z) = c :: R' ∧ Sym4 R' := ⟨0, Z, Or.inl rfl, rfl, hZ⟩
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  rcases Nat.lt_or_ge W.length r with hlt | hge
  · -- the label is beyond `w` by at least two
    have hF := labelFindFY (p + 1) d [] Z hdd NoB.nil hZ r [] W 0 (by simp) hW hlt
    refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ hF)
    · simp [MEnc, List.append_assoc]
    simp [UfullNS, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, List.append_assoc, unm1, Enc_append, Enc, U,
      List.replicate_succ']
  · have hrl : r ≤ W.length := by
      rcases Nat.lt_or_ge W.length r with h | h
      · omega
      · exact h
    have hL := labelFindY (p + 1) d (0 :: Z) hdd sZ0 hY r [] W 0 (by simp) hW hrl
    rw [hdf] at hL
    have hLd : (LDone false) = QG.gM1 := rfl
    rw [hLd] at hL
    have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
    rcases Nat.lt_or_ge r W.length with hrw | hrw
    · obtain ⟨n, Wr, hr, _⟩ := W_split W hW r hrw
      have hWr : ∀ e ∈ Wr, 1 ≤ e := by
        intro e he
        have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
        exact hW e (List.mem_of_mem_drop this)
      rw [hr] at hL
      have hW' : W.take r ++ (n + 1) :: Wr = W := by rw [← hr, List.take_append_drop]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.zero_add, List.nil_append] at hL hr hW'
        have hO := rowOkNS (W.take r) Wr d Z (r + 1) p hZ hms hWr hdd hx
        rw [hW'] at hO
        have sP0 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) := by
          refine (Sym4.app (fun a ha => ?_) (by simp [ALL])).app (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (by simp [ALL]))
          have := Enc_o13 W a ha; simp [O13, ALL] at this ⊢; omega
        have hw := lblWalk (List.replicate (r + 1) 2 ++ 0 :: Z)
          ((Sym4.rep _ _ (by simp [ALL])).app sZ0) d false _ hdd sP0
        simp only [Bool.false_xor, hdf, Y1_false] at hw
        have sP1 : Sym4 (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d) := sP0.app (MEnc_sym4 d)
        have nP1 : NoB (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d) := by
          simp only [NoB_app_iff]
          refine ⟨⟨⟨fun a ha => ?_, by simp [NB]⟩, by simp [NB]⟩, fun a ha => ?_⟩
          · have := Enc_o13 W a ha; simp [O13, NB] at this ⊢; omega
          · have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega
        obtain ⟨A, R1, hA, hR1, hAR, h2⟩ := y1eRunFail _ Z r sP1 nP1 hZ
        have hun : unm (A ++ R1) = UfullNS W (p + 1) d (r + 1) := by
          rw [hAR]
          simp [UfullNS, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, List.append_assoc, unm1, Enc, U,
            List.replicate_succ']
        have hw2 : zgiLogic.Reach
            (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (MEnc d ++ List.replicate (r + 1) 2 ++ 0 :: Z))
            (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d) (List.replicate (r + 1) 2 ++ 0 :: Z)) :=
          hw.of_eq (by simp [List.append_assoc]) rfl
        exact FailsTo.pre ((hL.trans (hO.trans hw2)).of_eq (by simp [MEnc]) rfl) ⟨A, R1, hA, hR1, hun, h2⟩
      · have hN := rowFailNS (W.take r) Wr d Z n (r + 1) p hZ hms hWr hdd hx hn
        rw [hW'] at hN
        refine FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc])) hN
    · have hr : r = W.length := by omega
      subst hr
      have hN := rowNoTargetNS W d Z p (W.length + 1) hW hdd hZ
      rw [List.drop_length, List.take_length] at hL
      exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc, Enc])) hN


theorem colNoTargetNS (W d Z : List Nat) (p y : Nat) (hW : ∀ e ∈ W, 1 ≤ e) (hZ : Sym4 Z) :
    FailsTo
      (hd QG.gIL0 (MEnc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate y 2) (0 :: Z))
      (UfullNS W (p + 1) d y) Z := by
  have sT : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  have nA : NoB (MEnc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++ List.replicate y 2) := by
    simp [NB]
  have h1 := il0Walk' _ _ nA sT
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have sL : Sym4 (List.replicate (p + 1) 3 ++ [1] ++ MEnc d ++ List.replicate y 2 ++ 0 :: Z) :=
    ((((Sym4.rep (p + 1) 3 a3).app (Sym4.cons a1 Sym4.nil)).app (MEnc_sym4 d)).app (Sym4.rep y 2 a2)).app sT
  have sR : Sym4 (1 :: (List.replicate (p + 1) 3 ++ [1] ++ MEnc d ++ List.replicate y 2 ++ 0 :: Z)) := Sym4.cons a1 sL
  have h2 := ilSkipList (1 :: (List.replicate (p + 1) 3 ++ [1] ++ MEnc d ++ List.replicate y 2 ++ 0 :: Z)) sR W [] hW Sym4.nil
  have h3 := ilNoTarget (MEnc W) (List.replicate (p + 1) 3 ++ [1] ++ MEnc d ++ List.replicate y 2 ++ 0 :: Z) (MEnc_sym4 W) sL
  have hall := h1.trans ((h2.of_eq (by simp [List.append_assoc]) rfl).trans (h3.of_eq rfl rfl))
  have nd : NoB (MEnc d) := by
    intro a ha; have := MEnc_o12 d a ha; simp [O12, NB] at this ⊢; omega
  refine ⟨MEnc W ++ [1], List.replicate (p + 1) 3 ++ [1] ++ MEnc d ++ List.replicate y 2,
    by simp [NB], ?_, ?_, ?_⟩
  · simp only [NoB_app_iff]
    simp [NB, nd]
  · simp [UfullNS, unm_append, unm_MEnc, unm_rep3, unm_rep2, unm_Enc, List.append_assoc, unm1, Enc_append, Enc, U]
  · refine hall.of_eq rfl ?_
    simp [List.append_assoc]


/-- The second label is the unterminated last entry of `X`: the check fails. -/
theorem secondFailNS (W d Z : List Nat) (p y : Nat) (hZ : Sym4 Z)
    (hW : ∀ e ∈ W, 1 ≤ e) (hdd : ∀ e ∈ d, 1 ≤ e) (hdl : d.length % 2 = 1) (hy : 1 ≤ y) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (MEnc d ++ List.replicate y 3 ++ 0 :: Z))
      (UfullNS W (p + 1) d y) Z := by
  obtain ⟨r, rfl⟩ : ∃ r, y = r + 1 := ⟨y - 1, by omega⟩
  have hdf : decide (d.length % 2 = 1) = true := by simp [hdl]
  have hY : ∃ c R', (c = 0 ∨ c = 1) ∧ (0 :: Z) = c :: R' ∧ Sym4 R' := ⟨0, Z, Or.inl rfl, rfl, hZ⟩
  have sZ0 : Sym4 (0 :: Z) := Sym4.cons (by simp [ALL]) hZ
  rcases Nat.lt_or_ge W.length r with hlt | hge
  · have hF := labelFindFY (p + 1) d [] Z hdd NoB.nil hZ r [] W 0 (by simp) hW hlt
    refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ hF)
    · simp [MEnc, List.append_assoc]
    simp [UfullNS, unm_append, unm_MEnc, unm_rep3, unm_Enc, List.append_assoc, unm1, Enc, U, List.replicate_succ']
  · have hrl : r ≤ W.length := by
      rcases Nat.lt_or_ge W.length r with h | h
      · omega
      · exact h
    have hL := labelFindY (p + 1) d (0 :: Z) hdd sZ0 hY r [] W 0 (by simp) hW hrl
    rw [hdf] at hL
    have hLd : (LDone true) = QG.gIL0 := rfl
    rw [hLd] at hL
    rcases Nat.lt_or_ge r W.length with hrw | hrw
    · obtain ⟨n, Wr, hr, _⟩ := W_split W hW r hrw
      have hWr : ∀ e ∈ Wr, 1 ≤ e := by
        intro e he
        have : e ∈ W.drop r := by rw [hr]; exact List.mem_cons_of_mem _ he
        exact hW e (List.mem_of_mem_drop this)
      have hms : ∀ e ∈ W.take r, 1 ≤ e := fun e he => hW e (List.mem_of_mem_take he)
      rw [hr] at hL
      obtain ⟨e, d', hdeq⟩ : ∃ e d', d = e :: d' := by
        cases d with
        | nil => simp at hdl
        | cons e d' => exact ⟨e, d', rfl⟩
      have hde : 1 ≤ e := hdd e (by simp [hdeq])
      have hd' : ∀ x ∈ d', 1 ≤ x := fun x hx => hdd x (by simp [hdeq, hx])
      let F := Fmark (r + 1) hy Z hZ
      have hnA : NoB (MEnc (W.take r) ++ Enc ((n + 1) :: Wr) ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]) ++ MEnc d ++
          List.replicate (0 + r + 1) 2) := by simp [NB]
      have hIL := il0Walk' _ (0 :: Z) hnA sZ0
      have hxs0 : ∀ x ∈ (List.replicate e 2 :: (d'.map fun e => List.replicate e 2)), Bits x ∧ x ≠ [] := by
        intro x hx
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨v, hv, rfl⟩
        · exact ⟨bits_rep2 e, by intro h; have := congrArg List.length h; simp at this; omega⟩
        · exact ⟨bits_rep2 v, by have := hd' v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
      have hwsb : ∀ x ∈ Wr.map (fun e => List.replicate e 3), Bits x ∧ x ≠ [] := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
        exact ⟨bits_rep3 v, by have := hWr v hv; intro h; have := congrArg List.length h; simp at this; omega⟩
      have hF : FailsTo
          (hdR QG.gIL1b [] (MEnc (W.take r) ++ List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ 1 ::
            (MEs (Wr.map fun e => List.replicate e 3) ++ 1 :: (List.replicate (p + 1) 3 ++ 1 ::
              (MEs (List.replicate e 2 :: (d'.map fun e => List.replicate e 2)) ++ (F.Hc 0 ++ 0 :: F.Zt))))))
          (UG (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2 :: (d'.map fun e => List.replicate e 2))
            n (p + 1) F.Hu) F.Zt := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exact colPartF4 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
            (d'.map fun e => List.replicate e 2)
            hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
            (p + 1) 0 0 (Nat.le_refl _) (List.replicate (r + 1) 2) (bits_rep2 _)
            (by intro h; have := congrArg List.length h; simp at this) rfl
        · exact colPartF1 F (W.take r) (Wr.map fun e => List.replicate e 3) (List.replicate e 2)
            (d'.map fun e => List.replicate e 2)
            hms hwsb (hxs0 _ (List.mem_cons_self ..)) (fun x hx => hxs0 x (List.mem_cons_of_mem _ hx))
            (p + 1) n 0 (Nat.le_refl _) (by show 0 < 0 + n; omega)
      refine FailsTo.pre (hL.of_eq (by simp [MEnc]) rfl) (FailsTo.pre (hIL.of_eq rfl ?_) (FailsTo.cast ?_ hF))
      · subst hdeq
        simp [F, Fmark, Enc, U, MEnc, Enc_MEs, MEnc_MEs, MEs_append, MEs, ME, List.append_assoc]
      have u3 : unm (MEs (Wr.map fun e => List.replicate e 3)) = Enc Wr := by
        rw [← Enc_MEs, unm_Enc]
      have e4 : unm (MEs (List.replicate e 2 :: (d'.map fun e => List.replicate e 2))) = Enc (e :: d') := by
        have := MEnc_MEs (e :: d')
        simp only [List.map_cons] at this
        rw [← this, unm_MEnc]
      have eW : Enc W = Enc (W.take r) ++ Enc ((n + 1) :: Wr) := by
        rw [← Enc_append, ← hr, List.take_append_drop]
      subst hdeq
      simp only [UG, UfullNS, u3, e4, eW, unm_Enc, unm_rep3]
      simp [F, Fmark, Enc, U, List.replicate_succ, rep3_cons, List.append_assoc]
    · have hr : r = W.length := by omega
      subst hr
      have hN := colNoTargetNS W d Z p (W.length + 1) hW hZ
      rw [List.drop_length, List.take_length] at hL
      exact FailsTo.pre (hL.of_eq (by simp [MEnc]) (by simp [MEnc, Enc])) hN


/-- `|X| = 2`, the second label unterminated: the check fails. -/
theorem twoFailNS (W Z : List Nat) (p x y : Nat) (hZ : Sym4 Z) (hW : ∀ e ∈ W, 1 ≤ e) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    FailsTo
      (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (Enc [x] ++ (List.replicate y 3 ++ 0 :: Z)))
      (UfullNS W (p + 1) [x] y) Z := by
  let F := HFam.ofEmpty (List.replicate y 3)
    (Or.inr (Or.inr (Or.inr ⟨List.replicate y 3, bits_rep3 y, by
      intro h; have := congrArg List.length h; simp at this; omega, rfl⟩)))
    (by simp [NB]) Z hZ
  have hd0 : ∀ e ∈ ([] : List Nat), 1 ≤ e := by simp
  by_cases hb : RowBad F W p x 0
  · have := firstFail F W [] [] p x 0 hW hd0 (by simp) (by simp) hx (Nat.le_refl _) hb
    refine FailsTo.ofCfg ?_ (FailsTo.cast ?_ this)
    · simp [Enc, U, MEnc, F, HFam.ofEmpty, List.append_assoc]
    · simp [Ufull, UfullNS, F, HFam.ofEmpty, unm_rep3, Enc, U, List.append_assoc]
  · obtain ⟨r, rfl⟩ : ∃ r, x = r + 1 := ⟨x - 1, by omega⟩
    have hrl : r < W.length := Classical.byContradiction fun h => hb (Or.inl (by omega))
    obtain ⟨n, Wr, hr, _⟩ := W_split W hW r hrl
    have hcn : 0 + (p + 1) * n ≤ F.N := Classical.byContradiction fun h => hb (Or.inr ⟨n, Wr, by simpa using hr, by omega⟩)
    have hn : n = 0 := by
      have hN0 : F.N = 0 := rfl
      have : (p + 1) * n ≤ 0 := by omega
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · have hpos := Nat.mul_pos (by omega : 0 < p + 1) h
        omega
    subst hn
    have hrow := rowHalf F W Wr [] [] r 0 p 0 hW hd0 (by simp) (by simp) hr (Nat.le_refl _) hcn
    have h2 := secondFailNS W [r + 1] Z p y hZ hW (by simp) (by simp) hy
    have hrow' : zgiLogic.Reach
        (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (Enc [r + 1] ++ (List.replicate y 3 ++ 0 :: Z)))
        (hdR QG.gY1e (Enc W ++ [1] ++ (List.replicate (p + 1) 3 ++ [1])) (MEnc [r + 1] ++ List.replicate y 3 ++ 0 :: Z)) :=
      hrow.of_eq (by simp [Enc, U, MEnc, F, HFam.ofEmpty, List.append_assoc])
        (by simp [Enc, U, MEnc, F, HFam.ofEmpty, List.append_assoc])
    exact FailsTo.pre hrow' h2

theorem checkSpecS3 (E : GEnv) (p : Nat) (d : List Nat) (y : Nat) (hd : d.length ≤ 1) (hdd : ∀ e ∈ d, 1 ≤ e) (hy : 1 ≤ y)
    (hTc : E.Tc = List.replicate (p + 1) 3 ++ 1 :: (Enc d ++ List.replicate y 3)) :
    E.CheckSpec (fun w => checkG w (p + 1) (d ++ [y]) []) (AccS E.Z) := by
  intro rest hv
  have hW : ∀ e ∈ rest, 1 ≤ e := fun e he => (hv.2 e he).1
  have hg : checkG rest (p + 1) (d ++ [y]) [] = false := by
    rw [checkG_nil]; simp
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · have h' : checkG rest (p + 1) (d ++ [y]) [] = true := h
    rw [hg] at h'; cases h'
  have hQ : ∀ a ∈ List.replicate y 3, a ∈ O13 := by
    intro a ha; rw [List.eq_of_mem_replicate ha]; simp [O13]
  have hpop := popG E rest hW p d (List.replicate y 3) hQ hTc
  have hfail : FailsTo (hdR QG.gY1e (Enc rest ++ [1] ++ (List.replicate (p + 1) 3 ++ [1]))
      (Enc d ++ (List.replicate y 3 ++ 0 :: E.Z))) (UfullNS rest (p + 1) d y) E.Z := by
    match d, hd, hdd with
    | [], _, _ =>
      have := firstFailNS rest [] E.Z p y E.hZ hW (by simp) (by simp) hy
      refine FailsTo.ofCfg ?_ this
      simp [Enc, MEnc]
    | [x], _, hdd => exact twoFailNS rest E.Z p x y E.hZ hW (hdd x (by simp)) hy
  obtain ⟨A, R1, hA, hR1, hu, hr⟩ := hfail
  have hf := failPath A R1 E.Z hA hR1 E.hZ
  refine (hpop.trans hr).trans (hf.of_eq rfl ?_)
  rw [hu]
  simp [UfullNS, GEnv.CfgD, GEnv.Rt, hTc, List.append_assoc]

end ZP.G
