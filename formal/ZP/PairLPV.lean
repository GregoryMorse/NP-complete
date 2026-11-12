module

public import ZP.PairLP
public import ZP.MHSetup
public import ZP.MHUnits

@[expose] public section

/-!
# Z_LP: the verifier half of the pair

The truth flag `inLP s`: the units, the setup, one multihead run of `s` on `s`, the erase of the storage.
-/

namespace ZP.MH

open ZP

/-- The storage (and the rest right of the flag) is erased and `M_3` written after the flag. -/
theorem eraseV (A1 : List Nat) (c : Nat) (hA : Sym4 A1) (hc : c ∈ O13) (Y : List Nat) (hY : Eras Y) :
    zlpLogic.Reach (hdR Q.VA3 (A1 ++ [c]) Y) (hdR Q.GRB (A1 ++ [c, 1]) []) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hc' : c ∈ ALL := by simp [O13] at hc; rcases hc with rfl | rfl <;> simp [ALL]
  have hAc : Sym4 (A1 ++ [c]) := hA.app (Sym4.cons hc' Sym4.nil)
  obtain ⟨m, h1⟩ := eraseLoop zlpLogic Q.VA3 QLP.EY Q.VA4
    (fun c hc A R hA hR => vaN A R c hA hR hc) (fun A R hA hR => vaB A R hA hR)
    (fun c hc A R hA hR => vxN A R c hA hR hc) (fun A hA => vxE A hA) (fun A hA => vaE A hA)
    Y.length Y rfl hY (A1 ++ [c]) hAc
  have h2 := skipBack zlpLogic Q.VA4 (fun A R hA hR => vbB A R hA hR) m (A1 ++ [c]) [0] hAc
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := vbF A1 (List.replicate m 0 ++ [0]) c hA hR0 hc
  have h4 := fbW (A1 ++ [c]) hAc
  have e : List.replicate m 0 ++ [0] = List.replicate (m + 1) 0 := by
    rw [List.replicate_succ', ]
  refine ((h1.trans h2).trans (h3.trans ?_))
  rw [e, hdR_zeros]
  exact h4.ofEq rfl (by simp)

/-- After the verifier's run: the truth flag, the storage erased. -/
theorem vPost (o : Bool) (j s Z : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hZne : Z ≠ [])
    (F' : List Nat) (hF' : NoB F') (x : List Bool) (pos : List Nat) (cur : Nat) :
    zlpLogic.Reach (hdR (dpOf (bn o)) [1] (j ++ 1 :: (s ++ 1 :: (2 :: Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)))))
      (hdR Q.GRB (1 :: (j ++ 1 :: (s ++ 1 :: 1 :: (tflag o ++ [1])))) []) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have hZb : NoB Z := z2_noB hZ
  have hA0 : Sym4 ([1] ++ j ++ [1] ++ s ++ [1]) := by
    have : Sym4 (1 :: (j ++ 1 :: (s ++ [1]))) :=
      Sym4.cons h1u (hj.sym4.app (Sym4.cons h1u (hs.sym4.app (Sym4.cons h1u Sym4.nil))))
    simpa using this
  have hY : NoB (Z ++ 1 :: F') := hZb.app (NoB.cons one_nb hF')
  have hE := Eras_gap_store hY x pos cur
  cases o with
  | true =>
    obtain ⟨Z', rfl⟩ : ∃ Z', Z = 2 :: Z' := by
      cases Z with
      | nil => exact absurd rfl hZne
      | cons a t => exact ⟨t, by have := hZ a (List.mem_cons_self ..); simp [Z2] at this; rw [this]⟩
    have hY' : NoB (Z' ++ 1 :: F') := fun a ha => hY a (List.mem_cons_of_mem _ ha)
    have hE' := Eras_gap_store hY' x pos cur
    have h1 := vTrue0 j s (Z' ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) hj hs
      (Eras.sym4 (by simpa using hE'))
    have h2 := eraseV ([1] ++ j ++ [1] ++ s ++ [1, 1]) 3
      (by simpa using hA0.app (Sym4.cons h1u Sym4.nil)) (by simp [O13])
      (Z' ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) (by simpa using hE')
    refine (h1.ofEq (hdR_eq (by simp [dpOf, bn]) (by simp)) rfl).trans (h2.ofEq (hdR_eq (by simp) rfl) ?_)
    simp [tflag]
  | false =>
    have h1 := vFalse j s (Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) hj hs
      (Eras.sym4 (by simpa using hE))
    have h2 := eraseV ([1] ++ j ++ [1] ++ s ++ [1]) 1 (by simpa using hA0) (by simp [O13])
      (Z ++ 1 :: (F' ++ 0 :: storeOf x pos cur)) (by simpa using hE)
    refine (h1.ofEq (hdR_eq (by simp [dpOf, bn]) (by simp)) rfl).trans (h2.ofEq (hdR_eq (by simp) rfl) ?_)
    simp [tflag]

/-! ## The verifier's units -/

/-- The dispatch state with `k` counter cells used and `m` left. -/
def GCk (j : List Nat) (x : List Bool) (F : List Nat) (k m : Nat) : ZC :=
  hdR QLP.GC2 ([0, 1] ++ j ++ [1] ++ bitsOf x ++ [1])
    (List.replicate k 2 ++ List.replicate m 3 ++ 1 :: (F ++ 0 :: ustoreN x k))

theorem vUnit (j : List Nat) (x : List Bool) (F : List Nat) (hj : Bits j) (hF : NoB F) (k m : Nat) :
    zlpLogic.Reach (GCk j x F k (m + 1)) (GCk j x F (k + 1) m) := by
  have hs : Bits (bitsOf x) := Bits.ofB x
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
  have hR : Sym4 (F ++ 0 :: ustoreN x k) := hF.sym4.app (Sym4.cons h0u (sym4_ustoreN x k))
  have h2u : (2 : Nat) ∈ ALL := by simp [ALL]
  have hMid : NoB (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: F) := by
    have := (z2_noB (rep_z2 (k + 1))).app ((t3_noB (rep_t3 m)).app (NoB.cons one_nb hF))
    simpa [List.append_assoc] using this
  have hL : Sym4 ([1] ++ j ++ [1] ++ bitsOf x ++ [1, 2] ++ List.replicate k 2) := by
    have : Sym4 (1 :: (j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate k 2))) :=
      Sym4.cons h1u (hj.sym4.app (Sym4.cons h1u (hs.sym4.app (Sym4.cons h1u (Sym4.cons h2u
        (Sym4.rep k 2 h2u))))))
    simpa using this
  have hRt : NoB (List.replicate m 3 ++ 1 :: F) := (t3_noB (rep_t3 _)).app (NoB.cons one_nb hF)
  -- the round: the first `1` of the counter becomes `0`, a unit is appended
  have hA : zlpLogic.Reach (GCk j x F k (m + 1))
      (hdR QMH.U0 ([0, 1] ++ j ++ [1] ++ bitsOf x ++ [1, 2] ++ List.replicate k 2)
        (List.replicate m 3 ++ 1 :: (F ++ 0 :: ustoreN x k))) := by
    cases k with
    | zero =>
      have := gcA j (bitsOf x) (List.replicate m 3) (F ++ 0 :: ustoreN x 0) hj hs (rep_t3 m) hR
      exact this.ofEq (hdR_eq rfl (by simp [GCk, List.replicate_succ])) (hdR_eq (by simp) (by simp))
    | succ k' =>
      have := gcB j (bitsOf x) (List.replicate k' 2) (List.replicate m 3) (F ++ 0 :: ustoreN x (k' + 1)) hj hs
        (rep_z2 k') (rep_t3 m) hR
      refine this.ofEq (hdR_eq rfl ?_) (hdR_eq ?_ ?_)
      · simp [GCk, List.replicate_succ, rep_cons_comm]
      · simp [List.replicate_succ', rep_snoc_eq]
      · simp
  have hU := unitApp x [] j (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: F)
    ([1] ++ j ++ [1] ++ bitsOf x ++ [1, 2] ++ List.replicate k 2) (List.replicate m 3 ++ 1 :: F)
    Bits.nil hj hMid hL hRt
    (by simp [List.replicate_succ]) k
  have hW := walkUnits x (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: F) hMid [] j (k + 1) Bits.nil hj
  have hR' : Sym4 (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: F ++ 0 :: ustoreN x (k + 1)) :=
    hMid.sym4.app (Sym4.cons h0u (sym4_ustoreN x (k + 1)))
  have hD := dispGC j (bitsOf x) (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: F ++ 0 :: ustoreN x (k + 1))
    hj hs hR'
  have hA1 : zlpLogic.Reach (GCk j x F k (m + 1))
      (hdR QMH.U0 ([1] ++ j ++ [1] ++ bitsOf x ++ [1, 2] ++ List.replicate k 2)
        (List.replicate m 3 ++ 1 :: (F ++ 0 :: ustoreN x k))) :=
    hA.ofEq rfl (hdR_lead0 _ ([1] ++ j ++ [1] ++ bitsOf x ++ [1, 2] ++ List.replicate k 2) _)
  have hU1 := (extLP.reach hU).trans_eq (hdR_eq (by first | rfl | simp) (by first | rfl | simp)) (extLP.reach hW)
  have hB := (hA1.ofEq rfl (hdR_eq rfl (by first | rfl | simp))).trans hU1
  refine hB.trans ((hD.ofEq (hd_eq (by first | rfl | simp) (by first | rfl | simp)) rfl).ofEq ?_ ?_)
  · first | rfl | simp
  · simp [GCk, List.replicate_succ]

theorem vLoop (j : List Nat) (x : List Bool) (F : List Nat) (hj : Bits j) (hF : NoB F) :
    ∀ m k, zlpLogic.Reach (GCk j x F k m) (GCk j x F (k + m) 0)
  | 0, k => LTM.Reach.refl _ _
  | m + 1, k => by
    have h1 := vUnit j x F hj hF k m
    have h2 := vLoop j x F hj hF m (k + 1)
    exact h1.trans (h2.ofEq rfl (by rw [Nat.add_right_comm]; rfl))

/-- The whole verifier: from the dispatch with `C = 1^(n+1)` to the truth flag. -/
theorem verPhase (x : List Bool) (hx : x ≠ []) (j : List Nat) (hj : Bits j) :
    zlpLogic.Reach (GCk j x (FWr [(x.length, x.length + 1)]) 0 (x.length + 1))
      (hdR Q.GRB (1 :: (j ++ 1 :: (bitsOf x ++ 1 :: 1 :: (tflag (inLP x) ++ [1])))) []) := by
  have hn : 1 ≤ x.length := by
    cases x with
    | nil => exact absurd rfl hx
    | cons a t => simp
  have hs : Bits (bitsOf x) := Bits.ofB x
  have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
  have eF : FWr [(x.length, x.length + 1)] = 1 :: List.replicate (x.length + 1) 3 := by
    simp [FWr, blkW_full]
  have hF : NoB (FWr [(x.length, x.length + 1)]) := FWr_noB _
  have hZb : Bits (2 :: List.replicate x.length 2) :=
    Bits.cons (by simp [bits]) (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [bits])
  have hR : Sym4 (FWr [(x.length, x.length + 1)] ++ 0 :: ustoreN x (x.length + 1)) :=
    hF.sym4.app (Sym4.cons h0u (sym4_ustoreN x _))
  have h1 := vLoop j x (FWr [(x.length, x.length + 1)]) hj hF (x.length + 1) 0
  have h2 := setV j (bitsOf x) (List.replicate x.length 2) (FWr [(x.length, x.length + 1)] ++ 0 :: ustoreN x (x.length + 1))
    hj hs (rep_z2 _) hR
  obtain ⟨g, hg, h3⟩ := setupMH zlpLogic extLP (1 :: j) x (2 :: List.replicate x.length 2)
    (FWr [(x.length, x.length + 1)]) (j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate x.length 2))
    (FWr [(x.length, x.length + 1)]) (ustoreN x (x.length + 1))
    (NoB.cons one_nb hj.noB) hZb hF (sym4_ustoreN x _)
    (hj.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons (by simp [NB])
      (z2_noB (rep_z2 _)))))))
    hF (fw_bit [(x.length, x.length + 1)] (by simp)) (by simp)
  have hW : NoB (j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate x.length 2)) :=
    hj.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons (by simp [NB])
      (z2_noB (rep_z2 _))))))
  have hdig : Dig [(x.length, x.length + 1)] := by
    intro p hp
    simp at hp
    subst hp
    exact Nat.le_refl _
  have hval : valr [(x.length, x.length + 1)] = x.length + 1 := by simp [valr]
  obtain ⟨ds', pos', cur', -, -, -, -, -, h4⟩ := runMHI zlpLogic extLP ghLP x
    (j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate x.length 2)) hW x.length (x.length + 1)
    (rot (x.reverse ++ [false])) g (List.replicate (x.length + 1) 0) 0 [(x.length, x.length + 1)]
    (inv0 x) hg (by simp) (by simp) (by intro p hp; simp at hp; omega) hdig (by simp) hval
  have h5 := vPost (runMHAux x.length x (x.length + 1) (rot (x.reverse ++ [false])) (List.replicate (x.length + 1) 0) 0)
    j (bitsOf x) (List.replicate x.length 2) hj hs (rep_z2 _)
    (by simp; omega) (FWr ds') (FWr_noB ds') x pos' cur'
  have c1 := h1.trans_eq (by simp [GCk, List.replicate_succ]) h2
  have c2 := c1.trans_eq (by simp) h3
  have eB : Bd (rot (x.reverse ++ [false])) g none
      (1 :: ((j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate x.length 2)) ++ 1 :: FWr [(x.length, x.length + 1)]))
      (0 :: ustoreN x (x.length + 1)) =
      Bd (rot (x.reverse ++ [false])) g (mhRead x ((List.replicate (x.length + 1) 0).getD 0 0))
        (1 :: ((j ++ 1 :: (bitsOf x ++ 1 :: 2 :: List.replicate x.length 2)) ++ 1 :: FWr [(x.length, x.length + 1)]))
        (0 :: storeOf x (List.replicate (x.length + 1) 0) 0) := by
    rw [← ustoreN_eq]
    simp [mhRead]
  have c3 := c2.trans_eq eB h4
  have c4 := c3.trans_eq (by simp [RE]) h5
  exact c4

end ZP.MH
