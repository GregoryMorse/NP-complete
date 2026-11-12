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
theorem vPost (o : Bool) (j s Z : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hZne : o = true → Z ≠ [])
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
      | nil => exact absurd rfl (hZne rfl)
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
theorem verPhase (x : List Bool) (j : List Nat) (hj : Bits j) :
    zlpLogic.Reach (GCk j x (FWr [(x.length, x.length + 1)]) 0 (x.length + 1))
      (hdR Q.GRB (1 :: (j ++ 1 :: (bitsOf x ++ 1 :: 1 :: (tflag (inLP x) ++ [1])))) []) := by
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
    (fun h => by
      cases x with
      | nil => exact absurd h (by decide)
      | cons a t => simp) (FWr ds') (FWr_noB ds') x pos' cur'
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

/-! ## From `lay` to the verifier -/

theorem vStartLP (J S : Nat) :
    zlpLogic.Reach1 (lay J S)
      (GCk (bitsOf (str J)) (str S) (FWr [((str S).length, (str S).length + 1)]) 0 ((str S).length + 1)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1LP _ _ hj hs
  rw [← lay_den, P1_hdR] at h1
  have hT : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3, 1], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h
      rcases h with rfl | rfl <;> simp [O13]
  have h2 := extLP.reach (blkCopy [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT)
  have h3 := blkVerLP (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3) hj hs
    (rep_t3 _)
  have b : ∀ k, List.replicate k 3 ++ [3] = 3 :: List.replicate k 3 := fun k => rep_snoc_eq k 3
  have e1 : (1 :: (List.replicate (bitsOf (str S)).length 3 ++ [3, 1] ++ 1 :: List.replicate (bitsOf (str S)).length 3)) =
      [1, 3] ++ List.replicate (bitsOf (str S)).length 3 ++ [1, 1] ++ List.replicate (bitsOf (str S)).length 3 := by
    have := b (bitsOf (str S)).length
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    exact congrArg (1 :: ·) (rep_cons_comm 3 _ _)
  have e2 : [3] ++ List.replicate (bitsOf (str S)).length 3 ++ [1, 1] ++ List.replicate (bitsOf (str S)).length 3 ++ [3] =
      List.replicate ((str S).length + 1) 3 ++ 1 :: (1 :: List.replicate ((str S).length + 1) 3) := by
    have := b (bitsOf (str S)).length
    rw [bitsOf_len] at this ⊢
    simp only [List.replicate_succ, List.append_assoc, List.cons_append, List.singleton_append, this]
    simp
  have eF : FWr [((str S).length, (str S).length + 1)] = 1 :: List.replicate ((str S).length + 1) 3 := by
    simp [FWr, blkW_full]
  have hX : zlpLogic.Reach
      (hdR Q.GRB (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (List.replicate (bitsOf (str S)).length 3 ++ [3, 1])))) [])
      (GCk (bitsOf (str J)) (str S) (FWr [((str S).length, (str S).length + 1)]) 0 ((str S).length + 1)) := by
    have eG : GCk (bitsOf (str J)) (str S) (FWr [((str S).length, (str S).length + 1)]) 0 ((str S).length + 1) =
        hdR QLP.GC2 ([0, 1] ++ bitsOf (str J) ++ [1] ++ bitsOf (str S) ++ [1])
          (List.replicate ((str S).length + 1) 3 ++ 1 :: (1 :: List.replicate ((str S).length + 1) 3)) := by
      unfold GCk
      rw [eF, ustoreN_zero]
      have : List.replicate 0 2 ++ List.replicate ((str S).length + 1) 3 ++
          1 :: (1 :: List.replicate ((str S).length + 1) 3 ++ 0 :: []) =
          (List.replicate ((str S).length + 1) 3 ++ 1 :: (1 :: List.replicate ((str S).length + 1) 3)) ++ [0] := by
        simp
      rw [this, hdR_trail0]
    rw [eG]
    exact (h2.trans_eq (hdR_eq (by simp) e1) h3).ofEq (hdR_eq (by simp) rfl) (hdR_eq rfl e2)
  exact h1.trans hX



/-! ## The decider -/

theorem valrFull (n : Nat) : ∀ k, valr (List.replicate k (n, n + 1)) + 1 = (n + 2) ^ k
  | 0 => rfl
  | k + 1 => by
    have ih := valrFull n k
    show n + 1 + (n + 2) * valr (List.replicate k (n, n + 1)) + 1 = (n + 2) ^ (k + 1)
    rw [Nat.pow_succ, ← ih, Nat.mul_comm (valr (List.replicate k (n, n + 1)) + 1), Nat.mul_add, Nat.mul_one]
    omega

theorem hd_trailz (q : Nat) (A : List Nat) : ∀ (k : Nat) (R : List Nat), hd q A (R ++ List.replicate k 0) = hd q A R
  | 0, R => by simp
  | k + 1, R => by
    rw [List.replicate_succ', ← List.append_assoc, hd_trail0]
    exact hd_trailz q A k R

/-- Erase after agreement: back to the successor of `s`. -/
theorem eraseOk (Jx s Y : List Nat) (hJx : Bits Jx) (hs : Bits s) (hY : Eras Y) :
    zlpLogic.Reach (hd Q.EAs ([1] ++ Jx ++ [1] ++ s ++ [1, 1]) Y)
      (hd Q.SINC (1 :: (Jx ++ 1 :: s)) []) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have hA' : Sym4 ([1] ++ Jx ++ [1] ++ s) := by
    have : Sym4 (1 :: (Jx ++ 1 :: s)) :=
      Sym4.cons h1u (hJx.sym4.app (Sym4.cons h1u hs.sym4))
    simpa using this
  have hA0 : Sym4 ([1] ++ Jx ++ [1] ++ s ++ [1]) := hA'.app (Sym4.cons h1u Sym4.nil)
  have e : [1] ++ Jx ++ [1] ++ s ++ [1, 1] = ([1] ++ Jx ++ [1] ++ s ++ [1]) ++ [1] := by simp
  rw [e, hd_snoc]
  obtain ⟨m, h1⟩ := eraseLoop zlpLogic Q.EAs QMH.EX Q.EBs
    (fun c hc A R hA hR => eaN A R c hA hR hc) (fun A R hA hR => eaB A R hA hR)
    (fun c hc A R hA hR => exN A R c hA hR hc) (fun A hA => exE A hA) (fun A hA => eaE A hA)
    (1 :: Y).length (1 :: Y) rfl (Eras.nb one_nb hY) _ hA0
  have h2 := skipBack zlpLogic Q.EBs (fun A R hA hR => ebB A R hA hR) m ([1] ++ Jx ++ [1] ++ s ++ [1]) [0] hA0
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := ebM ([1] ++ Jx ++ [1] ++ s) (List.replicate m 0 ++ [0]) hA' hR0
  have e2 : [0] ++ (List.replicate m 0 ++ [0]) = List.replicate (m + 2) 0 := by
    rw [← List.replicate_succ']; rfl
  refine (h1.trans (h2.trans h3)).ofEq rfl ?_
  rw [e2, hd_zeros]
  exact hd_eq (by simp) rfl

/-- Erase after the beep: the successor of `J` follows. -/
theorem eraseBad (Jx s Y : List Nat) (hJx : Bits Jx) (hs : Bits s) (hY : Eras Y) :
    zlpLogic.Reach (hdR Q.EAs ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) Y)
      (hd Q.JINC (1 :: Jx) [1]) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h2u : (2 : Nat) ∈ ALL := by simp [ALL]
  have hA0 : Sym4 ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) := by
    have : Sym4 (1 :: (Jx ++ 1 :: (s ++ [1, 2]))) :=
      Sym4.cons h1u (hJx.sym4.app (Sym4.cons h1u (hs.sym4.app (Sym4.cons h1u (Sym4.cons h2u Sym4.nil)))))
    simpa using this
  obtain ⟨m, h1⟩ := eraseLoop zlpLogic Q.EAs QMH.EX Q.EBs
    (fun c hc A R hA hR => eaN A R c hA hR hc) (fun A R hA hR => eaB A R hA hR)
    (fun c hc A R hA hR => exN A R c hA hR hc) (fun A hA => exE A hA) (fun A hA => eaE A hA)
    Y.length Y rfl hY _ hA0
  have h2 := skipBack zlpLogic Q.EBs (fun A R hA hR => ebB A R hA hR) m ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) [0] hA0
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := ebEnd Jx s (List.replicate m 0 ++ [0]) hJx hs hR0
  refine (h1.trans (h2.trans h3)).ofEq rfl ?_
  have e : [1] ++ List.replicate s.length 0 ++ [0, 0] ++ (List.replicate m 0 ++ [0]) =
      [1] ++ List.replicate (s.length + 2 + (m + 1)) 0 := by
    have z : ∀ a b : Nat, List.replicate a (0 : Nat) ++ List.replicate b 0 = List.replicate (a + b) 0 :=
      fun a b => List.replicate_append_replicate
    have t1 : ([0, 0] : List Nat) = List.replicate 2 0 := rfl
    have t2 : (List.replicate m 0 ++ [0] : List Nat) = List.replicate (m + 1) 0 := (List.replicate_succ' ..).symm
    rw [t1, t2, List.append_assoc, List.append_assoc, z, z, Nat.add_assoc]
  refine (hd_eq rfl e).trans ?_
  exact hd_trailz _ _ _ _


/-- The decider: from the flag (`GRB` after it) to the dispatch with the output of `J` on `x`. -/
theorem dPhaseLP (Jb x : List Bool) (t : List Nat) (ht : ∀ a ∈ t, a ∈ T3) :
    ∃ Fu, Eras Fu ∧ Sym4 Fu ∧
      zlpLogic.Reach (hdR Q.GRB (1 :: (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ [1])))) [])
        (hdR (dpOf (bn (runMH Jb x (clock Jb x)))) [1]
          (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ 1 :: Fu)))) := by
  have hj := Bits.ofB Jb
  have hs := Bits.ofB x
  have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h1 := decFuelU x t ht (bitsOf Jb) [] 0 Bits.nil hj
  have e0 : FWr (List.replicate 0 (x.length, x.length + 1)) = [] := rfl
  have e : 0 + (bitsOf Jb).length + 1 = Jb.length + 1 := by rw [bitsOf_len]; omega
  have e1 : ([] : List Nat).length + (bitsOf Jb).length + 1 = Jb.length + 1 := by simp [bitsOf_len]
  rw [e0, e, e1] at h1
  have h1' := extLP.reach h1
  obtain ⟨Fd, hFd⟩ : ∃ Fd, Fd = FWr (List.replicate (Jb.length + 1) (x.length, x.length + 1)) := ⟨_, rfl⟩
  rw [← hFd] at h1'
  have hFdN : NoB Fd := by rw [hFd]; exact FWr_noB _
  have hFb : ∃ a ∈ Fd, a ∈ bits := by rw [hFd]; exact fw_bit _ (by simp)
  have hR' : Sym4 ((t ++ 1 :: Fd) ++ 0 :: ustoreN x (Jb.length + 1)) :=
    ((t3_noB ht).app (NoB.cons one_nb hFdN)).sym4.app (Sym4.cons h0u (sym4_ustoreN x _))
  have h2 := dispGC (bitsOf Jb) (bitsOf x) (1 :: ((t ++ 1 :: Fd) ++ 0 :: ustoreN x (Jb.length + 1))) hj hs
    (Sym4.cons h1u hR')
  have h3 := setD (bitsOf Jb) (bitsOf x) ((t ++ 1 :: Fd) ++ 0 :: ustoreN x (Jb.length + 1)) hj hs hR'
  have hR0 : NoB (1 :: (t ++ 1 :: Fd)) := NoB.cons one_nb ((t3_noB ht).app (NoB.cons one_nb hFdN))
  have hW : NoB (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) :=
    hj.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb (t3_noB ht)))))
  obtain ⟨g, hg, h4⟩ := setupMH zlpLogic extLP [] Jb (bitsOf x) (1 :: (t ++ 1 :: Fd))
    (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) Fd (ustoreN x (Jb.length + 1))
    NoB.nil hs hR0 (sym4_ustoreN x _) hW hFdN hFb (by simp)
  have hdig : Dig (List.replicate (Jb.length + 1) (x.length, x.length + 1)) := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact Nat.le_refl _
  have hval : valr (List.replicate (Jb.length + 1) (x.length, x.length + 1)) = clock Jb x := by
    have := valrFull x.length (Jb.length + 1)
    unfold clock
    omega
  obtain ⟨ds', pos', cur', -, -, -, -, -, h5⟩ := runMHI zlpLogic extLP ghLP x
    (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) hW Jb.length (clock Jb x)
    (rot (Jb.reverse ++ [false])) g (List.replicate (Jb.length + 1) 0) 0
    (List.replicate (Jb.length + 1) (x.length, x.length + 1)) (inv0 Jb) hg (by simp) (by simp)
    (by intro p hp; simp at hp; omega) hdig (by simp) hval
  have c1 := h1'.trans_eq (hd_eq rfl (by simp)) h2
  have c2 := c1.trans_eq (hdR_eq (by simp) (by simp)) h3
  have c3 := c2.trans_eq (hd_eq (by simp) (by simp)) h4
  have eB : Bd (rot (Jb.reverse ++ [false])) g none
      (1 :: ((bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) ++ 1 :: Fd)) (0 :: ustoreN x (Jb.length + 1)) =
      Bd (rot (Jb.reverse ++ [false])) g (mhRead x ((List.replicate (Jb.length + 1) 0).getD 0 0))
        (1 :: ((bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) ++ 1 :: FWr (List.replicate (Jb.length + 1) (x.length, x.length + 1))))
        (0 :: storeOf x (List.replicate (Jb.length + 1) 0) 0) := by
    rw [← ustoreN_eq, hFd]
    simp [mhRead]
  have hE := Eras_gap_store (FWr_noB ds') x pos' cur'
  refine ⟨FWr ds' ++ 0 :: storeOf x pos' cur', hE, hE.sym4, ?_⟩
  refine (c3.trans_eq eB h5).ofEq (hdR_eq (by simp) rfl) ?_
  unfold RE runMH
  exact hdR_eq rfl (by simp)

end ZP.MH
