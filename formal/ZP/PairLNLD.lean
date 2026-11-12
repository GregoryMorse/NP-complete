module

public import ZP.LNLEraseSeg
public import ZP.LNLDec
public import ZP.MHLRun
public import ZP.MHErase

@[expose] public section

/-!
# Z_LNL: the decider half of the pair, and the successors
-/

namespace ZP.MH

open ZP




theorem sincLL (A : List Nat) (hA : NoB A) : ∀ (r : List Bool) (k : Nat),
    zlnlLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
      (hdR Q.GRB (A ++ 1 :: (bitsOf (incR r).reverse ++ List.replicate k 2)) [])
  | [], k => (sincEL A (List.replicate k 2) hA (rep_z2 k)).ofEq rfl (by rw [rep_snoc_eq]; rfl)
  | false :: r, k =>
    (sinc0L A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).ofEq
      (by simp [bitsOf]) (by simp [incR, bitsOf])
  | true :: r, k =>
    ((sinc1L A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).ofEq
      (by simp [bitsOf]) rfl).trans
      ((sincLL A hA r (k + 1)).ofEq rfl (by simp [incR, bitsOf, List.replicate_succ]))

theorem jincLL : ∀ (r : List Bool) (k : Nat),
    zlnlLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
      (hdR Q.GRB (1 :: (bitsOf (incR r).reverse ++ (List.replicate k 2 ++ [1]))) [])
  | [], k => (jincEL (List.replicate k 2) (rep_z2 k)).ofEq rfl (by rw [rep_cons_comm]; rfl)
  | false :: r, k =>
    (jinc0L (bitsOf r.reverse) (List.replicate k 2) (Bits.ofB _) (rep_z2 k)).ofEq
      (by simp [bitsOf]) (by simp [incR, bitsOf])
  | true :: r, k =>
    ((jinc1L (bitsOf r.reverse) (List.replicate k 2) (Bits.ofB _) (rep_z2 k)).ofEq
      (by simp [bitsOf]) rfl).trans
      ((jincLL r (k + 1)).ofEq rfl (by simp [incR, bitsOf, List.replicate_succ]))


/-- The one step out of the beep state. -/
theorem beepStepL (j s Y : List Nat) :
    zlnlLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1].reverse,
      [.blk 2 .id], true⟩ : SC).den [j, s, Y] = hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)


/-! ## Pair start -/


theorem hd_trailzL (q : Nat) (A : List Nat) : ∀ (k : Nat) (R : List Nat), hd q A (R ++ List.replicate k 0) = hd q A R
  | 0, R => by simp
  | k + 1, R => by
    rw [List.replicate_succ', ← List.append_assoc, hd_trail0]
    exact hd_trailzL q A k R

/-- Erase after agreement: back to the successor of `s`. -/
theorem eraseOkL (Jx s Y : List Nat) (hJx : Bits Jx) (hs : Bits s) (hY : Eras Y) :
    zlnlLogic.Reach (hd Q.EAs ([1] ++ Jx ++ [1] ++ s ++ [1, 1]) Y)
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
  obtain ⟨m, h1⟩ := eraseLoop zlnlLogic Q.EAs QMH.EX Q.EBs
    (fun c hc A R hA hR => eaNL A R c hA hR hc) (fun A R hA hR => eaBL A R hA hR)
    (fun c hc A R hA hR => exNL A R c hA hR hc) (fun A hA => exEL A hA) (fun A hA => eaEL A hA)
    (1 :: Y).length (1 :: Y) rfl (Eras.nb one_nb hY) _ hA0
  have h2 := skipBack zlnlLogic Q.EBs (fun A R hA hR => ebBL A R hA hR) m ([1] ++ Jx ++ [1] ++ s ++ [1]) [0] hA0
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := ebML ([1] ++ Jx ++ [1] ++ s) (List.replicate m 0 ++ [0]) hA' hR0
  have e2 : [0] ++ (List.replicate m 0 ++ [0]) = List.replicate (m + 2) 0 := by
    rw [← List.replicate_succ']; rfl
  refine (h1.trans (h2.trans h3)).ofEq rfl ?_
  rw [e2, hd_zeros]
  exact hd_eq (by simp) rfl

/-- Erase after the beep: the successor of `J` follows. -/
theorem eraseBadL (Jx s Y : List Nat) (hJx : Bits Jx) (hs : Bits s) (hY : Eras Y) :
    zlnlLogic.Reach (hdR Q.EAs ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) Y)
      (hd Q.JINC (1 :: Jx) [1]) := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h2u : (2 : Nat) ∈ ALL := by simp [ALL]
  have hA0 : Sym4 ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) := by
    have : Sym4 (1 :: (Jx ++ 1 :: (s ++ [1, 2]))) :=
      Sym4.cons h1u (hJx.sym4.app (Sym4.cons h1u (hs.sym4.app (Sym4.cons h1u (Sym4.cons h2u Sym4.nil)))))
    simpa using this
  obtain ⟨m, h1⟩ := eraseLoop zlnlLogic Q.EAs QMH.EX Q.EBs
    (fun c hc A R hA hR => eaNL A R c hA hR hc) (fun A R hA hR => eaBL A R hA hR)
    (fun c hc A R hA hR => exNL A R c hA hR hc) (fun A hA => exEL A hA) (fun A hA => eaEL A hA)
    Y.length Y rfl hY _ hA0
  have h2 := skipBack zlnlLogic Q.EBs (fun A R hA hR => ebBL A R hA hR) m ([1] ++ Jx ++ [1] ++ s ++ [1, 2]) [0] hA0
    (Sym4.cons h0 Sym4.nil)
  have hR0 : Sym4 (List.replicate m 0 ++ [0]) := (Sym4.rep m 0 h0).app (Sym4.cons h0 Sym4.nil)
  have h3 := ebEndL Jx s (List.replicate m 0 ++ [0]) hJx hs hR0
  refine (h1.trans (h2.trans h3)).ofEq rfl ?_
  have e : [1] ++ List.replicate s.length 0 ++ [0, 0] ++ (List.replicate m 0 ++ [0]) =
      [1] ++ List.replicate (s.length + 2 + (m + 1)) 0 := by
    have z : ∀ a b : Nat, List.replicate a (0 : Nat) ++ List.replicate b 0 = List.replicate (a + b) 0 :=
      fun a b => List.replicate_append_replicate
    have t1 : ([0, 0] : List Nat) = List.replicate 2 0 := rfl
    have t2 : (List.replicate m 0 ++ [0] : List Nat) = List.replicate (m + 1) 0 := (List.replicate_succ' ..).symm
    rw [t1, t2, List.append_assoc, List.append_assoc, z, z, Nat.add_assoc]
  refine (hd_eq rfl e).trans ?_
  exact hd_trailzL _ _ _ _



/-! ## The decider -/

theorem valrFullL (n : Nat) : ∀ k, valr (List.replicate k (n, n + 1)) + 1 = (n + 2) ^ k
  | 0 => rfl
  | k + 1 => by
    have ih := valrFullL n k
    show n + 1 + (n + 2) * valr (List.replicate k (n, n + 1)) + 1 = (n + 2) ^ (k + 1)
    rw [Nat.pow_succ, ← ih, Nat.mul_comm (valr (List.replicate k (n, n + 1)) + 1), Nat.mul_add, Nat.mul_one]
    omega

theorem stk_eq_store (x : List Bool) (j : Nat) :
    stk x (j + 1) = storeOf x (List.replicate (j + 1) 0) 0 := by
  simp [stk, storeOf, cfg, List.replicate_succ]

theorem sym4_storeOf' (x : List Bool) (pos : List Nat) (cur : Nat) : Sym4 (storeOf x pos cur) :=
  sym4_storeOf x pos cur

/-- The decider: from the flag (`GRB` after it) to the dispatch with the output of `J` on `x`. -/
theorem dPhaseL (Jb x : List Bool) (t : List Nat) (ht : ∀ a ∈ t, a ∈ T3) :
    ∃ Fu, Eras Fu ∧ Sym4 Fu ∧
      zlnlLogic.Reach (hdR Q.GRB (1 :: (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ [1])))) [])
        (hdR (dpOf (bn (runMH Jb x (clock Jb x)))) [1]
          (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ 1 :: Fu)))) := by
  have hj := Bits.ofB Jb
  have hs := Bits.ofB x
  have h0u : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 := decFuelL (bitsOf x) t x.length (bitsOf_len x) hs ht (bitsOf Jb) [] 0 Bits.nil hj
  have e0 : FWn x.length 0 = [] := rfl
  rw [e0] at h1
  obtain ⟨Fd, hFd⟩ : ∃ Fd, Fd = FWn x.length (0 + (bitsOf Jb).length + 1) := ⟨_, rfl⟩
  rw [← hFd] at h1
  have e : 0 + (bitsOf Jb).length + 1 = Jb.length + 1 := by rw [bitsOf_len]; omega
  rw [e] at hFd
  have hFdN : NoB Fd := by rw [hFd]; exact FWr_noB _
  have hFb : ∃ a ∈ Fd, a ∈ bits := by rw [hFd]; exact fw_bit _ (by simp)
  have hR0 : NoB (1 :: (t ++ 1 :: Fd)) := NoB.cons one_nb ((t3_noB ht).app (NoB.cons one_nb hFdN))
  have hW : NoB (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) :=
    hj.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb (t3_noB ht)))))
  have h2 := bwd x (1 :: (t ++ 1 :: Fd)) hR0 (bitsOf Jb).length (bitsOf Jb) [] 0 rfl hj Bits.nil
  have e2 : bitsOf x ++ 1 :: ((1 :: (t ++ 1 :: Fd)) ++ 0 :: stk x 0) =
      (bitsOf x ++ 1 :: 1 :: (t ++ 1 :: Fd)) ++ [0] := by simp [stk]
  rw [e2, hdR_zero] at h2
  have e3 : 0 + (bitsOf Jb).length + 1 = Jb.length + 1 := e
  rw [e3] at h2
  obtain ⟨g, hg, h4⟩ := setupD Jb x (1 :: (t ++ 1 :: Fd))
    (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) Fd (stk x (Jb.length + 1)) hR0 (sym4_stk x _) hW hFdN hFb
    (by simp)
  have hdig : Dig (List.replicate (Jb.length + 1) (x.length, x.length + 1)) := by
    intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact Nat.le_refl _
  have hval : valr (List.replicate (Jb.length + 1) (x.length, x.length + 1)) = clock Jb x := by
    have := valrFullL x.length (Jb.length + 1)
    unfold clock
    omega
  obtain ⟨ds', pos', cur', -, -, -, -, -, h5⟩ := runMHIL zlnlLogic mhBase_ext_zlnlLogic ghStepL_zlnl x
    (bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) hW Jb.length (clock Jb x)
    (rot (Jb.reverse ++ [false])) g (List.replicate (Jb.length + 1) 0) 0
    (List.replicate (Jb.length + 1) (x.length, x.length + 1)) (inv0L Jb) hg (by simp) (by simp)
    (by intro p hp; simp at hp; omega) hdig (by simp) hval
  have c1 := h1.trans_eq (hdR_eq (by simp) (by simp)) h2
  have c2 := c1.trans_eq (hd_eq (by simp) (by simp)) h4
  have eB : Bd (rot (Jb.reverse ++ [false])) g none
      (1 :: ((bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) ++ 1 :: Fd)) (0 :: stk x (Jb.length + 1)) =
      Bd (rot (Jb.reverse ++ [false])) g (mhRead x ((List.replicate (Jb.length + 1) 0).getD 0 0))
        (1 :: ((bitsOf Jb ++ 1 :: (bitsOf x ++ 1 :: 1 :: t)) ++ 1 :: FWr (List.replicate (Jb.length + 1) (x.length, x.length + 1))))
        (0 :: storeOf x (List.replicate (Jb.length + 1) 0) 0) := by
    rw [stk_eq_store, hFd]
    simp [mhRead, FWn]
  have hE := Eras_gap_store (FWr_noB ds') x pos' cur'
  refine ⟨FWr ds' ++ 0 :: storeOf x pos' cur', hE, hE.sym4, ?_⟩
  refine (c2.trans_eq eB h5).ofEq (hdR_eq (by simp) rfl) ?_
  unfold RE runMH
  exact hdR_eq rfl (by simp)

end ZP.MH
