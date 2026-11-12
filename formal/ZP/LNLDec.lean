module

public import ZP.LNLUnitSeg

@[expose] public section

/-!
# `Z_LNL` decider setup: the fuel blocks, the units, and the code copy

From the truth flag the machine builds the decider fuel (one block per position of the walker through `J`), then
the walker returns and appends one unit of the multihead storage per position (`stk x m`: `m` units of the
input `x`, every head at position `0`), then writes `H` and starts copying the code `J` into `Q`.
-/

namespace ZP.MH

open ZP

theorem hdR_unfold (q : Nat) (A R : List Nat) : hdR q A R = ⟨q, sapp A.reverse blank, sapp R blank⟩ := by
  unfold hdR atR SC.den
  show (⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem hdR_zero (q : Nat) (A R : List Nat) : hdR q A (R ++ [0]) = hdR q A R := by
  rw [hdR_unfold, hdR_unfold, sapp_append]
  show (⟨q, _, sapp R (scons 0 blank)⟩ : ZC) = _
  rw [scons_blank]

/-- The storage of `m` units of the input `x`, all heads at position `0` (head `0` is the rightmost unit). -/
def stk (x : List Bool) : Nat → List Nat
  | 0 => []
  | m + 1 => ucs (uOf x) (List.replicate m 0) ++ uc (uOf x) 0 0

theorem stk_one (x : List Bool) : stk x 1 = 1 :: 0 :: uOf x := by
  simp [stk, uc]

theorem stk_succ (x : List Bool) (m : Nat) :
    stk x (m + 2) = ucs (uOf x) (List.replicate m 0) ++ (1 :: 1 :: uOf x ++ (1 :: 0 :: uOf x)) := by
  simp [stk, uc, ucs_cons, List.replicate_succ, List.append_assoc]

/-! ## One unit -/

theorem ucpLoop (Jl Jr Y Z0 : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hY : NoB Y) (hZ0 : NoB Z0) :
    ∀ (v s1 ud : List Nat), Bits v → Bits s1 → Bits ud →
      zlnlLogic.Reach (hdR QMH.UCP (Jl ++ 1 :: (Jr ++ 1 :: s1)) (v ++ 1 :: (Y ++ 0 :: (Z0 ++ 1 :: 1 :: ud))))
        (hdR QMH.UCP (Jl ++ 1 :: (Jr ++ 1 :: (s1 ++ v))) (1 :: (Y ++ 0 :: (Z0 ++ 1 :: 1 :: (ud ++ v)))))
  | [], s1, ud, _, _, _ => by
    simp only [List.nil_append, List.append_nil]
    exact LTM.Reach.refl _ _
  | b :: v, s1, ud, hv, hs1, hud => by
    have h1 := ucpBody b hv.head Jl hJl Jr hJr s1 hs1 v hv.tail Y hY Z0 hZ0 ud hud
    have h2 := ucpLoop Jl Jr Y Z0 hJl hJr hY hZ0 v (s1 ++ [b]) (ud ++ [b]) hv.tail (hs1.snoc hv.head)
      (hud.snoc hv.head)
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

/-- Copy `s` into the new unit `M M`, close it and return to the left end. -/
theorem unitTail (Jl Jr : List Nat) (x : List Bool) (Y Z0 : List Nat) (hJl : Bits Jl) (hJr : Bits Jr)
    (hY : NoB Y) (hZ0 : NoB Z0) :
    zlnlLogic.Reach (hdR QMH.UCP (Jl ++ 1 :: (Jr ++ [1])) (bitsOf x ++ 1 :: (Y ++ 0 :: (Z0 ++ [1, 1]))))
      (hdR QMH.UDW [] (Jl ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: (Y ++ 0 :: (Z0 ++ 1 :: 0 :: uOf x)))))) := by
  have hs := Bits.ofB x
  have h1 := ucpLoop Jl Jr Y Z0 hJl hJr hY hZ0 (bitsOf x) [] [] hs Bits.nil Bits.nil
  have h2 := unitC Jl hJl Jr hJr (bitsOf x) hs Y hY Z0 hZ0 (bitsOf x) hs
  simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
  simp only [uOf, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  exact h1.trans h2

/-- Append one unit to the storage. -/
theorem unitAppL (Jl Jr : List Nat) (x : List Bool) (Y : List Nat) (m : Nat) (hJl : Bits Jl) (hJr : Bits Jr)
    (hY : NoB Y) :
    zlnlLogic.Reach (hdR QMH.U0 (Jl ++ 1 :: (Jr ++ [1])) (bitsOf x ++ 1 :: (Y ++ 0 :: stk x m)))
      (hdR QMH.UDW [] (Jl ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: (Y ++ 0 :: stk x (m + 1)))))) := by
  have hs := Bits.ofB x
  cases m with
  | zero =>
    have h1 := unitA0 Jl hJl Jr hJr (bitsOf x) hs Y hY
    have h2 := unitTail Jl Jr x Y [] hJl hJr hY NoB.nil
    simp only [stk, ucs_nil, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
      List.replicate_zero, uc, List.take_zero, List.drop_zero] at h1 h2 ⊢
    exact h1.trans h2
  | succ m =>
    obtain ⟨a, ur, e, ha, hur⟩ := uOf_cons x
    have hSu : NoB (ucs (uOf x) (List.replicate m 0)) := NoB.ucs (Bits.uOf x) _
    have h1 := unitA1 a ha Jl hJl Jr hJr (bitsOf x) hs Y hY (ucs (uOf x) (List.replicate m 0)) hSu ur hur
    have hZ0 : NoB (ucs (uOf x) (List.replicate m 0) ++ 1 :: 1 :: a :: ur) := by
      refine hSu.app (NoB.cons one_nb (NoB.cons one_nb (NoB.cons ?_ hur.noB)))
      rcases mem_bits ha with rfl | rfl <;> simp [NB]
    have h2 := unitTail Jl Jr x Y _ hJl hJr hY hZ0
    have e1 : stk x (m + 1) = ucs (uOf x) (List.replicate m 0) ++ (1 :: 0 :: a :: ur) := by
      simp [stk, uc, e]
    have e2 : stk x (m + 1 + 1) =
        ucs (uOf x) (List.replicate m 0) ++ 1 :: 1 :: a :: ur ++ 1 :: 0 :: uOf x := by
      rw [stk_succ, e]; simp
    rw [e1, e2]
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2


theorem sym4_stk (x : List Bool) (k : Nat) : Sym4 (stk x k) := by
  cases k with
  | zero => exact Sym4.nil
  | succ m => exact (NoB.ucs (Bits.uOf x) _).sym4.app (Sym4.uc (Bits.uOf x) 0 0 (by simp [ALL]))

/-! ## The walker returns, one unit per position -/

theorem bwd (x : List Bool) (Y : List Nat) (hY : NoB Y) :
    ∀ (n : Nat) (Jl Jr : List Nat) (m : Nat), Jl.length = n → Bits Jl → Bits Jr →
      zlnlLogic.Reach (hdR QMH.U0 (Jl ++ 1 :: (Jr ++ [1])) (bitsOf x ++ 1 :: (Y ++ 0 :: stk x m)))
        (hd Q.QC (1 :: 1 :: 1 :: (Jl ++ Jr)) (1 :: (bitsOf x ++ 1 :: (Y ++ 0 :: stk x (m + n + 1)))))
  | 0, Jl, Jr, m, hl, hJl, hJr => by
    have e : Jl = [] := List.length_eq_zero_iff.mp hl
    subst e
    have h1 := unitAppL [] Jr x Y m Bits.nil hJr hY
    have h2 := walkEnd Jr hJr (bitsOf x) (Bits.ofB x) Y hY (stk x (m + 1)) (sym4_stk x _)
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2
  | n + 1, Jl, Jr, m, hl, hJl, hJr => by
    obtain ⟨Jl', b, rfl⟩ : ∃ Jl' b, Jl = Jl' ++ [b] := by
      rcases List.eq_nil_or_concat Jl with h | ⟨L, b, h⟩
      · rw [h] at hl; simp at hl
      · exact ⟨L, b, by simpa using h⟩
    have hJl' : Bits Jl' := fun a ha => hJl a (List.mem_append_left _ ha)
    have hb : b ∈ bits := hJl b (by simp)
    have hl' : Jl'.length = n := by simpa using hl
    have h1 := unitAppL (Jl' ++ [b]) Jr x Y m hJl hJr hY
    have h2 := walkB b hb Jl' hJl' Jr hJr (bitsOf x) (Bits.ofB x) Y hY (stk x (m + 1)) (sym4_stk x _)
    have hL : Sym4 (Jl' ++ [1, b]) :=
      Sym4.app hJl'.sym4 (Sym4.cons (by simp [ALL]) (Sym4.cons (bits_all hb) Sym4.nil))
    have hY1 : NoB (Jr ++ [1]) := hJr.noB.app (NoB.cons one_nb NoB.nil)
    have hY2 : Sym4 (bitsOf x ++ 1 :: (Y ++ 0 :: stk x (m + 1))) :=
      (Bits.ofB x).sym4.app (Sym4.cons (by simp [ALL]) (hY.sym4.app (Sym4.cons (by simp [ALL]) (sym4_stk x _))))
    have h3 := u0skip (Jl' ++ [1, b]) hL (Jr ++ [1]) hY1 (bitsOf x ++ 1 :: (Y ++ 0 :: stk x (m + 1))) hY2
    have h4 := bwd x Y hY n Jl' (b :: Jr) (m + 1) hl' hJl' (Bits.cons hb hJr)
    have e : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
    rw [e] at h4
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))

/-! ## The fuel blocks, forward -/

theorem decFuelL (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zlnlLogic.Reach
        (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: FWn n i)))) [])
        (hdR QMH.U0 (Jl ++ Jr ++ [1, 1]) (s ++ 1 :: 1 :: (t ++ 1 :: FWn n (i + Jr.length + 1)))) := by
  intro Jr
  induction Jr with
  | nil =>
    intro Jl i hJl _
    have hBl := FWn_o13 n i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWn n i), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWn n (i + ([] : List Nat).length + 1) = FWn n i ++ 1 :: (List.replicate s.length 3 ++ [3]) := by
      rw [List.length_nil, Nat.add_zero, FWn_succ, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopyL Jl [] s _ hJl Bits.nil hs hT
    have hL := blkDecLastL Jl hJl s hs t ht (FWn n i) hBl
    rw [eF]
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at hA hL ⊢
    exact hA.trans hL
  | cons b Jr' ih =>
    intro Jl i hJl hJr
    have hBl := FWn_o13 n i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWn n i), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWn n (i + 1) = FWn n i ++ 1 :: (List.replicate s.length 3 ++ [3]) := by
      rw [FWn_succ, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopyL Jl (b :: Jr') s _ hJl hJr hs hT
    have hS := blkDecStepL Jl Jr' s t (FWn n i) b hJl hJr.tail hs ht hBl hJr.head
    have h2 := ih (Jl ++ [b]) (i + 1) (hJl.snoc hJr.head) hJr.tail
    have e : i + 1 + Jr'.length + 1 = i + (b :: Jr').length + 1 := by
      simp only [List.length_cons]; omega
    rw [e] at h2
    rw [eF] at h2
    simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] at hA hS h2 ⊢
    exact hA.trans (hS.trans h2)


/-! ## The code copy and the first rotation -/

theorem setupD (Pb Xb : List Bool) (R0 W F E : List Nat) (hR0 : NoB R0) (hE : Sym4 E)
    (hW : NoB W) (hF : NoB F) (hFb : ∃ a ∈ F, a ∈ bits)
    (hWF : bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: R0) = W ++ 1 :: F) :
    ∃ g, 1 ≤ g ∧ zlnlLogic.Reach
      (hd Q.QC (1 :: 1 :: 1 :: bitsOf Pb) (1 :: (bitsOf Xb ++ 1 :: (R0 ++ 0 :: E))))
      (Bd (rot (Pb.reverse ++ [false])) g none (1 :: (W ++ 1 :: F)) (0 :: E)) := by
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hX : Bits (bitsOf Xb) := Bits.ofB Xb
  have hV1 : NoB [1] := NoB.cons one_nb NoB.nil
  have hRest : Sym4 (R0 ++ 0 :: E) := hR0.sym4.app (Sym4.cons (by simp [ALL]) hE)
  have h3 := qcLoopL [] [1] (bitsOf Xb) (R0 ++ 0 :: E) Bits.nil hV1 hX hRest (bitsOf Pb).reverse [] hP.rev
    Bits.nil
  have h4 := qcEndL (bitsOf Pb) [] [] (bitsOf Xb) (R0 ++ 0 :: E) hP Bits.nil NoB.nil hX hRest
  simp only [List.reverse_reverse, List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc] at h3 h4
  have hG : Sym4 (0 :: (1 :: (1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: (R0 ++ 0 :: E)))))) :=
    Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL])
      (hP.sym4.app (Sym4.cons (by simp [ALL]) (hX.sym4.app (Sym4.cons (by simp [ALL]) hRest))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotNormal (Pb.reverse ++ [false]) (by simp) _ hG
  rw [rst_hd, rnav_hd] at hr
  have hcode : (bitsOf (Pb.reverse ++ [false])).reverse = 2 :: bitsOf Pb := by
    simp [bitsOf]
  have hB0 := (h3.trans h4).trans (lift (hr.ofEq (by rw [hcode]) rfl))
  have hVt : NoB (1 :: (W ++ 1 :: F)) := NoB.cons one_nb (hW.app (NoB.cons one_nb hF))
  obtain ⟨p, b, X', eV, hb, hX'⟩ := mb _ hVt (by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hab⟩)
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  have eV2 : List.replicate p 1 ++ b :: (X' ++ 0 :: E) = (1 :: (W ++ 1 :: F)) ++ 0 :: E := by
    rw [eV]; simp
  have eT : 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: (R0 ++ 0 :: E))) =
      List.replicate p 1 ++ b :: (X' ++ 0 :: E) := by
    rw [eV2]
    have : 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: (R0 ++ 0 :: E))) =
        1 :: ((bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: R0)) ++ 0 :: E) := by simp
    rw [this, hWF]
    simp
  have hXs : Sym4 (X' ++ 0 :: E) := hX'.app (Sym4.cons (by simp [ALL]) hE)
  have hB := segB R'.reverse [] (X' ++ 0 :: E) k 0 p 0 b (Or.inl rfl) hb hRr Bits.nil hXs
  refine ⟨k + 1, by omega, hB0.trans (lift (hB.ofEq ?_ ?_))⟩
  · rw [hk]
    simp only [List.cons_append, List.nil_append] at eT ⊢
    rw [eT]
    simp [List.replicate_succ, rep_cons_comm]
  · unfold Bd
    rw [hrr]
    simp only [cellN]
    rw [eV2]
    simp [List.replicate_succ, rep_cons_comm]

end ZP.MH
