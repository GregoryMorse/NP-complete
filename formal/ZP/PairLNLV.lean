module

public import ZP.PairLNLSeg

@[expose] public section

/-!
# `Z_LNL` pair: the verifier half

The loops of the outer machine (`BLK`, the guest and code copies), the run setup with the dummy cell, one whole
verifier run (`runFromL`), and the certificate loop `vLoopL` / `vFullL` with `run1` and `inLNL`.
-/

namespace ZP.MH

open ZP

/-! ## Small facts -/


theorem bitsOf_nil : bitsOf [] = [] := rfl

theorem bitsOf_reverse (l : List Bool) : bitsOf l.reverse = (bitsOf l).reverse := by
  simp [bitsOf]

/-- `blkW` blocks of full width: `i` of them. -/
def FWn (n i : Nat) : List Nat := FWr (List.replicate i (n, n + 1))

theorem FWn_succ (n i : Nat) : FWn n (i + 1) = FWn n i ++ (1 :: List.replicate (n + 1) 3) := by
  show FWr (List.replicate i (n, n + 1)) ++ blkW n (n + 1) = _
  rw [blkW_full]
  rfl

theorem FWn_o13 (n : Nat) : ∀ i, ∀ a ∈ FWn n i, a ∈ O13
  | 0 => fun _ h => by cases h
  | i + 1 => by
    intro a ha
    rw [FWn_succ] at ha
    rcases List.mem_append.mp ha with h | h
    · exact FWn_o13 n i a h
    · rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · rw [List.eq_of_mem_replicate h]; simp [O13]

/-! ## Loops of the outer machine -/


theorem copyLoopL (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zlnlLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
        (hdR Q.COPY (P ++ (u ++ v)) (1 :: (T ++ 1 :: List.replicate (u ++ v).length 3)))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := copyBodyL P u v T b hP hu hv.tail hT hv.head
    have h2 := copyLoopL P T hP hT v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.ofEq (by simp [List.replicate_succ']) (by simp only [List.append_assoc, List.singleton_append]))

/-- `BLK` up to the end of the `COPY` loop. -/
theorem blkCopyL (Jl Jr s T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s)
    (hT : ∀ a ∈ T, a ∈ O13) :
    zlnlLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStartL Jl Jr s T hJl hJr hs hT).trans
    ((copyLoopL _ T hP hT s [] Bits.nil hs).ofEq (by simp) (by simp))

theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zlnlLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
        (hdR Q.GC ((u ++ v).reverse ++ 1 :: (V ++ (P ++ 1 :: (u ++ v)))) (1 :: Rest))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := gcBody u.reverse V P u v Rest b hu.rev hV hP hu hv.tail hR hv.head
    have h2 := gcLoop V P Rest hV hP hR v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.ofEq (by simp) (by simp only [List.append_assoc, List.singleton_append]))

theorem qcLoopL (Xr V X Rest : List Nat) (hXr : Bits Xr) (hV : NoB V) (hX : Bits X) (hR : Sym4 Rest) :
    ∀ vr Qc, Bits vr → Bits Qc →
      zlnlLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBodyL Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoopL Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl (by simp))


/-! ## Pair start: `lay` to the first `GC` -/

theorem phase1L (j s : List Nat) (hj : ∀ a ∈ j, a ∈ bits) (hs : ∀ a ∈ s, a ∈ bits) :
    zlnlLogic.Reach1 (L0.den [j, s]) (P1.den [j, s]) := by
  have hA : zlnlLogic.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zlnlLogic.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zlnlLogic.Reach (F1.den [j, s, []]) (P1.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 19)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact (hA.trans hL).trans hB

/-! ## Run setup: copy the source left, the code into `Q`, rotate once -/

theorem setupL (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W F : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W) (hF : NoB F)
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: F) :
    ∃ g, 1 ≤ g ∧ zlnlLogic.Reach (hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
      (Bv (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ W F) := by
  have hVq' : NoB (2 :: Vq) := NoB.cons (by simp [NB]) hVq
  have hVn : NoB ((2 :: Vq) ++ [1]) := hVq'.app (NoB.cons one_nb NoB.nil)
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hX : Bits (bitsOf Xb) := Bits.ofB Xb
  have hXr : Bits (bitsOf Xb).reverse := bitsOf_rev Xb
  have h1 := gcLoop ((2 :: Vq) ++ [1]) (bitsOf Pb) Rest hVn hP hR (bitsOf Xb) [] Bits.nil hX
  have h2 := gcEnd (bitsOf Xb).reverse ((2 :: Vq) ++ [1]) (bitsOf Pb) (bitsOf Xb) Rest hXr hVn hP hX hR
  have h3 := qcLoopL (bitsOf Xb).reverse ((2 :: Vq) ++ [1]) (bitsOf Xb) Rest hXr hVn hX hR
    (bitsOf Pb).reverse [] hP.rev Bits.nil
  have h4 := qcEndL (bitsOf Pb) (bitsOf Xb).reverse (2 :: Vq) (bitsOf Xb) Rest hP hXr hVq' hX hR
  have e0 : hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest) =
      hdR Q.GC (([] : List Nat).reverse ++ 1 :: (((2 :: Vq) ++ [1]) ++ (bitsOf Pb ++ 1 :: [])))
        (bitsOf Xb ++ 1 :: Rest) := by
    rw [hV]; simp
  have hA := (h1.ofEq e0.symm (by simp)).trans (h2.trans ((h3.ofEq (by simp) (by simp)).trans h4))
  have hG : Sym4 (0 :: ((bitsOf Xb).reverse ++ 1 :: ((2 :: Vq) ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest))))) :=
    Sym4.cons (by simp [ALL]) (hXr.sym4.app (Sym4.cons (by simp [ALL]) (hVq'.sym4.app (Sym4.cons (by simp [ALL])
      (hP.sym4.app (Sym4.cons (by simp [ALL]) (hX.sym4.app (Sym4.cons (by simp [ALL]) hR))))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotNormal (Pb.reverse ++ [false]) (by simp) _ hG
  rw [rst_hd, rnav_hd] at hr
  have hcode : (bitsOf (Pb.reverse ++ [false])).reverse = 2 :: bitsOf Pb := by
    simp [bitsOf]
  have hB0 := hA.trans (lift (hr.ofEq (by rw [hcode]) rfl))
  have eT : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = 1 :: (W ++ 1 :: F) := by
    have e : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) =
        (Vq ++ [1]) ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) := by simp
    rw [e, ← hV, List.cons_append, hWF]
  have hX1 : Sym4 (1 :: (W ++ 1 :: F)) := (NoB.cons one_nb (hW.app (NoB.cons one_nb hF))).sym4
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  cases Xb with
  | nil =>
    have hB := segB R'.reverse [] (1 :: (W ++ 1 :: F)) k 0 0 0 2 (Or.inl rfl) (by simp [bits]) hRr Bits.nil hX1
    refine ⟨k + 1, by omega, hB0.trans (lift (hB.ofEq ?_ ?_))⟩
    · rw [hk]
      simp only [List.cons_append]
      rw [eT]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bv Zp.Lw Zp.Rw
      rw [hrr]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) (1 :: (W ++ 1 :: F)) (k + 1) 0 0 (bn x) 2 (bn_cases x)
      (by simp [bits]) hRr (Bits.ofB _) hX1
    refine ⟨k + 1 + 1, by omega, hB0.trans (lift (hB.ofEq ?_ ?_))⟩
    · rw [hk]
      simp only [List.cons_append]
      rw [eT]
      simp [List.replicate_succ, rep_cons_comm, bitsOf_reverse, bitsOf_cons]
    · unfold Bv Zp.Lw Zp.Rw
      rw [hrr]
      simp [cellN_some, bitsOf, List.replicate_succ, rep_cons_comm]

theorem inv0L (Pb : List Bool) : InvR (rot (Pb.reverse ++ [false])) := by
  apply inv_rot
  refine ⟨by simp, fun hl => ?_, fun hl => ?_⟩
  · rcases Pb with _ | ⟨a, Pb⟩
    · rfl
    · simp at hl
  · rcases Pb with _ | ⟨a, _ | ⟨b, Pb⟩⟩
    · simp at hl
    · simp
    · simp at hl

/-- One guest run from the setup position, to the dispatch state. -/
theorem runFromL (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W : List Nat) (ds : List Dg)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W)
    (hds : Dig ds) (hne : ds ≠ [])
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: FWr ds) :
    ∃ ds', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧
      zlnlLogic.Reach (hdR Q.GC (1 :: 2 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
        (RV (run1 Pb Xb (valr ds)) W (FWr ds')) := by
  obtain ⟨g, hg, h1⟩ := setupL W1 Vq Pb Xb Rest W (FWr ds) hV hVq hR hW (FWr_noB ds) hWF
  have hz : (⟨[], Xb.head?, Xb.tail⟩ : Zp).WF := by
    unfold Zp.WF
    cases Xb with
    | nil => intro _; rfl
    | cons x xt => intro h; simp at h
  obtain ⟨ds', hd', hl', h2⟩ := run1I W hW (valr ds) _ g _ ds (inv0L Pb) hg hz hds hne rfl
  have ht : (⟨[], Xb.head?, Xb.tail⟩ : Zp).tape = fun i => Xb[i]? := by
    cases Xb <;> rfl
  rw [ht] at h2
  exact ⟨ds', hd', hl', h1.trans (h2.ofEq rfl rfl)⟩


/-! ## Binary counters (least significant bit first) -/

def bitN : Bool → Nat
  | true => 1
  | false => 0

theorem bitN_le (b : Bool) : bitN b ≤ 1 := by cases b <;> decide

/-- Value of the certificate counter. -/
def bv : List Bool → Nat
  | [] => 0
  | b :: l => bitN b + 2 * bv l

theorem bv_falses : ∀ k, bv (List.replicate k false) = 0
  | 0 => rfl
  | k + 1 => by
    have := bv_falses k
    show 0 + 2 * bv (List.replicate k false) = 0
    omega

theorem bv_dec : ∀ k r, bv (List.replicate k true ++ false :: r) + 1 = bv (List.replicate k false ++ true :: r)
  | 0, r => by
    show 0 + 2 * bv r + 1 = 1 + 2 * bv r
    omega
  | k + 1, r => by
    have := bv_dec k r
    show 1 + 2 * bv (List.replicate k true ++ false :: r) + 1 = 0 + 2 * bv (List.replicate k false ++ true :: r)
    omega

theorem bv_le : ∀ c : List Bool, bv c ≤ bv (List.replicate c.length true)
  | [] => Nat.le_refl _
  | b :: c => by
    have := bv_le c
    have := bitN_le b
    show bitN b + 2 * bv c ≤ 1 + 2 * bv (List.replicate c.length true)
    omega

theorem bv_inj : ∀ a b : List Bool, a.length = b.length → bv a = bv b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | x :: a, y :: b, hl, h => by
    have h' : bitN x + 2 * bv a = bitN y + 2 * bv b := h
    have hx := bitN_le x
    have hy := bitN_le y
    have e1 : bitN x = bitN y := by omega
    have e2 : bv a = bv b := by omega
    have ex : x = y := by
      revert e1
      cases x <;> cases y <;> decide
    rw [ex, bv_inj a b (by simpa using hl) e2]

theorem cases_dec : ∀ l : List Bool,
    (∃ k, l = List.replicate k false) ∨ ∃ k r, l = List.replicate k false ++ true :: r
  | [] => Or.inl ⟨0, rfl⟩
  | true :: l => Or.inr ⟨0, l, rfl⟩
  | false :: l =>
    match cases_dec l with
    | Or.inl ⟨k, e⟩ => Or.inl ⟨k + 1, by rw [e]; rfl⟩
    | Or.inr ⟨k, r, e⟩ => Or.inr ⟨k + 1, r, by rw [e]; rfl⟩

theorem bv_zero (l : List Bool) (h : bv l = 0) : ∃ k, l = List.replicate k false := by
  rcases cases_dec l with hk | ⟨k, r, e⟩
  · exact hk
  · have := bv_dec k r
    rw [← e] at this
    omega

/-! ## Shortlex successor -/

/-- Successor of a bit string given least significant bit first. -/
def incR : List Bool → List Bool
  | [] => [false]
  | false :: r => true :: r
  | true :: r => false :: incR r

/-- `1 r.reverse` read in binary. -/
def numR : List Bool → Nat
  | [] => 1
  | b :: r => bitN b + 2 * numR r

theorem numR_inc : ∀ r, numR (incR r) = numR r + 1
  | [] => rfl
  | false :: r => by
    show 1 + 2 * numR r = 0 + 2 * numR r + 1
    omega
  | true :: r => by
    have := numR_inc r
    show 0 + 2 * numR (incR r) = 1 + 2 * numR r + 1
    omega

theorem numR_gt : ∀ r, r.length < numR r
  | [] => by decide
  | b :: r => by
    have := numR_gt r
    show r.length + 1 < bitN b + 2 * numR r
    omega

theorem strAux_numR : ∀ (r : List Bool) (f : Nat) (acc : List Bool), r.length ≤ f →
    strAux f (numR r) acc = r.reverse ++ acc
  | [], 0, _, _ => rfl
  | [], f + 1, acc, _ => by simp [strAux, numR]
  | b :: r, 0, _, h => absurd h (by simp)
  | b :: r, f + 1, acc, h => by
    have hg := numR_gt r
    have hb := bitN_le b
    have hN : ¬ numR (b :: r) ≤ 1 := by
      show ¬ (bitN b + 2 * numR r ≤ 1)
      omega
    have h2 : numR (b :: r) / 2 = numR r := by
      show (bitN b + 2 * numR r) / 2 = numR r
      omega
    have h3 : (numR (b :: r) % 2 == 1) = b := by
      cases b
      · have e : (bitN false + 2 * numR r) % 2 = 0 := by
          show (0 + 2 * numR r) % 2 = 0
          omega
        show ((bitN false + 2 * numR r) % 2 == 1) = false
        rw [e]
        rfl
      · have e : (bitN true + 2 * numR r) % 2 = 1 := by
          show (1 + 2 * numR r) % 2 = 1
          omega
        show ((bitN true + 2 * numR r) % 2 == 1) = true
        rw [e]
        rfl
    show (if numR (b :: r) ≤ 1 then acc
      else strAux f (numR (b :: r) / 2) ((numR (b :: r) % 2 == 1) :: acc)) = _
    rw [ite_eq_right hN, h2, h3, strAux_numR r f (b :: acc) (by simp at h; omega)]
    simp

theorem str_numR (r : List Bool) : str (numR r) = r.reverse := by
  have := numR_gt r
  show strAux (numR r) (numR r) [] = _
  rw [strAux_numR r _ [] (by omega), List.append_nil]

theorem numR_surj_aux : ∀ f N, 1 ≤ N → N ≤ f → ∃ r, numR r = N
  | 0, N, h, hf => absurd hf (by omega)
  | f + 1, N, h, hf => by
    by_cases h1 : N = 1
    · exact ⟨[], by rw [h1]; rfl⟩
    · obtain ⟨r, hr⟩ := numR_surj_aux f (N / 2) (by omega) (by omega)
      refine ⟨(N % 2 == 1) :: r, ?_⟩
      show bitN (N % 2 == 1) + 2 * numR r = N
      rw [hr]
      rcases Nat.mod_two_eq_zero_or_one N with h2 | h2
      · rw [h2]
        show 0 + 2 * (N / 2) = N
        omega
      · rw [h2]
        show 1 + 2 * (N / 2) = N
        omega

theorem numR_surj (N : Nat) (h : 1 ≤ N) : ∃ r, numR r = N := numR_surj_aux N N h (Nat.le_refl _)

theorem str_one : str 1 = [] := rfl

/-! ## Bit strings -/

theorem mem_strings : ∀ (n : Nat) (c : List Bool), c ∈ strings n ↔ c.length = n
  | 0, c => by cases c <;> simp [strings]
  | n + 1, c => by
    simp only [strings, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨d, hd, rfl | rfl⟩ <;> simp [(mem_strings n d).mp hd]
    · intro h
      cases c with
      | nil => simp at h
      | cons b d =>
        refine ⟨d, (mem_strings n d).mpr (by simpa using h), ?_⟩
        cases b <;> simp

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide



/-! ## The verifier -/

def tflag : Bool → List Nat
  | true => [3]
  | false => []

/-- Verifier run setup, certificate counter `cl` (least significant first). -/
def GCv (j : List Nat) (Sb cl : List Bool) : ZC :=
  hdR Q.GC (1 :: 2 :: (1 :: (j ++ [1]) ++ (bitsOf Sb ++ [1])))
    (bitsOf cl.reverse ++ 1 :: blkW Sb.length (Sb.length + 1))

/-- Truth flag written, `GRB` after it. -/
def TR (j : List Nat) (Sb : List Bool) (b : Bool) : ZC :=
  hdR Q.GRB (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: 1 :: (tflag b ++ [1])))) []

theorem split2 (u : List Bool) (F : List Nat) (hu : u ≠ []) (hF : NoB F) :
    ∃ c y Y, bitsOf u ++ 1 :: F = c :: y :: Y ∧ c ∈ bits ∧ y ∈ NB ∧ NoB Y := by
  match u, hu with
  | [x], _ => exact ⟨bn x, 1, F, rfl, bn_bits x, one_nb, hF⟩
  | x :: x' :: u', _ =>
    exact ⟨bn x, bn x', bitsOf u' ++ 1 :: F, rfl, bn_bits x, by cases x' <;> simp [bn, NB],
      (Bits.ofB u').noB.app (NoB.cons one_nb hF)⟩

/-- One verifier pass: accept, underflow, or decrement and refill. -/
theorem vStepL (j : List Nat) (hj : Bits j) (Sb cl : List Bool) (hcl : cl.length = Sb.length + 1) :
    (run1 Sb cl.reverse (Sb.length + 1) = true →
      zlnlLogic.Reach (GCv j Sb cl) (TR j Sb true)) ∧
    (run1 Sb cl.reverse (Sb.length + 1) = false → cl = List.replicate (Sb.length + 1) false →
      zlnlLogic.Reach (GCv j Sb cl) (TR j Sb false)) ∧
    (run1 Sb cl.reverse (Sb.length + 1) = false → ∀ k r, cl = List.replicate k false ++ true :: r →
      zlnlLogic.Reach (GCv j Sb cl) (GCv j Sb (List.replicate k true ++ false :: r))) := by
  have hW : NoB (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) :=
    hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)))
  obtain ⟨ds', hd', hl', h⟩ := runFromL (j ++ [1]) (1 :: j) Sb cl.reverse
    (blkW Sb.length (Sb.length + 1)) (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse))
    [(Sb.length, Sb.length + 1)]
    rfl (NoB.cons one_nb hj.noB) (blkW_noB _ _).sym4 hW
    (fun d hd => by simp at hd; subst hd; exact Nat.le_refl _) (by simp) (by simp [FWr])
  have hv : valr [(Sb.length, Sb.length + 1)] = Sb.length + 1 := by simp [valr]
  rw [hv] at h
  obtain ⟨d, rfl⟩ : ∃ d, ds' = [(Sb.length, d)] := by
    rcases ds' with _ | ⟨⟨n, d⟩, _ | ⟨e, t⟩⟩
    · simp at hl'
    · simp at hl'
      exact ⟨d, by rw [hl']⟩
    · simp at hl'
  have hdd : d ≤ Sb.length + 1 := hd' (Sb.length, d) (by simp)
  have hF : FWr [(Sb.length, d)] = 1 :: (List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 2) := by
    simp [FWr, blkW]
  have hRE : ∀ o, RV o (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) (FWr [(Sb.length, d)]) =
      hdR (dpOf (bn o)) [1] (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: FWr [(Sb.length, d)]))) := by
    intro o; unfold RV; simp
  have hne : cl.reverse ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [hcl] at this
  refine ⟨fun ho => ?_, fun ho hc => ?_, fun ho k r hc => ?_⟩
  · rw [ho, hRE] at h
    obtain ⟨c, y, Y, eS, hc, hy, hY⟩ := split2 cl.reverse (FWr [(Sb.length, d)]) hne (FWr_noB _)
    have hA := vAcc j (bitsOf Sb) Y c y hj (Bits.ofB _) hY hc hy
    exact (h.ofEq rfl rfl).trans (hA.ofEq (by rw [← eS]; simp [dpOf, bn]) (by simp [TR, tflag]))
  · rw [ho, hRE] at h
    have hcr : bitsOf cl.reverse = 2 :: List.replicate Sb.length 2 := by
      rw [hc]; simp [bitsOf, List.replicate_succ, rep_snoc_eq]
    have hU := vUnder j (bitsOf Sb) (List.replicate Sb.length 2) (FWr [(Sb.length, d)]) hj (Bits.ofB _)
      (rep_z2 _) (FWr_noB _)
    exact (h.ofEq rfl rfl).trans (hU.ofEq (by rw [hcr]; simp [dpOf, bn]) (by simp [TR, tflag]))
  · rw [ho, hRE] at h
    have hcr : cl.reverse = r.reverse ++ true :: List.replicate k false := by rw [hc]; simp
    have hcr' : (List.replicate k true ++ false :: r).reverse = r.reverse ++ false :: List.replicate k true := by
      simp
    have hDE : List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 3 = List.replicate (Sb.length + 1) 3 := by
      rw [List.replicate_append_replicate]
      congr 1
      omega
    cases hr : r.reverse with
    | nil =>
      have hE := vRejE j (bitsOf Sb) (List.replicate k 2) (List.replicate d 3)
        (List.replicate (Sb.length + 1 - d) 2) hj (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _)
      refine (h.ofEq rfl rfl).trans (hE.ofEq ?_ ?_)
      · rw [hF, hcr, hr]
        simp [dpOf, bn, bitsOf]
      · unfold GCv
        rw [hcr', hr]
        simp only [List.length_replicate]
        rw [hDE]
        simp [bitsOf, blkW]
    | cons x rr =>
      have hC := vRejC j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (List.replicate d 3)
        (List.replicate (Sb.length + 1 - d) 2) (bn x) hj (Bits.ofB _) (Bits.ofB _) (rep_z2 _) (rep_t3 _)
        (rep_z2 _) (bn_bits x)
      refine (h.ofEq rfl rfl).trans (hC.ofEq ?_ ?_)
      · rw [hF, hcr, hr]
        simp [dpOf, bn, bitsOf]
      · unfold GCv
        rw [hcr', hr]
        simp only [List.length_replicate]
        rw [hDE]
        simp [bitsOf, blkW, bn]


/-- The verifier loop from counter `cl` down to `0`. -/
theorem vLoopL (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    ∀ N cl, bv cl = N → cl.length = Sb.length + 1 →
      ∃ b, (b = true ↔ ∃ c : List Bool, c.length = Sb.length + 1 ∧ bv c ≤ bv cl ∧
          run1 Sb c.reverse (Sb.length + 1) = true) ∧
        zlnlLogic.Reach (GCv j Sb cl) (TR j Sb b) := by
  intro N
  induction N with
  | zero =>
    intro cl hN hcl
    have hS := vStepL j hj Sb cl hcl
    cases ho : run1 Sb cl.reverse (Sb.length + 1) with
    | true => exact ⟨true, ⟨fun _ => ⟨cl, hcl, Nat.le_refl _, ho⟩, fun _ => rfl⟩, hS.1 ho⟩
    | false =>
      have hz : cl = List.replicate (Sb.length + 1) false := by
        obtain ⟨k, hk⟩ := bv_zero cl hN
        rw [hk] at hcl ⊢
        simp at hcl
        rw [hcl]
      refine ⟨false, ⟨fun h => absurd h (by decide), fun ⟨c, hc, hle, hr⟩ => ?_⟩, hS.2.1 ho hz⟩
      have e : c = cl := bv_inj c cl (by rw [hc, hcl]) (by omega)
      rw [e, ho] at hr
      exact hr
  | succ N ih =>
    intro cl hN hcl
    have hS := vStepL j hj Sb cl hcl
    cases ho : run1 Sb cl.reverse (Sb.length + 1) with
    | true => exact ⟨true, ⟨fun _ => ⟨cl, hcl, Nat.le_refl _, ho⟩, fun _ => rfl⟩, hS.1 ho⟩
    | false =>
      rcases cases_dec cl with ⟨k, hk⟩ | ⟨k, r, hk⟩
      · rw [hk, bv_falses] at hN
        exact absurd hN (by omega)
      · have hd := bv_dec k r
        rw [← hk] at hd
        have hcl' : (List.replicate k true ++ false :: r).length = Sb.length + 1 := by
          rw [← hcl, hk]; simp
        obtain ⟨b, hb, hR⟩ := ih (List.replicate k true ++ false :: r) (by omega) hcl'
        refine ⟨b, ?_, (hS.2.2 ho k r hk).trans hR⟩
        rw [hb]
        constructor
        · rintro ⟨c, hc, hle, hrun⟩
          exact ⟨c, hc, by omega, hrun⟩
        · rintro ⟨c, hc, hle, hrun⟩
          refine ⟨c, hc, ?_, hrun⟩
          rcases Nat.lt_or_ge (bv c) (bv cl) with hlt | hge
          · omega
          · have e : c = cl := bv_inj c cl (by rw [hc, hcl]) (by omega)
            rw [e, ho] at hrun
            exact absurd hrun (by decide)

/-- The whole verifier: it leaves the truth flag `inL s`. -/
theorem vFullL (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    zlnlLogic.Reach (GCv j Sb (List.replicate (Sb.length + 1) true)) (TR j Sb (inLNL Sb)) := by
  obtain ⟨b, hb, hR⟩ := vLoopL j hj Sb _ (List.replicate (Sb.length + 1) true) rfl (by simp)
  have e : b = inLNL Sb := by
    apply bool_eq_of_iff
    rw [hb]
    unfold inLNL
    rw [List.any_eq_true]
    constructor
    · rintro ⟨c, hc, -, hr⟩
      exact ⟨c.reverse, (mem_strings _ _).mpr (by simp [hc]), hr⟩
    · rintro ⟨c, hc, hr⟩
      have hc' := (mem_strings _ _).mp hc
      refine ⟨c.reverse, by simp [hc'], ?_, by simpa using hr⟩
      have := bv_le c.reverse
      simp only [List.length_reverse, hc'] at this
      exact this
  rw [← e]
  exact hR



/-! ## From `lay` to the verifier -/

theorem lay_hdR (J S : Nat) : lay J S = hdR Q.GRB (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [] := by
  rw [lay_den]
  exact den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (by osimp) (by osimp)

theorem P1_hdR (j s : List Nat) :
    P1.den [j, s] = hdR Q.GRB (1 :: (j ++ 1 :: (s ++ 1 :: (List.replicate s.length 3 ++ [3, 1])))) [] :=
  den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 1 (.const 3), .sym 3, .sym 1])
    (by osimp) (by osimp)

theorem vStartL (J S : Nat) :
    zlnlLogic.Reach1 (lay J S) (GCv (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1L _ _ hj hs
  rw [← lay_den, P1_hdR] at h1
  have hT : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3, 1], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h
      rcases h with rfl | rfl <;> simp [O13]
  have h2 := blkCopyL [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT
  have h3 := blkVerL (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3) hj hs
    (rep_t3 _)
  refine h1.trans ((h2.ofEq (by simp) rfl).trans (h3.ofEq ?_ ?_))
  · simp [rep_cons_comm]
  · unfold GCv
    simp [bitsOf, blkW, List.replicate_succ, rep_cons_comm]

end ZP.MH
