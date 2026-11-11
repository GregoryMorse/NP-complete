module

public import ZP.MHDecSeg

@[expose] public section

/-!
# Multihead decider fuel with units (shared by `Z_LP` and `Z_LNL`)

The decider fuel is one block per position of a walker through `J`; at `M_1` the first unit is appended and
on the walk back one unit per step (`walkUnits`). Everything is stated for `mhBase`.
-/

namespace ZP.MH

open ZP

theorem Bits.rev {u : List Nat} (h : Bits u) : Bits u.reverse := fun a ha => h a (List.mem_reverse.mp ha)

theorem bits_all {b : Nat} (h : b ∈ bits) : b ∈ ALL := by
  rcases mem_bits h with rfl | rfl <;> simp [ALL]

theorem o13_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ O13) : NoB T := fun a ha => by
  have := h a ha
  simp [O13] at this
  simp [NB]
  omega

theorem t3_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ T3) : NoB T := fun a ha => by
  have := h a ha
  simp [T3] at this
  simp [NB]
  omega

theorem z2_noB {T : List Nat} (h : ∀ a ∈ T, a ∈ Z2) : NoB T := fun a ha => by
  have := h a ha
  simp [Z2] at this
  simp [NB]
  omega

theorem rep_t3 (k : Nat) : ∀ a ∈ List.replicate k 3, a ∈ T3 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [T3]

theorem rep_z2 (k : Nat) : ∀ a ∈ List.replicate k 2, a ∈ Z2 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [Z2]

theorem one_nb : (1 : Nat) ∈ NB := by simp [NB]

theorem rep_snoc_eq (n a : Nat) : List.replicate n a ++ [a] = a :: List.replicate n a := by
  have := rep_cons_comm a [] n
  simpa using this

theorem bitsOf_len (l : List Bool) : (bitsOf l).length = l.length := by
  simp [bitsOf]

theorem blkW_full (n : Nat) : blkW n (n + 1) = 1 :: List.replicate (n + 1) 3 := by
  simp [blkW]

theorem hdR_trail0 (q : Nat) (A R : List Nat) : hdR q A (R ++ [0]) = hdR q A R := by
  rw [hdR_eq', hdR_eq', sapp_lead0]

theorem FWr_full_o13 (n : Nat) : ∀ i, ∀ a ∈ FWr (List.replicate i (n, n + 1)), a ∈ O13
  | 0 => fun _ h => by cases h
  | i + 1 => by
    intro a ha
    have e : FWr (List.replicate (i + 1) (n, n + 1)) =
        FWr (List.replicate i (n, n + 1)) ++ blkW n (n + 1) := rfl
    rw [e] at ha
    rcases List.mem_append.mp ha with h | h
    · exact FWr_full_o13 n i a h
    · rw [blkW_full] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · rw [List.eq_of_mem_replicate h]; simp [O13]

/-! ## Loops -/

theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      mhBase.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
        (hdR Q.COPY (P ++ (u ++ v)) (1 :: (T ++ 1 :: List.replicate (u ++ v).length 3)))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := copyBody P u v T b hP hu hv.tail hT hv.head
    have h2 := copyLoop P T hP hT v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact (h1.trans_eq (hdR_eq (by simp) (by simp [List.replicate_succ'])) h2).ofEq (by simp) (by simp)

/-- `BLK` up to the end of the `COPY` loop. -/
theorem blkCopy (Jl Jr s T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s)
    (hT : ∀ a ∈ T, a ∈ O13) :
    mhBase.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) :=
    hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact ((blkStart Jl Jr s T hJl hJr hs hT).trans_eq (hdR_eq (by simp) (by simp))
    (copyLoop _ T hP hT s [] Bits.nil hs)).ofEq (by simp) (by simp)

theorem qcLoop (Xr V X Rest : List Nat) (hXr : Bits Xr) (hV : NoB V) (hX : Bits X) (hR : Sym4 Rest) :
    ∀ vr Qc, Bits vr → Bits Qc →
      mhBase.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.trans_eq (hd_eq (by simp) (by simp)) h2).ofEq (by simp) (by simp)

/-! ## The decider fuel -/

/-- The decider fuel and the units: from `GRB` right of the layout `Jl M Jr M s M M t M fuel` (the walker
is the first `M`) to the walker at home (`WB2` on the blank left of it) with `|Jl| + |Jr| + 1` units and
`|Jr| + 1` more blocks of fuel. -/
theorem decFuelU (x : List Bool) (t : List Nat) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      mhBase.Reach
        (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ 1 ::
          FWr (List.replicate i (x.length, x.length + 1)))))) [])
        (hd Q.WB2 [0] (1 :: (Jl ++ Jr ++ 1 :: (bitsOf x ++ 1 :: (1 :: (t ++ 1 ::
          FWr (List.replicate (i + Jr.length + 1) (x.length, x.length + 1))) ++
            0 :: ustoreN x (Jl.length + Jr.length + 1)))))) := by
  intro Jr
  induction Jr with
  | nil =>
    intro Jl i hJl _
    have hs : Bits (bitsOf x) := Bits.ofB x
    have hBl := FWr_full_o13 x.length i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWr (List.replicate i (x.length, x.length + 1))), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWr (List.replicate (i + ([] : List Nat).length + 1) (x.length, x.length + 1)) =
        FWr (List.replicate i (x.length, x.length + 1)) ++ (1 :: (List.replicate (bitsOf x).length 3 ++ [3])) := by
      show FWr (List.replicate i (x.length, x.length + 1)) ++ blkW x.length (x.length + 1) = _
      rw [blkW_full, bitsOf_len, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopy Jl [] (bitsOf x) _ hJl Bits.nil hs hT
    have hL := blkDecLastU Jl (bitsOf x) t (FWr (List.replicate i (x.length, x.length + 1))) hJl hs ht hBl
    obtain ⟨Mid, hMidD⟩ : ∃ Mid, Mid = 1 :: (t ++ 1 :: (FWr (List.replicate i (x.length, x.length + 1)) ++
        1 :: (List.replicate (bitsOf x).length 3 ++ [3]))) := ⟨_, rfl⟩
    have hMid : NoB Mid := by
      rw [hMidD]
      exact NoB.cons one_nb ((t3_noB ht).app (NoB.cons one_nb ((o13_noB hBl).app (NoB.cons one_nb
        ((t3_noB (rep_t3 _)).app (NoB.cons (by simp [NB]) NoB.nil))))))
    have hRt : NoB (bitsOf x ++ 1 :: Mid) := hs.noB.app (NoB.cons one_nb hMid)
    have hLs : Sym4 (Jl ++ [1, 1]) := by
      have h1' : (1 : Nat) ∈ ALL := by simp [ALL]
      exact hJl.sym4.app (Sym4.cons h1' (Sym4.cons h1' Sym4.nil))
    have hU := unitApp x Jl [] Mid (Jl ++ [1, 1]) (bitsOf x ++ 1 :: Mid) hJl Bits.nil hMid hLs hRt (by simp) 0
    have hW := walkUnits x Mid hMid Jl.reverse [] 1 hJl.rev Bits.nil
    have hL' : mhBase.Reach
        (hdR Q.COPY (Jl ++ 1 :: ([] ++ 1 :: bitsOf x))
          (1 :: ((1 :: (t ++ 1 :: FWr (List.replicate i (x.length, x.length + 1)))) ++
            1 :: List.replicate (bitsOf x).length 3)))
        (hdR QMH.U0 (Jl ++ [1, 1]) (bitsOf x ++ 1 :: Mid ++ 0 :: ustoreN x 0)) := by
      refine hL.ofEq (hdR_eq (by simp) (by simp)) ?_
      rw [show [0] ++ Jl ++ [1, 1] = 0 :: (Jl ++ [1, 1]) by simp, hdR_lead0, ustoreN_zero]
      exact (hdR_eq rfl (by simp [hMidD])).trans (hdR_trail0 _ _ _).symm
    have hU' : mhBase.Reach
        (hdR QMH.U0 (Jl ++ [1, 1]) (bitsOf x ++ 1 :: Mid ++ 0 :: ustoreN x 0))
        (hd Q.WB2 [0] (1 :: (Jl.reverse.reverse ++ [] ++ 1 :: (bitsOf x ++ 1 :: (Mid ++
          0 :: ustoreN x (1 + Jl.reverse.length)))))) :=
      hU.trans_eq (hdR_eq (by simp) (by simp)) hW
    have h2 := (hA.trans hL').trans hU'
    refine h2.ofEq (hdR_eq (by simp) rfl) ?_
    rw [hMidD, eF, List.reverse_reverse, List.length_reverse]
    refine hd_eq rfl ?_
    simp [Nat.add_comm]
  | cons b Jr' ih =>
    intro Jl i hJl hJr
    have hs : Bits (bitsOf x) := Bits.ofB x
    have hBl := FWr_full_o13 x.length i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWr (List.replicate i (x.length, x.length + 1))), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWr (List.replicate (i + 1) (x.length, x.length + 1)) =
        FWr (List.replicate i (x.length, x.length + 1)) ++ (1 :: (List.replicate (bitsOf x).length 3 ++ [3])) := by
      show FWr (List.replicate i (x.length, x.length + 1)) ++ blkW x.length (x.length + 1) = _
      rw [blkW_full, bitsOf_len, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopy Jl (b :: Jr') (bitsOf x) _ hJl hJr hs hT
    have hS := blkDecStep Jl Jr' (bitsOf x) t (FWr (List.replicate i (x.length, x.length + 1))) b hJl hJr.tail hs ht
      hBl hJr.head
    have h2 := ih (Jl ++ [b]) (i + 1) (hJl.snoc hJr.head) hJr.tail
    have e : i + 1 + Jr'.length + 1 = i + (b :: Jr').length + 1 := by
      simp only [List.length_cons]; omega
    rw [e] at h2
    have hS' : mhBase.Reach
        (hdR Q.COPY (Jl ++ 1 :: (b :: Jr' ++ 1 :: bitsOf x))
          (1 :: ((1 :: (t ++ 1 :: FWr (List.replicate i (x.length, x.length + 1)))) ++
            1 :: List.replicate (bitsOf x).length 3)))
        (hdR Q.GRB ((Jl ++ [b]) ++ 1 :: (Jr' ++ 1 :: (bitsOf x ++ 1 :: 1 :: (t ++ 1 ::
          FWr (List.replicate (i + 1) (x.length, x.length + 1)))))) []) :=
      hS.ofEq (hdR_eq (by simp) (by simp)) (hdR_eq (by rw [eF]; simp) rfl)
    refine (hA.trans hS').trans (h2.ofEq rfl ?_)
    refine hd_eq rfl ?_
    simp
    congr 1
    omega

end ZP.MH
