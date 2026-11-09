module

public import ZP.MulRun
public import ZP.Pair

@[expose] public section

/-!
# Z_MUL: the outer layer (setup, fuel build, one decider run)

The layout is `M_g J M_1 s M_2 fuel B storage`; the walker builds the fuel (one full block, then
one short block per position of `J`) and, going back, one empty stack per position.
-/

namespace ZP.Mul

open ZP

def B0 : List Nat := [0]

/-! ## Small facts -/

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

theorem one_nb : (1 : Nat) ∈ NB := by simp [NB]

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zmulLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zmulLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
      (hdR Q.COPY (P ++ (u ++ [b])) (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ [3])))))) := by
  have hV : Valid [NB, bits, bits, O13] [P, u, v, T] := Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hT (Valid.nil _))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [P, u, v, T]) (E := []) (k := 13) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, u, v, T]) (E := []) (k := 13) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zmulLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
      (hdR Q.GC (b :: (Ur ++ (1 :: (V ++ (P ++ (1 :: (u ++ [b]))))))) (v ++ (1 :: Rest))) := by
  have hV : Valid [bits, NB, bits, bits, bits, ALL] [Ur, V, P, u, v, Rest] := Valid.cons hUr (Valid.cons hV (Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hRest (Valid.nil _))))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 2, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 2]) (rs' := [.blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Ur, V, P, u, v, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 3, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3]) (rs' := [.blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gcEnd (Xr : List Nat) (V : List Nat) (P : List Nat) (X : List Nat) (Rest : List Nat) (hXr : Bits Xr) (hV : NoB V) (hP : Bits P) (hX : Bits X) (hRest : Sym4 Rest) :
    zmulLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: Rest))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: Rest)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zmulLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.QC (b :: (Qc ++ (1 :: (Xr ++ (1 :: (V ++ v)))))) (b :: (Qc ++ (1 :: (X ++ (1 :: Rest)))))) := by
  have hV : Valid [bits, bits, NB, bits, bits, ALL] [Qc, Xr, V, v, X, Rest] := Valid.cons hQc (Valid.cons hXr (Valid.cons hV (Valid.cons hv (Valid.cons hX (Valid.cons hRest (Valid.nil _))))))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Qc, Xr, V, v, X, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id, .sym 2]) (rs := [.blk 0 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 2, .blk 0 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Qc, Xr, V, v, X, Rest]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id, .sym 3]) (rs := [.blk 0 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 3, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 3, .blk 0 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Code copied: the sentinel `0`, the separator becomes the gap, one rotation. -/
theorem qcEnd (P : List Nat) (Xr : List Nat) (Vq : List Nat) (X : List Nat) (Rest : List Nat) (hP : Bits P) (hXr : Bits Xr) (hVq : NoB Vq) (hX : Bits X) (hRest : Sym4 Rest) :
    zmulLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zmulLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
        (hdR Q.COPY (P ++ (u ++ v)) (1 :: (T ++ 1 :: List.replicate (u ++ v).length 3)))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := copyBody P u v T b hP hu hv.tail hT hv.head
    have h2 := copyLoop P T hP hT v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.of_eq (by simp [List.replicate_succ']) (by simp only [List.append_assoc, List.singleton_append]))

/-- `BLK` up to the end of the `COPY` loop. -/
theorem blkCopy (Jl Jr s T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s)
    (hT : ∀ a ∈ T, a ∈ O13) :
    zmulLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))

theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zmulLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
        (hdR Q.GC ((u ++ v).reverse ++ 1 :: (V ++ (P ++ 1 :: (u ++ v)))) (1 :: Rest))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := gcBody u.reverse V P u v Rest b hu.rev hV hP hu hv.tail hR hv.head
    have h2 := gcLoop V P Rest hV hP hR v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.of_eq (by simp) (by simp only [List.append_assoc, List.singleton_append]))

theorem qcLoop (Xr V X Rest : List Nat) (hXr : Bits Xr) (hV : NoB V) (hX : Bits X) (hR : Sym4 Rest) :
    ∀ vr Qc, Bits vr → Bits Qc →
      zmulLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- New instance: `M_2` at the end of `s`. -/
theorem niM (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zmulLogic.Reach (hdR QMul.NI (1 :: (j ++ (1 :: (s)))) ([]))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ ([1]))))) ([])) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkFF (env := [j, s]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy done: the last digit of the full block, back to the walker. -/
theorem cxM (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zmulLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (1 :: (List.replicate s.length 3))))
      (hd Q.DW1 (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (List.replicate s.length 3))))))) ([3])) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkFT (env := [j, s]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 1 (.const 3)])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 1 (.const 3)]) (rs' := [.sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One walker step: the short block. -/
theorem dwStep (Jl : List Nat) (Jr : List Nat) (s : List Nat) (Fp : List Nat) (b : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hFp : ∀ a ∈ Fp, a ∈ O13) (hb : b ∈ bits) :
    zmulLogic.Reach (hd Q.DW1 (Jl ++ (1 :: (b :: (Jr ++ (1 :: (s ++ (1 :: (Fp)))))))) ([3]))
      (hd Q.DW1 (Jl ++ (b :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (Fp ++ (3 :: ([1])))))))))) ([3])) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, Fp] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hFp (Valid.nil _))))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Jl, Jr, s, Fp]) (E := []) (k := 22) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 3])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .sym 1]) (rs' := [.sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Jl, Jr, s, Fp]) (E := []) (k := 22) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 3])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .sym 1]) (rs' := [.sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The walker is at the end of `J`. -/
theorem dwLast (Jl : List Nat) (s : List Nat) (Fp : List Nat) (hJl : Bits Jl) (hs : Bits s) (hFp : ∀ a ∈ Fp, a ∈ O13) :
    zmulLogic.Reach (hd Q.DW1 (Jl ++ (1 :: (1 :: (s ++ (1 :: (Fp)))))) ([3]))
      (hd Q.WB1 (Jl ++ ([1])) (1 :: (s ++ (1 :: (Fp ++ ([3])))))) := by
  have hV : Valid [bits, bits, O13] [Jl, s, Fp] := Valid.cons hJl (Valid.cons hs (Valid.cons hFp (Valid.nil _)))
  exact checkTT (env := [Jl, s, Fp]) (E := []) (k := 10) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 3])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One step back: the marker moves left, an empty stack is appended. -/
theorem wbBodyM (Jl : List Nat) (Y : List Nat) (ST : List Nat) (b : Nat) (hJl : Bits Jl) (hY : NoB Y) (hST : NoB ST) (hb : b ∈ bits) :
    zmulLogic.Reach (hd Q.WB2 (0 :: (Jl ++ ([b]))) (1 :: (Y ++ (0 :: (ST)))))
      (hd Q.WB2 (0 :: (Jl)) (1 :: (b :: (Y ++ (0 :: (ST ++ ([1]))))))) := by
  have hV : Valid [bits, NB, NB] [Jl, Y, ST] := Valid.cons hJl (Valid.cons hY (Valid.cons hST (Valid.nil _)))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Jl, Y, ST]) (E := []) (k := 15) hV trivial
      (ls := [.sym 0, .blk 0 .id, .sym 2]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.sym 0, .blk 0 .id]) (rs' := [.sym 1, .sym 2, .blk 1 .id, .sym 0, .blk 2 .id, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Jl, Y, ST]) (E := []) (k := 15) hV trivial
      (ls := [.sym 0, .blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.sym 0, .blk 0 .id]) (rs' := [.sym 1, .sym 3, .blk 1 .id, .sym 0, .blk 2 .id, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The marker is home: write `H`. -/
theorem wbEndM (j : List Nat) (Y : List Nat) (hj : Bits j) (hY : Sym4 Y) :
    zmulLogic.Reach (hd Q.WB2 ([0]) (1 :: (j ++ (1 :: (Y)))))
      (hdR Q.GC (1 :: (1 :: (j ++ ([1])))) (Y)) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 4) hV trivial
    (ls := [.sym 0]) (rs := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- The marker cell is left, to the cell before it. -/
theorem wb12 (Jl : List Nat) (Y : List Nat) (hJl : Bits Jl) (hY : Sym4 Y) :
    zmulLogic.Reach (hd Q.WB1 (Jl ++ ([1])) (Y))
      (hd Q.WB2 (0 :: (Jl)) (1 :: (Y))) := by
  have hV : Valid [bits, ALL] [Jl, Y] := Valid.cons hJl (Valid.cons hY (Valid.nil _))
  exact checkTT (env := [Jl, Y]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.sym 0, .blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-! ## The fuel build -/

/-- The short blocks `M 1`. -/
def shortF : Nat → List Nat
  | 0 => []
  | k + 1 => 1 :: 3 :: shortF k

theorem shortF_snoc (k : Nat) : shortF k ++ [1, 3] = 1 :: 3 :: shortF k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [shortF, List.cons_append]
    rw [ih]

theorem shortF_o13 : ∀ k, ∀ a ∈ shortF k, a ∈ O13
  | 0 => fun _ h => by cases h
  | k + 1 => by
    intro a ha
    simp only [shortF, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · simp [O13]
    · simp [O13]
    · exact shortF_o13 k a ha

theorem FWr_short (k : Nat) : FWr (List.replicate k (0, 1)) = shortF k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    show FWr (List.replicate k (0, 1)) ++ blkW 0 1 = _
    rw [ih, show blkW 0 1 = [1, 3] by rfl, shortF_snoc]
    rfl

/-- The fuel: a full block (width `n + 1`) and `k` short blocks. -/
def fz (n k : Nat) : List Dg := List.replicate k (0, 1) ++ [(n, n + 1)]

theorem fz_FWr (n k : Nat) : FWr (fz n k) = 1 :: (List.replicate (n + 1) 3 ++ shortF k) := by
  unfold fz
  have : ∀ (xs ys : List Dg), FWr (xs ++ ys) = FWr ys ++ FWr xs := by
    intro xs
    induction xs with
    | nil => intro ys; simp [FWr]
    | cons x xs ih => intro ys; obtain ⟨a, d⟩ := x; simp [FWr, ih, List.append_assoc]
  rw [this, FWr_short]
  simp [FWr, blkW]

theorem fz_dig (n k : Nat) : Dig (fz n k) := by
  intro p hp
  unfold fz at hp
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hp
  rcases hp with ⟨_, rfl⟩ | rfl
  · simp
  · simp

theorem fz_valr (n k : Nat) : valr (full (fz n k)) + 1 = (n + 2) * 2 ^ k := by
  rw [valr_full]
  unfold fz
  induction k with
  | zero => simp [rad]
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [List.cons_append, rad] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm 2 (2 ^ k)]

theorem dwLoop (s : List Nat) (hs : Bits s) :
    ∀ (Jr Jl Fp : List Nat), Bits Jl → Bits Jr → (∀ a ∈ Fp, a ∈ O13) →
      zmulLogic.Reach (hd Q.DW1 (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: Fp))) [3])
        (hd Q.WB1 (Jl ++ Jr ++ [1]) (1 :: (s ++ 1 :: (Fp ++ 3 :: shortF Jr.length))))
  | [], Jl, Fp, hJl, _, hFp => by
    have h := dwLast Jl s Fp hJl hs hFp
    simpa [shortF] using h
  | b :: Jr', Jl, Fp, hJl, hJr, hFp => by
    have h1 := dwStep Jl Jr' s Fp b hJl hJr.tail hs hFp hJr.head
    have hFp' : ∀ a ∈ Fp ++ [3, 1], a ∈ O13 := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hFp a h
      · simp at h; rcases h with rfl | rfl <;> simp [O13]
    have h2 := dwLoop s hs Jr' (Jl ++ [b]) (Fp ++ [3, 1]) (hJl.snoc hJr.head) hJr.tail hFp'
    refine h1.trans (h2.of_eq (by simp) ?_)
    simp [shortF]

theorem wbLoopM : ∀ (jr Y ST : List Nat), Bits jr → NoB Y → NoB ST →
    zmulLogic.Reach (hd Q.WB2 (0 :: jr.reverse) (1 :: (Y ++ 0 :: ST)))
      (hd Q.WB2 [0] (1 :: (jr.reverse ++ Y ++ 0 :: (ST ++ List.replicate jr.length 1))))
  | [], Y, ST, _, _, _ => by
    simp only [List.reverse_nil, List.nil_append, List.length_nil, List.replicate_zero, List.append_nil]
    exact LTM.Reach.refl _ _
  | b :: jr, Y, ST, hj, hY, hST => by
    have hjr : Bits jr := hj.tail
    have hb : b ∈ bits := hj.head
    have h1 := wbBodyM jr.reverse Y ST b hjr.rev hY hST hb
    have hY' : NoB (b :: Y) := NoB.cons (by rcases mem_bits hb with rfl | rfl <;> simp [NB]) hY
    have hST' : NoB (ST ++ [1]) := hST.app (NoB.cons one_nb NoB.nil)
    have h2 := wbLoopM jr (b :: Y) (ST ++ [1]) hjr hY' hST'
    refine (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl ?_)
    simp [List.replicate_succ, List.append_assoc]

theorem decFuelM (s : List Nat) (hs : Bits s) (J : List Nat) (hJ : Bits J) :
    zmulLogic.Reach (hdR QMul.NI (1 :: (J ++ 1 :: s)) [])
      (hdR Q.GC (1 :: 1 :: (J ++ [1]))
        (s ++ 1 :: (FWr (fz s.length J.length) ++ 0 :: List.replicate J.length 1))) := by
  have h0 := niM J s hJ hs
  have h1 := blkCopy [] J s [] Bits.nil hJ hs (fun a h => by cases h)
  have h2 := cxM J s hJ hs
  have hFp : ∀ a ∈ 1 :: List.replicate s.length 3, a ∈ O13 := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [O13]
    · rw [List.eq_of_mem_replicate ha]; simp [O13]
  have h3 := dwLoop s hs J [] (1 :: List.replicate s.length 3) Bits.nil hJ hFp
  have hFuel : NoB ((1 :: List.replicate s.length 3) ++ 3 :: shortF J.length) := by
    apply o13_noB
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hFp a h
    · rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact shortF_o13 _ a h
  have hY : NoB (1 :: (s ++ 1 :: ((1 :: List.replicate s.length 3) ++ 3 :: shortF J.length))) :=
    NoB.cons one_nb (hs.noB.app (NoB.cons one_nb hFuel))
  have h4 := wb12 J _ hJ hY.sym4
  have h5 := wbLoopM J.reverse _ [] hJ.rev hY NoB.nil
  have hY2 : Sym4 (s ++ 1 :: (((1 :: List.replicate s.length 3) ++ 3 :: shortF J.length) ++
      0 :: List.replicate J.length 1)) := by
    refine hs.sym4.app (Sym4.cons (by simp [ALL]) (hFuel.sym4.app (Sym4.cons (by simp [ALL]) (Sym4.rep _ 1 (by simp [ALL])))))
  have h6 := wbEndM J _ hJ hY2
  have a1 := h0.trans (h1.of_eq (by simp) rfl)
  have a2 := a1.trans (h2.of_eq (by simp) rfl)
  have a3 := a2.trans (h3.of_eq (by simp) rfl)
  have a4 := a3.trans (h4.of_eq (by simp) rfl)
  have a5 := a4.trans (h5.of_eq (by have := hd_pad Q.WB2 (0 :: J) (1 :: (1 :: (s ++ 1 :: ((1 :: List.replicate s.length 3) ++ 3 :: shortF J.length)))) 1; simpa using this) rfl)
  have a6 := a5.trans (h6.of_eq (by simp) rfl)
  refine a6.of_eq rfl ?_
  rw [fz_FWr]
  simp [List.replicate_succ']

theorem setupM (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W F ST : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W) (hF : NoB F) (hST : NoB ST)
    (hFb : ∃ a ∈ F, a ∈ bits)
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: (F ++ 0 :: ST)) :
    ∃ g, 1 ≤ g ∧ zmulLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
      (Bd (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ W F ST) := by
  have hVn : NoB (Vq ++ [1]) := hVq.app (NoB.cons one_nb NoB.nil)
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hX : Bits (bitsOf Xb) := Bits.ofB Xb
  have hXr : Bits (bitsOf Xb).reverse := bitsOf_rev Xb
  have h1 := gcLoop (Vq ++ [1]) (bitsOf Pb) Rest hVn hP hR (bitsOf Xb) [] Bits.nil hX
  have h2 := gcEnd (bitsOf Xb).reverse (Vq ++ [1]) (bitsOf Pb) (bitsOf Xb) Rest hXr hVn hP hX hR
  have h3 := qcLoop (bitsOf Xb).reverse (Vq ++ [1]) (bitsOf Xb) Rest hXr hVn hX hR (bitsOf Pb).reverse []
    hP.rev Bits.nil
  have h4 := qcEnd (bitsOf Pb) (bitsOf Xb).reverse Vq (bitsOf Xb) Rest hP hXr hVq hX hR
  have e0 : hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest) =
      hdR Q.GC (([] : List Nat).reverse ++ 1 :: ((Vq ++ [1]) ++ (bitsOf Pb ++ 1 :: [])))
        (bitsOf Xb ++ 1 :: Rest) := by
    rw [hV]; simp
  have hA := (h1.of_eq e0.symm (by simp)).trans (h2.trans ((h3.of_eq (by simp) (by simp)).trans h4))
  have hG : Sym4 (0 :: ((bitsOf Xb).reverse ++ 1 :: (Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest))))) :=
    Sym4.cons (by simp [ALL]) (hXr.sym4.app (Sym4.cons (by simp [ALL]) (hVq.sym4.app (Sym4.cons (by simp [ALL])
      (hP.sym4.app (Sym4.cons (by simp [ALL]) (hX.sym4.app (Sym4.cons (by simp [ALL]) hR))))))))
  obtain ⟨R', H, hrot, hH, -, hr⟩ := rotate rotNormal (Pb.reverse ++ [false]) (by simp) _ hG
  rw [rst_hd, rnav_hd] at hr
  have hcode : (bitsOf (Pb.reverse ++ [false])).reverse = 2 :: bitsOf Pb := by
    simp [bitsOf]
  have hB0 := hA.trans (lift (hr.of_eq (by rw [hcode]) rfl))
  have eT : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = (1 :: (W ++ 1 :: F)) ++ 0 :: ST := by
    have e : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) =
        (Vq ++ [1]) ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) := by simp
    rw [e, ← hV, List.cons_append, hWF]
    simp
  have hVt : NoB (1 :: (W ++ 1 :: F)) := NoB.cons one_nb (hW.app (NoB.cons one_nb hF))
  obtain ⟨p, b, X', eV, hb, hX'⟩ := mb2 _ (0 :: ST) hVt (Sym4.cons (by simp [ALL]) hST.sym4) (by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hab⟩)
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  cases Xb with
  | nil =>
    have hB := segB R'.reverse [] X' k 0 p 0 b (Or.inl rfl) hb hRr Bits.nil hX'
    refine ⟨k + 1, by omega, hB0.trans (lift (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (lift (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk, bitsOf_cons, List.reverse_cons, bitsOf_reverse]
      simp
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN_some, bitsOf, List.replicate_succ, rep_cons_comm]

theorem inv0 (Pb : List Bool) : InvR (rot (Pb.reverse ++ [false])) := by
  apply inv_rot
  refine ⟨by simp, fun hl => ?_, fun hl => ?_⟩
  · rcases Pb with _ | ⟨a, Pb⟩
    · rfl
    · simp at hl
  · rcases Pb with _ | ⟨a, _ | ⟨b, Pb⟩⟩
    · simp at hl
    · simp
    · simp at hl


theorem stext_rep (r : Nat) : stext (List.replicate r []) = List.replicate r 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have ih' : (List.map stxt (List.replicate r ([] : List Bool)).reverse).flatten = List.replicate r 1 := ih
    rw [List.replicate_succ, stext_cons, ih']
    simp [stxt, bitsOf, List.replicate_succ']

theorem cap_rep (r ρ : Nat) : Cap (List.replicate r []) ρ := by
  intro f hf
  rw [List.eq_of_mem_replicate hf]
  simp

/-- One guest run from the setup position, to the result state. -/
theorem runFromM (Pb Xb : List Bool) (ds : List Dg) (hds : Dig ds) (hne : ds ≠ []) :
    ∃ ds' ST', Dig ds' ∧ ds'.map Prod.fst = ds.map Prod.fst ∧ NoB ST' ∧
      zmulLogic.Reach
        (hdR Q.GC (1 :: 1 :: (bitsOf Pb ++ [1]))
          (bitsOf Xb ++ 1 :: (FWr ds ++ 0 :: List.replicate Pb.length 1)))
        (REm (runMulAux (valr ds) (rot (Pb.reverse ++ [false])) Xb 0 (List.replicate Pb.length []))
          (bitsOf Pb ++ 1 :: bitsOf Xb) (FWr ds') ST') := by
  have hS := stext_noB (List.replicate Pb.length [])
  have hF := FWr_noB ds
  have hR : Sym4 (FWr ds ++ 0 :: List.replicate Pb.length 1) :=
    hF.sym4.app (Sym4.cons (by simp [ALL]) (Sym4.rep _ 1 (by simp [ALL])))
  have hW : NoB (bitsOf Pb ++ 1 :: bitsOf Xb) :=
    (Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)
  obtain ⟨g, hg, h1⟩ := setupM [] [] Pb Xb (FWr ds ++ 0 :: List.replicate Pb.length 1)
    (bitsOf Pb ++ 1 :: bitsOf Xb) (FWr ds) (List.replicate Pb.length 1) rfl NoB.nil hR hW hF
    (by rw [← stext_rep]; exact hS) (fw_bit ds hne) (by simp)
  have hz : (⟨[], Xb.head?, Xb.tail⟩ : Zp).WF := by
    unfold Zp.WF
    cases Xb with
    | nil => intro _; rfl
    | cons x xt => intro h; simp at h
  have hq : (List.replicate Pb.length ([] : List Bool) ≠ [] ∨ rot (Pb.reverse ++ [false]) = [false]) := by
    cases Pb with
    | nil => exact Or.inr (by simp [rot_single])
    | cons a Pb => exact Or.inl (by simp [List.replicate_succ])
  obtain ⟨ds', ST', hd', hl', hS', h2⟩ := runM (bitsOf Pb ++ 1 :: bitsOf Xb)  hW (valr ds)
    (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ ds (List.replicate Pb.length [])
    (inv0 Pb) hg hz hds hne rfl hq (cap_rep _ _)
  have ht : (⟨[], Xb.head?, Xb.tail⟩ : Zp).list = Xb := by cases Xb <;> rfl
  rw [ht] at h2
  rw [stext_rep] at h2
  exact ⟨ds', ST', hd', hl', hS', h1.trans (by simpa using h2)⟩

/-- Halt with output 0: the dispatch reaches the beep state. -/
theorem dHalt0 (j : List Nat) (s : List Nat) (Fp : List Nat) (hj : Bits j) (hs : Bits s) (hFp : Sym4 Fp) :
    zmulLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (1 :: (Fp)))))))
      (hdR Q.DP30 (1 :: (j ++ (1 :: (s ++ ([1]))))) (1 :: (Fp))) := by
  have hV : Valid [bits, bits, ALL] [j, s, Fp] := Valid.cons hj (Valid.cons hs (Valid.cons hFp (Valid.nil _)))
  exact checkFF (env := [j, s, Fp]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The outcome 1 erases the first `M` of the fuel. -/
theorem dp31 (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    zmulLogic.Reach (hdR Q.DP31 (A) (1 :: (R)))
      (hdR Q.EAs (A ++ ([0])) (R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [A, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Erase the fuel. -/
theorem eaF (A : List Nat) (F : List Nat) (Rest : List Nat) (hA : Sym4 A) (hF : NoB F) (hRest : Sym4 Rest) :
    zmulLogic.Reach (hdR Q.EAs (A) (F ++ (0 :: (Rest))))
      (hdR QMul.EAs2 (A ++ (List.replicate F.length 0 ++ ([0]))) (Rest)) := by
  have hV : Valid [ALL, NB, ALL] [A, F, Rest] := Valid.cons hA (Valid.cons hF (Valid.cons hRest (Valid.nil _)))
  exact checkFF (env := [A, F, Rest]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 0), .sym 0]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The storage is empty. -/
theorem ea2nil (A : List Nat) (hA : Sym4 A) :
    zmulLogic.Reach (hdR QMul.EAs2 (A) ([]))
      (hd Q.EBs (A) ([])) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Erase the storage. -/
theorem ea2cons (A : List Nat) (T : List Nat) (hA : Sym4 A) (hT : NoB T) :
    zmulLogic.Reach (hdR QMul.EAs2 (A) (1 :: (T)))
      (hd Q.EBs (A ++ (0 :: (List.replicate T.length 0 ++ ([0])))) ([])) := by
  have hV : Valid [ALL, NB] [A, T] := Valid.cons hA (Valid.cons hT (Valid.nil _))
  exact checkFT (env := [A, T]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Sweep back to `M_2`: the next `s`. -/
theorem ebM (A : List Nat) (Z : List Nat) (hA : Sym4 A) (hZ : ∀ a ∈ Z, a ∈ B0) :
    zmulLogic.Reach (hd Q.EBs (A ++ (1 :: (Z))) ([]))
      (hd Q.SINC (A) (0 :: (Z))) := by
  have hV : Valid [ALL, B0] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [A, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Sweep back to the flag: the next `J`. -/
theorem ebZ (j : List Nat) (s : List Nat) (Z : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ B0) :
    zmulLogic.Reach (hd Q.EBs (1 :: (j ++ (1 :: (s ++ (1 :: (2 :: (Z))))))) ([]))
      (hd Q.JINC (1 :: (j)) (1 :: (List.replicate s.length 0 ++ (0 :: (0 :: (Z)))))) := by
  have hV : Valid [bits, bits, B0] [j, s, Z] := Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [j, s, Z]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id]) (rs := [])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 0), .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Increment `s`: all ones, one more digit. -/
theorem sincEM (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.SINC (A ++ ([1])) (Z))
      (hdR QMul.NI (A ++ (1 :: (Z ++ ([2])))) ([])) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment `s`: a `0` becomes `1`. -/
theorem sinc0M (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ ([2])))) (Z))
      (hdR QMul.NI (A ++ (1 :: (r ++ (3 :: (Z))))) ([])) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment `s`: carry. -/
theorem sinc1M (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ ([3])))) (Z))
      (hd Q.SINC (A ++ (1 :: (r))) (2 :: (Z))) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment `J`: all ones. -/
theorem jincEM (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.JINC ([1]) (Z ++ ([1])))
      (hdR QMul.NI (1 :: (Z ++ (2 :: ([1])))) ([])) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment `J`: a `0` becomes `1`. -/
theorem jinc0M (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.JINC (1 :: (r ++ ([2]))) (Z ++ ([1])))
      (hdR QMul.NI (1 :: (r ++ (3 :: (Z ++ ([1]))))) ([])) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment `J`: carry. -/
theorem jinc1M (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zmulLogic.Reach (hd Q.JINC (1 :: (r ++ ([3]))) (Z ++ ([1])))
      (hd Q.JINC (1 :: (r)) (2 :: (Z ++ ([1])))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- The one step out of the beep state. -/
theorem beepStepM (j s Y : List Nat) :
    zmulLogic.zstep (hdR Q.DP30 (1 :: (j ++ 1 :: (s ++ [1]))) (1 :: Y)) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ [1, 2]))) Y) := by
  have e1 : (⟨Q.DP30, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1].reverse,
      [.sym 1, .blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.DP30 (1 :: (j ++ 1 :: (s ++ [1]))) (1 :: Y) :=
    den_tapeR (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ [1, 2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

end ZP.Mul
