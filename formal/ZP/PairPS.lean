module

public import ZP.Pair
public import ZP.CompilePS
public import ZP.DefsPS

@[expose] public section

/-! The pair lemma for the P = PSPACE machine, copied from `ZP/Pair.lean` and adapted. -/

namespace ZP.PS

open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zpsLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zpsLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
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


/-- Verifier fuel block done: write `H`, go to the guest source `C`. -/
theorem blkVer (j : List Nat) (s : List Nat) (C : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) :
    zpsLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: s))) (1 :: (3 :: (C ++ (1 :: (1 :: (List.replicate s.length 3)))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (3 :: (C ++ (1 :: (1 :: (List.replicate s.length 3 ++ [3])))))) := by
  have hV : Valid [bits, bits, T3] [j, s, C] := Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.nil _)))
  exact checkFF (env := [j, s, C]) (E := []) (k := 39) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 1, .blk 1 (.const 3)])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 1, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Decider fuel block done, the walker steps right. -/
theorem blkDecStep (Jl : List Nat) (Jr : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (b : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) (hb : b ∈ bits) :
    zpsLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hdR Q.GRB (Jl ++ (b :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3]))))))))))))) []) := by
  have hV : Valid [bits, bits, bits, T3, O13] [Jl, Jr, s, t, Bl] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _)))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Jl, Jr, s, t, Bl]) (E := []) (k := 54) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3)])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, t, Bl]) (E := []) (k := 54) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3)])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Last decider fuel block: the walker goes home. -/
theorem blkDecLast (Jl : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (hJl : Bits Jl) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) :
    zpsLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, O13] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 35) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zpsLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
      (hd Q.WB1 (Jl ++ [1]) (b :: Y)) := by
  have hV : Valid [bits, ALL] [Jl, Y] := Valid.cons hJl (Valid.cons hY (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Jl, Y]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 2, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 2, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Jl, Y]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 3, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbEnd (j : List Nat) (Y : List Nat) (hj : Bits j) (hY : Sym4 Y) :
    zpsLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zpsLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zpsLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: Rest))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: Rest)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zpsLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zpsLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR Q.GRB (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR Q.GRB (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR Q.GRB (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR Q.GRB (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zpsLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zpsLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
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
    zpsLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zpsLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zpsLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zpsLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zpsLogic.Reach
        (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1)))))) [])
        (hdR Q.GC (1 :: 1 :: (Jl ++ Jr ++ [1]))
          (s ++ 1 :: 1 :: (t ++ 1 :: FWr n (List.replicate (i + Jr.length + 1) (n + 1))))) := by
  intro Jr
  induction Jr with
  | nil =>
    intro Jl i hJl _
    have hBl := FWr_full_o13 n i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1))), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWr n (List.replicate (i + ([] : List Nat).length + 1) (n + 1)) =
        FWr n (List.replicate i (n + 1)) ++ (1 :: (List.replicate s.length 3 ++ [3])) := by
      show FWr n (List.replicate i (n + 1)) ++ blkW n (n + 1) = _
      rw [blkW_full, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopy Jl [] s _ hJl Bits.nil hs hT
    have hL := blkDecLast Jl s t (FWr n (List.replicate i (n + 1))) hJl hs ht hBl
    have hY : NoB (1 :: (s ++ 1 :: 1 :: (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++
        1 :: (List.replicate s.length 3 ++ [3]))))) :=
      NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb ((t3_noB ht).app (NoB.cons one_nb
        ((o13_noB hBl).app (NoB.cons one_nb ((t3_noB (rep_t3 _)).app (NoB.cons (by simp [NB]) NoB.nil)))))))))
    have hW := wbLoop Jl.reverse _ hJl.rev hY.sym4
    have hE := wbEnd Jl (s ++ 1 :: 1 :: (t ++ 1 :: (FWr n (List.replicate i (n + 1)) ++
        1 :: (List.replicate s.length 3 ++ [3])))) hJl (by
          have := hY.sym4
          intro a ha; exact this a (List.mem_cons_of_mem _ ha))
    refine (hA.trans ((hL.of_eq (by simp) rfl).trans ((hW.of_eq (by simp) (by simp)).trans hE))).of_eq rfl ?_
    rw [eF]
    simp
  | cons b Jr' ih =>
    intro Jl i hJl hJr
    have hBl := FWr_full_o13 n i
    have hT : ∀ a ∈ 1 :: (t ++ 1 :: FWr n (List.replicate i (n + 1))), a ∈ O13 := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [O13]
      rcases List.mem_append.mp ha with h | h
      · have := ht a h; simp [T3] at this; subst this; simp [O13]
      rcases List.mem_cons.mp h with rfl | h
      · simp [O13]
      · exact hBl a h
    have eF : FWr n (List.replicate (i + 1) (n + 1)) =
        FWr n (List.replicate i (n + 1)) ++ (1 :: (List.replicate s.length 3 ++ [3])) := by
      show FWr n (List.replicate i (n + 1)) ++ blkW n (n + 1) = _
      rw [blkW_full, hn, rep_snoc_eq, List.replicate_succ]
    have hA := blkCopy Jl (b :: Jr') s _ hJl hJr hs hT
    have hS := blkDecStep Jl Jr' s t (FWr n (List.replicate i (n + 1))) b hJl hJr.tail hs ht hBl hJr.head
    have h2 := ih (Jl ++ [b]) (i + 1) (hJl.snoc hJr.head) hJr.tail
    have e : i + 1 + Jr'.length + 1 = i + (b :: Jr').length + 1 := by
      simp only [List.length_cons]; omega
    rw [e] at h2
    refine hA.trans ((hS.of_eq (by simp) rfl).trans (h2.of_eq ?_ (by simp)))
    rw [eF]
    simp



theorem setup (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W F : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W) (hF : NoB F)
    (hFb : ∃ a ∈ F, a ∈ bits)
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: F) :
    ∃ g, 1 ≤ g ∧ zpsLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
      (Bd (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ W F) := by
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
  have hB0 := hA.trans (zpBase_ext_zpsLogic.reach (hr.of_eq (by rw [hcode]) rfl))
  have eT : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = 1 :: (W ++ 1 :: F) := by
    have e : Vq ++ 1 :: (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) =
        (Vq ++ [1]) ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) := by simp
    rw [e, ← hV, List.cons_append, hWF]
  have hVt : NoB (1 :: (W ++ 1 :: F)) := NoB.cons one_nb (hW.app (NoB.cons one_nb hF))
  obtain ⟨p, b, X', eV, hb, hX'⟩ := mb _ hVt (by
    obtain ⟨a, ha, hab⟩ := hFb
    exact ⟨a, List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ ha)), hab⟩)
  have hRr := bits_of_eq hrot
  have hrr : (bitsOf (rot (Pb.reverse ++ [false]))).reverse = 2 :: R'.reverse := by rw [hrot]; simp
  obtain ⟨k, hk⟩ : ∃ k, H.length = k + 1 := ⟨entryOnes (Pb.reverse ++ [false]) + 1, by omega⟩
  cases Xb with
  | nil =>
    have hB := segB R'.reverse [] X' k 0 p 0 b (Or.inl rfl) hb hRr Bits.nil hX'
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zpsLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zpsLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk, bitsOf_cons, bitsOf_reverse]
      simp
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN_some, bitsOf, List.replicate_succ, rep_cons_comm]


/-- One guest run from the setup position, to the dispatch state. -/
theorem runFrom (n : Nat) (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W : List Nat) (ds : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W)
    (hds : Dig n ds) (hne : ds ≠ [])
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: FWr n ds) :
    ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧
      zpsLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
        (RE (run Pb Xb (valr n ds)) W (FWr n ds')) := by
  obtain ⟨g, hg, h1⟩ := setup W1 Vq Pb Xb Rest W (FWr n ds) hV hVq hR hW (FWr_noB n ds)
    (fw_bit n ds hne) hWF
  have hz : (⟨[], Xb.head?, Xb.tail⟩ : Zp).WF := by
    unfold Zp.WF
    cases Xb with
    | nil => intro _; rfl
    | cons x xt => intro h; simp at h
  obtain ⟨ds', hd', hl', h2⟩ := runI n W hW _ _ g _ ds (inv0 Pb) hg hz hds hne rfl
  have ht : (⟨[], Xb.head?, Xb.tail⟩ : Zp).tape = fun i => Xb[i]? := by
    cases Xb <;> rfl
  rw [ht] at h2
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zpsLogic.reach h2)⟩



theorem phase1PS (j s : List Nat) (hj : ∀ a ∈ j, a ∈ bits) (hs : ∀ a ∈ s, a ∈ bits) :
    zpsLogic.Reach1 (L0.den [j, s]) (P1.den [j, s]) := by
  have hA : zpsLogic.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zpsLogic.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zpsLogic.Reach (F1.den [j, s, []]) (P1.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 19)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact (hA.trans hL).trans hB

theorem vStart (J S : Nat) :
    zpsLogic.Reach1 (lay J S) (GCv (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1PS _ _ hj hs
  rw [← lay_den, P1_hdR] at h1
  have hT : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3, 1], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h
      rcases h with rfl | rfl <;> simp [O13]
  have h2 := blkCopy [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT
  have h3 := blkVer (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3) hj hs
    (rep_t3 _)
  refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq ?_ ?_))
  · simp [rep_cons_comm]
  · unfold GCv
    simp [bitsOf, blkW, List.replicate_succ, rep_cons_comm]


/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zpsLogic.Reach (TR (bitsOf Jb) Sb b)
      (hdR (dpOf (bn (run Jb Sb (clock Jb Sb)))) [1]
        (bitsOf Jb ++ 1 :: (bitsOf Sb ++ 1 :: (1 :: (tflag b ++ 1 :: Fu))))) := by
  have hj := Bits.ofB Jb
  have hs := Bits.ofB Sb
  have ht : ∀ a ∈ tflag b, a ∈ T3 := by cases b <;> simp [tflag, T3]
  have h1 := decFuel (bitsOf Sb) (tflag b) Sb.length (bitsOf_len Sb) hs ht (bitsOf Jb) [] 0 Bits.nil hj
  have e : 0 + (bitsOf Jb).length + 1 = Jb.length + 1 := by rw [bitsOf_len]; omega
  rw [e] at h1
  have hW : NoB (bitsOf Jb ++ 1 :: (bitsOf Sb ++ 1 :: (1 :: tflag b))) :=
    hj.noB.app (NoB.cons one_nb (hs.noB.app (NoB.cons one_nb (NoB.cons one_nb (t3_noB ht)))))
  have hR : Sym4 (1 :: (tflag b ++ 1 :: FWr Sb.length (List.replicate (Jb.length + 1) (Sb.length + 1)))) :=
    NoB.sym4 (NoB.cons one_nb ((t3_noB ht).app (NoB.cons one_nb (FWr_noB _ _))))
  obtain ⟨ds', -, -, h2⟩ := runFrom Sb.length [] [] Jb Sb _ _ (List.replicate (Jb.length + 1) (Sb.length + 1))
    rfl NoB.nil hR hW (fun d hd => by rw [List.eq_of_mem_replicate hd]; exact Nat.le_refl _) (by simp)
    (by simp)
  have hv : valr Sb.length (List.replicate (Jb.length + 1) (Sb.length + 1)) = clock Jb Sb := by
    have := valr_full Sb.length (Jb.length + 1)
    unfold clock
    omega
  rw [hv] at h2
  exact ⟨FWr Sb.length ds', FWr_noB _ _,
    (h1.of_eq (by simp [TR, FWr]) (by simp)).trans (h2.of_eq rfl (by unfold RE; simp))⟩


theorem sincL (A : List Nat) (hA : NoB A) : ∀ (r : List Bool) (k : Nat),
    zpsLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
      (hdR Q.GRB (A ++ 1 :: (bitsOf (incR r).reverse ++ List.replicate k 2)) [])
  | [], k => (sincE A (List.replicate k 2) hA (rep_z2 k)).of_eq rfl (by rw [rep_snoc_eq]; rfl)
  | false :: r, k =>
    (sinc0 A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) (by simp [incR, bitsOf])
  | true :: r, k =>
    ((sinc1 A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) rfl).trans
      ((sincL A hA r (k + 1)).of_eq rfl (by simp [incR, bitsOf, List.replicate_succ]))


theorem jincL : ∀ (r : List Bool) (k : Nat),
    zpsLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
      (hdR Q.GRB (1 :: (bitsOf (incR r).reverse ++ (List.replicate k 2 ++ [1]))) [])
  | [], k => (jincE (List.replicate k 2) (rep_z2 k)).of_eq rfl (by rw [rep_cons_comm]; rfl)
  | false :: r, k =>
    (jinc0 (bitsOf r.reverse) (List.replicate k 2) (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) (by simp [incR, bitsOf])
  | true :: r, k =>
    ((jinc1 (bitsOf r.reverse) (List.replicate k 2) (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) rfl).trans
      ((jincL r (k + 1)).of_eq rfl (by simp [incR, bitsOf, List.replicate_succ]))


/-- The one step out of the beep state. -/
theorem beepStep (j s Y : List Nat) :
    zpsLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1].reverse,
      [.blk 2 .id], true⟩ : SC).den [j, s, Y] = hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)





/-! ## The walker (generated) -/

/-- After a verifier run with result 0, `|C| = 1`: the walker starts at the last bit. -/
theorem toWK1_0 (j : List Nat) (s : List Nat) (Fu : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) (hc : c ∈ bits) :
    zpsLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (1 :: (Fu))))))))
      (hd QPS.WK0E (1 :: (j ++ (1 :: (s ++ (1 :: ([c])))))) (1 :: (Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  rcases mem_bits hc with rfl | rfl
  · exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- After a verifier run with result 0, `|C| ≥ 2`: the walker starts at the last bit. -/
theorem toWK2_0 (j : List Nat) (s : List Nat) (Cm : List Nat) (Fu : List Nat) (c0 : Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCm : Bits Cm) (hFu : NoB Fu) (hc0 : c0 ∈ bits) (hc : c ∈ bits) :
    zpsLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (c0 :: (Cm ++ (c :: (1 :: (Fu))))))))))
      (hd QPS.WK0E (1 :: (j ++ (1 :: (s ++ (1 :: (c0 :: (Cm ++ ([c])))))))) (1 :: (Fu))) := by
  have hV : Valid [bits, bits, bits, NB] [j, s, Cm, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hCm (Valid.cons hFu (Valid.nil _))))
  rcases mem_bits hc0 with rfl | rfl <;> rcases mem_bits hc with rfl | rfl
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 2, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 2]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 2, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 2]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- After a verifier run with result 1, `|C| = 1`: the walker starts at the last bit. -/
theorem toWK1_1 (j : List Nat) (s : List Nat) (Fu : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) (hc : c ∈ bits) :
    zpsLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (1 :: (Fu))))))))
      (hd QPS.WK1E (1 :: (j ++ (1 :: (s ++ (1 :: ([c])))))) (1 :: (Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  rcases mem_bits hc with rfl | rfl
  · exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- After a verifier run with result 1, `|C| ≥ 2`: the walker starts at the last bit. -/
theorem toWK2_1 (j : List Nat) (s : List Nat) (Cm : List Nat) (Fu : List Nat) (c0 : Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCm : Bits Cm) (hFu : NoB Fu) (hc0 : c0 ∈ bits) (hc : c ∈ bits) :
    zpsLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c0 :: (Cm ++ (c :: (1 :: (Fu))))))))))
      (hd QPS.WK1E (1 :: (j ++ (1 :: (s ++ (1 :: (c0 :: (Cm ++ ([c])))))))) (1 :: (Fu))) := by
  have hV : Valid [bits, bits, bits, NB] [j, s, Cm, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hCm (Valid.cons hFu (Valid.nil _))))
  rcases mem_bits hc0 with rfl | rfl <;> rcases mem_bits hc with rfl | rfl
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 2, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 2]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 2, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 2]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, Cm, Fu]) (E := []) (k := 8) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3]) (rs' := [.sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `0` bit: set it to `1`, go up. -/
theorem wk0_0E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0E (Y ++ ([2])) (R))
      (hd QPS.WK0A (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `1` bit, result not dominant: start the second child. -/
theorem wk1n_0E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0E (Y ++ ([3])) (R))
      (hdR Q.VFE (Y ++ ([2])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `0` bit: set it to `1`, go up. -/
theorem wk0_0A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0A (Y ++ ([2])) (R))
      (hd QPS.WK0E (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `1` bit, result dominant: go up. -/
theorem wk1d_0A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0A (Y ++ ([3])) (R))
      (hd QPS.WK0E (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker reached `M_2`. -/
theorem wkM_0E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0E (Y ++ ([1])) (R))
      (hdR Q.VU2 (Y ++ ([1])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker reached `M_2`. -/
theorem wkM_0A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK0A (Y ++ ([1])) (R))
      (hdR Q.VU2 (Y ++ ([1])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `0` bit: set it to `1`, go up. -/
theorem wk0_1E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1E (Y ++ ([2])) (R))
      (hd QPS.WK1A (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `1` bit, result dominant: go up. -/
theorem wk1d_1E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1E (Y ++ ([3])) (R))
      (hd QPS.WK1A (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `0` bit: set it to `1`, go up. -/
theorem wk0_1A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1A (Y ++ ([2])) (R))
      (hd QPS.WK1E (Y) (3 :: (R))) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker on a `1` bit, result not dominant: start the second child. -/
theorem wk1n_1A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1A (Y ++ ([3])) (R))
      (hdR Q.VFE (Y ++ ([2])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker reached `M_2`. -/
theorem wkM_1E (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1E (Y ++ ([1])) (R))
      (hdR QPS.VA1 (Y ++ ([1])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Walker reached `M_2`. -/
theorem wkM_1A (Y : List Nat) (R : List Nat) (hY : NoB Y) (hR : NoB R) :
    zpsLogic.Reach (hd QPS.WK1A (Y ++ ([1])) (R))
      (hdR QPS.VA1 (Y ++ ([1])) (R)) := by
  have hV : Valid [NB, NB] [Y, R] := Valid.cons hY (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Y, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Second child: refill the fuel and run again. -/
theorem refill (j : List Nat) (s : List Nat) (X : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (hj : Bits j) (hs : Bits s) (hX : Bits X) (hZ : ∀ a ∈ Z, a ∈ T3) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) :
    zpsLogic.Reach (hdR Q.VFE (1 :: (j ++ (1 :: (s ++ (1 :: (X ++ ([2]))))))) (Z ++ (1 :: (1 :: (D ++ (E))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (X ++ (2 :: (Z ++ (1 :: (1 :: (D ++ (List.replicate E.length 3)))))))) := by
  have hV : Valid [bits, bits, bits, T3, T3, Z2] [j, s, X, Z, D, E] := Valid.cons hj (Valid.cons hs (Valid.cons hX (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.nil _))))))
  exact checkFF (env := [j, s, X, Z, D, E]) (E := []) (k := 24) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 2]) (rs := [.blk 3 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 2, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Root value `1`, `|C| = 1`. -/
theorem rootT1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR QPS.VA1 (1 :: (j ++ (1 :: (s ++ ([1]))))) (3 :: (1 :: (Fu))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFF (env := [j, s, Fu]) (E := []) (k := 8) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Root value `1`. -/
theorem rootT2 (j : List Nat) (s : List Nat) (Cq : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hCq : ∀ a ∈ Cq, a ∈ T3) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR QPS.VA1 (1 :: (j ++ (1 :: (s ++ ([1]))))) (3 :: (3 :: (Cq ++ (1 :: (Fu))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [bits, bits, T3, NB] [j, s, Cq, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hCq (Valid.cons hFu (Valid.nil _))))
  exact checkFF (env := [j, s, Cq, Fu]) (E := []) (k := 12) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs := [.sym 3, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Root value `0`. -/
theorem rootF (j : List Nat) (s : List Nat) (Cq : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hCq : ∀ a ∈ Cq, a ∈ T3) (hFu : NoB Fu) :
    zpsLogic.Reach (hdR Q.VU2 (1 :: (j ++ (1 :: (s ++ ([1]))))) (3 :: (Cq ++ (1 :: (Fu)))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: ([1]))))))) ([])) := by
  have hV : Valid [bits, bits, T3, NB] [j, s, Cq, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hCq (Valid.cons hFu (Valid.nil _))))
  exact checkFF (env := [j, s, Cq, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## The game tree -/

/-- The walker state for a finished node with `d` levels below it. -/
def wkQ (r : Bool) (d : Nat) : Nat :=
  if r then (if d % 2 = 0 then QPS.WK1E else QPS.WK1A)
  else (if d % 2 = 0 then QPS.WK0E else QPS.WK0A)

/-- The walker has finished the node with prefix `p` and `d` levels below it, value `r`. -/
def WKcfg (j : List Nat) (Sb p : List Bool) (d : Nat) (r : Bool) (dd : Nat) : ZC :=
  hd (wkQ r d) (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p)))
    (List.replicate d 3 ++ 1 :: FWr Sb.length [dd])

/-- The run of the verifier from `GCv`: its result is passed to the dispatch. -/
theorem runPS (j : List Nat) (hj : Bits j) (Sb cl : List Bool) (hcl : cl.length = Sb.length + 1) :
    ∃ d, d ≤ Sb.length + 1 ∧
      zpsLogic.Reach (GCv j Sb cl)
        (hdR (dpOf (bn (run Sb cl.reverse (Sb.length + 1)))) [1]
          (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: FWr Sb.length [d])))) := by
  have hW : NoB (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) :=
    hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)))
  obtain ⟨ds', hd', hl', h⟩ := runFrom Sb.length (j ++ [1]) (1 :: j) Sb cl.reverse
    (blkW Sb.length (Sb.length + 1)) (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf cl.reverse)) [Sb.length + 1]
    rfl (NoB.cons one_nb hj.noB) (blkW_noB _ _).sym4 hW
    (fun d hd => by simp at hd; omega) (by simp) (by simp [FWr])
  have hv : valr Sb.length [Sb.length + 1] = Sb.length + 1 := by simp [valr]
  rw [hv] at h
  obtain ⟨d, rfl⟩ : ∃ d, ds' = [d] := by
    rcases ds' with _ | ⟨d, _ | ⟨e, t⟩⟩
    · simp at hl'
    · exact ⟨d, rfl⟩
    · simp at hl'
  refine ⟨d, hd' d (by simp), ?_⟩
  unfold RE at h
  unfold GCv
  simpa using h


theorem toWK (j : List Nat) (hj : Bits j) (Sb p : List Bool) (hp : p ≠ []) (o : Bool) (Fu : List Nat)
    (hFu : NoB Fu) :
    zpsLogic.Reach (hdR (dpOf (bn o)) [1] (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf p ++ 1 :: Fu))))
      (hd (wkQ o 0) (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p))) (1 :: Fu)) := by
  rcases p with _ | ⟨c, rest⟩
  · exact absurd rfl hp
  rcases List.eq_nil_or_concat rest with rfl | ⟨Cm, c1, rfl⟩
  · cases o
    · exact (toWK1_0 j (bitsOf Sb) Fu (bn c) hj (Bits.ofB _) hFu (bn_bits c)).of_eq
        (by simp [dpOf, bn, bitsOf]) (by simp [wkQ, QPS.WK0E, bitsOf, bn])
    · exact (toWK1_1 j (bitsOf Sb) Fu (bn c) hj (Bits.ofB _) hFu (bn_bits c)).of_eq
        (by simp [dpOf, bn, bitsOf]) (by simp [wkQ, bitsOf, bn])
  · cases o
    · exact (toWK2_0 j (bitsOf Sb) (bitsOf Cm) Fu (bn c) (bn c1) hj (Bits.ofB _) (Bits.ofB _) hFu
        (bn_bits c) (bn_bits c1)).of_eq (by simp [dpOf, bn, bitsOf]) (by simp [wkQ, bitsOf, bn])
    · exact (toWK2_1 j (bitsOf Sb) (bitsOf Cm) Fu (bn c) (bn c1) hj (Bits.ofB _) (Bits.ofB _) hFu
        (bn_bits c) (bn_bits c1)).of_eq (by simp [dpOf, bn, bitsOf]) (by simp [wkQ, bitsOf, bn])


theorem rep_succ_cons (d : Nat) : 3 :: List.replicate d 3 = List.replicate (d + 1) 3 := rfl

theorem wk0_gen (Y R : List Nat) (hY : NoB Y) (hR : NoB R) (b : Bool) (d : Nat) :
    zpsLogic.Reach (hd (wkQ b d) (Y ++ [2]) R) (hd (wkQ b (d + 1)) Y (3 :: R)) := by
  by_cases h : d % 2 = 0
  · have h' : ¬ (d + 1) % 2 = 0 := by omega
    cases b
    · simpa [wkQ, h, h'] using wk0_0E Y R hY hR
    · simpa [wkQ, h, h'] using wk0_1E Y R hY hR
  · have h' : (d + 1) % 2 = 0 := by omega
    cases b
    · simpa [wkQ, h, h'] using wk0_0A Y R hY hR
    · simpa [wkQ, h, h'] using wk0_1A Y R hY hR

theorem wk1d_gen (Y R : List Nat) (hY : NoB Y) (hR : NoB R) (b : Bool) (d : Nat)
    (hdom : (b == (d % 2 == 0)) = true) :
    zpsLogic.Reach (hd (wkQ b d) (Y ++ [3]) R) (hd (wkQ b (d + 1)) Y (3 :: R)) := by
  by_cases h : d % 2 = 0
  · have h' : ¬ (d + 1) % 2 = 0 := by omega
    cases b
    · simp [h] at hdom
    · simpa [wkQ, h, h'] using wk1d_1E Y R hY hR
  · have h' : (d + 1) % 2 = 0 := by omega
    cases b
    · simpa [wkQ, h, h'] using wk1d_0A Y R hY hR
    · simp [h] at hdom

theorem wk1n_gen (Y R : List Nat) (hY : NoB Y) (hR : NoB R) (b : Bool) (d : Nat)
    (hdom : ¬ (b == (d % 2 == 0)) = true) :
    zpsLogic.Reach (hd (wkQ b d) (Y ++ [3]) R) (hdR Q.VFE (Y ++ [2]) R) := by
  by_cases h : d % 2 = 0
  · cases b
    · simpa [wkQ, h] using wk1n_0E Y R hY hR
    · simp [h] at hdom
  · cases b
    · simp [h] at hdom
    · simpa [wkQ, h] using wk1n_1A Y R hY hR


/-- Running the subtree at prefix `p` (with `d` levels below) from the first leaf. -/
theorem nodePS (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    ∀ d (p : List Bool), p.length + d = Sb.length + 1 →
      ∃ dd, dd ≤ Sb.length + 1 ∧ zpsLogic.Reach (GCv j Sb (p ++ List.replicate d true).reverse)
        (WKcfg j Sb p d (gval Sb d p) dd) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hp' : p.length = Sb.length + 1 := by omega
    obtain ⟨dd, hdd, h⟩ := runPS j hj Sb p.reverse (by simp [hp'])
    have hne : p ≠ [] := by
      intro e; rw [e] at hp'; simp at hp'
    refine ⟨dd, hdd, ?_⟩
    have hT := toWK j hj Sb p hne (run Sb p (Sb.length + 1)) (FWr Sb.length [dd]) (FWr_noB _ _)
    simp only [List.reverse_reverse] at h
    simp only [List.replicate_zero, List.append_nil]
    refine h.trans (hT.of_eq rfl ?_)
    simp [WKcfg, gval]
  | succ d ih =>
    intro p hp
    have hq : (p ++ [true]).length + d = Sb.length + 1 := by simp; omega
    obtain ⟨dd, hdd, h1⟩ := ih (p ++ [true]) hq
    have e1 : (p ++ [true]) ++ List.replicate d true = p ++ List.replicate (d + 1) true := by
      simp [List.replicate_succ]
    rw [e1] at h1
    have hY : NoB (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p))) :=
      NoB.cons one_nb (hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app
        (NoB.cons one_nb (Bits.ofB _).noB))))
    have hR : NoB (List.replicate d 3 ++ 1 :: FWr Sb.length [dd]) :=
      (t3_noB (rep_t3 d)).app (NoB.cons one_nb (FWr_noB _ _))
    have hL1 : WKcfg j Sb (p ++ [true]) d (gval Sb d (p ++ [true])) dd =
        hd (wkQ (gval Sb d (p ++ [true])) d) (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p)) ++ [3])
          (List.replicate d 3 ++ 1 :: FWr Sb.length [dd]) := by
      simp [WKcfg, bitsOf]
    rw [hL1] at h1
    by_cases hdom : (gval Sb d (p ++ [true]) == (d % 2 == 0)) = true
    · refine ⟨dd, hdd, h1.trans ?_⟩
      have hv : gval Sb (d + 1) p = gval Sb d (p ++ [true]) := by
        simp only [gval]
        rw [if_pos hdom]
      rw [hv]
      refine (wk1d_gen _ _ hY hR _ d hdom).of_eq rfl ?_
      simp [WKcfg, List.replicate_succ]
    · -- second child
      have hdom' : ¬ (gval Sb d (p ++ [true]) == (d % 2 == 0)) = true := hdom
      have hv : gval Sb (d + 1) p = gval Sb d (p ++ [false]) := by
        simp only [gval]
        rw [if_neg hdom]
      have hq' : (p ++ [false]).length + d = Sb.length + 1 := by simp; omega
      obtain ⟨dd', hdd', h2⟩ := ih (p ++ [false]) hq'
      have e2 : (p ++ [false]) ++ List.replicate d true = p ++ false :: List.replicate d true := by
        simp
      rw [e2] at h2
      have hF : FWr Sb.length [dd] = 1 :: (List.replicate dd 3 ++ List.replicate (Sb.length + 1 - dd) 2) := by
        simp [FWr, blkW]
      have hRef := refill j (bitsOf Sb) (bitsOf p) (List.replicate d 3) (List.replicate dd 3)
        (List.replicate (Sb.length + 1 - dd) 2) hj (Bits.ofB _) (Bits.ofB _) (rep_t3 _) (rep_t3 _)
        (rep_z2 _)
      have hDE : List.replicate dd 3 ++ List.replicate (Sb.length + 1 - dd) 3 = List.replicate (Sb.length + 1) 3 := by
        rw [List.replicate_append_replicate]; congr 1; omega
      have h3 : zpsLogic.Reach (hdR Q.VFE (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p)) ++ [2])
          (List.replicate d 3 ++ 1 :: FWr Sb.length [dd]))
          (GCv j Sb (p ++ false :: List.replicate d true).reverse) := by
        refine hRef.of_eq (by simp [hF]) ?_
        unfold GCv
        simp [bitsOf, blkW, hDE]
      have hR' : NoB (List.replicate d 3 ++ 1 :: FWr Sb.length [dd']) :=
        (t3_noB (rep_t3 d)).app (NoB.cons one_nb (FWr_noB _ _))
      have hL2 : WKcfg j Sb (p ++ [false]) d (gval Sb d (p ++ [false])) dd' =
          hd (wkQ (gval Sb d (p ++ [false])) d) (1 :: (j ++ 1 :: (bitsOf Sb ++ 1 :: bitsOf p)) ++ [2])
            (List.replicate d 3 ++ 1 :: FWr Sb.length [dd']) := by
        simp [WKcfg, bitsOf]
      rw [hL2] at h2
      refine ⟨dd', hdd', h1.trans ((wk1n_gen _ _ hY hR _ d hdom).trans (h3.trans (h2.trans ?_)))⟩
      rw [hv]
      refine (wk0_gen _ _ hY hR' _ d).of_eq rfl ?_
      simp [WKcfg, List.replicate_succ]


theorem wkM_true (Y R : List Nat) (hY : NoB Y) (hR : NoB R) (d : Nat) :
    zpsLogic.Reach (hd (wkQ true d) (Y ++ [1]) R) (hdR QPS.VA1 (Y ++ [1]) R) := by
  by_cases h : d % 2 = 0
  · simpa [wkQ, h] using wkM_1E Y R hY hR
  · simpa [wkQ, h] using wkM_1A Y R hY hR

theorem wkM_false (Y R : List Nat) (hY : NoB Y) (hR : NoB R) (d : Nat) :
    zpsLogic.Reach (hd (wkQ false d) (Y ++ [1]) R) (hdR Q.VU2 (Y ++ [1]) R) := by
  by_cases h : d % 2 = 0
  · simpa [wkQ, h] using wkM_0E Y R hY hR
  · simpa [wkQ, h] using wkM_0A Y R hY hR

/-- The whole verifier: it leaves the truth flag `inPS s`. -/
theorem vFullPS (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    zpsLogic.Reach (GCv j Sb (List.replicate (Sb.length + 1) true)) (TR j Sb (inPS Sb)) := by
  obtain ⟨dd, hdd, h⟩ := nodePS j hj Sb (Sb.length + 1) [] (by simp)
  simp only [List.nil_append, List.reverse_replicate] at h
  have hY : NoB (1 :: (j ++ 1 :: bitsOf Sb)) :=
    NoB.cons one_nb (hj.noB.app (NoB.cons one_nb (Bits.ofB _).noB))
  have hR : NoB (List.replicate (Sb.length + 1) 3 ++ 1 :: FWr Sb.length [dd]) :=
    (t3_noB (rep_t3 _)).app (NoB.cons one_nb (FWr_noB _ _))
  have hL : WKcfg j Sb [] (Sb.length + 1) (gval Sb (Sb.length + 1) []) dd =
      hd (wkQ (gval Sb (Sb.length + 1) []) (Sb.length + 1)) (1 :: (j ++ 1 :: bitsOf Sb) ++ [1])
        (List.replicate (Sb.length + 1) 3 ++ 1 :: FWr Sb.length [dd]) := by
    simp [WKcfg, bitsOf]
  rw [hL] at h
  have hinPS : inPS Sb = gval Sb (Sb.length + 1) [] := rfl
  rw [hinPS]
  refine h.trans ?_
  cases hr : gval Sb (Sb.length + 1) [] with
  | true =>
    refine (wkM_true _ _ hY hR _).trans ?_
    by_cases hn : Sb.length = 0
    · have := rootT1 j (bitsOf Sb) (FWr Sb.length [dd]) hj (Bits.ofB _) (FWr_noB _ _)
      refine this.of_eq (by rw [hn]; simp [List.replicate_succ]) (by simp [TR, tflag])
    · have := rootT2 j (bitsOf Sb) (List.replicate (Sb.length - 1) 3) (FWr Sb.length [dd]) hj
        (Bits.ofB _) (rep_t3 _) (FWr_noB _ _)
      refine this.of_eq (by
        rw [show Sb.length + 1 = (Sb.length - 1) + 1 + 1 by omega]
        simp [List.replicate_succ]) (by simp [TR, tflag])
  | false =>
    refine (wkM_false _ _ hY hR _).trans ?_
    have := rootF j (bitsOf Sb) (List.replicate Sb.length 3) (FWr Sb.length [dd]) hj (Bits.ofB _)
      (rep_t3 _) (FWr_noB _ _)
    refine this.of_eq (by simp [List.replicate_succ]) (by simp [TR, tflag])

/-! ## One pair -/

theorem pair_mainPS (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectPS J S → zpsLogic.zrun n (lay J S) = some (lay (absStepC CorrectPS (J, S)).1 (absStepC CorrectPS (J, S)).2)) ∧
       (¬ CorrectPS J S → ∃ a c1 c2, a < n ∧ zpsLogic.zrun a (lay J S) = some c1 ∧ c1.q = zpsLogic.beep ∧
          zpsLogic.zstep c1 = some c2 ∧
          zpsLogic.zrun (n - a - 1) c2 = some (lay (absStepC CorrectPS (J, S)).1 (absStepC CorrectPS (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨Fu, hFu, hD⟩ := dPhase (str J) (str S) (inPS (str S))
  have hA := (vStart J S).trans ((vFullPS _ hj (str S)).trans hD)
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectPS J S
  · have e : absStepC CorrectPS (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = inPS (str S) := hc
    rw [ho] at hA
    have hok : zpsLogic.Reach
        (hdR (dpOf (bn (inPS (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inPS (str S)) ++ 1 :: Fu)))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inPS (str S)
      · exact (dOk0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
      · exact (dOk1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
    have hinc := sincL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.of_eq (c4 := lay J (S + 1)) (by rw [eS]; rfl) (by rw [lay_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectPS (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = !inPS (str S) := by
      have h' : run (str J) (str S) (clock (str J) (str S)) ≠ inPS (str S) := hc
      revert h'
      cases run (str J) (str S) (clock (str J) (str S)) <;> cases inPS (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zpsLogic.Reach
        (hdR (dpOf (bn (!inPS (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inPS (str S)) ++ 1 :: Fu)))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zpsLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inPS (str S)
      · exact ⟨1 :: Fu, (dBad1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad1E _ _ Fu hj hs hFu⟩
      · exact ⟨3 :: 1 :: Fu, (dBad0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad0E _ _ Fu hj hs hFu⟩
    obtain ⟨n1, hn1⟩ := hA.trans h1
    obtain ⟨n2, hn2⟩ := h3.trans ((jincL rJ 0).of_eq (c4 := lay (J + 1) 1) (by rw [eJ]; rfl) (by rw [lay_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, beepStep _ _ Y, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2


end ZP.PS
