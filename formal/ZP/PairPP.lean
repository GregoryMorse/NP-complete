module

public import ZP.Pair
public import ZP.CompilePP
public import ZP.DefsPP
public import ZP.Count

@[expose] public section

/-! The pair lemma for the P = PP machine, copied from `ZP/Pair.lean` and adapted. -/

namespace ZP.PP

open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zppLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zppLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
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


/-- Decider fuel block done, the walker steps right. -/
theorem blkDecStep (Jl : List Nat) (Jr : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (b : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) (hb : b ∈ bits) :
    zppLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
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
    zppLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, O13] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 35) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zppLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
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
    zppLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zppLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zppLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: Rest))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: Rest)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zppLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zppLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Verifier rejected at `C = 0`: truth flag `0`. -/
theorem vUnder (j : List Nat) (s : List Nat) (Z : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (2 :: (Z ++ (1 :: Fu))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: [1])))))) []) := by
  have hV : Valid [bits, bits, Z2, NB] [j, s, Z, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hFu (Valid.nil _))))
  exact checkFF (env := [j, s, Z, Fu]) (E := []) (k := 21) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zppLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR Q.GRB (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR Q.GRB (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR Q.GRB (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR Q.GRB (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zppLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zppLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
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
    zppLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zppLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zppLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zppLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zppLogic.Reach
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
    ∃ g, 1 ≤ g ∧ zppLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  have hB0 := hA.trans (zpBase_ext_zppLogic.reach (hr.of_eq (by rw [hcode]) rfl))
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
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zppLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zppLogic.reach (hB.of_eq ?_ ?_))⟩
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
      zppLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zppLogic.reach h2)⟩



/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zppLogic.Reach (TR (bitsOf Jb) Sb b)
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
    zppLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
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
    zppLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
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
    zppLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1].reverse,
      [.blk 2 .id], true⟩ : SC).den [j, s, Y] = hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)


/-! ## Dispatch after a verifier run (generated; see `plans/02-zpp.md`) -/

/-- Verifier rejected, `C = 1 0^k`: `C -= 1`, refill the fuel, run again. -/
theorem rejE (j : List Nat) (s : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (A : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hA : Bits A) :
    zppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (3 :: (Z ++ (1 :: (A ++ (1 :: (1 :: (D ++ (E)))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (2 :: (List.replicate Z.length 3 ++ (1 :: (A ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))) := by
  have hV : Valid [bits, bits, Z2, T3, Z2, bits] [j, s, Z, D, E, A] := Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.cons hA (Valid.nil _))))))
  exact checkFF (env := [j, s, Z, D, E, A]) (E := []) (k := 36) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 5 .id, .sym 1, .sym 1, .blk 3 .id, .blk 4 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 (.const 3), .sym 1, .blk 5 .id, .sym 1, .sym 1, .blk 3 .id, .blk 4 (.const 3)])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier rejected, `C = c C' 1 0^k`. -/
theorem rejC (j : List Nat) (s : List Nat) (Cp : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (A : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCp : Bits Cp) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hA : Bits A) (hc : c ∈ bits) :
    zppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (3 :: (Z ++ (1 :: (A ++ (1 :: (1 :: (D ++ (E)))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (c :: (Cp ++ (2 :: (List.replicate Z.length 3 ++ (1 :: (A ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))))) := by
  have hV : Valid [bits, bits, bits, Z2, T3, Z2, bits] [j, s, Cp, Z, D, E, A] := Valid.cons hj (Valid.cons hs (Valid.cons hCp (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.cons hA (Valid.nil _)))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Cp, Z, D, E, A]) (E := []) (k := 40) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, D, E, A]) (E := []) (k := 40) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted, `A` does not reach its threshold, `C = 1 0^k`: `A -= 1`, `C -= 1`, refill. -/
theorem accEnt (j : List Nat) (s : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (Ul : List Nat) (Za : List Nat) (x : Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hx : x ∈ bits) :
    zppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (3 :: (Z ++ (1 :: (Ul ++ (x :: (3 :: (Za ++ (1 :: (1 :: (D ++ (E))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (2 :: (List.replicate Z.length 3 ++ (1 :: (Ul ++ (x :: (2 :: (List.replicate Za.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3)))))))))))) := by
  have hV : Valid [bits, bits, Z2, T3, Z2, bits, Z2] [j, s, Z, D, E, Ul, Za] := Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.cons hUl (Valid.cons hZa (Valid.nil _)))))))
  rcases mem_bits hx with rfl | rfl
  · exact checkFF (env := [j, s, Z, D, E, Ul, Za]) (E := []) (k := 52) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 5 .id, .sym 2, .sym 3, .blk 6 .id, .sym 1, .sym 1, .blk 3 .id, .blk 4 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 (.const 3), .sym 1, .blk 5 .id, .sym 2, .sym 2, .blk 6 (.const 3), .sym 1, .sym 1, .blk 3 .id, .blk 4 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Z, D, E, Ul, Za]) (E := []) (k := 52) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 5 .id, .sym 3, .sym 3, .blk 6 .id, .sym 1, .sym 1, .blk 3 .id, .blk 4 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 (.const 3), .sym 1, .blk 5 .id, .sym 3, .sym 2, .blk 6 (.const 3), .sym 1, .sym 1, .blk 3 .id, .blk 4 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted, `A` below threshold, `C = c C' 1 0^k`. -/
theorem accCnt (j : List Nat) (s : List Nat) (Cp : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (Ul : List Nat) (Za : List Nat) (c : Nat) (x : Nat) (hj : Bits j) (hs : Bits s) (hCp : Bits Cp) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hc : c ∈ bits) (hx : x ∈ bits) :
    zppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (3 :: (Z ++ (1 :: (Ul ++ (x :: (3 :: (Za ++ (1 :: (1 :: (D ++ (E))))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (c :: (Cp ++ (2 :: (List.replicate Z.length 3 ++ (1 :: (Ul ++ (x :: (2 :: (List.replicate Za.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3)))))))))))))) := by
  have hV : Valid [bits, bits, bits, Z2, T3, Z2, bits, Z2] [j, s, Cp, Z, D, E, Ul, Za] := Valid.cons hj (Valid.cons hs (Valid.cons hCp (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.cons hUl (Valid.cons hZa (Valid.nil _))))))))
  rcases mem_bits hc with rfl | rfl <;> rcases mem_bits hx with rfl | rfl
  · exact checkFF (env := [j, s, Cp, Z, D, E, Ul, Za]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 2, .sym 3, .blk 7 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 2, .sym 2, .blk 7 (.const 3), .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, D, E, Ul, Za]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 3, .sym 3, .blk 7 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 3, .sym 2, .blk 7 (.const 3), .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, D, E, Ul, Za]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 2, .sym 3, .blk 7 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 2, .sym 2, .blk 7 (.const 3), .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, D, E, Ul, Za]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 6 .id, .sym 3, .sym 3, .blk 7 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 6 .id, .sym 3, .sym 2, .blk 7 (.const 3), .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted, `A` below threshold, `C = 0^k`: truth flag `0`. -/
theorem accUnt (j : List Nat) (s : List Nat) (Z : List Nat) (Ul : List Nat) (Za : List Nat) (Fu : List Nat) (x : Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hFu : NoB Fu) (hx : x ∈ bits) :
    zppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (2 :: (Z ++ (1 :: (Ul ++ (x :: (3 :: (Za ++ (1 :: (Fu))))))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: ([1]))))))) ([])) := by
  have hV : Valid [bits, bits, Z2, bits, Z2, NB] [j, s, Z, Ul, Za, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hUl (Valid.cons hZa (Valid.cons hFu (Valid.nil _))))))
  rcases mem_bits hx with rfl | rfl
  · exact checkFF (env := [j, s, Z, Ul, Za, Fu]) (E := []) (k := 41) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 2, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Z, Ul, Za, Fu]) (E := []) (k := 41) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted, `A` reaches its threshold, `|C| = 1`: truth flag `1`. -/
theorem accThr1 (j : List Nat) (s : List Nat) (Za : List Nat) (Fu : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hZa : ∀ a ∈ Za, a ∈ Z2) (hFu : NoB Fu) (hc : c ∈ bits) :
    zppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (1 :: (3 :: (Za ++ (1 :: (Fu)))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [bits, bits, Z2, NB] [j, s, Za, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hZa (Valid.cons hFu (Valid.nil _))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Za, Fu]) (E := []) (k := 27) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Za, Fu]) (E := []) (k := 27) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted, `A` reaches its threshold: truth flag `1`. -/
theorem accThr2 (j : List Nat) (s : List Nat) (Cq : List Nat) (Za : List Nat) (Fu : List Nat) (c : Nat) (y : Nat) (hj : Bits j) (hs : Bits s) (hCq : Bits Cq) (hZa : ∀ a ∈ Za, a ∈ Z2) (hFu : NoB Fu) (hc : c ∈ bits) (hy : y ∈ bits) :
    zppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (y :: (Cq ++ (1 :: (3 :: (Za ++ (1 :: (Fu)))))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [bits, bits, bits, Z2, NB] [j, s, Cq, Za, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hCq (Valid.cons hZa (Valid.cons hFu (Valid.nil _)))))
  rcases mem_bits hc with rfl | rfl <;> rcases mem_bits hy with rfl | rfl
  · exact checkFF (env := [j, s, Cq, Za, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 2, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## Building `C`, `A` and the verifier fuel -/

/-- The second `BLK` (the accept counter `A`) is done: write `M_4`, start the fuel `BLK`. -/
theorem blkA (j : List Nat) (s : List Nat) (C : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) :
    zppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (List.replicate s.length 3))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (3 :: (C ++ (1 :: (List.replicate s.length 3 ++ (3 :: ([1]))))))))))) ([])) := by
  have hV : Valid [bits, bits, T3] [j, s, C] := Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.nil _)))
  exact checkFF (env := [j, s, C]) (E := []) (k := 27) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 1 (.const 3), .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Fuel block done: write `H`, go to the guest source `C`. -/
theorem blkVerPP (j : List Nat) (s : List Nat) (C : List Nat) (A : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hA : ∀ a ∈ A, a ∈ T3) :
    zppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (1 :: (List.replicate s.length 3)))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (3 :: (C ++ (1 :: (A ++ (1 :: (1 :: (List.replicate s.length 3 ++ ([3]))))))))) := by
  have hV : Valid [bits, bits, T3, T3] [j, s, C, A] := Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hA (Valid.nil _))))
  exact checkFF (env := [j, s, C, A]) (E := []) (k := 47) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 1 (.const 3)])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- `BLK` for `A`: starts like the `GRB` step, from `BD6` on the blank after `C`. -/
theorem blkStart2 (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zppLogic.Reach (hdR Q.BD6 (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `M_g J M_1 s M_2 C`, state `BD6` on the blank after `C`. -/
def P1pre : SC := ⟨Q.BD6, [.sym 3, .blk 1 (.const 3), .sym 1, .blk 1 .id, .sym 1,
  .blk 0 .id, .sym 1], [], false⟩

theorem phase1PP (j s : List Nat) (hj : ∀ a ∈ j, a ∈ bits) (hs : ∀ a ∈ s, a ∈ bits) :
    zppLogic.Reach1 (L0.den [j, s]) (P1pre.den [j, s]) := by
  have hA : zppLogic.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zppLogic.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zppLogic.Reach (F1.den [j, s, []]) (P1pre.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 18)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact (hA.trans hL).trans hB

theorem P1pre_hdR (j s : List Nat) :
    P1pre.den [j, s] = hdR Q.BD6 (1 :: (j ++ 1 :: (s ++ 1 :: (List.replicate s.length 3 ++ [3])))) [] :=
  den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by osimp) (by osimp)

/-- The verifier run starts: guest source `C` (counter `cl`), then `M_3`, the accept counter
`A`, `M_4`, and the fuel. -/
def GCvPP (j : List Nat) (Sb cl a : List Bool) : ZC :=
  hdR Q.GC (1 :: (1 :: (j ++ [1]) ++ (bitsOf Sb ++ [1])))
    (bitsOf cl.reverse ++ 1 :: (bitsOf a.reverse ++ 1 :: blkW Sb.length (Sb.length + 1)))

theorem vStartPP (J S : Nat) :
    zppLogic.Reach1 (lay J S)
      (GCvPP (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)
        (List.replicate ((str S).length + 1) true)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1PP _ _ hj hs
  rw [← lay_den, P1pre_hdR] at h1
  have hT0 : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h; rw [h]; simp [O13]
  have hr : ∀ a ∈ List.replicate (bitsOf (str S)).length 3, a ∈ T3 := rep_t3 _
  have hP : NoB (1 :: (bitsOf (str J) ++ [1])) := NoB.cons one_nb (hj.noB.app (NoB.cons one_nb NoB.nil))
  have h2 := blkStart2 [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT0
  have h3 := (copyLoop (1 :: (bitsOf (str J) ++ [1])) (List.replicate (bitsOf (str S)).length 3 ++ [3])
    hP hT0 (bitsOf (str S)) [] Bits.nil hs)
  have h4 := blkA (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3) hj hs hr
  have hT1 : ∀ a ∈ 3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (List.replicate (bitsOf (str S)).length 3 ++ [3, 1])), a ∈ O13 := by
    intro a ha
    simp [List.mem_replicate] at ha
    simp [O13]
    omega
  have h5 := blkCopy [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT1
  have hA3 : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3], a ∈ T3 := by
    intro a ha
    simp [List.mem_replicate] at ha
    simp [T3]
    omega
  have h6 := blkVerPP (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3)
    (List.replicate (bitsOf (str S)).length 3 ++ [3]) hj hs hr hA3
  have e3 : ∀ n : Nat, List.replicate n 3 ++ [3] = 3 :: List.replicate n 3 := fun n => rep_snoc_eq n 3
  have a1 := h2.of_eq (c3 := hdR Q.BD6 (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 ::
      (List.replicate (bitsOf (str S)).length 3 ++ [3])))) [])
    (c4 := hdR Q.COPY (1 :: (bitsOf (str J) ++ [1]))
      (bitsOf (str S) ++ 1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ [1]))) (by simp) (by simp)
  have a2 := h3.of_eq (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ [1]))
      (bitsOf (str S) ++ 1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ [1])))
    (c4 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ 1 :: List.replicate (bitsOf (str S)).length 3)))
    (by simp) (by simp)
  have a3 := h4.of_eq (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ 1 :: List.replicate (bitsOf (str S)).length 3)))
    (c4 := hdR Q.GRB (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (List.replicate (bitsOf (str S)).length 3 ++ [3, 1])))))) [])
    (by simp [e3]) (by simp)
  have a4 := h5.of_eq (c3 := hdR Q.GRB (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (List.replicate (bitsOf (str S)).length 3 ++ [3, 1])))))) [])
    (c4 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: 3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ 1 :: 1 :: List.replicate (bitsOf (str S)).length 3)))) (by simp) (by simp)
  have a5 := h6.of_eq (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: 3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: ((List.replicate (bitsOf (str S)).length 3 ++ [3]) ++ 1 :: 1 :: List.replicate (bitsOf (str S)).length 3))))
    (c4 := GCvPP (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)
        (List.replicate ((str S).length + 1) true)) (by simp) (by
      unfold GCvPP
      simp [bitsOf, blkW, List.replicate_succ, rep_cons_comm, List.reverse_replicate])
  exact h1.trans (a1.trans (a2.trans (a3.trans (a4.trans a5))))


/-! ## One verifier pass -/

/-- The run of the verifier from `GCvPP`: `A` is just more of the work area. -/
theorem runPP (j : List Nat) (hj : Bits j) (Sb cl al : List Bool) (hcl : cl.length = Sb.length + 1) :
    ∃ d, d ≤ Sb.length + 1 ∧
      zppLogic.Reach (GCvPP j Sb cl al)
        (hdR (dpOf (bn (run Sb cl.reverse (Sb.length + 1)))) [1]
          (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: (bitsOf al.reverse ++
            1 :: FWr Sb.length [d]))))) := by
  have hW : NoB (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: bitsOf al.reverse))) :=
    hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb
      ((Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)))))
  have hR : Sym4 (bitsOf al.reverse ++ 1 :: blkW Sb.length (Sb.length + 1)) :=
    (Bits.ofB _).sym4.app (Sym4.cons (by simp [ALL]) (blkW_noB _ _).sym4)
  obtain ⟨ds', hd', hl', h⟩ := runFrom Sb.length (j ++ [1]) (1 :: j) Sb cl.reverse
    (bitsOf al.reverse ++ 1 :: blkW Sb.length (Sb.length + 1))
    (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: bitsOf al.reverse))) [Sb.length + 1]
    rfl (NoB.cons one_nb hj.noB) hR hW
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
  unfold GCvPP
  simpa using h


/-- LSB-first decrement. -/
def decA : List Bool → List Bool
  | [] => []
  | false :: l => true :: decA l
  | true :: l => false :: l

theorem decA_spec (k : Nat) (r : List Bool) :
    decA (List.replicate k false ++ true :: r) = List.replicate k true ++ false :: r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, decA, ih]

theorem bitsOf_rep_false (n : Nat) : bitsOf (List.replicate n false) = List.replicate n 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, bitsOf] using ih

theorem bitsOf_rep_true (n : Nat) : bitsOf (List.replicate n true) = List.replicate n 3 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, bitsOf] using ih


theorem bitsOf_rev_cons (x : Bool) (rr : List Bool) (k : Nat) :
    bitsOf (List.replicate k false ++ true :: x :: rr).reverse =
      bitsOf rr.reverse ++ bn x :: 3 :: List.replicate k 2 := by
  simp [bitsOf, bn, List.reverse_append, List.reverse_replicate, List.map_append,
    List.map_reverse]

/-- One verifier pass of the P = PP machine. -/
theorem vStepPP (j : List Nat) (hj : Bits j) (Sb cl al : List Bool) (hcl : cl.length = Sb.length + 1)
    (hA : ∃ k r, al = List.replicate k false ++ true :: r) :
    (run Sb cl.reverse (Sb.length + 1) = true → ∀ k, al = List.replicate k false ++ [true] →
      zppLogic.Reach (GCvPP j Sb cl al) (TR j Sb true)) ∧
    (cl = List.replicate (Sb.length + 1) false →
      (run Sb cl.reverse (Sb.length + 1) = false ∨ ∀ k, al ≠ List.replicate k false ++ [true]) →
      zppLogic.Reach (GCvPP j Sb cl al) (TR j Sb false)) ∧
    (∀ k r, cl = List.replicate k false ++ true :: r →
      (run Sb cl.reverse (Sb.length + 1) = false ∨ ∀ k, al ≠ List.replicate k false ++ [true]) →
      zppLogic.Reach (GCvPP j Sb cl al) (GCvPP j Sb (List.replicate k true ++ false :: r)
        (if run Sb cl.reverse (Sb.length + 1) = true then decA al else al))) := by
  obtain ⟨d, hdd, h⟩ := runPP j hj Sb cl al hcl
  have hF : FWr Sb.length [d] = 1 :: (List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 2) := by
    simp [FWr, blkW]
  have hne : cl.reverse ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [hcl] at this
  refine ⟨fun ho k hk => ?_, fun hz hor => ?_, fun k r hc hor => ?_⟩
  · rw [ho] at h
    have hAr : bitsOf al.reverse = 3 :: List.replicate k 2 := by
      rw [hk]; simp [bitsOf, bn, List.reverse_append, List.reverse_replicate, bitsOf_rep_false]
    cases hr : cl.reverse with
    | nil => exact absurd hr hne
    | cons c rest =>
      cases rest with
      | nil =>
        have hT := accThr1 j (bitsOf Sb) (List.replicate k 2) (FWr Sb.length [d]) (bn c) hj
          (Bits.ofB _) (rep_z2 k) (FWr_noB _ _) (bn_bits c)
        refine h.trans (hT.of_eq ?_ (by simp [TR, tflag]))
        rw [hr, hAr]
        simp [dpOf, bn, bitsOf]
      | cons y Cq =>
        have hT := accThr2 j (bitsOf Sb) (bitsOf Cq) (List.replicate k 2) (FWr Sb.length [d]) (bn c) (bn y)
          hj (Bits.ofB _) (Bits.ofB _) (rep_z2 k) (FWr_noB _ _) (bn_bits c) (bn_bits y)
        refine h.trans (hT.of_eq ?_ (by simp [TR, tflag]))
        rw [hr, hAr]
        simp [dpOf, bn, bitsOf]
  · have hcr : bitsOf cl.reverse = 2 :: List.replicate Sb.length 2 := by
      rw [hz]; simp [bitsOf, List.replicate_succ, rep_snoc_eq]
    obtain ⟨k0, r0, hal⟩ := hA
    cases ho : run Sb cl.reverse (Sb.length + 1) with
    | false =>
      rw [ho] at h
      have hU := vUnder j (bitsOf Sb) (List.replicate Sb.length 2)
        (bitsOf al.reverse ++ 1 :: FWr Sb.length [d]) hj (Bits.ofB _) (rep_z2 _)
        ((Bits.ofB _).noB.app (NoB.cons one_nb (FWr_noB _ _)))
      exact h.trans (hU.of_eq (by rw [hcr]; simp [dpOf, bn]) (by simp [TR, tflag]))
    | true =>
      rw [ho] at h
      rw [ho] at hor
      have hnt := hor.resolve_left (by decide)
      cases r0 with
      | nil => exact absurd hal (hnt k0)
      | cons x rr =>
        have hU := accUnt j (bitsOf Sb) (List.replicate Sb.length 2) (bitsOf rr.reverse)
          (List.replicate k0 2) (FWr Sb.length [d]) (bn x) hj (Bits.ofB _) (rep_z2 _) (Bits.ofB _)
          (rep_z2 _) (FWr_noB _ _) (bn_bits x)
        refine h.trans (hU.of_eq ?_ (by simp [TR, tflag]))
        rw [hcr, hal, bitsOf_rev_cons]
        simp [dpOf, bn]
  · obtain ⟨k0, r0, hal⟩ := hA
    have hcr : cl.reverse = r.reverse ++ true :: List.replicate k false := by rw [hc]; simp
    have hcr' : (List.replicate k true ++ false :: r).reverse = r.reverse ++ false :: List.replicate k true := by
      simp
    have hDE : List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 3 = List.replicate (Sb.length + 1) 3 := by
      rw [List.replicate_append_replicate]
      congr 1
      omega
    have hBl : blkW Sb.length (Sb.length + 1) = 1 :: List.replicate (Sb.length + 1) 3 := by
      simp [blkW]
    cases ho : run Sb cl.reverse (Sb.length + 1) with
    | false =>
      rw [ho] at h
      simp only [Bool.false_eq_true, if_false]
      cases hr : r.reverse with
      | nil =>
        have hE := rejE j (bitsOf Sb) (List.replicate k 2) (List.replicate d 3)
          (List.replicate (Sb.length + 1 - d) 2) (bitsOf al.reverse) hj (Bits.ofB _) (rep_z2 _) (rep_t3 _)
          (rep_z2 _) (Bits.ofB _)
        refine h.trans (hE.of_eq ?_ ?_)
        · rw [hF, hcr, hr]
          simp [dpOf, bn, bitsOf]
        · unfold GCvPP
          rw [hcr', hr]
          simp only [List.length_replicate]
          rw [hDE, hBl]
          simp [bitsOf]
      | cons x rr =>
        have hC := rejC j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (List.replicate d 3)
          (List.replicate (Sb.length + 1 - d) 2) (bitsOf al.reverse) (bn x) hj (Bits.ofB _) (Bits.ofB _)
          (rep_z2 _) (rep_t3 _) (rep_z2 _) (Bits.ofB _) (bn_bits x)
        refine h.trans (hC.of_eq ?_ ?_)
        · rw [hF, hcr, hr]
          simp [dpOf, bn, bitsOf]
        · unfold GCvPP
          rw [hcr', hr]
          simp only [List.length_replicate]
          rw [hDE, hBl]
          simp [bitsOf, bn]
    | true =>
      rw [ho] at h
      rw [ho] at hor
      have hnt := hor.resolve_left (by decide)
      simp only [if_true]
      cases r0 with
      | nil => exact absurd hal (hnt k0)
      | cons x0 rr0 =>
        have hAr : bitsOf al.reverse = bitsOf rr0.reverse ++ bn x0 :: 3 :: List.replicate k0 2 := by
          rw [hal, bitsOf_rev_cons]
        have hAr' : bitsOf (decA al).reverse = bitsOf rr0.reverse ++ bn x0 :: 2 :: List.replicate k0 3 := by
          rw [hal, decA_spec]
          simp [bitsOf, bn, List.reverse_append, List.reverse_replicate, List.map_append,
            List.map_reverse]
        cases hr : r.reverse with
        | nil =>
          have hE := accEnt j (bitsOf Sb) (List.replicate k 2) (List.replicate d 3)
            (List.replicate (Sb.length + 1 - d) 2) (bitsOf rr0.reverse) (List.replicate k0 2) (bn x0)
            hj (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _) (Bits.ofB _) (rep_z2 _) (bn_bits x0)
          refine h.trans (hE.of_eq ?_ ?_)
          · rw [hF, hcr, hr, hAr]
            simp [dpOf, bn, bitsOf]
          · unfold GCvPP
            rw [hcr', hr, hAr']
            simp only [List.length_replicate]
            rw [hDE, hBl]
            simp [bitsOf]
        | cons x rr =>
          have hC := accCnt j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (List.replicate d 3)
            (List.replicate (Sb.length + 1 - d) 2) (bitsOf rr0.reverse) (List.replicate k0 2) (bn x) (bn x0)
            hj (Bits.ofB _) (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _) (Bits.ofB _) (rep_z2 _)
            (bn_bits x) (bn_bits x0)
          refine h.trans (hC.of_eq ?_ ?_)
          · rw [hF, hcr, hr, hAr]
            simp [dpOf, bn, bitsOf]
          · unfold GCvPP
            rw [hcr', hr, hAr']
            simp only [List.length_replicate]
            rw [hDE, hBl]
            simp [bitsOf, bn]


/-! ## Counting accepted certificates -/

/-- `1` if the certificate `v` (as a counter value) is accepted. -/
def accV (Sb : List Bool) (v : Nat) : Nat :=
  if run Sb (ofBv (Sb.length + 1) v).reverse (Sb.length + 1) = true then 1 else 0

theorem length_filter_sum {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length = (l.map fun c => if p c = true then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    by_cases h : p c = true
    · simp [List.filter_cons, h, ih]; omega
    · simp [List.filter_cons, h, ih]

theorem pow_pos' (k : Nat) : 0 < 2 ^ k := Nat.pow_pos (by decide)

theorem accCount_eq (Sb : List Bool) : accCount Sb = psum (accV Sb) (2 ^ (Sb.length + 1) - 1) := by
  unfold accCount
  rw [length_filter_sum]
  have h1 : ((strings (Sb.length + 1)).map fun c => if run Sb c (Sb.length + 1) = true then 1 else 0).sum =
      T (Sb.length + 1) (fun c => if run Sb c (Sb.length + 1) = true then 1 else 0) := rfl
  rw [h1, ← T_rev, T_range, ← sum_range_psum]
  have h2 : 2 ^ (Sb.length + 1) - 1 + 1 = 2 ^ (Sb.length + 1) := by
    have := pow_pos' (Sb.length + 1); omega
  rw [h2]
  rfl

theorem accV_le (Sb : List Bool) (v : Nat) : accV Sb v ≤ 1 := by
  unfold accV; split <;> omega

theorem accV_cl (Sb cl : List Bool) (hcl : cl.length = Sb.length + 1) :
    accV Sb (bv cl) = if run Sb cl.reverse (Sb.length + 1) = true then 1 else 0 := by
  unfold accV
  rw [← hcl, ofBv_bv]

theorem bv_rep_true : ∀ k, bv (List.replicate k true) + 1 = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    have ih := bv_rep_true k
    show 1 + 2 * bv (List.replicate k true) + 1 = 2 ^ (k + 1)
    rw [Nat.pow_succ]
    omega

theorem bv_pre_zeros : ∀ (k : Nat) (r : List Bool),
    bv (List.replicate k false ++ true :: r) = 2 ^ k * (1 + 2 * bv r)
  | 0, r => by simp [bv, bitN]
  | k + 1, r => by
    have ih := bv_pre_zeros k r
    show 0 + 2 * bv (List.replicate k false ++ true :: r) = 2 ^ (k + 1) * (1 + 2 * bv r)
    rw [ih, Nat.pow_succ, Nat.zero_add]
    generalize 2 ^ k = P
    generalize 1 + 2 * bv r = Q
    ac_rfl


theorem rep_inj : ∀ (k k' : Nat) (r r' : List Bool),
    List.replicate k false ++ true :: r = List.replicate k' false ++ true :: r' → k = k' ∧ r = r'
  | 0, 0, r, r', h => by simpa using h
  | 0, k' + 1, r, r', h => by simp [List.replicate_succ] at h
  | k + 1, 0, r, r', h => by simp [List.replicate_succ] at h
  | k + 1, k' + 1, r, r', h => by
    have h' : List.replicate k false ++ true :: r = List.replicate k' false ++ true :: r' := by
      simpa [List.replicate_succ] using h
    have := rep_inj k k' r r' h'
    exact ⟨by omega, this.2⟩

theorem thr_arith (n k : Nat) (r : List Bool) (a : Nat)
    (hbv : 2 ^ k * (1 + 2 * bv r) + a + 1 = 2 ^ (n + 1)) (ha : a < 2 ^ n)
    (hlen : k + r.length = n) :
    (r = [] → a + 1 = 2 ^ n) ∧ (r ≠ [] → a + 1 < 2 ^ n) := by
  constructor
  · rintro rfl
    have hk : k = n := by simpa using hlen
    subst hk
    simp [bv, Nat.pow_succ] at hbv
    omega
  · intro hr
    obtain ⟨x, rr, rfl⟩ := List.exists_cons_of_ne_nil hr
    by_cases h : a + 1 < 2 ^ n
    · exact h
    · exfalso
      have e1 : a + 1 = 2 ^ n := by omega
      have e2 : n = k + (rr.length + 1) := by simpa using hlen.symm
      have e3 : 2 ^ k * (1 + 2 * bv (x :: rr)) = 2 ^ k * (2 * 2 ^ rr.length) := by
        have : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ ..
        have h4 : 2 ^ n = 2 ^ k * (2 * 2 ^ rr.length) := by
          rw [e2, Nat.pow_add, Nat.pow_succ]
          generalize 2 ^ k = P
          generalize 2 ^ rr.length = Q
          ac_rfl
        omega
      have e4 := Nat.eq_of_mul_eq_mul_left (pow_pos' k) e3
      omega


theorem length_decA : ∀ al : List Bool, (decA al).length = al.length
  | [] => rfl
  | false :: l => by simp [decA, length_decA l]
  | true :: l => rfl

/-- The verifier loop: `cl` counts down, `al` counts the accepting runs so far (down from
`2^(n+1) - 1`), and the truth flag says whether `a + #accepting ≥ 2^n`. -/
theorem vLoopPP (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    ∀ N cl al a, bv cl = N → cl.length = Sb.length + 1 → al.length = Sb.length + 1 →
      bv al + a + 1 = 2 ^ (Sb.length + 1) → a < 2 ^ Sb.length →
      ∃ b, (b = true ↔ 2 ^ Sb.length ≤ a + psum (accV Sb) N) ∧
        zppLogic.Reach (GCvPP j Sb cl al) (TR j Sb b) := by
  intro N
  induction N with
  | zero =>
    intro cl al a hN hcl hal hbv ha
    have hpow : 2 ^ (Sb.length + 1) = 2 * 2 ^ Sb.length := by rw [Nat.pow_succ]; omega
    obtain ⟨k0, r0, hA⟩ : ∃ k r, al = List.replicate k false ++ true :: r := by
      rcases cases_dec al with ⟨k, hk⟩ | h
      · rw [hk, bv_falses] at hbv; omega
      · exact h
    have hS := vStepPP j hj Sb cl al hcl ⟨k0, r0, hA⟩
    have hz : cl = List.replicate (Sb.length + 1) false := by
      obtain ⟨k, hk⟩ := bv_zero cl hN
      rw [hk] at hcl ⊢
      simp at hcl
      rw [hcl]
    have hacc := accV_cl Sb cl hcl
    rw [hN] at hacc
    have hbv' := hbv
    rw [hA, bv_pre_zeros] at hbv'
    have hlen : k0 + r0.length = Sb.length := by
      rw [hA] at hal; simp at hal; omega
    have hth := thr_arith Sb.length k0 r0 a hbv' ha hlen
    cases ho : run Sb cl.reverse (Sb.length + 1) with
    | true =>
      rw [ho] at hacc
      simp at hacc
      cases r0 with
      | nil =>
        refine ⟨true, ⟨fun _ => ?_, fun _ => rfl⟩, hS.1 ho k0 (by rw [hA])⟩
        have := hth.1 rfl
        have := psum_ge (accV Sb) 0
        simp [psum] at *
        omega
      | cons x rr =>
        have hnt : ∀ k, al ≠ List.replicate k false ++ [true] := by
          intro k hk
          rw [hA] at hk
          have := (rep_inj k0 k (x :: rr) [] (by simpa using hk)).2
          simp at this
        refine ⟨false, ⟨fun h => absurd h (by decide), fun h => ?_⟩, hS.2.1 hz (Or.inr hnt)⟩
        have := hth.2 (by simp)
        simp [psum] at *
        omega
    | false =>
      rw [ho] at hacc
      simp at hacc
      refine ⟨false, ⟨fun h => absurd h (by decide), fun h => ?_⟩, hS.2.1 hz (Or.inl ho)⟩
      simp [psum, hacc] at h
      omega
  | succ M ih =>
    intro cl al a hN hcl hal hbv ha
    have hpow : 2 ^ (Sb.length + 1) = 2 * 2 ^ Sb.length := by rw [Nat.pow_succ]; omega
    obtain ⟨k0, r0, hA⟩ : ∃ k r, al = List.replicate k false ++ true :: r := by
      rcases cases_dec al with ⟨k, hk⟩ | h
      · rw [hk, bv_falses] at hbv; omega
      · exact h
    have hS := vStepPP j hj Sb cl al hcl ⟨k0, r0, hA⟩
    obtain ⟨k, r, hc⟩ : ∃ k r, cl = List.replicate k false ++ true :: r := by
      rcases cases_dec cl with ⟨k, hk⟩ | h
      · rw [hk, bv_falses] at hN; omega
      · exact h
    have hd := bv_dec k r
    rw [← hc] at hd
    have hcl' : (List.replicate k true ++ false :: r).length = Sb.length + 1 := by
      rw [← hcl, hc]; simp
    have hacc := accV_cl Sb cl hcl
    rw [hN] at hacc
    have hbv' := hbv
    rw [hA, bv_pre_zeros] at hbv'
    have hlen : k0 + r0.length = Sb.length := by
      rw [hA] at hal; simp at hal; omega
    have hth := thr_arith Sb.length k0 r0 a hbv' ha hlen
    have hps : psum (accV Sb) (M + 1) = psum (accV Sb) M + accV Sb (M + 1) := rfl
    cases ho : run Sb cl.reverse (Sb.length + 1) with
    | true =>
      rw [ho] at hacc
      simp at hacc
      cases r0 with
      | nil =>
        refine ⟨true, ⟨fun _ => ?_, fun _ => rfl⟩, hS.1 ho k0 (by rw [hA])⟩
        have := hth.1 rfl
        have := psum_ge (accV Sb) (M + 1)
        omega
      | cons x rr =>
        have hnt : ∀ k, al ≠ List.replicate k false ++ [true] := by
          intro k hk
          rw [hA] at hk
          have := (rep_inj k0 k (x :: rr) [] (by simpa using hk)).2
          simp at this
        have hlt := hth.2 (by simp)
        have hdA : decA al = List.replicate k0 true ++ false :: x :: rr := by rw [hA, decA_spec]
        have hbd := bv_dec k0 (x :: rr)
        rw [← hdA, ← hA] at hbd
        obtain ⟨b, hb, hR⟩ := ih (List.replicate k true ++ false :: r) (decA al) (a + 1) (by omega) hcl'
          (by rw [length_decA, hal]) (by omega) (by omega)
        refine ⟨b, ?_, (hS.2.2 k r hc (Or.inr hnt)).trans (by simpa [ho] using hR)⟩
        rw [hb, hps, hacc]
        omega
    | false =>
      rw [ho] at hacc
      simp at hacc
      obtain ⟨b, hb, hR⟩ := ih (List.replicate k true ++ false :: r) al a (by omega) hcl' hal hbv ha
      refine ⟨b, ?_, (hS.2.2 k r hc (Or.inl ho)).trans (by simpa [ho] using hR)⟩
      rw [hb, hps, hacc]
      omega


/-- The whole verifier: it leaves the truth flag `inPP s`. -/
theorem vFullPP (j : List Nat) (hj : Bits j) (Sb : List Bool) :
    zppLogic.Reach (GCvPP j Sb (List.replicate (Sb.length + 1) true) (List.replicate (Sb.length + 1) true))
      (TR j Sb (inPP Sb)) := by
  have hpow : 2 ^ (Sb.length + 1) = 2 * 2 ^ Sb.length := by rw [Nat.pow_succ]; omega
  have hb := bv_rep_true (Sb.length + 1)
  obtain ⟨b, hb', hR⟩ := vLoopPP j hj Sb (bv (List.replicate (Sb.length + 1) true))
    (List.replicate (Sb.length + 1) true) (List.replicate (Sb.length + 1) true) 0 rfl (by simp) (by simp)
    (by omega) (pow_pos' _)
  have e : b = inPP Sb := by
    apply bool_eq_of_iff
    rw [hb']
    unfold inPP
    have hN : bv (List.replicate (Sb.length + 1) true) = 2 ^ (Sb.length + 1) - 1 := by omega
    rw [hN, ← accCount_eq]
    simp only [decide_eq_true_eq]
    omega
  rw [← e]
  exact hR

/-! ## One pair -/

theorem pair_mainPP (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectPP J S → zppLogic.zrun n (lay J S) = some (lay (absStepC CorrectPP (J, S)).1 (absStepC CorrectPP (J, S)).2)) ∧
       (¬ CorrectPP J S → ∃ a c1 c2, a < n ∧ zppLogic.zrun a (lay J S) = some c1 ∧ c1.q = zppLogic.beep ∧
          zppLogic.zstep c1 = some c2 ∧
          zppLogic.zrun (n - a - 1) c2 = some (lay (absStepC CorrectPP (J, S)).1 (absStepC CorrectPP (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨Fu, hFu, hD⟩ := dPhase (str J) (str S) (inPP (str S))
  have hA := (vStartPP J S).trans ((vFullPP _ hj (str S)).trans hD)
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectPP J S
  · have e : absStepC CorrectPP (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = inPP (str S) := hc
    rw [ho] at hA
    have hok : zppLogic.Reach
        (hdR (dpOf (bn (inPP (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inPP (str S)) ++ 1 :: Fu)))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inPP (str S)
      · exact (dOk0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
      · exact (dOk1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
    have hinc := sincL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.of_eq (c4 := lay J (S + 1)) (by rw [eS]; rfl) (by rw [lay_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectPP (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = !inPP (str S) := by
      have h' : run (str J) (str S) (clock (str J) (str S)) ≠ inPP (str S) := hc
      revert h'
      cases run (str J) (str S) (clock (str J) (str S)) <;> cases inPP (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zppLogic.Reach
        (hdR (dpOf (bn (!inPP (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inPP (str S)) ++ 1 :: Fu)))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zppLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inPP (str S)
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


end ZP.PP
