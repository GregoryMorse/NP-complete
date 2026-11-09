module

public import ZP.Pair
public import ZP.CompileF
public import ZP.DefsF

@[expose] public section

/-! The pair lemma for the FACTOR machine, adapted from `ZP/Pair.lean`. -/

namespace ZP.F

open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zfacLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zfacLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
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
    zfacLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hdR Q.GRB (Jl ++ (b :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3]))))))))))))) []) := by
  have hV : Valid [bits, bits, bits, T3, O13] [Jl, Jr, s, t, Bl] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _)))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Jl, Jr, s, t, Bl]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3)])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, t, Bl]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3)])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Last decider fuel block: the walker goes home. -/
theorem blkDecLast (Jl : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (hJl : Bits Jl) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) :
    zfacLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, O13] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 23) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zfacLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
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
    zfacLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zfacLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zfacLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: (1 :: Rest)))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: (1 :: Rest))))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 19) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zfacLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zfacLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zfacLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR QF.NI (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR QF.NI (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR QF.NI (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR QF.NI (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zfacLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zfacLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
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
    zfacLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zfacLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zfacLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zfacLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zfacLogic.Reach
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
    (hFb : ∃ a ∈ F, a ∈ bits) (hR1 : ∃ R', Rest = 1 :: R')
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: F) :
    ∃ g, 1 ≤ g ∧ zfacLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
      (Bd (rot (Pb.reverse ++ [false])) g ⟨[], Xb.head?, Xb.tail⟩ W F) := by
  obtain ⟨R1, hRe⟩ := hR1
  have hVn : NoB (Vq ++ [1]) := hVq.app (NoB.cons one_nb NoB.nil)
  have hP : Bits (bitsOf Pb) := Bits.ofB Pb
  have hX : Bits (bitsOf Xb) := Bits.ofB Xb
  have hXr : Bits (bitsOf Xb).reverse := bitsOf_rev Xb
  have h1 := gcLoop (Vq ++ [1]) (bitsOf Pb) Rest hVn hP hR (bitsOf Xb) [] Bits.nil hX
  have hR1' : Sym4 R1 := fun a ha => hR a (by rw [hRe]; exact List.mem_cons_of_mem _ ha)
  have h2 := gcEnd (bitsOf Xb).reverse (Vq ++ [1]) (bitsOf Pb) (bitsOf Xb) R1 hXr hVn hP hX hR1'
  rw [← hRe] at h2
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
  have hB0 := hA.trans (zpBase_ext_zfacLogic.reach (hr.of_eq (by rw [hcode]) rfl))
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
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zfacLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zfacLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk, bitsOf_cons, bitsOf_reverse]
      simp
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN_some, bitsOf, List.replicate_succ, rep_cons_comm]


/-- One guest run from the setup position, to the dispatch state. -/
theorem runFrom (n : Nat) (W1 Vq : List Nat) (Pb Xb : List Bool) (Rest W : List Nat) (ds : List Nat)
    (hV : 1 :: W1 = Vq ++ [1]) (hVq : NoB Vq) (hR : Sym4 Rest) (hW : NoB W)
    (hds : Dig n ds) (hne : ds ≠ []) (hR1 : ∃ R', Rest = 1 :: R')
    (hWF : W1 ++ (bitsOf Pb ++ 1 :: (bitsOf Xb ++ 1 :: Rest)) = W ++ 1 :: FWr n ds) :
    ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧
      zfacLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
        (RE (run Pb Xb (valr n ds)) W (FWr n ds')) := by
  obtain ⟨g, hg, h1⟩ := setup W1 Vq Pb Xb Rest W (FWr n ds) hV hVq hR hW (FWr_noB n ds)
    (fw_bit n ds hne) hR1 hWF
  have hz : (⟨[], Xb.head?, Xb.tail⟩ : Zp).WF := by
    unfold Zp.WF
    cases Xb with
    | nil => intro _; rfl
    | cons x xt => intro h; simp at h
  obtain ⟨ds', hd', hl', h2⟩ := runI n W hW _ _ g _ ds (inv0 Pb) hg hz hds hne rfl
  have ht : (⟨[], Xb.head?, Xb.tail⟩ : Zp).tape = fun i => Xb[i]? := by
    cases Xb <;> rfl
  rw [ht] at h2
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zfacLogic.reach h2)⟩



/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zfacLogic.Reach (TR (bitsOf Jb) Sb b)
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
    ⟨_, rfl⟩ (by simp)
  have hv : valr Sb.length (List.replicate (Jb.length + 1) (Sb.length + 1)) = clock Jb Sb := by
    have := valr_full Sb.length (Jb.length + 1)
    unfold clock
    omega
  rw [hv] at h2
  exact ⟨FWr Sb.length ds', FWr_noB _ _,
    (h1.of_eq (by simp [TR, FWr]) (by simp)).trans (h2.of_eq rfl (by unfold RE; simp))⟩


theorem sincL (A : List Nat) (hA : NoB A) : ∀ (r : List Bool) (k : Nat),
    zfacLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
      (hdR QF.NI (A ++ 1 :: (bitsOf (incR r).reverse ++ List.replicate k 2)) [])
  | [], k => (sincE A (List.replicate k 2) hA (rep_z2 k)).of_eq rfl (by rw [rep_snoc_eq]; rfl)
  | false :: r, k =>
    (sinc0 A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) (by simp [incR, bitsOf])
  | true :: r, k =>
    ((sinc1 A (bitsOf r.reverse) (List.replicate k 2) hA (Bits.ofB _) (rep_z2 k)).of_eq
      (by simp [bitsOf]) rfl).trans
      ((sincL A hA r (k + 1)).of_eq rfl (by simp [incR, bitsOf, List.replicate_succ]))


theorem jincL : ∀ (r : List Bool) (k : Nat),
    zfacLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
      (hdR QF.NI (1 :: (bitsOf (incR r).reverse ++ (List.replicate k 2 ++ [1]))) [])
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
    zfacLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1].reverse,
      [.blk 2 .id], true⟩ : SC).den [j, s, Y] = hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)



/-! ## The conversion to unary (generated) -/

/-- Conversion: a pair `1 1` is consumed; the target gets its marked cell. -/
theorem dig3 (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zfacLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ (3 :: ([3]))))) (0 :: (Rt)))
      (hdR QF.DR ([2]) (T ++ (1 :: (L ++ (0 :: (0 :: (0 :: (Rt)))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .sym 3]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.sym 2]) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a pair `1 0` is consumed. -/
theorem dig2 (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zfacLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ (2 :: ([3]))))) (0 :: (Rt)))
      (hdR QF.DR ([]) (T ++ (1 :: (L ++ (0 :: (0 :: (0 :: (Rt)))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 3]) (rs := [.sym 0, .blk 2 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling: one unmarked `1` is marked and a marked cell appended. -/
theorem dstep (Z : List Nat) (X : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hX : Sym4 X) :
    zfacLogic.Reach (hdR QF.DR (Z) (3 :: (X)))
      (hdR QF.DR (2 :: (Z ++ ([2]))) (X)) := by
  have hV : Valid [Z2, ALL] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.sym 2, .blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling is done: unmark, back to the copy. -/
theorem dEnd (Z : List Nat) (Y : List Nat) (R : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hY : NoB Y) (hR : Sym4 R) :
    zfacLogic.Reach (hdR QF.DR (Z) (1 :: (Y ++ (0 :: (R)))))
      (hd QF.HPF (List.replicate Z.length 3 ++ (1 :: (Y))) (0 :: (R))) := by
  have hV : Valid [Z2, NB, ALL] [Z, Y, R] := Valid.cons hZ (Valid.cons hY (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [Z, Y, R]) (E := []) (k := 7) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 (.const 3), .sym 1, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a `0` ends the number; a new separator opens the next target. -/
theorem sepStep (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zfacLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ ([2])))) (0 :: (Rt)))
      (hd QF.HPF (1 :: (T ++ (1 :: (L)))) (0 :: (0 :: (Rt)))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTT (env := [T, L, Rt]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done (the copy is used up). -/
theorem endM (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zfacLogic.Reach (hd QF.HPF (Lp ++ ([1])) (0 :: (Rt)))
      (hd QF.RS1 (Lp) (1 :: (0 :: (Rt)))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done after a trailing lone `1`. -/
theorem endLone (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zfacLogic.Reach (hd QF.HPF (Lp ++ (1 :: ([3]))) (0 :: (Rt)))
      (hd QF.RS1 (Lp) (1 :: (0 :: (0 :: (Rt))))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 3]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 0, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## The conversion loop -/

theorem rep2_ext (m : Nat) : 2 :: (List.replicate m 2 ++ [2]) = List.replicate (m + 2) 2 := by
  rw [rep_snoc_eq]; rfl

theorem dloop (X : List Nat) (hX : Sym4 X) : ∀ u m : Nat,
    zfacLogic.Reach (hdR QF.DR (List.replicate m 2) (List.replicate u 3 ++ X))
      (hdR QF.DR (List.replicate (m + 2 * u) 2) X)
  | 0, m => by simpa using LTM.Reach.refl _ _
  | u + 1, m => by
    have hX' : Sym4 (List.replicate u 3 ++ X) := (Sym4.rep u 3 (by simp [ALL])).app hX
    have h1 := dstep (List.replicate m 2) (List.replicate u 3 ++ X) (rep_z2 m) hX'
    have h2 := dloop X hX u (m + 2)
    refine (h1.of_eq (by simp [List.replicate_succ]) (by rw [rep2_ext])).trans (h2.of_eq rfl ?_)
    congr 2
    omega


theorem digitStep (t : Nat) (L Rt : List Nat) (hL : NoB L) (hRt : Sym4 Rt) (b : Bool) :
    zfacLogic.Reach (hd QF.HPF (List.replicate t 3 ++ 1 :: (L ++ [bn b, 3])) (0 :: Rt))
      (hd QF.HPF (List.replicate (bitN b + 2 * t) 3 ++ 1 :: L) (0 :: 0 :: 0 :: Rt)) := by
  have hX : Sym4 (1 :: (L ++ 0 :: (0 :: 0 :: Rt))) :=
    Sym4.cons (by simp [ALL]) (hL.sym4.app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL])
      (Sym4.cons (by simp [ALL]) hRt))))
  have hR2 : Sym4 (0 :: 0 :: Rt) := Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hRt)
  have hE := dEnd
  cases b
  · have h1 := dig2 (List.replicate t 3) L Rt (rep_t3 t) hL hRt
    have h2 := dloop (1 :: (L ++ 0 :: (0 :: 0 :: Rt))) hX t 0
    have h3 := dEnd (List.replicate (0 + 2 * t) 2) L (0 :: 0 :: Rt) (rep_z2 _) hL hR2
    refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq rfl ?_))
    simp [bitN]
  · have h1 := dig3 (List.replicate t 3) L Rt (rep_t3 t) hL hRt
    have h2 := dloop (1 :: (L ++ 0 :: (0 :: 0 :: Rt))) hX t 1
    have h3 := dEnd (List.replicate (1 + 2 * t) 2) L (0 :: 0 :: Rt) (rep_z2 _) hL hR2
    refine h1.trans ((h2.of_eq (by simp) rfl).trans (h3.of_eq rfl ?_))
    simp [bitN]

/-- Layout of the finished numbers, newest first: `n M … `. -/
def lyt : List Nat → List Nat
  | [] => []
  | n :: fr => List.replicate n 3 ++ 1 :: lyt fr

/-- `lyt`-layout without the last separator. -/
def lay1 : Nat → List Nat → List Nat
  | c, [] => List.replicate c 3
  | c, n :: fr => List.replicate c 3 ++ 1 :: lay1 n fr

theorem lay1_eq : ∀ (c : Nat) (fr : List Nat), List.replicate c 3 ++ 1 :: lyt fr = lay1 c fr ++ [1]
  | c, [] => by simp [lyt, lay1]
  | c, n :: fr => by
    have ih := lay1_eq n fr
    simp only [lyt, lay1, List.cons_append, List.append_assoc]
    rw [ih]

theorem lyt_noB : ∀ fr : List Nat, NoB (lyt fr)
  | [] => NoB.nil
  | n :: fr => (t3_noB (rep_t3 n)).app (NoB.cons one_nb (lyt_noB fr))

def crev (r : List Bool) : List Nat := (bitsOf r).reverse

theorem crev_noB (r : List Bool) : NoB (crev r) := by
  unfold crev
  exact (Bits.ofB r).rev.noB

/-- The parser state after consuming `r` (fuel `f`): current number and finished numbers
(newest first). -/
def parseState : Nat → List Bool → Nat → List Nat → Nat × List Nat
  | 0, _, cur, fr => (cur, fr)
  | _ + 1, [], cur, fr => (cur, fr)
  | _ + 1, [true], cur, fr => (cur, fr)
  | f + 1, true :: b :: r, cur, fr => parseState f r (bitN b + 2 * cur) fr
  | f + 1, false :: r, cur, fr => parseState f r 0 (cur :: fr)


theorem crev_cons2 (b : Bool) (r : List Bool) : crev (true :: b :: r) = crev r ++ [bn b, 3] := by
  simp [crev, bitsOf, bn]

theorem crev_false (r : List Bool) : crev (false :: r) = crev r ++ [2] := by
  simp [crev, bitsOf]

theorem rep_zero_split (g : Nat) (Rt : List Nat) (hg : 1 ≤ g) :
    List.replicate g 0 ++ Rt = 0 :: (List.replicate (g - 1) 0 ++ Rt) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp [List.replicate_succ]

theorem lay1_sym4 : ∀ (c : Nat) (fr : List Nat), Sym4 (lay1 c fr)
  | c, [] => Sym4.rep c 3 (by simp [ALL])
  | c, n :: fr => (Sym4.rep c 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) (lay1_sym4 n fr))

theorem rep_add3 (g : Nat) (Rt : List Nat) (hg : 1 ≤ g) :
    List.replicate (g + 2) 0 ++ Rt = 0 :: 0 :: 0 :: (List.replicate (g - 1) 0 ++ Rt) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp [List.replicate_succ]

theorem rep_add2 (g : Nat) (Rt : List Nat) (hg : 1 ≤ g) :
    List.replicate (g + 1) 0 ++ Rt = 0 :: 0 :: (List.replicate (g - 1) 0 ++ Rt) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  simp [List.replicate_succ]

theorem convLoop (Rt : List Nat) (hRt : Sym4 Rt) : ∀ (f : Nat) (r : List Bool) (cur : Nat) (fr : List Nat)
    (g : Nat), 1 ≤ g → r.length ≤ f →
    zfacLogic.Reach (hd QF.HPF (List.replicate cur 3 ++ 1 :: (lyt fr ++ crev r)) (List.replicate g 0 ++ Rt))
      (hd QF.RS1 (lay1 (parseState f r cur fr).1 (parseState f r cur fr).2)
        (1 :: (List.replicate (g + r.length) 0 ++ Rt))) := by
  intro f
  induction f with
  | zero =>
    intro r cur fr g hg hf
    have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hR' : Sym4 (List.replicate (g - 1) 0 ++ Rt) := (zeros4 _).app hRt
    have h := endM (lay1 cur fr) (List.replicate (g - 1) 0 ++ Rt) (lay1_sym4 _ _) hR'
    refine h.of_eq ?_ ?_
    · rw [rep_zero_split g Rt hg]
      simp [crev, bitsOf, lay1_eq]
    · rw [← rep_zero_split g Rt hg]
      simp [parseState]
  | succ f ih =>
    intro r cur fr g hg hf
    have hR' : Sym4 (List.replicate (g - 1) 0 ++ Rt) := (zeros4 _).app hRt
    have hsplit := rep_zero_split g Rt hg
    cases r with
    | nil =>
      have h := endM (lay1 cur fr) (List.replicate (g - 1) 0 ++ Rt) (lay1_sym4 _ _) hR'
      refine h.of_eq ?_ ?_
      · rw [hsplit]
        simp [crev, bitsOf, lay1_eq]
      · rw [← hsplit]
        simp [parseState]
    | cons x r1 =>
      cases x with
      | true =>
        cases r1 with
        | nil =>
          have h := endLone (lay1 cur fr) (List.replicate (g - 1) 0 ++ Rt) (lay1_sym4 _ _) hR'
          refine h.of_eq ?_ ?_
          · rw [hsplit]
            have e := lay1_eq cur fr
            have e2 : List.replicate cur 3 ++ 1 :: (lyt fr ++ crev [true]) = lay1 cur fr ++ [1, 3] :=
              calc List.replicate cur 3 ++ 1 :: (lyt fr ++ crev [true])
                  = (List.replicate cur 3 ++ 1 :: lyt fr) ++ [3] := by simp [crev, bitsOf]
                _ = lay1 cur fr ++ [1, 3] := by rw [e]; simp
            rw [e2]
          · simp only [parseState, List.length_cons, List.length_nil]
            rw [show g + (0 + 1) = g + 1 by omega, rep_add2 g Rt hg]
        | cons b r' =>
          have hL : NoB (lyt fr ++ crev r') := (lyt_noB fr).app (crev_noB r')
          have h1 := digitStep cur (lyt fr ++ crev r') (List.replicate (g - 1) 0 ++ Rt) hL hR' b
          have h2 := ih r' (bitN b + 2 * cur) fr (g + 2) (by omega) (by simp at hf; omega)
          refine (h1.of_eq ?_ rfl).trans (h2.of_eq ?_ ?_)
          · rw [hsplit, crev_cons2]
            simp
          · rw [rep_add3 g Rt hg]
          · have e : g + (true :: b :: r').length = g + 2 + r'.length := by
              simp only [List.length_cons]; omega
            simp only [parseState]
            rw [e]
      | false =>
        have hL : NoB (lyt fr ++ crev r1) := (lyt_noB fr).app (crev_noB r1)
        have h1 := sepStep (List.replicate cur 3) (lyt fr ++ crev r1) (List.replicate (g - 1) 0 ++ Rt)
          (rep_t3 cur) hL hR'
        have h2 := ih r1 0 (cur :: fr) (g + 1) (by omega) (by simp at hf; omega)
        refine (h1.of_eq ?_ rfl).trans (h2.of_eq ?_ ?_)
        · rw [hsplit, crev_false]
          simp
        · rw [rep_add2 g Rt hg]
          simp [lyt]
        · have e : g + (false :: r1).length = g + 1 + r1.length := by
            simp only [List.length_cons]; omega
          simp only [parseState]
          rw [e]


/-! ## Divisibility segments (generated) -/

/-- Divisibility: mark one cell of `A`, then one of `K` (not full). -/
theorem aIter1 (Pre : List Nat) (A1 : List Nat) (A2 : List Nat) (K1 : List Nat) (K2 : List Nat) (G : List Nat) (hPre : Sym4 Pre) (hA1 : ∀ a ∈ A1, a ∈ T3) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK1 : ∀ a ∈ K1, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (Pre ++ (A1 ++ (3 :: (A2)))) (1 :: (K1 ++ (3 :: (3 :: (K2 ++ (1 :: (G))))))))
      (hd QF.SA (Pre ++ (A1 ++ (2 :: (A2)))) (1 :: (K1 ++ (2 :: (3 :: (K2 ++ (1 :: (G)))))))) := by
  have hV : Valid [ALL, T3, Z2, Z2, T3, ALL] [Pre, A1, A2, K1, K2, G] := Valid.cons hPre (Valid.cons hA1 (Valid.cons hA2 (Valid.cons hK1 (Valid.cons hK2 (Valid.cons hG (Valid.nil _))))))
  exact checkTT (env := [Pre, A1, A2, K1, K2, G]) (E := []) (k := 10) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id, .sym 3, .blk 2 .id]) (rs := [.sym 1, .blk 3 .id, .sym 3, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 2, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 2, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Divisibility: mark one cell of `A`, then the last of `K`: `K` is full, reset it. -/
theorem aIter2 (Pre : List Nat) (A1 : List Nat) (A2 : List Nat) (K1 : List Nat) (G : List Nat) (hPre : Sym4 Pre) (hA1 : ∀ a ∈ A1, a ∈ T3) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK1 : ∀ a ∈ K1, a ∈ Z2) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (Pre ++ (A1 ++ (3 :: (A2)))) (1 :: (K1 ++ (3 :: (1 :: (G))))))
      (hd QF.SA (Pre ++ (A1 ++ (2 :: (A2)))) (1 :: (List.replicate K1.length 3 ++ (3 :: (1 :: (G)))))) := by
  have hV : Valid [ALL, T3, Z2, Z2, ALL] [Pre, A1, A2, K1, G] := Valid.cons hPre (Valid.cons hA1 (Valid.cons hA2 (Valid.cons hK1 (Valid.cons hG (Valid.nil _)))))
  exact checkTT (env := [Pre, A1, A2, K1, G]) (E := []) (k := 10) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id, .sym 3, .blk 2 .id]) (rs := [.sym 1, .blk 3 .id, .sym 3, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 2, .blk 2 .id]) (rs' := [.sym 1, .blk 3 (.const 3), .sym 3, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `A` used up, `K` untouched: it divides. -/
theorem endDivM (X : List Nat) (A2 : List Nat) (K2 : List Nat) (G : List Nat) (hX : NoB X) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (X ++ (1 :: (A2))) (1 :: (K2 ++ (1 :: (G)))))
      (hdR QF.FR1 (X ++ (1 :: (List.replicate A2.length 3 ++ (1 :: (K2 ++ ([1])))))) (G)) := by
  have hV : Valid [NB, Z2, T3, ALL] [X, A2, K2, G] := Valid.cons hX (Valid.cons hA2 (Valid.cons hK2 (Valid.cons hG (Valid.nil _))))
  exact checkTF (env := [X, A2, K2, G]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 (.const 3), .sym 1, .blk 2 .id, .sym 1]) (rs' := [.blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `A` used up, `K` touched: shrink `K` and try again. -/
theorem endNdivM (X : List Nat) (A2 : List Nat) (K1 : List Nat) (K2 : List Nat) (G : List Nat) (hX : NoB X) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK1 : ∀ a ∈ K1, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (X ++ (1 :: (A2))) (1 :: (2 :: (K1 ++ (K2 ++ (3 :: (1 :: (G))))))))
      (hd QF.RS1 (X ++ (1 :: (List.replicate A2.length 3 ++ (1 :: (2 :: (K1 ++ (K2))))))) (1 :: (1 :: (G)))) := by
  have hV : Valid [NB, Z2, Z2, T3, ALL] [X, A2, K1, K2, G] := Valid.cons hX (Valid.cons hA2 (Valid.cons hK1 (Valid.cons hK2 (Valid.cons hG (Valid.nil _)))))
  exact checkTT (env := [X, A2, K1, K2, G]) (E := []) (k := 10) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 2, .blk 2 .id, .blk 3 .id, .sym 3, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 (.const 3), .sym 1, .sym 2, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 1, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `A` used up, `K` untouched: it divides. -/
theorem endDivB (A2 : List Nat) (K2 : List Nat) (G : List Nat) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (A2) (1 :: (K2 ++ (1 :: (G)))))
      (hdR QF.FR1 (List.replicate A2.length 3 ++ (1 :: (K2 ++ ([1])))) (G)) := by
  have hV : Valid [Z2, T3, ALL] [A2, K2, G] := Valid.cons hA2 (Valid.cons hK2 (Valid.cons hG (Valid.nil _)))
  exact checkTF (env := [A2, K2, G]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 (.const 3), .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `A` used up, `K` touched: shrink `K` and try again. -/
theorem endNdivB (A2 : List Nat) (K1 : List Nat) (K2 : List Nat) (G : List Nat) (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK1 : ∀ a ∈ K1, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (A2) (1 :: (2 :: (K1 ++ (K2 ++ (3 :: (1 :: (G))))))))
      (hd QF.RS1 (List.replicate A2.length 3 ++ (1 :: (2 :: (K1 ++ (K2))))) (1 :: (1 :: (G)))) := by
  have hV : Valid [Z2, Z2, T3, ALL] [A2, K1, K2, G] := Valid.cons hA2 (Valid.cons hK1 (Valid.cons hK2 (Valid.cons hG (Valid.nil _))))
  exact checkTT (env := [A2, K1, K2, G]) (E := []) (k := 10) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 2, .blk 1 .id, .blk 2 .id, .sym 3, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 (.const 3), .sym 1, .sym 2, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Restore `K`, check `|K| ≥ 2`, go to `A`. -/
theorem rsStart (Pre : List Nat) (Ac : List Nat) (Kb : List Nat) (G : List Nat) (c1 : Nat) (c2 : Nat) (hPre : Sym4 Pre) (hAc : ∀ a ∈ Ac, a ∈ T3) (hKb : Bits Kb) (hG : Sym4 G) (hc1 : c1 ∈ bits) (hc2 : c2 ∈ bits) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (Ac ++ (1 :: (Kb ++ (c1 :: ([c2])))))) (1 :: (G)))
      (hd QF.SA (Pre ++ (Ac)) (1 :: (List.replicate Kb.length 3 ++ (3 :: (3 :: (1 :: (G))))))) := by
  have hV : Valid [ALL, T3, bits, ALL] [Pre, Ac, Kb, G] := Valid.cons hPre (Valid.cons hAc (Valid.cons hKb (Valid.cons hG (Valid.nil _))))
  rcases mem_bits hc1 with rfl | rfl <;> rcases mem_bits hc2 with rfl | rfl
  · exact checkTT (env := [Pre, Ac, Kb, G]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 2, .sym 2]) (rs := [.sym 1, .blk 3 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3, .sym 3, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Pre, Ac, Kb, G]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 2, .sym 3]) (rs := [.sym 1, .blk 3 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3, .sym 3, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Pre, Ac, Kb, G]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 3, .sym 2]) (rs := [.sym 1, .blk 3 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3, .sym 3, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Pre, Ac, Kb, G]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id, .sym 3, .sym 3]) (rs := [.sym 1, .blk 3 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3, .sym 3, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `|K| = 1`: no divisor. -/
theorem fr0K1 (Pre : List Nat) (Ac : List Nat) (G : List Nat) (c : Nat) (hPre : Sym4 Pre) (hAc : ∀ a ∈ Ac, a ∈ T3) (hG : Sym4 G) (hc : c ∈ bits) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (Ac ++ (1 :: ([c])))) (1 :: (G)))
      (hdR QF.FR0 (Pre ++ (Ac ++ ([1]))) (3 :: (1 :: (G)))) := by
  have hV : Valid [ALL, T3, ALL] [Pre, Ac, G] := Valid.cons hPre (Valid.cons hAc (Valid.cons hG (Valid.nil _)))
  rcases mem_bits hc with rfl | rfl
  · exact checkTF (env := [Pre, Ac, G]) (E := []) (k := 2) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [Pre, Ac, G]) (E := []) (k := 2) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3]) (rs := [.sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `|K| = 0`: no divisor. -/
theorem fr0K0 (Pre : List Nat) (Ac : List Nat) (G : List Nat) (hPre : Sym4 Pre) (hAc : ∀ a ∈ Ac, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (Ac ++ ([1]))) (1 :: (G)))
      (hdR QF.FR0 (Pre ++ (Ac ++ ([1]))) (1 :: (G))) := by
  have hV : Valid [ALL, T3, ALL] [Pre, Ac, G] := Valid.cons hPre (Valid.cons hAc (Valid.cons hG (Valid.nil _)))
  exact checkTF (env := [Pre, Ac, G]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One number, `k = 0`. -/
theorem fr0N0 (G : List Nat) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.RS1 ([]) (1 :: (G)))
      (hdR QF.FR0 ([]) (1 :: (G))) := by
  have hV : Valid [ALL] [G] := Valid.cons hG (Valid.nil _)
  exact checkTF (env := [G]) (E := []) (k := 1) hV trivial
    (ls := []) (rs := [.sym 1, .blk 0 .id])
    (ls' := []) (rs' := [.sym 1, .blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One number, `k = 1`. -/
theorem fr0N1 (G : List Nat) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.RS1 ([3]) (1 :: (G)))
      (hdR QF.FR0 ([]) (3 :: (1 :: (G)))) := by
  have hV : Valid [ALL] [G] := Valid.cons hG (Valid.nil _)
  exact checkTF (env := [G]) (E := []) (k := 2) hV trivial
    (ls := [.sym 3]) (rs := [.sym 1, .blk 0 .id])
    (ls' := []) (rs' := [.sym 3, .sym 1, .blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One number, `k ≥ 2`. -/
theorem fr0N2 (K : List Nat) (G : List Nat) (hK : ∀ a ∈ K, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.RS1 (K ++ (3 :: ([3]))) (1 :: (G)))
      (hdR QF.FR0 ([]) (K ++ (3 :: (3 :: (1 :: (G)))))) := by
  have hV : Valid [T3, ALL] [K, G] := Valid.cons hK (Valid.cons hG (Valid.nil _))
  exact checkTF (env := [K, G]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3, .sym 3]) (rs := [.sym 1, .blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 3, .sym 3, .sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem succ_mod (i d : Nat) (hd2 : 2 ≤ d) :
    (i + 1) % d = if i % d + 1 < d then i % d + 1 else 0 := by
  have h1 : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (i + 1) % d = (i % d + 1) % d := by
    rw [Nat.add_mod, h1]
  have h3 : i % d < d := Nat.mod_lt _ (by omega)
  split
  · rw [h2]; exact Nat.mod_eq_of_lt (by assumption)
  · have : i % d + 1 = d := by omega
    rw [h2, this, Nat.mod_self]

theorem aLoop (Pre G : List Nat) (hPre : Sym4 Pre) (hG : Sym4 G) (d : Nat) (hd2 : 2 ≤ d) :
    ∀ u i : Nat,
    zfacLogic.Reach
      (hd QF.SA (Pre ++ (List.replicate u 3 ++ List.replicate i 2))
        (1 :: (List.replicate (i % d) 2 ++ (List.replicate (d - i % d) 3 ++ 1 :: G))))
      (hd QF.SA (Pre ++ List.replicate (i + u) 2)
        (1 :: (List.replicate ((i + u) % d) 2 ++ (List.replicate (d - (i + u) % d) 3 ++ 1 :: G))))
  | 0, i => by simpa using LTM.Reach.refl _ _
  | u + 1, i => by
    have hj : i % d < d := Nat.mod_lt _ (by omega)
    have ih := fun i' => aLoop Pre G hPre hG d hd2 u i'
    have hsm := succ_mod i d hd2
    have e : i + 1 + u = i + (u + 1) := by omega
    have hmid := ih (i + 1)
    rw [e] at hmid
    by_cases hlt : i % d + 1 < d
    · simp only [hlt, ↓reduceIte] at hsm
      have h1 := aIter1 Pre (List.replicate u 3) (List.replicate i 2) (List.replicate (i % d) 2)
        (List.replicate (d - i % d - 2) 3) G hPre (rep_t3 u) (rep_z2 i) (rep_z2 _) (rep_t3 _) hG
      have hrep : List.replicate (d - i % d) 3 = 3 :: 3 :: List.replicate (d - i % d - 2) 3 := by
        obtain ⟨k, hk⟩ : ∃ k, d - i % d = k + 2 := ⟨d - i % d - 2, by omega⟩
        rw [hk]; simp [List.replicate_succ]
      have hrep2 : List.replicate (d - (i + 1) % d) 3 = 3 :: List.replicate (d - i % d - 2) 3 := by
        rw [hsm]
        obtain ⟨k, hk⟩ : ∃ k, d - i % d = k + 2 := ⟨d - i % d - 2, by omega⟩
        have : d - (i % d + 1) = k + 1 := by omega
        rw [this, show d - i % d - 2 = k by omega]
        simp [List.replicate_succ]
      refine LTM.Reach.trans (c' := hd QF.SA (Pre ++ (List.replicate u 3 ++ List.replicate (i + 1) 2))
        (1 :: (List.replicate ((i + 1) % d) 2 ++ (List.replicate (d - (i + 1) % d) 3 ++ 1 :: G))))
        (h1.of_eq ?_ ?_) hmid
      · rw [hrep]; simp [List.replicate_succ']
      · have hA : List.replicate (i + 1) 2 = 2 :: List.replicate i 2 := rfl
        have hK : List.replicate (i % d + 1) 2 = List.replicate (i % d) 2 ++ [2] := List.replicate_succ' ..
        rw [hA, hrep2, hsm, hK]; simp
    · simp only [hlt, ↓reduceIte] at hsm
      have e3 : d - i % d = 1 := by omega
      have h1 := aIter2 Pre (List.replicate u 3) (List.replicate i 2) (List.replicate (i % d) 2) G hPre
        (rep_t3 u) (rep_z2 i) (rep_z2 _) hG
      refine LTM.Reach.trans (c' := hd QF.SA (Pre ++ (List.replicate u 3 ++ List.replicate (i + 1) 2))
        (1 :: (List.replicate ((i + 1) % d) 2 ++ (List.replicate (d - (i + 1) % d) 3 ++ 1 :: G))))
        (h1.of_eq ?_ ?_) hmid
      · rw [e3]; simp [List.replicate_succ']
      · have hA : List.replicate (i + 1) 2 = 2 :: List.replicate i 2 := rfl
        have hd' : List.replicate d 3 = List.replicate (i % d) 3 ++ [3] := by
          rw [← List.replicate_succ']; congr 1; omega
        rw [hA, hsm]
        simp only [List.length_replicate, Nat.sub_zero, List.replicate_zero, List.nil_append, hd']
        simp


def B0 : List Nat := [0]

/-- The cell left of `A` is a separator `M` (or blank). -/
def LeftEnd (Pre : List Nat) : Prop := Pre = [] ∨ ∃ X, NoB X ∧ Pre = X ++ [1]

theorem endDivG (Pre : List Nat) (hLE : LeftEnd Pre) (A2 K2 G : List Nat)
    (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (Pre ++ A2) (1 :: (K2 ++ 1 :: G)))
      (hdR QF.FR1 (Pre ++ (List.replicate A2.length 3 ++ 1 :: (K2 ++ [1]))) G) := by
  rcases hLE with rfl | ⟨X, hX, rfl⟩
  · simpa using endDivB A2 K2 G hA2 hK2 hG
  · simpa using endDivM X A2 K2 G hX hA2 hK2 hG

theorem endNdivG (Pre : List Nat) (hLE : LeftEnd Pre) (A2 K1 K2 G : List Nat)
    (hA2 : ∀ a ∈ A2, a ∈ Z2) (hK1 : ∀ a ∈ K1, a ∈ Z2) (hK2 : ∀ a ∈ K2, a ∈ T3) (hG : Sym4 G) :
    zfacLogic.Reach (hd QF.SA (Pre ++ A2) (1 :: (2 :: (K1 ++ (K2 ++ 3 :: 1 :: G)))))
      (hd QF.RS1 (Pre ++ (List.replicate A2.length 3 ++ 1 :: (2 :: (K1 ++ K2)))) (1 :: 1 :: G)) := by
  rcases hLE with rfl | ⟨X, hX, rfl⟩
  · simpa using endNdivB A2 K1 K2 G hA2 hK1 hK2 hG
  · simpa using endNdivM X A2 K1 K2 G hX hA2 hK1 hK2 hG


/-- RS1 → SA: `K` is reset to `1^d` (`d ≥ 2`). -/
theorem rsG (Pre G : List Nat) (hPre : Sym4 Pre) (hG : Sym4 G) (a d : Nat) (hd2 : 2 ≤ d)
    (Kw : List Nat) (hK : Bits Kw) (hl : Kw.length = d) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (List.replicate a 3 ++ 1 :: Kw)) (1 :: G))
      (hd QF.SA (Pre ++ List.replicate a 3) (1 :: (List.replicate d 3 ++ 1 :: G))) := by
  rcases List.eq_nil_or_concat Kw with rfl | ⟨K1, c2, rfl⟩
  · simp at hl; omega
  rcases List.eq_nil_or_concat K1 with rfl | ⟨Kb, c1, rfl⟩
  · simp at hl; omega
  have hc2 : c2 ∈ bits := hK c2 (by simp)
  have hc1 : c1 ∈ bits := hK c1 (by simp)
  have hKb : Bits Kb := fun a ha => hK a (by simp [ha])
  have h := rsStart Pre (List.replicate a 3) Kb G c1 c2 hPre (rep_t3 a) hKb hG hc1 hc2
  refine h.of_eq (by simp) ?_
  have : d = Kb.length + 2 := by simp at hl; omega
  rw [this, ← List.replicate_append_replicate]
  simp

theorem roundDiv (Pre G : List Nat) (hPre : Sym4 Pre) (hLE : LeftEnd Pre) (hG : Sym4 G) (a d : Nat)
    (hd2 : 2 ≤ d) (Kw : List Nat) (hK : Bits Kw) (hl : Kw.length = d) (hdiv : a % d = 0) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (List.replicate a 3 ++ 1 :: Kw)) (1 :: G))
      (hdR QF.FR1 (Pre ++ (List.replicate a 3 ++ 1 :: (List.replicate d 3 ++ [1]))) G) := by
  have h1 := rsG Pre G hPre hG a d hd2 Kw hK hl
  have h2 := aLoop Pre G hPre hG d hd2 a 0
  have h2' : zfacLogic.Reach (hd QF.SA (Pre ++ List.replicate a 3) (1 :: (List.replicate d 3 ++ 1 :: G)))
      (hd QF.SA (Pre ++ List.replicate a 2) (1 :: (List.replicate d 3 ++ 1 :: G))) :=
    h2.of_eq (by simp) (by simp [hdiv])
  have h3 := endDivG Pre hLE (List.replicate a 2) (List.replicate d 3) G (rep_z2 a) (rep_t3 d) hG
  exact h1.trans (h2'.trans (by simpa using h3))

theorem roundNdiv (Pre G : List Nat) (hPre : Sym4 Pre) (hLE : LeftEnd Pre) (hG : Sym4 G) (a d : Nat)
    (hd2 : 2 ≤ d) (Kw : List Nat) (hK : Bits Kw) (hl : Kw.length = d) (hdiv : a % d ≠ 0) :
    zfacLogic.Reach (hd QF.RS1 (Pre ++ (List.replicate a 3 ++ 1 :: Kw)) (1 :: G))
      (hd QF.RS1 (Pre ++ (List.replicate a 3 ++ 1 :: (List.replicate (a % d) 2 ++
        List.replicate (d - a % d - 1) 3))) (1 :: 1 :: G)) := by
  have h1 := rsG Pre G hPre hG a d hd2 Kw hK hl
  have h2 := aLoop Pre G hPre hG d hd2 a 0
  have hj : a % d < d := Nat.mod_lt _ (by omega)
  obtain ⟨j, hjj⟩ : ∃ j, a % d = j + 1 := ⟨a % d - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, d - a % d = k + 1 := ⟨d - a % d - 1, by omega⟩
  have h2' : zfacLogic.Reach (hd QF.SA (Pre ++ List.replicate a 3) (1 :: (List.replicate d 3 ++ 1 :: G)))
      (hd QF.SA (Pre ++ List.replicate a 2)
        (1 :: (2 :: (List.replicate j 2 ++ (List.replicate k 3 ++ 3 :: 1 :: G))))) := by
    refine h2.of_eq (by simp) ?_
    have hk' : d - (j + 1) = k + 1 := by rw [← hjj]; exact hk
    rw [Nat.zero_add, hjj, hk']
    simp [List.replicate_succ, rep_cons_comm]
  have h3 := endNdivG Pre hLE (List.replicate a 2) (List.replicate j 2) (List.replicate k 3) G
    (rep_z2 a) (rep_z2 j) (rep_t3 k) hG
  refine h1.trans (h2'.trans (h3.of_eq rfl ?_))
  have e : d - a % d - 1 = k := by omega
  rw [e, hjj]
  simp [List.replicate_succ]


/-- `∃ d', 2 ≤ d' ≤ d` dividing `a`. -/
def divRes (a d : Nat) : Bool := (List.range (d + 1)).any fun d' => decide (2 ≤ d') && a % d' == 0

theorem divRes_succ (a n : Nat) :
    divRes a (n + 1) = (divRes a n || (decide (2 ≤ n + 1) && a % (n + 1) == 0)) := by
  unfold divRes
  rw [List.range_succ (n := n + 1)]
  simp [List.any_append]

theorem divRes_small (a d : Nat) (hd : d < 2) : divRes a d = false := by
  unfold divRes
  rw [Bool.eq_false_iff]
  intro h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨x, hx, h1, -⟩ := h
  omega

theorem divLoop (Pre : List Nat) (hPre : Sym4 Pre) (hLE : LeftEnd Pre) (a : Nat) :
    ∀ (d : Nat) (Kw : List Nat), Bits Kw → Kw.length = d → ∀ G : List Nat, Sym4 G →
    ∃ L Mr, NoB L ∧ NoB Mr ∧
      zfacLogic.Reach (hd QF.RS1 (Pre ++ (List.replicate a 3 ++ 1 :: Kw)) (1 :: G))
        (hdR (if divRes a d then QF.FR1 else QF.FR0) (Pre ++ L) (Mr ++ G)) := by
  intro d
  induction d with
  | zero =>
    intro Kw hK hl G hG
    have hKw : Kw = [] := List.eq_nil_of_length_eq_zero hl
    subst hKw
    have h := fr0K0 Pre (List.replicate a 3) G hPre (rep_t3 a) hG
    refine ⟨List.replicate a 3 ++ [1], [1], (t3_noB (rep_t3 a)).app (NoB.cons one_nb NoB.nil),
      NoB.cons one_nb NoB.nil, ?_⟩
    simp only [divRes_small a 0 (by omega), Bool.false_eq_true, ↓reduceIte]
    simpa using h
  | succ n ih =>
    intro Kw hK hl G hG
    by_cases h1 : n + 1 < 2
    · -- `|K| = 1`
      have hn : n = 0 := by omega
      subst hn
      obtain ⟨c, rfl⟩ : ∃ c, Kw = [c] := by
        match Kw, hl with
        | [c], _ => exact ⟨c, rfl⟩
      have hc : c ∈ bits := hK c (by simp)
      have h := fr0K1 Pre (List.replicate a 3) G c hPre (rep_t3 a) hG hc
      refine ⟨List.replicate a 3 ++ [1], [3, 1], (t3_noB (rep_t3 a)).app (NoB.cons one_nb NoB.nil),
        NoB.cons (by simp [NB]) (NoB.cons one_nb NoB.nil), ?_⟩
      simp only [divRes_small a 1 (by omega), Bool.false_eq_true, ↓reduceIte]
      simpa using h
    · have hd2 : 2 ≤ n + 1 := by omega
      by_cases hdiv : a % (n + 1) = 0
      · have h := roundDiv Pre G hPre hLE hG a (n + 1) hd2 Kw hK hl hdiv
        refine ⟨List.replicate a 3 ++ 1 :: (List.replicate (n + 1) 3 ++ [1]), [],
          (t3_noB (rep_t3 a)).app (NoB.cons one_nb ((t3_noB (rep_t3 _)).app (NoB.cons one_nb NoB.nil))),
          NoB.nil, ?_⟩
        have : divRes a (n + 1) = true := by
          rw [divRes_succ]; simp [hdiv, hd2]
        simp only [this, ↓reduceIte]
        simpa using h
      · have h := roundNdiv Pre G hPre hLE hG a (n + 1) hd2 Kw hK hl hdiv
        have hj : a % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
        have hK' : Bits (List.replicate (a % (n + 1)) 2 ++ List.replicate (n + 1 - a % (n + 1) - 1) 3) := by
          intro x hx
          simp only [List.mem_append, List.mem_replicate] at hx
          rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [bits]
        have hl' : (List.replicate (a % (n + 1)) 2 ++ List.replicate (n + 1 - a % (n + 1) - 1) 3).length = n := by
          simp; omega
        obtain ⟨L, Mr, hL, hMr, hR⟩ := ih _ hK' hl' (1 :: G) (Sym4.cons (by simp [ALL]) hG)
        refine ⟨L, Mr ++ [1], hL, hMr.app (NoB.cons one_nb NoB.nil), ?_⟩
        have : divRes a (n + 1) = divRes a n := by
          rw [divRes_succ]; simp [hdiv]
        rw [this]
        refine h.trans (hR.of_eq rfl ?_)
        simp


theorem numbers_eq : ∀ (f : Nat) (r : List Bool) (cur : Nat) (fr : List Nat),
    fr.reverse ++ numsAux f r cur =
      (parseState f r cur fr).2.reverse ++ [(parseState f r cur fr).1]
  | 0, r, cur, fr => by simp [numsAux, parseState]
  | f + 1, [], cur, fr => by simp [numsAux, parseState]
  | f + 1, [true], cur, fr => by simp [numsAux, parseState]
  | f + 1, true :: b :: r, cur, fr => by
    have := numbers_eq f r (2 * cur + if b then 1 else 0) fr
    simp only [numsAux, parseState]
    rw [this]
    cases b <;> simp [bitN, Nat.add_comm]
  | f + 1, false :: r, cur, fr => by
    have := numbers_eq f r 0 (cur :: fr)
    simp only [numsAux, parseState]
    rw [← this]
    simp

theorem lay1_last2 : ∀ (fr : List Nat) (c k a : Nat) (rest : List Nat),
    fr.reverse ++ [c] = k :: a :: rest →
    ∃ Pre, lay1 c fr = Pre ++ (List.replicate a 3 ++ 1 :: List.replicate k 3) ∧ LeftEnd Pre ∧ Sym4 Pre
  | [], c, k, a, rest, h => by simp at h
  | [n], c, k, a, rest, h => by
    simp at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨[], by simp [lay1], Or.inl rfl, Sym4.nil⟩
  | n :: n' :: fr, c, k, a, rest, h => by
    have h2 : (n' :: fr).reverse ++ [n] ++ [c] = k :: a :: rest := by simpa using h
    have hlen : 2 ≤ ((n' :: fr).reverse ++ [n]).length := by simp
    obtain ⟨rest', hL1⟩ : ∃ rest', (n' :: fr).reverse ++ [n] = k :: a :: rest' := by
      generalize (n' :: fr).reverse ++ [n] = L at h2 hlen
      match L, hlen, h2 with
      | x :: y :: L'', _, h2 =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl, -⟩ := h2
        exact ⟨L'', rfl⟩
    obtain ⟨Pre, hP, hLE, hS⟩ := lay1_last2 (n' :: fr) n k a rest' hL1
    refine ⟨List.replicate c 3 ++ 1 :: Pre, ?_, ?_, ?_⟩
    · rw [show lay1 c (n :: n' :: fr) = List.replicate c 3 ++ 1 :: lay1 n (n' :: fr) from rfl, hP]
      simp
    · rcases hLE with rfl | ⟨X, hX, rfl⟩
      · exact Or.inr ⟨List.replicate c 3, t3_noB (rep_t3 c), by simp⟩
      · exact Or.inr ⟨List.replicate c 3 ++ 1 :: X, (t3_noB (rep_t3 c)).app (NoB.cons one_nb hX), by simp⟩
    · exact (Sym4.rep c 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hS)


theorem truthPhase (Sb : List Bool) (Rt : List Nat) (hRt : Sym4 Rt) :
    ∃ L Mr, NoB L ∧ NoB Mr ∧
      zfacLogic.Reach (hd QF.HPF (1 :: crev Sb) (0 :: Rt))
        (hdR (if inLF Sb then QF.FR1 else QF.FR0) L
          (Mr ++ (List.replicate (Sb.length + 1) 0 ++ Rt))) := by
  have hconv := convLoop Rt hRt Sb.length Sb 0 [] 1 (Nat.le_refl _) (Nat.le_refl _)
  have hnum := numbers_eq Sb.length Sb 0 []
  have hG : Sym4 (List.replicate (1 + Sb.length) 0 ++ Rt) := (zeros4 _).app hRt
  simp only [List.reverse_nil, List.nil_append] at hnum
  have hnum' : numbers Sb = (parseState Sb.length Sb 0 []).2.reverse ++ [(parseState Sb.length Sb 0 []).1] := hnum
  generalize parseState Sb.length Sb 0 [] = p at hconv hnum'
  obtain ⟨c, fr⟩ := p
  simp only at hconv hnum'
  have hconv' : zfacLogic.Reach (hd QF.HPF (1 :: crev Sb) (0 :: Rt))
      (hd QF.RS1 (lay1 c fr) (1 :: (List.replicate (1 + Sb.length) 0 ++ Rt))) := by
    refine hconv.of_eq ?_ rfl
    simp [lyt]
  have e : 1 + Sb.length = Sb.length + 1 := by omega
  rw [e] at hconv' hG
  cases fr with
  | nil =>
    refine ⟨[], List.replicate c 3 ++ [1], NoB.nil, (t3_noB (rep_t3 c)).app (NoB.cons one_nb NoB.nil), ?_⟩
    have hin : inLF Sb = false := by
      unfold inLF; rw [hnum']; simp
    rw [hin]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine hconv'.trans ?_
    match c with
    | 0 => simpa [lay1] using fr0N0 _ hG
    | 1 => simpa [lay1] using fr0N1 _ hG
    | k + 2 =>
      have h := fr0N2 (List.replicate k 3) _ (rep_t3 k) hG
      refine h.of_eq ?_ ?_
      · have e2 : List.replicate (k + 2) 3 = List.replicate k 3 ++ [3, 3] := by
          rw [← List.replicate_append_replicate]; rfl
        simp [lay1, e2]
      · simp [List.replicate_succ, rep_cons_comm]
  | cons n fr' =>
    obtain ⟨k, a, rest, hkar⟩ : ∃ k a rest, (n :: fr').reverse ++ [c] = k :: a :: rest := by
      have hlen : 2 ≤ ((n :: fr').reverse ++ [c]).length := by simp
      generalize (n :: fr').reverse ++ [c] = L at hlen
      match L, hlen with
      | k :: a :: rest, _ => exact ⟨k, a, rest, rfl⟩
    obtain ⟨Pre, hP, hLE, hS⟩ := lay1_last2 (n :: fr') c k a rest hkar
    have hin : inLF Sb = divRes a k := by
      unfold inLF
      rw [hnum', hkar]
      rfl
    obtain ⟨L, Mr, hL, hMr, hR⟩ := divLoop Pre hS hLE a k (List.replicate k 3)
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; simp [bits]) (by simp) _ hG
    refine ⟨Pre ++ L, Mr, ?_, hMr, ?_⟩
    · have hPreN : NoB Pre := by
        rcases hLE with rfl | ⟨X, hX, rfl⟩
        · exact NoB.nil
        · exact hX.app (NoB.cons one_nb NoB.nil)
      exact hPreN.app hL
    · rw [hin]
      refine hconv'.trans ?_
      rw [hP]
      exact hR


/-! ## Blank prefix -/

theorem hdR_eq' (q : Nat) (A R : List Nat) :
    hdR q A R = ⟨q, sapp A.reverse blank, sapp R blank⟩ := by
  show (⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem sapp_zeros (g : Nat) : sapp (List.replicate g 0) blank = blank := by
  induction g with
  | zero => rfl
  | succ g ih => 
    show scons 0 (sapp (List.replicate g 0) blank) = blank
    rw [ih, scons_blank]

theorem hdR_zeros (q : Nat) (Gp A R : List Nat) (hGp : ∀ a ∈ Gp, a ∈ B0) :
    hdR q (Gp ++ A) R = hdR q A R := by
  have hz : Gp = List.replicate Gp.length 0 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, fun a ha => ?_⟩
    have := hGp a ha
    simpa [B0] using this
  rw [hdR_eq', hdR_eq', List.reverse_append, sapp_append, hz]
  simp [sapp_zeros]


/-! ## New instance and result (generated) -/

/-- New instance: `M_2`, `H`, walk to the start of `s`. -/
theorem ni0 (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zfacLogic.Reach (hdR QF.NI (1 :: (j ++ (1 :: (s)))) ([]))
      (hdR Q.GC (1 :: (1 :: (j ++ ([1])))) (s ++ ([1]))) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkFF (env := [j, s]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The copy is done: `M_2` meets the empty slot, the truth routine starts. -/
theorem ni2 (Xr : List Nat) (j : List Nat) (s : List Nat) (hXr : Bits Xr) (hj : Bits j) (hs : Bits s) :
    zfacLogic.Reach (hdR Q.GC (Xr ++ (1 :: (1 :: (j ++ (1 :: (s)))))) ([1]))
      (hd QF.HPF (1 :: (Xr)) (0 :: (1 :: (j ++ (1 :: (s ++ ([1]))))))) := by
  have hV : Valid [bits, bits, bits] [Xr, j, s] := Valid.cons hXr (Valid.cons hj (Valid.cons hs (Valid.nil _)))
  exact checkFT (env := [Xr, j, s]) (E := []) (k := 12) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 0, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The result 0 is reported and the left side erased. -/
theorem frPath0 (Lc : List Nat) (Mr : List Nat) (Gp : List Nat) (j : List Nat) (s : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hGp : ∀ a ∈ Gp, a ∈ B0) (hj : Bits j) (hs : Bits s) :
    zfacLogic.Reach (hdR QF.FR0 (Lc) (Mr ++ (0 :: (Gp ++ (1 :: (j ++ (1 :: (s ++ ([1])))))))))
      (hdR Q.GRB (Gp ++ (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: ([1])))))))) ([])) := by
  have hV : Valid [NB, NB, B0, bits, bits] [Lc, Mr, Gp, j, s] := Valid.cons hLc (Valid.cons hMr (Valid.cons hGp (Valid.cons hj (Valid.cons hs (Valid.nil _)))))
  exact checkFF (env := [Lc, Mr, Gp, j, s]) (E := []) (k := 16) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1])
    (ls' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The result 1 is reported and the left side erased. -/
theorem frPath1 (Lc : List Nat) (Mr : List Nat) (Gp : List Nat) (j : List Nat) (s : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hGp : ∀ a ∈ Gp, a ∈ B0) (hj : Bits j) (hs : Bits s) :
    zfacLogic.Reach (hdR QF.FR1 (Lc) (Mr ++ (0 :: (Gp ++ (1 :: (j ++ (1 :: (s ++ ([1])))))))))
      (hdR Q.GRB (Gp ++ (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1]))))))))) ([])) := by
  have hV : Valid [NB, NB, B0, bits, bits] [Lc, Mr, Gp, j, s] := Valid.cons hLc (Valid.cons hMr (Valid.cons hGp (Valid.cons hj (Valid.cons hs (Valid.nil _)))))
  exact checkFF (env := [Lc, Mr, Gp, j, s]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1])
    (ls' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## One pair -/

/-- Pair start: `M_g J M_1 s`, state `NI` on the blank after `s`. -/
def layF (J S : Nat) : ZC := ⟨QF.NI, sapp (layWord J S).reverse blank, blank⟩

theorem layF_hdR (J S : Nat) :
    layF J S = hdR QF.NI (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) [] := by
  rw [hdR_eq']
  simp only [layF, layWord, sapp]

theorem Reach_pos {M : LTM} {c c' : ZC} (h : M.Reach c c') (hq : c.q ≠ c'.q) : M.Reach1 c c' := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    have : c = c' := Option.some.inj hn
    exact absurd (by rw [this]) hq
  | succ n => exact ⟨n, hn⟩

theorem newInstF (J S : Nat) :
    zfacLogic.Reach1 (layF J S) (TR (bitsOf (str J)) (str S) (inLF (str S))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  rw [layF_hdR]
  have h0 := ni0 (bitsOf (str J)) (bitsOf (str S)) hj hs
  have h1 := gcLoop [1] (bitsOf (str J)) [] (NoB.cons one_nb NoB.nil) hj Sym4.nil (bitsOf (str S)) []
    Bits.nil hs
  have h2 := ni2 (bitsOf (str S)).reverse (bitsOf (str J)) (bitsOf (str S)) (Bits.ofB _).rev hj hs
  have hRt : Sym4 (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1]))) :=
    Sym4.cons (by simp [ALL]) (hj.sym4.app (Sym4.cons (by simp [ALL]) ((Bits.ofB _).sym4.app
      (Sym4.cons (by simp [ALL]) Sym4.nil))))
  obtain ⟨L, Mr, hL, hMr, h3⟩ := truthPhase (str S) _ hRt
  have hGp : ∀ a ∈ List.replicate (str S).length 0, a ∈ B0 := fun a ha => by
    rw [List.eq_of_mem_replicate ha]; simp [B0]
  have hfin : ∀ o : Bool, zfacLogic.Reach (hdR (if o then QF.FR1 else QF.FR0) L
      (Mr ++ (List.replicate ((str S).length + 1) 0 ++ (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ [1]))))))
      (TR (bitsOf (str J)) (str S) o) := by
    intro o
    cases o
    · have h := frPath0 L Mr (List.replicate (str S).length 0) (bitsOf (str J)) (bitsOf (str S)) hL hMr hGp hj hs
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine h.of_eq (by simp [List.replicate_succ]) ?_
      rw [hdR_zeros _ _ _ _ hGp]
      simp [TR, tflag]
    · have h := frPath1 L Mr (List.replicate (str S).length 0) (bitsOf (str J)) (bitsOf (str S)) hL hMr hGp hj hs
      simp only [↓reduceIte]
      refine h.of_eq (by simp [List.replicate_succ]) ?_
      rw [hdR_zeros _ _ _ _ hGp]
      simp [TR, tflag]
  have hall := (h0.trans ((h1.of_eq (by simp) rfl).trans (h2.of_eq (by simp) rfl))).trans
    ((h3.of_eq (by simp [crev, bitsOf]) rfl).trans (hfin (inLF (str S))))
  refine Reach_pos hall ?_
  show ((atR QF.NI).den _).q ≠ ((atR Q.GRB).den _).q
  rw [SC.den_q, SC.den_q]
  show QF.NI ≠ Q.GRB
  decide

theorem pair_mainF (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      ((¬ ¬ CorrectF J S → zfacLogic.zrun n (layF J S) = some (layF (absStepC CorrectF (J, S)).1 (absStepC CorrectF (J, S)).2)) ∧
       (¬ CorrectF J S → ∃ a c1 c2, a < n ∧ zfacLogic.zrun a (layF J S) = some c1 ∧ c1.q = zfacLogic.beep ∧
          zfacLogic.zstep c1 = some c2 ∧
          zfacLogic.zrun (n - a - 1) c2 = some (layF (absStepC CorrectF (J, S)).1 (absStepC CorrectF (J, S)).2))) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  obtain ⟨Fu, hFu, hD⟩ := dPhase (str J) (str S) (inLF (str S))
  have hA := (newInstF J S).trans hD
  obtain ⟨rS, hrS⟩ := numR_surj S hS
  obtain ⟨rJ, hrJ⟩ := numR_surj J hJ
  have eS : str S = rS.reverse := by rw [← hrS, str_numR]
  have eS1 : str (S + 1) = (incR rS).reverse := by rw [← hrS, ← numR_inc, str_numR]
  have eJ : str J = rJ.reverse := by rw [← hrJ, str_numR]
  have eJ1 : str (J + 1) = (incR rJ).reverse := by rw [← hrJ, ← numR_inc, str_numR]
  by_cases hc : CorrectF J S
  · have e : absStepC CorrectF (J, S) = (J, S + 1) := absStepC_pos hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = inLF (str S) := hc
    rw [ho] at hA
    have hok : zfacLogic.Reach
        (hdR (dpOf (bn (inLF (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inLF (str S)) ++ 1 :: Fu)))))
        (hd Q.SINC (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))) []) := by
      cases inLF (str S)
      · exact (dOk0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
      · exact (dOk1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl
    have hinc := sincL (1 :: bitsOf (str J)) (NoB.cons one_nb hj.noB) rS 0
    obtain ⟨n, hn⟩ := hA.trans (hok.trans (hinc.of_eq (c4 := layF J (S + 1)) (by rw [eS]; rfl) (by rw [layF_hdR, eS1]; simp)))
    exact ⟨n + 1, by omega, fun _ => hn, fun h => absurd hc h⟩
  · have e : absStepC CorrectF (J, S) = (J + 1, 1) := absStepC_neg hc
    rw [e]
    have ho : run (str J) (str S) (clock (str J) (str S)) = !inLF (str S) := by
      have h' : run (str J) (str S) (clock (str J) (str S)) ≠ inLF (str S) := hc
      revert h'
      cases run (str J) (str S) (clock (str J) (str S)) <;> cases inLF (str S) <;> decide
    rw [ho] at hA
    obtain ⟨Y, h1, h3⟩ : ∃ Y, zfacLogic.Reach
        (hdR (dpOf (bn (!inLF (str S)))) [1]
          (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: (1 :: (tflag (inLF (str S)) ++ 1 :: Fu)))))
        (hd Q.BEEP (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [1]))) Y) ∧
        zfacLogic.Reach (hdR Q.EAs (1 :: (bitsOf (str J) ++ 1 :: (bitsOf (str S) ++ 1 :: [2]))) Y)
          (hd Q.JINC (1 :: bitsOf (str J)) [1]) := by
      cases inLF (str S)
      · exact ⟨1 :: Fu, (dBad1 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad1E _ _ Fu hj hs hFu⟩
      · exact ⟨3 :: 1 :: Fu, (dBad0 _ _ Fu hj hs hFu).of_eq (by simp [dpOf, bn, tflag]) rfl,
          dBad0E _ _ Fu hj hs hFu⟩
    obtain ⟨n1, hn1⟩ := hA.trans h1
    obtain ⟨n2, hn2⟩ := h3.trans ((jincL rJ 0).of_eq (c4 := layF (J + 1) 1) (by rw [eJ]; rfl) (by rw [layF_hdR, eJ1, str_one]; rfl))
    refine ⟨n1 + 1 + 1 + n2, by omega, fun h => absurd hc h,
      fun _ => ⟨n1 + 1, _, _, by omega, hn1, rfl, beepStep _ _ Y, ?_⟩⟩
    rw [show n1 + 1 + 1 + n2 - (n1 + 1) - 1 = n2 by omega]
    exact hn2


end ZP.F
