module

public import ZP.PairF
public import ZP.CompileD
public import ZP.DefsD

@[expose] public section

/-! The pair lemma for the DLOG machine; the shared part is copied from `ZP/PairF.lean`. -/

namespace ZP.D

open ZP



open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zdlLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zdlLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
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
    zdlLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
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
    zdlLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, O13] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 23) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zdlLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
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
    zdlLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zdlLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zdlLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: (1 :: Rest)))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: (1 :: Rest))))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 19) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zdlLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zdlLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zdlLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR QF.NI (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR QF.NI (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR QF.NI (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR QF.NI (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zdlLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zdlLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
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
    zdlLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zdlLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zdlLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zdlLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zdlLogic.Reach
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
    ∃ g, 1 ≤ g ∧ zdlLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  have hB0 := hA.trans (zpBase_ext_zdlLogic.reach (hr.of_eq (by rw [hcode]) rfl))
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
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zdlLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zdlLogic.reach (hB.of_eq ?_ ?_))⟩
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
      zdlLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zdlLogic.reach h2)⟩



/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zdlLogic.Reach (TR (bitsOf Jb) Sb b)
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
    zdlLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
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
    zdlLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
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
    zdlLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
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
    zdlLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ (3 :: ([3]))))) (0 :: (Rt)))
      (hdR QF.DR ([2]) (T ++ (1 :: (L ++ (0 :: (0 :: (0 :: (Rt)))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .sym 3]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.sym 2]) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a pair `1 0` is consumed. -/
theorem dig2 (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zdlLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ (2 :: ([3]))))) (0 :: (Rt)))
      (hdR QF.DR ([]) (T ++ (1 :: (L ++ (0 :: (0 :: (0 :: (Rt)))))))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTF (env := [T, L, Rt]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 3]) (rs := [.sym 0, .blk 2 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 0, .sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling: one unmarked `1` is marked and a marked cell appended. -/
theorem dstep (Z : List Nat) (X : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hX : Sym4 X) :
    zdlLogic.Reach (hdR QF.DR (Z) (3 :: (X)))
      (hdR QF.DR (2 :: (Z ++ ([2]))) (X)) := by
  have hV : Valid [Z2, ALL] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.sym 2, .blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Doubling is done: unmark, back to the copy. -/
theorem dEnd (Z : List Nat) (Y : List Nat) (R : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) (hY : NoB Y) (hR : Sym4 R) :
    zdlLogic.Reach (hdR QF.DR (Z) (1 :: (Y ++ (0 :: (R)))))
      (hd QF.HPF (List.replicate Z.length 3 ++ (1 :: (Y))) (0 :: (R))) := by
  have hV : Valid [Z2, NB, ALL] [Z, Y, R] := Valid.cons hZ (Valid.cons hY (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [Z, Y, R]) (E := []) (k := 7) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 (.const 3), .sym 1, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion: a `0` ends the number; a new separator opens the next target. -/
theorem sepStep (T : List Nat) (L : List Nat) (Rt : List Nat) (hT : ∀ a ∈ T, a ∈ T3) (hL : NoB L) (hRt : Sym4 Rt) :
    zdlLogic.Reach (hd QF.HPF (T ++ (1 :: (L ++ ([2])))) (0 :: (Rt)))
      (hd QF.HPF (1 :: (T ++ (1 :: (L)))) (0 :: (0 :: (Rt)))) := by
  have hV : Valid [T3, NB, ALL] [T, L, Rt] := Valid.cons hT (Valid.cons hL (Valid.cons hRt (Valid.nil _)))
  exact checkTT (env := [T, L, Rt]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 0, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done (the copy is used up). -/
theorem endM (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zdlLogic.Reach (hd QF.HPF (Lp ++ ([1])) (0 :: (Rt)))
      (hd QD.E0 (Lp) (1 :: (0 :: (Rt)))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Conversion done after a trailing lone `1`. -/
theorem endLone (Lp : List Nat) (Rt : List Nat) (hLp : Sym4 Lp) (hRt : Sym4 Rt) :
    zdlLogic.Reach (hd QF.HPF (Lp ++ (1 :: ([3]))) (0 :: (Rt)))
      (hd QD.E0 (Lp) (1 :: (0 :: (0 :: (Rt))))) := by
  have hV : Valid [ALL, ALL] [Lp, Rt] := Valid.cons hLp (Valid.cons hRt (Valid.nil _))
  exact checkTT (env := [Lp, Rt]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 3]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 0, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## The conversion loop -/

theorem rep2_ext (m : Nat) : 2 :: (List.replicate m 2 ++ [2]) = List.replicate (m + 2) 2 := by
  rw [rep_snoc_eq]; rfl

theorem dloop (X : List Nat) (hX : Sym4 X) : ∀ u m : Nat,
    zdlLogic.Reach (hdR QF.DR (List.replicate m 2) (List.replicate u 3 ++ X))
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
    zdlLogic.Reach (hd QF.HPF (List.replicate t 3 ++ 1 :: (L ++ [bn b, 3])) (0 :: Rt))
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
    zdlLogic.Reach (hd QF.HPF (List.replicate cur 3 ++ 1 :: (lyt fr ++ crev r)) (List.replicate g 0 ++ Rt))
      (hd QD.E0 (lay1 (parseState f r cur fr).1 (parseState f r cur fr).2)
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




/-! ## Primality segments (generated) -/

/-- Conversion done: write the separator `D | P` at the left edge. -/
theorem e0 (X : List Nat) (R : List Nat) (hX : NoB X) (hR : Sym4 R) :
    zdlLogic.Reach (hd QD.E0 (X) (R))
      (hdR QD.CP1 ([1]) (X ++ (R))) := by
  have hV : Valid [NB, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [X, R]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy `P` into `D`: one cell. -/
theorem cpIter (Dd : List Nat) (Pm : List Nat) (Pu : List Nat) (G : List Nat) (hDd : ∀ a ∈ Dd, a ∈ T3) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hPu : ∀ a ∈ Pu, a ∈ T3) (hG : Sym4 G) :
    zdlLogic.Reach (hdR QD.CP1 (Dd ++ ([1])) (Pm ++ (3 :: (Pu ++ (1 :: (G))))))
      (hdR QD.CP1 (3 :: (Dd ++ ([1]))) (Pm ++ (2 :: (Pu ++ (1 :: (G)))))) := by
  have hV : Valid [T3, Z2, T3, ALL] [Dd, Pm, Pu, G] := Valid.cons hDd (Valid.cons hPm (Valid.cons hPu (Valid.cons hG (Valid.nil _))))
  exact checkFF (env := [Dd, Pm, Pu, G]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 3, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `P` is copied: unmark it. -/
theorem cpEnd (Dd : List Nat) (Pm : List Nat) (G : List Nat) (hDd : ∀ a ∈ Dd, a ∈ T3) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hG : Sym4 G) :
    zdlLogic.Reach (hdR QD.CP1 (Dd ++ ([1])) (Pm ++ (1 :: (G))))
      (hd QD.XS1 (Dd) (1 :: (List.replicate Pm.length 3 ++ (1 :: (G))))) := by
  have hV : Valid [T3, Z2, ALL] [Dd, Pm, G] := Valid.cons hDd (Valid.cons hPm (Valid.cons hG (Valid.nil _)))
  exact checkFT (env := [Dd, Pm, G]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 3), .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Primality: mark one cell of `P`, then one of `D` (not full). -/
theorem pIter1 (Dm : List Nat) (Du : List Nat) (Pm : List Nat) (Pu : List Nat) (Q : List Nat) (hDm : ∀ a ∈ Dm, a ∈ Z2) (hDu : ∀ a ∈ Du, a ∈ T3) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hPu : ∀ a ∈ Pu, a ∈ T3) (hQ : Sym4 Q) :
    zdlLogic.Reach (hdR QD.X4 (Dm ++ (3 :: (3 :: (Du ++ ([1]))))) (Pm ++ (3 :: (Pu ++ (1 :: (Q))))))
      (hdR QD.X4 (Dm ++ (2 :: (3 :: (Du ++ ([1]))))) (Pm ++ (2 :: (Pu ++ (1 :: (Q)))))) := by
  have hV : Valid [Z2, T3, Z2, T3, ALL] [Dm, Du, Pm, Pu, Q] := Valid.cons hDm (Valid.cons hDu (Valid.cons hPm (Valid.cons hPu (Valid.cons hQ (Valid.nil _)))))
  exact checkFF (env := [Dm, Du, Pm, Pu, Q]) (E := []) (k := 14) hV trivial
    (ls := [.blk 0 .id, .sym 3, .sym 3, .blk 1 .id, .sym 1]) (rs := [.blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 2, .sym 3, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Primality: mark one cell of `P`, then the last of `D`: reset `D`. -/
theorem pIter2 (Dm : List Nat) (Pm : List Nat) (Pu : List Nat) (Q : List Nat) (hDm : ∀ a ∈ Dm, a ∈ Z2) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hPu : ∀ a ∈ Pu, a ∈ T3) (hQ : Sym4 Q) :
    zdlLogic.Reach (hdR QD.X4 (Dm ++ (3 :: ([1]))) (Pm ++ (3 :: (Pu ++ (1 :: (Q))))))
      (hdR QD.X4 (List.replicate Dm.length 3 ++ (3 :: ([1]))) (Pm ++ (2 :: (Pu ++ (1 :: (Q)))))) := by
  have hV : Valid [Z2, Z2, T3, ALL] [Dm, Pm, Pu, Q] := Valid.cons hDm (Valid.cons hPm (Valid.cons hPu (Valid.cons hQ (Valid.nil _))))
  exact checkFF (env := [Dm, Pm, Pu, Q]) (E := []) (k := 16) hV trivial
    (ls := [.blk 0 .id, .sym 3, .sym 1]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 (.const 3), .sym 3, .sym 1]) (rs' := [.blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `P` used up, `D` untouched: `d` divides `p`. -/
theorem pEndDiv (Du : List Nat) (Pm : List Nat) (Q : List Nat) (hDu : ∀ a ∈ Du, a ∈ T3) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hQ : Sym4 Q) :
    zdlLogic.Reach (hdR QD.X4 (Du ++ ([1])) (Pm ++ (1 :: (Q))))
      (hdR QF.FR0 ([]) (Du ++ (1 :: (List.replicate Pm.length 3 ++ (1 :: (Q)))))) := by
  have hV : Valid [T3, Z2, ALL] [Du, Pm, Q] := Valid.cons hDu (Valid.cons hPm (Valid.cons hQ (Valid.nil _)))
  exact checkFF (env := [Du, Pm, Q]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 (.const 3), .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `P` used up, `D` touched: shrink `D`. -/
theorem pEndNdiv (Dm0 : List Nat) (Du : List Nat) (Pm : List Nat) (Q : List Nat) (hDm0 : ∀ a ∈ Dm0, a ∈ Z2) (hDu : ∀ a ∈ Du, a ∈ T3) (hPm : ∀ a ∈ Pm, a ∈ Z2) (hQ : Sym4 Q) :
    zdlLogic.Reach (hdR QD.X4 (Dm0 ++ (2 :: (Du ++ ([1])))) (Pm ++ (1 :: (Q))))
      (hd QD.XS1 (Dm0) (2 :: (Du ++ (1 :: (List.replicate Pm.length 3 ++ (1 :: (Q))))))) := by
  have hV : Valid [Z2, T3, Z2, ALL] [Dm0, Du, Pm, Q] := Valid.cons hDm0 (Valid.cons hDu (Valid.cons hPm (Valid.cons hQ (Valid.nil _))))
  exact checkFT (env := [Dm0, Du, Pm, Q]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs := [.blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1, .blk 2 (.const 3), .sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` shrinks at its left edge. -/
theorem xs1sweep (Dl : List Nat) (R : List Nat) (hDl : Bits Dl) (hR : Sym4 R) :
    zdlLogic.Reach (hd QD.XS1 (Dl) (R))
      (hdR QD.XS2 ([]) (Dl ++ (R))) := by
  have hV : Valid [bits, ALL] [Dl, R] := Valid.cons hDl (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [Dl, R]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Shrink `D` (`d ≥ 2`) and restore it. -/
theorem shr3 (Dr : List Nat) (Q : List Nat) (c0 : Nat) (c1 : Nat) (c2 : Nat) (hDr : Bits Dr) (hQ : Sym4 Q) (hc0 : c0 ∈ bits) (hc1 : c1 ∈ bits) (hc2 : c2 ∈ bits) :
    zdlLogic.Reach (hdR QD.XS2 ([]) (c0 :: (c1 :: (c2 :: (Dr ++ (1 :: (Q)))))))
      (hdR QD.X4 (3 :: (3 :: (List.replicate Dr.length 3 ++ ([1])))) (Q)) := by
  have hV : Valid [bits, ALL] [Dr, Q] := Valid.cons hDr (Valid.cons hQ (Valid.nil _))
  rcases mem_bits hc0 with rfl | rfl <;> rcases mem_bits hc1 with rfl | rfl <;> rcases mem_bits hc2 with rfl | rfl
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 2, .sym 2, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 2, .sym 2, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 2, .sym 3, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 2, .sym 3, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 3, .sym 2, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 3, .sym 2, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 3, .sym 3, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dr, Q]) (E := []) (k := 5) hV trivial
      (ls := []) (rs := [.sym 3, .sym 3, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Shrink `D` to one cell: `p` is prime. -/
theorem shr2 (Q : List Nat) (c0 : Nat) (c1 : Nat) (hQ : Sym4 Q) (hc0 : c0 ∈ bits) (hc1 : c1 ∈ bits) :
    zdlLogic.Reach (hdR QD.XS2 ([]) (c0 :: (c1 :: (1 :: (Q)))))
      (hd QD.QL ([3]) (1 :: (Q))) := by
  have hV : Valid [ALL] [Q] := Valid.cons hQ (Valid.nil _)
  rcases mem_bits hc0 with rfl | rfl <;> rcases mem_bits hc1 with rfl | rfl
  · exact checkFT (env := [Q]) (E := []) (k := 3) hV trivial
      (ls := []) (rs := [.sym 2, .sym 2, .sym 1, .blk 0 .id])
      (ls' := [.sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Q]) (E := []) (k := 3) hV trivial
      (ls := []) (rs := [.sym 2, .sym 3, .sym 1, .blk 0 .id])
      (ls' := [.sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Q]) (E := []) (k := 3) hV trivial
      (ls := []) (rs := [.sym 3, .sym 2, .sym 1, .blk 0 .id])
      (ls' := [.sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Q]) (E := []) (k := 3) hV trivial
      (ls := []) (rs := [.sym 3, .sym 3, .sym 1, .blk 0 .id])
      (ls' := [.sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` has one cell: `p = 1`. -/
theorem shr1 (Q : List Nat) (c0 : Nat) (hQ : Sym4 Q) (hc0 : c0 ∈ bits) :
    zdlLogic.Reach (hdR QD.XS2 ([]) (c0 :: (1 :: (Q))))
      (hdR QF.FR0 ([1]) (Q)) := by
  have hV : Valid [ALL] [Q] := Valid.cons hQ (Valid.nil _)
  rcases mem_bits hc0 with rfl | rfl
  · exact checkFF (env := [Q]) (E := []) (k := 2) hV trivial
      (ls := []) (rs := [.sym 2, .sym 1, .blk 0 .id])
      (ls' := [.sym 1]) (rs' := [.blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Q]) (E := []) (k := 2) hV trivial
      (ls := []) (rs := [.sym 3, .sym 1, .blk 0 .id])
      (ls' := [.sym 1]) (rs' := [.blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` is empty: `p = 0`. -/
theorem shr0 (Q : List Nat) (hQ : Sym4 Q) :
    zdlLogic.Reach (hdR QD.XS2 ([]) (1 :: (Q)))
      (hdR QF.FR0 ([1]) (Q)) := by
  have hV : Valid [ALL] [Q] := Valid.cons hQ (Valid.nil _)
  exact checkFF (env := [Q]) (E := []) (k := 1) hV trivial
    (ls := []) (rs := [.sym 1, .blk 0 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



/-! ## Copying `P` into `D` -/

theorem cpLoop (G : List Nat) (hG : Sym4 G) : ∀ (u i : Nat),
    zdlLogic.Reach
      (hdR QD.CP1 (List.replicate i 3 ++ [1]) (List.replicate i 2 ++ (List.replicate u 3 ++ 1 :: G)))
      (hdR QD.CP1 (List.replicate (i + u) 3 ++ [1]) (List.replicate (i + u) 2 ++ 1 :: G))
  | 0, i => by simpa using LTM.Reach.refl _ _
  | u + 1, i => by
    have h1 := cpIter (List.replicate i 3) (List.replicate i 2) (List.replicate u 3) G (rep_t3 i)
      (rep_z2 i) (rep_t3 u) hG
    have h2 := cpLoop G hG u (i + 1)
    refine (h1.of_eq ?_ ?_).trans (h2.of_eq rfl ?_)
    · simp [List.replicate_succ]
    · have a1 : List.replicate (i + 1) 3 = 3 :: List.replicate i 3 := rfl
      have a2 : List.replicate (i + 1) 2 = List.replicate i 2 ++ [2] := List.replicate_succ' ..
      rw [a1, a2]; simp
    · have : i + 1 + u = i + (u + 1) := by omega
      rw [this]


/-! ## Primality: the division test -/

theorem succ_modD (i d : Nat) (hd2 : 2 ≤ d) :
    (i + 1) % d = if i % d + 1 < d then i % d + 1 else 0 := F.succ_mod i d hd2

theorem pLoop (Q : List Nat) (hQ : Sym4 Q) (d : Nat) (hd2 : 2 ≤ d) : ∀ u i : Nat,
    zdlLogic.Reach
      (hdR QD.X4 (List.replicate (i % d) 2 ++ (List.replicate (d - i % d) 3 ++ [1]))
        (List.replicate i 2 ++ (List.replicate u 3 ++ 1 :: Q)))
      (hdR QD.X4 (List.replicate ((i + u) % d) 2 ++ (List.replicate (d - (i + u) % d) 3 ++ [1]))
        (List.replicate (i + u) 2 ++ 1 :: Q))
  | 0, i => by simpa using LTM.Reach.refl _ _
  | u + 1, i => by
    have hj : i % d < d := Nat.mod_lt _ (by omega)
    have hsm := succ_modD i d hd2
    have e : i + 1 + u = i + (u + 1) := by omega
    have hmid := pLoop Q hQ d hd2 u (i + 1)
    rw [e] at hmid
    have hA : List.replicate (i + 1) 2 = List.replicate i 2 ++ [2] := List.replicate_succ' ..
    by_cases hlt : i % d + 1 < d
    · simp only [hlt, ↓reduceIte] at hsm
      have h1 := pIter1 (List.replicate (i % d) 2) (List.replicate (d - i % d - 2) 3)
        (List.replicate i 2) (List.replicate u 3) Q (rep_z2 _) (rep_t3 _) (rep_z2 _) (rep_t3 _) hQ
      have hrep : List.replicate (d - i % d) 3 = 3 :: 3 :: List.replicate (d - i % d - 2) 3 := by
        obtain ⟨k, hk⟩ : ∃ k, d - i % d = k + 2 := ⟨d - i % d - 2, by omega⟩
        rw [hk]; simp [List.replicate_succ]
      have hrep2 : List.replicate (d - (i + 1) % d) 3 = 3 :: List.replicate (d - i % d - 2) 3 := by
        rw [hsm]
        obtain ⟨k, hk⟩ : ∃ k, d - i % d = k + 2 := ⟨d - i % d - 2, by omega⟩
        have : d - (i % d + 1) = k + 1 := by omega
        rw [this, show d - i % d - 2 = k by omega]
        simp [List.replicate_succ]
      have hK : List.replicate (i % d + 1) 2 = List.replicate (i % d) 2 ++ [2] := List.replicate_succ' ..
      refine LTM.Reach.trans (c' := hdR QD.X4
        (List.replicate ((i + 1) % d) 2 ++ (List.replicate (d - (i + 1) % d) 3 ++ [1]))
        (List.replicate (i + 1) 2 ++ (List.replicate u 3 ++ 1 :: Q)))
        (h1.of_eq ?_ ?_) hmid
      · rw [hrep]; simp [List.replicate_succ]
      · rw [hrep2, hsm, hK, hA]; simp
    · simp only [hlt, ↓reduceIte] at hsm
      have e3 : d - i % d = 1 := by omega
      have h1 := pIter2 (List.replicate (i % d) 2) (List.replicate i 2) (List.replicate u 3) Q
        (rep_z2 _) (rep_z2 _) (rep_t3 _) hQ
      have hd' : List.replicate d 3 = List.replicate (i % d) 3 ++ [3] := by
        rw [← List.replicate_succ']; congr 1; omega
      refine LTM.Reach.trans (c' := hdR QD.X4
        (List.replicate ((i + 1) % d) 2 ++ (List.replicate (d - (i + 1) % d) 3 ++ [1]))
        (List.replicate (i + 1) 2 ++ (List.replicate u 3 ++ 1 :: Q)))
        (h1.of_eq ?_ ?_) hmid
      · rw [e3]; simp [List.replicate_succ]
      · rw [hsm, hA]
        simp only [List.length_replicate, Nat.sub_zero, List.replicate_zero, List.nil_append, hd']
        simp


theorem Bits_rep2 (j : Nat) : Bits (List.replicate j 2) := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [bits]

/-- One division test of the primality loop. -/
theorem pRoundDiv (p d : Nat) (Q : List Nat) (hQ : Sym4 Q) (hd2 : 2 ≤ d) (hdiv : p % d = 0) :
    ∃ L Mr, NoB L ∧ NoB Mr ∧
      zdlLogic.Reach (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 3 ++ 1 :: Q))
        (hdR QF.FR0 L (Mr ++ Q)) := by
  have h1 := pLoop Q hQ d hd2 p 0
  have h1' : zdlLogic.Reach (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 3 ++ 1 :: Q))
      (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 2 ++ 1 :: Q)) :=
    h1.of_eq (by simp) (by simp [hdiv])
  have h2 := pEndDiv (List.replicate d 3) (List.replicate p 2) Q (rep_t3 d) (rep_z2 p) hQ
  have h2' : zdlLogic.Reach (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 2 ++ 1 :: Q))
      (hdR QF.FR0 [] (List.replicate d 3 ++ 1 :: (List.replicate p 3 ++ 1 :: Q))) := by
    simpa using h2
  refine ⟨[], List.replicate d 3 ++ 1 :: (List.replicate p 3 ++ [1]), NoB.nil,
    (t3_noB (rep_t3 d)).app (NoB.cons one_nb ((t3_noB (rep_t3 p)).app (NoB.cons one_nb NoB.nil))), ?_⟩
  refine (h1'.trans h2').of_eq rfl ?_
  simp

theorem pRoundNdiv (p d : Nat) (Q : List Nat) (hQ : Sym4 Q) (hd2 : 2 ≤ d) (hdiv : p % d ≠ 0) :
    zdlLogic.Reach (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 3 ++ 1 :: Q))
      (hdR QD.XS2 [] ((List.replicate (p % d) 2 ++ List.replicate (d - p % d) 3) ++
        1 :: (List.replicate p 3 ++ 1 :: Q))) := by
  have h1 := pLoop Q hQ d hd2 p 0
  have hj : p % d < d := Nat.mod_lt _ (by omega)
  obtain ⟨j, hjj⟩ : ∃ j, p % d = j + 1 := ⟨p % d - 1, by omega⟩
  have h1' : zdlLogic.Reach (hdR QD.X4 (List.replicate d 3 ++ [1]) (List.replicate p 3 ++ 1 :: Q))
      (hdR QD.X4 (List.replicate j 2 ++ (2 :: (List.replicate (d - p % d) 3 ++ [1])))
        (List.replicate p 2 ++ 1 :: Q)) :=
    h1.of_eq (by simp) (by simp [hjj, List.replicate_succ'])
  have h2 := pEndNdiv (List.replicate j 2) (List.replicate (d - p % d) 3) (List.replicate p 2) Q
    (rep_z2 j) (rep_t3 _) (rep_z2 p) hQ
  have h2' : zdlLogic.Reach (hdR QD.X4 (List.replicate j 2 ++ (2 :: (List.replicate (d - p % d) 3 ++ [1])))
        (List.replicate p 2 ++ 1 :: Q))
      (hd QD.XS1 (List.replicate j 2) (2 :: (List.replicate (d - p % d) 3 ++
        1 :: (List.replicate p 3 ++ 1 :: Q)))) := by
    simpa using h2
  have h3 := xs1sweep (List.replicate j 2) (2 :: (List.replicate (d - p % d) 3 ++
    1 :: (List.replicate p 3 ++ 1 :: Q))) (Bits_rep2 j)
    (Sym4.cons (by simp [ALL]) (((Sym4.rep _ 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL])
      ((Sym4.rep p 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hQ))))))
  refine (h1'.trans h2').trans (h3.of_eq rfl ?_)
  simp [hjj, List.replicate_succ']

def scanOK (p m : Nat) : Prop := 2 ≤ m ∧ ∀ d', 2 ≤ d' → d' ≤ m - 1 → p % d' ≠ 0

/-- The rounds of the primality test, from `XS2` at the left edge of `D` (`|D| = m`). -/
theorem scanXS (p : Nat) (Q : List Nat) (hQ : Sym4 Q) : ∀ (m : Nat) (Dw : List Nat), Bits Dw →
    Dw.length = m →
    (scanOK p m → zdlLogic.Reach (hdR QD.XS2 [] (Dw ++ 1 :: (List.replicate p 3 ++ 1 :: Q)))
        (hd QD.QL [3] (1 :: (List.replicate p 3 ++ 1 :: Q)))) ∧
    (¬ scanOK p m → ∃ L Mr, NoB L ∧ NoB Mr ∧
        zdlLogic.Reach (hdR QD.XS2 [] (Dw ++ 1 :: (List.replicate p 3 ++ 1 :: Q)))
          (hdR QF.FR0 L (Mr ++ Q))) := by
  intro m
  induction m with
  | zero =>
    intro Dw hD hl
    have hDw : Dw = [] := List.eq_nil_of_length_eq_zero hl
    subst hDw
    refine ⟨fun h => absurd h.1 (by omega), fun _ => ?_⟩
    have h := shr0 (List.replicate p 3 ++ 1 :: Q) (Sym4.app (Sym4.rep p 3 (by simp [ALL]))
      (Sym4.cons (by simp [ALL]) hQ))
    refine ⟨[1], List.replicate p 3 ++ [1], NoB.cons one_nb NoB.nil,
      (t3_noB (rep_t3 p)).app (NoB.cons one_nb NoB.nil), ?_⟩
    simpa using h
  | succ m ih =>
    intro Dw hD hl
    have hPQ : Sym4 (List.replicate p 3 ++ 1 :: Q) :=
      (Sym4.rep p 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hQ)
    have hMr : NoB (List.replicate p 3 ++ [1]) := (t3_noB (rep_t3 p)).app (NoB.cons one_nb NoB.nil)
    have hm : m = 0 ∨ m = 1 ∨ ∃ m', m = m' + 2 := by
      rcases m with _ | _ | m
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨m, rfl⟩)
    rcases hm with rfl | rfl | ⟨m, rfl⟩
    · obtain ⟨c0, rfl⟩ : ∃ c0, Dw = [c0] := by
        match Dw, hl with
        | [c0], _ => exact ⟨c0, rfl⟩
      have hc0 : c0 ∈ bits := hD c0 (by simp)
      refine ⟨fun h => absurd h.1 (by omega), fun _ => ?_⟩
      have h := shr1 (List.replicate p 3 ++ 1 :: Q) c0 hPQ hc0
      exact ⟨[1], List.replicate p 3 ++ [1], NoB.cons one_nb NoB.nil, hMr, by simpa using h⟩
    · obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, Dw = [c0, c1] := by
        match Dw, hl with
        | [c0, c1], _ => exact ⟨c0, c1, rfl⟩
      have hc0 : c0 ∈ bits := hD c0 (by simp)
      have hc1 : c1 ∈ bits := hD c1 (by simp)
      have hok : scanOK p 2 := ⟨by omega, fun d' h1 h2 => by omega⟩
      refine ⟨fun _ => ?_, fun h => absurd hok h⟩
      have h := shr2 (List.replicate p 3 ++ 1 :: Q) c0 c1 hPQ hc0 hc1
      simpa using h
    · obtain ⟨c0, c1, c2, Dr, rfl⟩ : ∃ c0 c1 c2 Dr, Dw = c0 :: c1 :: c2 :: Dr := by
        match Dw, hl with
        | c0 :: c1 :: c2 :: Dr, _ => exact ⟨c0, c1, c2, Dr, rfl⟩
      have hDr : Bits Dr := fun a ha => hD a (by simp [ha])
      have hc0 : c0 ∈ bits := hD c0 (by simp)
      have hc1 : c1 ∈ bits := hD c1 (by simp)
      have hc2 : c2 ∈ bits := hD c2 (by simp)
      have hDrl : Dr.length = m := by simpa using hl
      have hd2 : 2 ≤ m + 2 := by omega
      have hsh := shr3 Dr (List.replicate p 3 ++ 1 :: Q) c0 c1 c2 hDr hPQ hc0 hc1 hc2
      have hsh' : zdlLogic.Reach (hdR QD.XS2 [] ((c0 :: c1 :: c2 :: Dr) ++ 1 :: (List.replicate p 3 ++ 1 :: Q)))
          (hdR QD.X4 (List.replicate (m + 2) 3 ++ [1]) (List.replicate p 3 ++ 1 :: Q)) := by
        refine hsh.of_eq (by simp) ?_
        have : m + 2 = Dr.length + 2 := by omega
        rw [this]
        simp [List.replicate_succ]
      by_cases hdiv : p % (m + 2) = 0
      · obtain ⟨L, Mr, hL, hMr', hR⟩ := pRoundDiv p (m + 2) Q hQ hd2 hdiv
        refine ⟨fun h => absurd hdiv (h.2 (m + 2) hd2 (by omega)), fun _ => ⟨L, Mr, hL, hMr', hsh'.trans hR⟩⟩
      · have hR := pRoundNdiv p (m + 2) Q hQ hd2 hdiv
        have hj : p % (m + 2) < m + 2 := Nat.mod_lt _ (by omega)
        have hKb : Bits (List.replicate (p % (m + 2)) 2 ++ List.replicate (m + 2 - p % (m + 2)) 3) := by
          intro x hx
          simp only [List.mem_append, List.mem_replicate] at hx
          rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [bits]
        have hKl : (List.replicate (p % (m + 2)) 2 ++ List.replicate (m + 2 - p % (m + 2)) 3).length = m + 1 + 1 := by
          simp; omega
        obtain ⟨hI1, hI2⟩ := ih _ hKb hKl
        refine ⟨fun hok => ?_, fun hnok => ?_⟩
        · have hok' : scanOK p (m + 2) := ⟨by omega, fun d' h1 h2 => hok.2 d' h1 (by omega)⟩
          exact hsh'.trans (hR.trans (hI1 hok'))
        · have hnok' : ¬ scanOK p (m + 2) := fun hok' => hnok ⟨by omega, fun d' h1 h2 => by
            by_cases he : d' = m + 2
            · rw [he]; exact hdiv
            · exact hok'.2 d' h1 (by omega)⟩
          obtain ⟨L, Mr, hL, hMr', hRf⟩ := hI2 hnok'
          exact ⟨L, Mr, hL, hMr', hsh'.trans (hR.trans hRf)⟩

end ZP.D
