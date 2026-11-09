module

public import ZP.PairF
public import ZP.CompileG
public import ZP.DefsG

@[expose] public section

/-! The pair lemma for the GI machine; the shared part is copied from `ZP/PairD.lean`. -/

namespace ZP.G

open ZP


open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zgiLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, O13] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hb : b ∈ bits) :
    zgiLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
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
    zgiLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
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
    zgiLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, O13] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 23) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zgiLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
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
    zgiLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zgiLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zgiLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: (1 :: Rest)))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: (1 :: Rest))))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 19) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zgiLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zgiLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zgiLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR QF.NI (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR QF.NI (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR QF.NI (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR QF.NI (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zgiLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ O13) :
    ∀ v u, Bits u → Bits v →
      zgiLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
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
    zgiLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zgiLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zgiLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zgiLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zgiLogic.Reach
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
    ∃ g, 1 ≤ g ∧ zgiLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  have hB0 := hA.trans (zpBase_ext_zgiLogic.reach (hr.of_eq (by rw [hcode]) rfl))
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
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zgiLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zgiLogic.reach (hB.of_eq ?_ ?_))⟩
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
      zgiLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zgiLogic.reach h2)⟩



/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zgiLogic.Reach (TR (bitsOf Jb) Sb b)
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
    zgiLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
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
    zgiLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
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
    zgiLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
      some (hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y) := by
  have e1 : (⟨Q.BEEP, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1].reverse,
      [.blk 2 .id], true⟩ : SC).den [j, s, Y] = hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y :=
    den_tape (by osimp) (by osimp)
  have e2 : (⟨Q.EAs, [Item.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2].reverse,
      [.blk 2 .id], false⟩ : SC).den [j, s, Y] = hdR Q.EAs (1 :: (j ++ 1 :: (s ++ 1 :: [2]))) Y :=
    den_tapeR (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)




/-- New instance: `M_2`, `H`, walk to the start of `s`. -/
theorem ni0 (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zgiLogic.Reach (hdR QF.NI (1 :: (j ++ (1 :: (s)))) ([]))
      (hdR Q.GC (1 :: (1 :: (j ++ ([1])))) (s ++ ([1]))) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkFF (env := [j, s]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The copy is done: the head goes left to the blank and writes the boundary `M`. -/
theorem ni2a (Xr : List Nat) (j : List Nat) (s : List Nat) (hXr : Bits Xr) (hj : Bits j) (hs : Bits s) :
    zgiLogic.Reach (hdR Q.GC (Xr ++ (1 :: (1 :: (j ++ (1 :: (s)))))) ([1]))
      (hdR QG.gTC [1] (Xr ++ (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))))) := by
  have hV : Valid [bits, bits, bits] [Xr, j, s] := Valid.cons hXr (Valid.cons hj (Valid.cons hs (Valid.nil _)))
  exact checkFF (env := [Xr, j, s]) (E := []) (k := 40) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `0` becomes the separator `M`, `1` stays. -/
def fz (r : List Nat) : List Nat := r.map fun a => if a = 2 then 1 else a

theorem gtcBody (P R : List Nat) (b : Nat) (hP : Sym4 P) (hR : Sym4 R) (hb : b ∈ bits) :
    zgiLogic.Reach (hdR QG.gTC P (b :: R)) (hdR QG.gTC (P ++ [if b = 2 then 1 else b]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gtcEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gTC P (1 :: R)) (hd QG.gUP P (0 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gtcLoop (R : List Nat) (hR : Sym4 R) : ∀ (Xr P : List Nat), Bits Xr → Sym4 P →
    zgiLogic.Reach (hdR QG.gTC P (Xr ++ 1 :: R)) (hd QG.gUP (P ++ fz Xr) (0 :: R)) := by
  intro Xr
  induction Xr with
  | nil =>
    intro P _ hP
    exact (gtcEnd P R hP hR).of_eq rfl (by simp [fz])
  | cons b Xr ih =>
    intro P hXr hP
    have hb : b ∈ bits := hXr b (List.mem_cons_self ..)
    have hXr' : Bits Xr := fun a ha => hXr a (List.mem_cons_of_mem _ ha)
    have hstep := gtcBody P (Xr ++ 1 :: R) b hP (Sym4.app hXr'.sym4 (Sym4.cons (by simp [ALL]) hR)) hb
    have hP' : Sym4 (P ++ [if b = 2 then 1 else b]) := by
      refine hP.app (Sym4.cons ?_ Sym4.nil)
      rcases mem_bits hb with rfl | rfl <;> simp [ALL]
    exact (hstep.of_eq rfl rfl).trans ((ih _ hXr' hP').of_eq rfl (by simp [fz]))

/-! ## Search: pushing a copy of `m` -/

/-- A stack entry: `v` unmarked cells and its own `M`. -/
def U (v : Nat) : List Nat := List.replicate v 3 ++ [1]

/-- The stack, top first. -/
def Enc : List Nat → List Nat
  | [] => []
  | v :: r => U v ++ Enc r

def Mk : List Nat := [2]

theorem rep3_o13 (k : Nat) : ∀ a ∈ List.replicate k 3, a ∈ O13 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [O13]

theorem rep2_mk (k : Nat) : ∀ a ∈ List.replicate k 2, a ∈ Mk := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [Mk]

theorem Enc_o13 : ∀ r : List Nat, ∀ a ∈ Enc r, a ∈ O13
  | [] => fun a h => by cases h
  | v :: r => fun a ha => by
    rw [Enc, U, List.append_assoc] at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact rep3_o13 v a ha
    · rcases List.mem_append.1 ha with ha | ha
      · have : a = 1 := by simpa using ha
        rw [this]; simp [O13]
      · exact Enc_o13 r a ha

theorem o13_sym4 {w : List Nat} (h : ∀ a ∈ w, a ∈ O13) : Sym4 w := fun a ha => by
  have := h a ha
  simp [O13] at this
  rcases this with rfl | rfl <;> simp [ALL]

theorem o13_noB {w : List Nat} (h : ∀ a ∈ w, a ∈ O13) : NoB w := fun a ha => by
  have := h a ha
  simp [O13] at this
  rcases this with rfl | rfl <;> simp [NB]

theorem mk_noB {w : List Nat} (h : ∀ a ∈ w, a ∈ Mk) : NoB w := fun a ha => by
  have := h a ha
  simp [Mk] at this
  subst this; simp [NB]

theorem gprStep3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPR P (3 :: R)) (hdR QG.gPR (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gprStepM (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPR P (1 :: R)) (hdR QG.gPR2 (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gpr2Step3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPR2 P (3 :: R)) (hdR QG.gPR (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gpr2End (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPR2 P (1 :: R)) (hdR QG.gPM (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gprCells (R : List Nat) (hR : Sym4 R) : ∀ (k : Nat) (P : List Nat), Sym4 P →
    zgiLogic.Reach (hdR QG.gPR P (List.replicate k 3 ++ 1 :: R))
      (hdR QG.gPR2 (P ++ (List.replicate k 3 ++ [1])) R)
  | 0, P, hP => (gprStepM P R hP hR).of_eq rfl rfl
  | k + 1, P, hP => by
    have h1 := gprStep3 P (List.replicate k 3 ++ 1 :: R) hP
      (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (Sym4.cons (by simp [ALL]) hR))
    have h2 := gprCells R hR k (P ++ [3]) (hP.app (Sym4.cons (by simp [ALL]) Sym4.nil))
    exact (h1.of_eq (by simp [List.replicate_succ]) rfl).trans (h2.of_eq rfl (by simp [List.replicate_succ, List.append_assoc]))

theorem gprEntry (P R : List Nat) (k : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPR2 P (U (k + 1) ++ R)) (hdR QG.gPR2 (P ++ U (k + 1)) R) := by
  have h1 := gpr2Step3 P (List.replicate k 3 ++ 1 :: R) hP
    (Sym4.app (Sym4.rep _ _ (by simp [ALL])) (Sym4.cons (by simp [ALL]) hR))
  have h2 := gprCells R hR k (P ++ [3]) (hP.app (Sym4.cons (by simp [ALL]) Sym4.nil))
  exact (h1.of_eq (by simp [U, List.replicate_succ]) rfl).trans
    (h2.of_eq rfl (by simp [U, List.replicate_succ]))

theorem gprWalk (R : List Nat) (hR : Sym4 R) : ∀ (rest : List Nat), (∀ v ∈ rest, 1 ≤ v) →
    ∀ P : List Nat, Sym4 P →
    zgiLogic.Reach (hdR QG.gPR2 P (Enc rest ++ R)) (hdR QG.gPR2 (P ++ Enc rest) R)
  | [], _, P, _ => by
    simp only [Enc, List.nil_append, List.append_nil]
    exact LTM.Reach.refl _ _
  | v :: rest, hv, P, hP => by
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by have := hv v (List.mem_cons_self ..); omega⟩
    have hrest : ∀ v ∈ rest, 1 ≤ v := fun a ha => hv a (List.mem_cons_of_mem _ ha)
    have hE : Sym4 (Enc rest ++ R) := (o13_sym4 (Enc_o13 rest)).app hR
    have h1 := gprEntry P (Enc rest ++ R) k hP hE
    have hP' : Sym4 (P ++ U (k + 1)) := hP.app (o13_sym4 (fun a ha => by
      simp only [U, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | ha
      · exact rep3_o13 _ a ha
      · rw [ha]; simp [O13]))
    have h2 := gprWalk R hR rest hrest (P ++ U (k + 1)) hP'
    exact (h1.of_eq (by simp [Enc]) rfl).trans (h2.of_eq rfl (by simp [Enc, List.append_assoc]))

theorem gpmMark (P R : List Nat) (c : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPM P (List.replicate c 2 ++ 3 :: R))
      (hd QG.gPL (P ++ List.replicate c 2) (2 :: R)) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate c 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk c) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [P, List.replicate c 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gpmEnd1 (P R : List Nat) (c : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPM P (List.replicate c 2 ++ 1 :: R))
      (hd QG.gPU (P ++ List.replicate c 2) (1 :: R)) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate c 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk c) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [P, List.replicate c 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gpmEnd0 (P R : List Nat) (c : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gPM P (List.replicate c 2 ++ 0 :: R))
      (hd QG.gPU (P ++ List.replicate c 2) (0 :: R)) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate c 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk c) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [P, List.replicate c 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gplWalk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gPL A R) (hdR QG.gPR [3] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gupFirst (A R : List Nat) (hA : ∀ a ∈ A, a ∈ O13) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gUP A R) (hdR QG.gPR2 [1] (A ++ R)) := by
  have hV : Valid [O13, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gpuWalk (m : Nat) (E R : List Nat) (hE : ∀ a ∈ E, a ∈ O13) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gPU (List.replicate m 3 ++ 1 :: (E ++ 1 :: List.replicate m 2)) R)
      (hdR QG.gDP [] (List.replicate m 3 ++ 1 :: (E ++ 1 :: (List.replicate m 3 ++ R)))) := by
  have hV : Valid [O13, O13, Mk, ALL] [List.replicate m 3, E, List.replicate m 2, R] :=
    Valid.cons (rep3_o13 m) (Valid.cons hE (Valid.cons (rep2_mk m) (Valid.cons hR (Valid.nil _))))
  exact checkTF (env := [List.replicate m 3, E, List.replicate m 2, R]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.blk 3 .id])
    (ls' := []) (rs' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 (.const 3), .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sym4_rep (k c : Nat) (h : c ∈ ALL) : Sym4 (List.replicate k c) := Sym4.rep k c h

theorem U_o13 (v : Nat) : ∀ a ∈ U v, a ∈ O13 := fun a ha => by
  have := Enc_o13 [v] a (by simpa [Enc] using ha)
  exact this

theorem pushIter (m c : Nat) (hc : c < m) (rest Zt : List Nat) (hr : ∀ v ∈ rest, 1 ≤ v) (hZ : Sym4 Zt) :
    zgiLogic.Reach
      (hdR QG.gPR2 (List.replicate c 3 ++ [1])
        (Enc rest ++ 1 :: (List.replicate c 2 ++ (List.replicate (m - c) 3 ++ Zt))))
      (hdR QG.gPR2 (List.replicate (c + 1) 3 ++ [1])
        (Enc rest ++ 1 :: (List.replicate (c + 1) 2 ++ (List.replicate (m - (c + 1)) 3 ++ Zt)))) := by
  have hP0 : Sym4 (List.replicate c 3 ++ [1]) := o13_sym4 (U_o13 c)
  have hEnc : Sym4 (Enc rest) := o13_sym4 (Enc_o13 rest)
  have hmk : Sym4 (List.replicate c 2) := sym4_rep _ _ (by simp [ALL])
  have hr3 : Sym4 (List.replicate (m - (c + 1)) 3 ++ Zt) :=
    (sym4_rep _ _ (by simp [ALL])).app hZ
  have hX : Sym4 (List.replicate c 2 ++ 3 :: (List.replicate (m - (c + 1)) 3 ++ Zt)) :=
    hmk.app (Sym4.cons (by simp [ALL]) hr3)
  have hmc : m - c = (m - (c + 1)) + 1 := by omega
  have eX : List.replicate c 2 ++ (List.replicate (m - c) 3 ++ Zt)
      = List.replicate c 2 ++ 3 :: (List.replicate (m - (c + 1)) 3 ++ Zt) := by
    rw [hmc]; simp [List.replicate_succ]
  have h1 := gprWalk (1 :: (List.replicate c 2 ++ 3 :: (List.replicate (m - (c + 1)) 3 ++ Zt)))
    (Sym4.cons (by simp [ALL]) hX) rest hr (List.replicate c 3 ++ [1]) hP0
  have hPP : Sym4 (List.replicate c 3 ++ [1] ++ Enc rest) := hP0.app hEnc
  have h2 := gpr2End (List.replicate c 3 ++ [1] ++ Enc rest)
    (List.replicate c 2 ++ 3 :: (List.replicate (m - (c + 1)) 3 ++ Zt)) hPP hX
  have hPP2 : Sym4 (List.replicate c 3 ++ [1] ++ Enc rest ++ [1]) := hPP.app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h3 := gpmMark (List.replicate c 3 ++ [1] ++ Enc rest ++ [1]) (List.replicate (m - (c + 1)) 3 ++ Zt) c hPP2 hr3
  have hA : NoB (List.replicate c 3 ++ [1] ++ Enc rest ++ [1] ++ List.replicate c 2) :=
    (((o13_noB (U_o13 c)).app (o13_noB (Enc_o13 rest))).app (NoB.cons one_nb NoB.nil)).app (mk_noB (rep2_mk c))
  have h4 := gplWalk (List.replicate c 3 ++ [1] ++ Enc rest ++ [1] ++ List.replicate c 2)
    (2 :: (List.replicate (m - (c + 1)) 3 ++ Zt)) hA (Sym4.cons (by simp [ALL]) hr3)
  have hS : Sym4 (Enc rest ++ 1 :: (List.replicate (c + 1) 2 ++ (List.replicate (m - (c + 1)) 3 ++ Zt))) :=
    hEnc.app (Sym4.cons (by simp [ALL]) ((sym4_rep _ _ (by simp [ALL])).app hr3))
  have h5 := gprCells (Enc rest ++ 1 :: (List.replicate (c + 1) 2 ++ (List.replicate (m - (c + 1)) 3 ++ Zt))) hS c [3]
    (Sym4.cons (by simp [ALL]) Sym4.nil)
  rw [eX]
  have hh := h1.trans (h2.trans (h3.trans h4))
  have e1 : hdR QG.gPR [3] (List.replicate c 3 ++ 1 :: (Enc rest ++ 1 :: (List.replicate (c + 1) 2 ++ (List.replicate (m - (c + 1)) 3 ++ Zt))))
      = hdR QG.gPR [3] (List.replicate c 3 ++ [1] ++ Enc rest ++ [1] ++ List.replicate c 2 ++ 2 :: (List.replicate (m - (c + 1)) 3 ++ Zt)) := by
    simp [List.replicate_succ', List.append_assoc]
  have hh' := hh.trans (h5.of_eq e1 rfl)
  refine hh'.of_eq rfl ?_
  simp [List.replicate_succ, List.append_assoc]

theorem pushLoop (m : Nat) (rest Zt : List Nat) (hr : ∀ v ∈ rest, 1 ≤ v) (hZ : Sym4 Zt) :
    ∀ d c, c + d = m →
    zgiLogic.Reach
      (hdR QG.gPR2 (List.replicate c 3 ++ [1])
        (Enc rest ++ 1 :: (List.replicate c 2 ++ (List.replicate (m - c) 3 ++ Zt))))
      (hdR QG.gPR2 (List.replicate m 3 ++ [1])
        (Enc rest ++ 1 :: (List.replicate m 2 ++ (List.replicate (m - m) 3 ++ Zt)))) := by
  intro d
  induction d with
  | zero =>
    intro c hc
    obtain rfl : c = m := by omega
    exact LTM.Reach.refl _ _
  | succ d ih =>
    intro c hc
    have h1 := pushIter m c (by omega) rest Zt hr hZ
    have h2 := ih (c + 1) (by omega)
    exact h1.trans h2

theorem pushDone (m : Nat) (rest : List Nat) (Z' : List Nat) (z : Nat) (hz : z = 0 ∨ z = 1)
    (hr : ∀ v ∈ rest, 1 ≤ v) (hZ : Sym4 Z') :
    zgiLogic.Reach
      (hdR QG.gPR2 (List.replicate m 3 ++ [1])
        (Enc rest ++ 1 :: (List.replicate m 2 ++ (List.replicate (m - m) 3 ++ (z :: Z')))))
      (hdR QG.gDP [] (Enc (m :: rest) ++ 1 :: (List.replicate m 3 ++ (z :: Z')))) := by
  have hP0 : Sym4 (List.replicate m 3 ++ [1]) := o13_sym4 (U_o13 m)
  have hEnc : Sym4 (Enc rest) := o13_sym4 (Enc_o13 rest)
  have hmk : Sym4 (List.replicate m 2) := sym4_rep _ _ (by simp [ALL])
  have hz4 : Sym4 (z :: Z') := Sym4.cons (by rcases hz with rfl | rfl <;> simp [ALL]) hZ
  have hX : Sym4 (List.replicate m 2 ++ (z :: Z')) := hmk.app hz4
  have h1 := gprWalk (1 :: (List.replicate m 2 ++ (z :: Z'))) (Sym4.cons (by simp [ALL]) hX) rest hr
    (List.replicate m 3 ++ [1]) hP0
  have hPP : Sym4 (List.replicate m 3 ++ [1] ++ Enc rest) := hP0.app hEnc
  have h2 := gpr2End (List.replicate m 3 ++ [1] ++ Enc rest) (List.replicate m 2 ++ (z :: Z')) hPP hX
  have hPP2 : Sym4 (List.replicate m 3 ++ [1] ++ Enc rest ++ [1]) := hPP.app (Sym4.cons (by simp [ALL]) Sym4.nil)
  have h3 : zgiLogic.Reach (hdR QG.gPM (List.replicate m 3 ++ [1] ++ Enc rest ++ [1]) (List.replicate m 2 ++ (z :: Z')))
      (hd QG.gPU (List.replicate m 3 ++ [1] ++ Enc rest ++ [1] ++ List.replicate m 2) (z :: Z')) := by
    rcases hz with rfl | rfl
    · exact gpmEnd0 _ Z' m hPP2 hZ
    · exact gpmEnd1 _ Z' m hPP2 hZ
  have h4 := gpuWalk m (Enc rest) (z :: Z') (Enc_o13 rest) hz4
  have hh := h1.trans (h2.trans h3)
  have hh' := hh.trans (h4.of_eq (by simp [List.append_assoc]) rfl)
  refine hh'.of_eq (by simp) ?_
  simp [Enc, U, List.append_assoc]

/-- The push: the head enters `gUP` at the right end of the stack and the boundary; a new top
equal to `m` is built. -/
theorem pushAll (m : Nat) (rest : List Nat) (Z' : List Nat) (z : Nat) (hz : z = 0 ∨ z = 1)
    (hr : ∀ v ∈ rest, 1 ≤ v) (hZ : Sym4 Z') :
    zgiLogic.Reach
      (hdR QG.gPR2 [1] (Enc rest ++ 1 :: (List.replicate m 3 ++ (z :: Z'))))
      (hdR QG.gDP [] (Enc (m :: rest) ++ 1 :: (List.replicate m 3 ++ (z :: Z')))) := by
  have hz4 : Sym4 (z :: Z') := Sym4.cons (by rcases hz with rfl | rfl <;> simp [ALL]) hZ
  have h := pushLoop m rest (z :: Z') hr hz4 m 0 (by omega)
  exact (h.of_eq (by simp) rfl).trans (pushDone m rest Z' z hz hr hZ)

/-! ## Unmarking walks -/

/-- Unmark a cell. -/
def unm1 (a : Nat) : Nat := if a = 2 then 3 else a

def unm (A : List Nat) : List Nat := A.map unm1

theorem unm_append (A B : List Nat) : unm (A ++ B) = unm A ++ unm B := List.map_append ..

theorem unm_rep3 (k : Nat) : unm (List.replicate k 3) = List.replicate k 3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp_all [unm, unm1, List.replicate_succ]

theorem unm_rep2 (k : Nat) : unm (List.replicate k 2) = List.replicate k 3 := by
  induction k with
  | zero => rfl
  | succ k ih => simp_all [unm, unm1, List.replicate_succ]

theorem unm_nb {A : List Nat} (h : NoB A) : NoB (unm A) := fun a ha => by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  have := h b hb
  simp [NB] at this
  rcases this with rfl | rfl | rfl <;> simp [unm1, NB]

theorem gupStep (P R : List Nat) (a : Nat) (ha : a ∈ NB) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gUP (P ++ [a]) R) (hd QG.gUP P (unm1 a :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  simp [NB] at ha
  rcases ha with rfl | rfl | rfl
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gUP) (A' := P) (R' := 1 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gUP) (A' := P) (R' := 3 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gUP) (A' := P) (R' := 3 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])

theorem gupBase (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gUP [] R) (hdR QG.gPR2 [1] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTF (env := [R]) (E := []) (k := 3) hV trivial
    (ls := []) (rs := [.blk 0 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gupWalkW (W : List Nat) : ∀ R, NoB W → Sym4 R →
    zgiLogic.Reach (hd QG.gUP W.reverse R) (hdR QG.gPR2 [1] (unm W.reverse ++ R)) := by
  induction W with
  | nil => intro R _ hR; exact (gupBase R hR).of_eq rfl (by simp [unm])
  | cons a W ih =>
    intro R hW hR
    have ha : a ∈ NB := hW a (List.mem_cons_self ..)
    have hW' : NoB W := fun b hb => hW b (List.mem_cons_of_mem _ hb)
    have hu : unm1 a ∈ NB := by
      simp [NB] at ha; rcases ha with rfl | rfl | rfl <;> simp [unm1, NB]
    have h1 := gupStep W.reverse R a ha (NoB.sym4 (fun b hb => hW' b (List.mem_reverse.mp hb))) hR
    have h2 := ih (unm1 a :: R) hW' (Sym4.cons (by simp [NB] at hu; simp [ALL]; omega) hR)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp [unm, unm_append]))

theorem gupWalk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gUP A R) (hdR QG.gPR2 [1] (unm A ++ R)) := by
  have := gupWalkW A.reverse R (fun a ha => hA a (List.mem_reverse.mp ha)) hR
  simpa using this


theorem gflStep (P R : List Nat) (a : Nat) (ha : a ∈ NB) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gFL (P ++ [a]) R) (hd QG.gFL P (unm1 a :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  simp [NB] at ha
  rcases ha with rfl | rfl | rfl
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gFL) (A' := P) (R' := 1 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gFL) (A' := P) (R' := 3 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkTT (env := [P, R]) (E := []) (k := 3) (q' := QG.gFL) (A' := P) (R' := 3 :: R) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])

theorem gflBase (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gFL [] R) (hdR QG.gDC [] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTF (env := [R]) (E := []) (k := 3) hV trivial
    (ls := []) (rs := [.blk 0 .id])
    (ls' := []) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gflWalkW (W : List Nat) : ∀ R, NoB W → Sym4 R →
    zgiLogic.Reach (hd QG.gFL W.reverse R) (hdR QG.gDC [] (unm W.reverse ++ R)) := by
  induction W with
  | nil => intro R _ hR; exact (gflBase R hR).of_eq rfl (by simp [unm])
  | cons a W ih =>
    intro R hW hR
    have ha : a ∈ NB := hW a (List.mem_cons_self ..)
    have hW' : NoB W := fun b hb => hW b (List.mem_cons_of_mem _ hb)
    have hu : unm1 a ∈ NB := by
      simp [NB] at ha; rcases ha with rfl | rfl | rfl <;> simp [unm1, NB]
    have h1 := gflStep W.reverse R a ha (NoB.sym4 (fun b hb => hW' b (List.mem_reverse.mp hb))) hR
    have h2 := ih (unm1 a :: R) hW' (Sym4.cons (by simp [NB] at hu; simp [ALL]; omega) hR)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp [unm, unm_append]))

theorem gflWalk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gFL A R) (hdR QG.gDC [] (unm A ++ R)) := by
  have := gflWalkW A.reverse R (fun a ha => hA a (List.mem_reverse.mp ha)) hR
  simpa using this


/-! ## Collision check of the top against the other entries -/

def O12 : List Nat := [1, 2]

/-- Entries that have been compared: all their cells are marked. -/
def MEnc : List Nat → List Nat
  | [] => []
  | v :: r => List.replicate v 2 ++ 1 :: MEnc r

theorem rep2_o12 (k : Nat) : ∀ a ∈ List.replicate k 2, a ∈ O12 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [O12]

theorem MEnc_o12 : ∀ r : List Nat, ∀ a ∈ MEnc r, a ∈ O12
  | [] => fun a h => by cases h
  | v :: r => fun a ha => by
    rw [MEnc] at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact rep2_o12 v a ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · simp [O12]
      · exact MEnc_o12 r a ha

theorem o12_noB {w : List Nat} (h : ∀ a ∈ w, a ∈ O12) : NoB w := fun a ha => by
  have := h a ha
  simp [O12] at this
  rcases this with rfl | rfl <;> simp [NB]

theorem o12_sym4 {w : List Nat} (h : ∀ a ∈ w, a ∈ O12) : Sym4 w := (o12_noB h).sym4

theorem bits_rep3 (k : Nat) : Bits (List.replicate k 3) := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [bits]

theorem bits_rep2 (k : Nat) : Bits (List.replicate k 2) := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [bits]

theorem rep_cons_snoc (a k : Nat) : a :: (List.replicate k a ++ [a]) = List.replicate (k + 2) a := by
  rw [show k + 2 = (k + 1) + 1 from rfl, List.replicate_succ, List.replicate_succ']

theorem gkeTop (P T R : List Nat) (hP : Sym4 P) (hT : Bits T) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKE P (T ++ 1 :: R)) (hdR QG.gKE1 (P ++ T ++ [1]) R) := by
  have hV : Valid [ALL, bits, ALL] [P, T, R] := Valid.cons hP (Valid.cons hT (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [P, T, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gke1Skip (P R : List Nat) (e : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKE1 P (List.replicate (e + 1) 2 ++ 1 :: R))
      (hdR QG.gKE1 (P ++ (List.replicate (e + 1) 2 ++ [1])) R) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate e 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk e) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gKE1 P (2 :: (List.replicate e 2 ++ 1 :: R)))
      (hdR QG.gKE1 (P ++ 2 :: (List.replicate e 2 ++ [1])) R) := checkFF (env := [P, List.replicate e 2, R]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

theorem gke1Walk (R : List Nat) (hR : Sym4 R) : ∀ (fm : List Nat), (∀ v ∈ fm, 1 ≤ v) → ∀ P : List Nat, Sym4 P →
    zgiLogic.Reach (hdR QG.gKE1 P (MEnc fm ++ R)) (hdR QG.gKE1 (P ++ MEnc fm) R)
  | [], _, P, _ => by
    simp only [MEnc, List.nil_append, List.append_nil]; exact LTM.Reach.refl _ _
  | v :: fm, hv, P, hP => by
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by have := hv v (List.mem_cons_self ..); omega⟩
    have hfm : ∀ v ∈ fm, 1 ≤ v := fun a ha => hv a (List.mem_cons_of_mem _ ha)
    have hE : Sym4 (MEnc fm ++ R) := (o12_sym4 (MEnc_o12 fm)).app hR
    have h1 := gke1Skip P (MEnc fm ++ R) k hP hE
    have hP' : Sym4 (P ++ (List.replicate (k + 1) 2 ++ [1])) :=
      hP.app ((sym4_rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) Sym4.nil))
    have h2 := gke1Walk R hR fm hfm _ hP'
    exact (h1.of_eq (by simp [MEnc]) rfl).trans (h2.of_eq rfl (by simp [MEnc, List.append_assoc]))

theorem gkeMark0 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKE1 P (3 :: R)) (hdR QG.gKP (P ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkeMark (P R : List Nat) (k : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKE1 P (List.replicate k 2 ++ 3 :: R))
      (hdR QG.gKP (P ++ List.replicate (k + 1) 2) R) := by
  cases k with
  | zero => exact (gkeMark0 P R hP hR).of_eq (by simp) (by simp)
  | succ k =>
    have hV : Valid [ALL, Mk, ALL] [P, List.replicate k 2, R] :=
      Valid.cons hP (Valid.cons (rep2_mk k) (Valid.cons hR (Valid.nil _)))
    have : zgiLogic.Reach (hdR QG.gKE1 P (2 :: (List.replicate k 2 ++ 3 :: R)))
        (hdR QG.gKP (P ++ 2 :: (List.replicate k 2 ++ [2])) R) := checkFF (env := [P, List.replicate k 2, R]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    exact this.of_eq (by simp [List.replicate_succ]) (by rw [rep_cons_snoc])

theorem gkp3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKP P (3 :: R)) (hd QG.gKBm P (3 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkp1 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKP P (1 :: R)) (hd QG.gKBd P (1 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkbm (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gKBm A R) (hdR QG.gKVm [] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkvm (k : Nat) (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKVm [] (List.replicate k 2 ++ 3 :: R)) (hdR QG.gKQm (List.replicate (k + 1) 2) R) := by
  have hV : Valid [Mk, ALL] [List.replicate k 2, R] := Valid.cons (rep2_mk k) (Valid.cons hR (Valid.nil _))
  have : zgiLogic.Reach (hdR QG.gKVm [] (List.replicate k 2 ++ 3 :: R)) (hdR QG.gKQm (List.replicate k 2 ++ [2]) R) :=
    checkFF (env := [List.replicate k 2, R]) (E := []) (k := 4) hV trivial
      (ls := []) (rs := [.blk 0 .id, .sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq rfl (by simp [List.replicate_succ'])

theorem gkbd (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gKBd A R) (hdR QG.gKVd [] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkvd (k : Nat) (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKVd [] (List.replicate k 2 ++ 3 :: R)) (hdR QG.gKQd (List.replicate (k + 1) 2) R) := by
  have hV : Valid [Mk, ALL] [List.replicate k 2, R] := Valid.cons (rep2_mk k) (Valid.cons hR (Valid.nil _))
  have : zgiLogic.Reach (hdR QG.gKVd [] (List.replicate k 2 ++ 3 :: R)) (hdR QG.gKQd (List.replicate k 2 ++ [2]) R) :=
    checkFF (env := [List.replicate k 2, R]) (E := []) (k := 4) hV trivial
      (ls := []) (rs := [.blk 0 .id, .sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq rfl (by simp [List.replicate_succ'])

theorem gkqm3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKQm P (3 :: R)) (hdR QG.gKE (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkqm1 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKQm P (1 :: R)) (hdR QG.gKR1 (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkqd3 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKQd P (3 :: R)) (hd QG.gKUV P (3 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkqd1 (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKQd P (1 :: R)) (hdR QG.gFG (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkr (P G R : List Nat) (r : Nat) (hP : Sym4 P) (hG : ∀ a ∈ G, a ∈ O12) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKR1 P (G ++ 3 :: (List.replicate r 3 ++ 1 :: R)))
      (hd QG.gKUV (P ++ G ++ 2 :: List.replicate r 2) (1 :: R)) := by
  have hV : Valid [ALL, O12, T3, ALL] [P, G, List.replicate r 3, R] :=
    Valid.cons hP (Valid.cons hG (Valid.cons (rep_t3 r) (Valid.cons hR (Valid.nil _))))
  exact checkFT (env := [P, G, List.replicate r 3, R]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 2, .blk 2 (.const 2)]) (rs' := [.sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gkuv (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gKUV A R) (hdR QG.gKU2 [] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gku2 (a b : Nat) (R : List Nat) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKU2 [] (List.replicate a 2 ++ List.replicate b 3 ++ 1 :: R))
      (hdR QG.gKE1 (List.replicate (a + b) 3 ++ [1]) R) := by
  have hV : Valid [Mk, T3, ALL] [List.replicate a 2, List.replicate b 3, R] :=
    Valid.cons (rep2_mk a) (Valid.cons (rep_t3 b) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gKU2 [] (List.replicate a 2 ++ List.replicate b 3 ++ 1 :: R))
      (hdR QG.gKE1 (List.replicate a 3 ++ (List.replicate b 3 ++ [1])) R) :=
    checkFF (env := [List.replicate a 2, List.replicate b 3, R]) (E := []) (k := 6) hV trivial
      (ls := []) (rs := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 (.const 3), .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq rfl (by rw [← List.append_assoc, List.replicate_append_replicate])

theorem gdpTop (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gDP P (3 :: R)) (hdR QG.gKE (P ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gke1End (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gKE1 P (1 :: R)) (hd QG.gUP P (1 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Comparing the top (`k` marked, `a` unmarked cells left) with an entry (`k` marked, `b` left). -/
def KC (fm rest : List Nat) (k a b : Nat) : ZC :=
  hdR QG.gKE1 (List.replicate k 2 ++ List.replicate a 3 ++ [1])
    (MEnc fm ++ (List.replicate k 2 ++ List.replicate b 3 ++ [1]) ++ rest)

theorem noB_marked (k a : Nat) : NoB (List.replicate k 2 ++ List.replicate a 3 ++ [1]) :=
  ((mk_noB (rep2_mk k)).app (o13_noB (rep3_o13 a))).app (NoB.cons one_nb NoB.nil)

theorem sym4_marked (k a : Nat) : Sym4 (List.replicate k 2 ++ List.replicate a 3 ++ [1]) :=
  (noB_marked k a).sym4

theorem noB_mk_rep (k : Nat) : NoB (List.replicate k 2) := mk_noB (rep2_mk k)

/-- The prefix of a comparison step: the next cell of the entry is marked. -/
theorem cmpPre (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) (k a b : Nat) :
    zgiLogic.Reach (KC fm rest k a (b + 1))
      (hdR QG.gKP (List.replicate k 2 ++ List.replicate a 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
        (List.replicate b 3 ++ 1 :: rest)) := by
  have hE : Sym4 ((List.replicate k 2 ++ List.replicate (b + 1) 3 ++ [1]) ++ rest) :=
    (sym4_marked k (b + 1)).app hrest
  have h1 := gke1Walk _ hE fm hfm _ (sym4_marked k a)
  have hP : Sym4 (List.replicate k 2 ++ List.replicate a 3 ++ [1] ++ MEnc fm) :=
    (sym4_marked k a).app (o12_sym4 (MEnc_o12 fm))
  have hR : Sym4 (List.replicate b 3 ++ 1 :: rest) :=
    (sym4_rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hrest)
  have h2 := gkeMark (List.replicate k 2 ++ List.replicate a 3 ++ [1] ++ MEnc fm) (List.replicate b 3 ++ 1 :: rest) k hP hR
  refine (h1.of_eq ?_ rfl).trans (h2.of_eq ?_ rfl)
  · simp [KC, List.append_assoc]
  · simp [List.replicate_succ, List.append_assoc]

@[simp] theorem Sym4_app_iff {u v : List Nat} : Sym4 (u ++ v) ↔ Sym4 u ∧ Sym4 v := by
  constructor
  · intro h; exact ⟨fun a ha => h a (List.mem_append_left _ ha), fun a ha => h a (List.mem_append_right _ ha)⟩
  · rintro ⟨h1, h2⟩; exact h1.app h2

@[simp] theorem Sym4_cons_iff {a : Nat} {v : List Nat} : Sym4 (a :: v) ↔ a ∈ ALL ∧ Sym4 v := by
  constructor
  · intro h; exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
  · rintro ⟨h1, h2⟩; exact Sym4.cons h1 h2

@[simp] theorem Sym4_nil_iff : Sym4 [] ↔ True := ⟨fun _ => trivial, fun _ => Sym4.nil⟩

@[simp] theorem Sym4_rep_iff {k c : Nat} : Sym4 (List.replicate k c) ↔ (k = 0 ∨ c ∈ ALL) := by
  constructor
  · intro h
    cases k with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr (h c (by simp))
  · rintro (rfl | h)
    · exact Sym4.nil
    · exact Sym4.rep k c h

@[simp] theorem Sym4_MEnc {fm : List Nat} : Sym4 (MEnc fm) := o12_sym4 (MEnc_o12 fm)
@[simp] theorem Sym4_Enc {fm : List Nat} : Sym4 (Enc fm) := o13_sym4 (Enc_o13 fm)

@[simp] theorem NoB_app_iff {u v : List Nat} : NoB (u ++ v) ↔ NoB u ∧ NoB v := by
  constructor
  · intro h; exact ⟨fun a ha => h a (List.mem_append_left _ ha), fun a ha => h a (List.mem_append_right _ ha)⟩
  · rintro ⟨h1, h2⟩; exact h1.app h2

@[simp] theorem NoB_cons_iff {a : Nat} {v : List Nat} : NoB (a :: v) ↔ a ∈ NB ∧ NoB v := by
  constructor
  · intro h; exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
  · rintro ⟨h1, h2⟩; exact NoB.cons h1 h2

@[simp] theorem NoB_nil_iff : NoB [] ↔ True := ⟨fun _ => trivial, fun _ => NoB.nil⟩

@[simp] theorem NoB_rep_iff {k c : Nat} : NoB (List.replicate k c) ↔ (k = 0 ∨ c ∈ NB) := by
  constructor
  · intro h
    cases k with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr (h c (by simp))
  · rintro (rfl | h)
    · exact NoB.nil
    · intro a ha; rw [List.eq_of_mem_replicate ha]; exact h

@[simp] theorem NoB_MEnc {fm : List Nat} : NoB (MEnc fm) := o12_noB (MEnc_o12 fm)
@[simp] theorem NoB_Enc {fm : List Nat} : NoB (Enc fm) := o13_noB (Enc_o13 fm)

/-- Both have more cells: the comparison continues. -/
theorem cmpCont (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) (k a b : Nat) :
    zgiLogic.Reach (KC fm rest k (a + 2) (b + 2)) (KC fm rest (k + 1) (a + 1) (b + 1)) := by
  have h1 := cmpPre fm rest hfm hrest k (a + 2) (b + 1)
  have hA : NoB (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2) := by simp [NB]
  have hX : Sym4 (List.replicate b 3 ++ 1 :: rest) := by simp [ALL, hrest]
  have h2 := gkp3 (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (List.replicate b 3 ++ 1 :: rest) hA.sym4 hX
  have h3 := gkbm (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (3 :: (List.replicate b 3 ++ 1 :: rest)) hA (by simp [ALL, hrest])
  have h4 := gkvm k (List.replicate (a + 1) 3 ++ 1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 3 :: (List.replicate b 3 ++ 1 :: rest))) (by simp [ALL, hrest])
  have h5 := gkqm3 (List.replicate (k + 1) 2) (List.replicate a 3 ++ 1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 3 :: (List.replicate b 3 ++ 1 :: rest))) (by simp [ALL, hrest]) (by simp [ALL, hrest])
  have h6 := gkeTop (List.replicate (k + 1) 2 ++ [3]) (List.replicate a 3) (MEnc fm ++ List.replicate (k + 1) 2 ++ 3 :: (List.replicate b 3 ++ 1 :: rest)) (by simp [ALL, hrest]) (bits_rep3 a) (by simp [ALL, hrest])
  have hh := h1.trans ((h2.of_eq (by simp [List.replicate_succ]) rfl).trans (h3.trans
    ((h4.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
      ((h5.of_eq (by simp [List.replicate_succ]) rfl).trans h6))))
  refine hh.of_eq rfl ?_
  simp [KC, List.replicate_succ, List.append_assoc]

/-- The top is exhausted first: the entry is marked completely. -/
theorem cmpVlt (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) (k b : Nat) :
    zgiLogic.Reach (KC fm rest k 1 (b + 2))
      (hdR QG.gKE1 (List.replicate (k + 1) 3 ++ [1]) (MEnc fm ++ List.replicate (k + b + 2) 2 ++ 1 :: rest)) := by
  have h1 := cmpPre fm rest hfm hrest k 1 (b + 1)
  have hA : NoB (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2) := by simp [NB]
  have h2 := gkp3 (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (List.replicate b 3 ++ 1 :: rest) hA.sym4 (by simp [ALL, hrest])
  have h3 := gkbm (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (3 :: (List.replicate b 3 ++ 1 :: rest)) hA (by simp [ALL, hrest])
  have h4 := gkvm k (1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 3 :: (List.replicate b 3 ++ 1 :: rest))) (by simp [ALL, hrest])
  have h5 := gkqm1 (List.replicate (k + 1) 2) (MEnc fm ++ List.replicate (k + 1) 2 ++ 3 :: (List.replicate b 3 ++ 1 :: rest)) (by simp [ALL]) (by simp [ALL, hrest])
  have h6 := gkr (List.replicate (k + 1) 2 ++ [1]) (MEnc fm ++ List.replicate (k + 1) 2) rest b (by simp [ALL]) (by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact MEnc_o12 fm a ha
    · exact rep2_o12 _ a ha) hrest
  have hB : NoB (List.replicate (k + 1) 2 ++ [1] ++ (MEnc fm ++ List.replicate (k + 1) 2) ++ 2 :: List.replicate b 2) := by simp [NB]
  have h7 := gkuv _ (1 :: rest) hB (by simp [ALL, hrest])
  have h8 := gku2 (k + 1) 0 (MEnc fm ++ List.replicate (k + 1) 2 ++ 2 :: List.replicate b 2 ++ 1 :: rest) (by simp [ALL, hrest])
  have hh := h1.trans ((h2.of_eq (by simp [List.replicate_succ]) rfl).trans (h3.trans
    ((h4.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
      ((h5.of_eq rfl rfl).trans ((h6.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans (h7.trans
        (h8.of_eq (by simp [List.append_assoc]) rfl)))))))
  refine hh.of_eq rfl ?_
  have e : List.replicate (k + b + 2) 2 = List.replicate (k + 1) 2 ++ 2 :: List.replicate b 2 := by
    rw [show k + b + 2 = (k + 1) + (b + 1) by omega, ← List.replicate_append_replicate]
    simp [List.replicate_succ]
  rw [e]
  simp [List.append_assoc, List.replicate_succ]

/-- The entry is exhausted first: it is marked completely, the top is unmarked. -/
theorem cmpElt (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) (k a : Nat) :
    zgiLogic.Reach (KC fm rest k (a + 2) 1)
      (hdR QG.gKE1 (List.replicate (k + a + 2) 3 ++ [1]) (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest)) := by
  have h1 := cmpPre fm rest hfm hrest k (a + 2) 0
  have hA : NoB (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2) := by simp [NB]
  have h2 := gkp1 (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    rest hA.sym4 hrest
  have h3 := gkbd (List.replicate k 2 ++ List.replicate (a + 2) 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (1 :: rest) hA (by simp [ALL, hrest])
  have h4 := gkvd k (List.replicate (a + 1) 3 ++ 1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest)) (by simp [ALL, hrest])
  have h5 := gkqd3 (List.replicate (k + 1) 2) (List.replicate a 3 ++ 1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest)) (by simp [ALL]) (by simp [ALL, hrest])
  have h6 := gkuv (List.replicate (k + 1) 2) (3 :: (List.replicate a 3 ++ 1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest))) (by simp [NB]) (by simp [ALL, hrest])
  have h7 := gku2 (k + 1) (a + 1) (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest) (by simp [ALL, hrest])
  have hh := h1.trans ((h2.of_eq (by simp) rfl).trans (h3.trans
    ((h4.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
      ((h5.of_eq (by simp [List.replicate_succ]) rfl).trans (h6.trans
        (h7.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl))))))
  refine hh.of_eq rfl ?_
  have e : k + 1 + (a + 1) = k + a + 2 := by omega
  rw [e]

/-- Both are exhausted together: collision. -/
theorem cmpEq (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) (k : Nat) :
    zgiLogic.Reach (KC fm rest k 1 1)
      (hdR QG.gFG (List.replicate (k + 1) 2 ++ [1]) (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest)) := by
  have h1 := cmpPre fm rest hfm hrest k 1 0
  have hA : NoB (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2) := by simp [NB]
  have h2 := gkp1 (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    rest hA.sym4 hrest
  have h3 := gkbd (List.replicate k 2 ++ List.replicate 1 3 ++ [1] ++ MEnc fm ++ List.replicate (k + 1) 2)
    (1 :: rest) hA (by simp [ALL, hrest])
  have h4 := gkvd k (1 :: (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest)) (by simp [ALL, hrest])
  have h5 := gkqd1 (List.replicate (k + 1) 2) (MEnc fm ++ List.replicate (k + 1) 2 ++ 1 :: rest) (by simp [ALL]) (by simp [ALL, hrest])
  have hh := h1.trans ((h2.of_eq (by simp) rfl).trans (h3.trans
    ((h4.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans h5)))
  exact hh

theorem cmpAll (fm rest : List Nat) (hfm : ∀ v ∈ fm, 1 ≤ v) (hrest : Sym4 rest) :
    ∀ n k a b, min a b = n + 1 →
      (a = b → zgiLogic.Reach (KC fm rest k a b)
        (hdR QG.gFG (List.replicate (k + a) 2 ++ [1]) (MEnc fm ++ List.replicate (k + a) 2 ++ 1 :: rest))) ∧
      (a ≠ b → zgiLogic.Reach (KC fm rest k a b)
        (hdR QG.gKE1 (List.replicate (k + a) 3 ++ [1]) (MEnc fm ++ List.replicate (k + b) 2 ++ 1 :: rest))) := by
  intro n
  induction n with
  | zero =>
    intro k a b hm
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · have ha : a = 1 := by omega
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
      subst ha
      exact ⟨fun h => by omega, fun _ => cmpVlt fm rest hfm hrest k b'⟩
    · have ha : a = 1 := by omega
      subst hab; subst ha
      exact ⟨fun _ => cmpEq fm rest hfm hrest k, fun h => absurd rfl h⟩
    · have hb : b = 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
      subst hb
      exact ⟨fun h => by omega, fun _ => cmpElt fm rest hfm hrest k a'⟩
  | succ n ih =>
    intro k a b hm
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have h1 := cmpCont fm rest hfm hrest k a' b'
    obtain ⟨hF, hO⟩ := ih (k + 1) (a' + 1) (b' + 1) (by omega)
    have e1 : k + 1 + (a' + 1) = k + (a' + 2) := by omega
    have e2 : k + 1 + (b' + 1) = k + (b' + 2) := by omega
    rw [e1] at hF hO
    rw [e2] at hO
    exact ⟨fun h => h1.trans (hF (by omega)), fun h => h1.trans (hO (by omega))⟩

theorem MEnc_append (a b : List Nat) : MEnc (a ++ b) = MEnc a ++ MEnc b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [MEnc, ih, List.append_assoc]

theorem Enc_append (a b : List Nat) : Enc (a ++ b) = Enc a ++ Enc b := by
  induction a with
  | nil => rfl
  | cons v a ih => simp [Enc, ih, List.append_assoc]

@[simp] theorem unm_cons (a : Nat) (l : List Nat) : unm (a :: l) = unm1 a :: unm l := rfl
@[simp] theorem unm_nil : unm [] = [] := rfl
attribute [simp] unm_append unm_rep2 unm_rep3

theorem unm_MEnc : ∀ fm : List Nat, unm (MEnc fm) = Enc fm
  | [] => rfl
  | v :: fm => by simp [MEnc, Enc, U, unm_MEnc fm, unm1]

/-- Failure: unmark everything and return to the top of the stack. -/
theorem failPath (P R1 Z : List Nat) (hP : NoB P) (hR : NoB R1) (hZ : Sym4 Z) :
    zgiLogic.Reach (hdR QG.gFG P (R1 ++ 0 :: Z)) (hdR QG.gDC [] (unm (P ++ R1) ++ 0 :: Z)) := by
  have hV : Valid [NB, NB, ALL] [P, R1, Z] := Valid.cons hP (Valid.cons hR (Valid.cons hZ (Valid.nil _)))
  have h1 : zgiLogic.Reach (hdR QG.gFG P (R1 ++ 0 :: Z)) (hd QG.gFL (P ++ R1) (0 :: Z)) :=
    checkFT (env := [P, R1, Z]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact h1.trans (gflWalk (P ++ R1) (0 :: Z) (hP.app hR) (by simp [ALL, hZ]))

theorem unm_o13 {W : List Nat} (h : ∀ a ∈ W, a ∈ O13) : unm W = W := by
  induction W with
  | nil => rfl
  | cons a W ih =>
    have ha := h a (List.mem_cons_self ..)
    have hW : ∀ b ∈ W, b ∈ O13 := fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp [O13] at ha
    rcases ha with rfl | rfl <;> simp [unm1, ih hW]

theorem unm_Enc (l : List Nat) : unm (Enc l) = Enc l := unm_o13 (Enc_o13 l)

theorem scanLoop (v : Nat) (Tc Z : List Nat) (hTc : ∀ a ∈ Tc, a ∈ O13) (hZ : Sym4 Z) :
    ∀ ents fm, (∀ e ∈ ents, 1 ≤ e) → (∀ e ∈ fm, 1 ≤ e) → 1 ≤ v →
    (v ∉ ents → zgiLogic.Reach
      (hdR QG.gKE1 (List.replicate v 3 ++ [1]) (MEnc fm ++ Enc ents ++ 1 :: (Tc ++ 0 :: Z)))
      (hd QG.gUP (List.replicate v 3 ++ [1] ++ MEnc (fm ++ ents)) (1 :: (Tc ++ 0 :: Z)))) ∧
    (v ∈ ents → zgiLogic.Reach
      (hdR QG.gKE1 (List.replicate v 3 ++ [1]) (MEnc fm ++ Enc ents ++ 1 :: (Tc ++ 0 :: Z)))
      (hdR QG.gDC [] (List.replicate v 3 ++ 1 :: (Enc fm ++ Enc ents ++ 1 :: Tc) ++ 0 :: Z))) := by
  intro ents
  induction ents with
  | nil =>
    intro fm _ hfm _
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    have hR : Sym4 (1 :: (Tc ++ 0 :: Z)) := by simp [ALL, (o13_sym4 hTc), hZ]
    have h1 := gke1Walk (1 :: (Tc ++ 0 :: Z)) hR fm hfm (List.replicate v 3 ++ [1]) (by simp [ALL])
    have h2 := gke1End (List.replicate v 3 ++ [1] ++ MEnc fm) (Tc ++ 0 :: Z) (by simp [ALL]) (by simp [ALL, (o13_sym4 hTc), hZ])
    exact (h1.of_eq (by simp [Enc]) rfl).trans (h2.of_eq rfl (by simp))
  | cons e ents ih =>
    intro fm hents hfm hv
    have he : 1 ≤ e := hents e (List.mem_cons_self ..)
    have hents' : ∀ x ∈ ents, 1 ≤ x := fun x hx => hents x (List.mem_cons_of_mem _ hx)
    have hrest : Sym4 (Enc ents ++ 1 :: (Tc ++ 0 :: Z)) := by simp [ALL, (o13_sym4 hTc), hZ]
    obtain ⟨hF, hO⟩ := cmpAll fm (Enc ents ++ 1 :: (Tc ++ 0 :: Z)) hfm hrest (min v e - 1) 0 v e (by omega)
    have hstart : hdR QG.gKE1 (List.replicate v 3 ++ [1]) (MEnc fm ++ Enc (e :: ents) ++ 1 :: (Tc ++ 0 :: Z))
        = KC fm (Enc ents ++ 1 :: (Tc ++ 0 :: Z)) 0 v e := by
      simp [KC, Enc, U, List.append_assoc]
    by_cases hve : v = e
    · subst hve
      have hf := hF rfl
      refine ⟨fun h => absurd (List.mem_cons_self ..) h, fun _ => ?_⟩
      rw [hstart]
      have h2 := failPath (List.replicate (0 + v) 2 ++ [1])
        (MEnc fm ++ List.replicate (0 + v) 2 ++ 1 :: (Enc ents ++ 1 :: Tc)) Z (by simp [NB]) (by simp [NB, o13_noB hTc]) hZ
      refine hf.trans (h2.of_eq (by simp [List.append_assoc]) ?_)
      simp [unm_MEnc, unm_Enc, unm_o13 hTc, Enc, U, unm1, List.append_assoc]
    · have ho := hO hve
      have hfm' : ∀ x ∈ fm ++ [e], 1 ≤ x := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hfm x hx
        · simp at hx; omega
      obtain ⟨ih1, ih2⟩ := ih (fm ++ [e]) hents' hfm' hv
      have hmid : zgiLogic.Reach (hdR QG.gKE1 (List.replicate v 3 ++ [1]) (MEnc fm ++ Enc (e :: ents) ++ 1 :: (Tc ++ 0 :: Z)))
          (hdR QG.gKE1 (List.replicate v 3 ++ [1]) (MEnc (fm ++ [e]) ++ Enc ents ++ 1 :: (Tc ++ 0 :: Z))) := by
        rw [hstart]
        exact ho.of_eq rfl (by simp [MEnc, List.append_assoc, MEnc_append])
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hn : v ∉ ents := fun hh => h (List.mem_cons_of_mem _ hh)
        exact hmid.trans ((ih1 hn).of_eq rfl (by simp [List.append_assoc]))
      · have hm : v ∈ ents := by
          rcases List.mem_cons.1 h with h | h
          · exact absurd h hve
          · exact h
        exact hmid.trans ((ih2 hm).of_eq rfl (by simp [Enc_append, Enc, U, List.append_assoc]))

theorem gdpPop (X : List Nat) (hX : Sym4 X) :
    zgiLogic.Reach (hdR QG.gDP [] (1 :: X)) (hdR QG.gGL [0] X) := by
  have hV : Valid [ALL] [X] := Valid.cons hX (Valid.nil _)
  exact checkFF (env := [X]) (E := []) (k := 3) hV trivial
    (ls := []) (rs := [.sym 1, .blk 0 .id])
    (ls' := [.sym 0]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gdcDec (X : List Nat) (hX : Sym4 X) :
    zgiLogic.Reach (hdR QG.gDC [] (3 :: X)) (hdR QG.gDP [0] X) := by
  have hV : Valid [ALL] [X] := Valid.cons hX (Valid.nil _)
  exact checkFF (env := [X]) (E := []) (k := 3) hV trivial
    (ls := []) (rs := [.sym 3, .blk 0 .id])
    (ls' := [.sym 0]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gdcEmpty (X : List Nat) (hX : Sym4 X) :
    zgiLogic.Reach (hdR QG.gDC [] (1 :: X)) (hdR QG.FR0 [1] X) := by
  have hV : Valid [ALL] [X] := Valid.cons hX (Valid.nil _)
  exact checkFF (env := [X]) (E := []) (k := 3) hV trivial
    (ls := []) (rs := [.sym 1, .blk 0 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

end ZP.G
