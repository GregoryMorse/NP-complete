module

public import ZP.Pair
public import ZP.CompileBPP
public import ZP.AllDefs
public import ZP.Count

@[expose] public section

/-! The pair lemma for the P = PP machine, copied from `ZP/Pair.lean` and adapted. -/

namespace ZP.BPP

open ZP

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStart (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ NB) :
    zbppLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ [1]))) (s ++ (1 :: (T ++ [1])))) := by
  have hV : Valid [bits, bits, bits, NB] [Jl, Jr, s, T] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.nil _))))
  exact checkFF (env := [Jl, Jr, s, T]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- One `COPY` round: a `1` at the far end for each bit of `s`. -/
theorem copyBody (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ NB) (hb : b ∈ bits) :
    zbppLogic.Reach (hdR Q.COPY (P ++ u) (b :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3)))))))
      (hdR Q.COPY (P ++ (u ++ [b])) (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ [3])))))) := by
  have hV : Valid [NB, bits, bits, NB] [P, u, v, T] := Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hT (Valid.nil _))))
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
theorem blkDecStep (Jl : List Nat) (Jr : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (b : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ NB) (hb : b ∈ bits) :
    zbppLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (b :: (Jr ++ (1 :: s))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hdR Q.GRB (Jl ++ (b :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3]))))))))))))) []) := by
  have hV : Valid [bits, bits, bits, T3, NB] [Jl, Jr, s, t, Bl] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _)))))
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
theorem blkDecLast (Jl : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (hJl : Bits Jl) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ NB) :
    zbppLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: s))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3))))))))
      (hd Q.WB1 (Jl ++ [1]) (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, NB] [Jl, s, t, Bl] := Valid.cons hJl (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))
  exact checkFT (env := [Jl, s, t, Bl]) (E := []) (k := 35) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3)])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem wbBody (Jl : List Nat) (Y : List Nat) (b : Nat) (hJl : Bits Jl) (hY : Sym4 Y) (hb : b ∈ bits) :
    zbppLogic.Reach (hd Q.WB1 (Jl ++ (b :: [1])) Y)
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
    zbppLogic.Reach (hd Q.WB1 [1] (j ++ (1 :: Y)))
      (hdR Q.GC (1 :: (1 :: (j ++ [1]))) Y) := by
  have hV : Valid [bits, ALL] [j, Y] := Valid.cons hj (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [j, Y]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Guest source copy: one bit to the far left. -/
theorem gcBody (Ur : List Nat) (V : List Nat) (P : List Nat) (u : List Nat) (v : List Nat) (Rest : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hP : Bits P) (hu : Bits u) (hv : Bits v) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zbppLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (b :: (v ++ (1 :: Rest))))
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
    zbppLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: X))))) (1 :: Rest))
      (hd Q.QC (1 :: (Xr ++ (1 :: (V ++ P)))) (1 :: (X ++ (1 :: Rest)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Code copy: one bit into `Q`. -/
theorem qcBody (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (b : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hb : b ∈ bits) :
    zbppLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ [b])))))) (Qc ++ (1 :: (X ++ (1 :: Rest)))))
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
    zbppLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ [1]))))) (P ++ (1 :: (X ++ (1 :: Rest)))))
      (hd Q.TW (2 :: P) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (1 :: (X ++ (1 :: Rest)))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL] [P, Xr, Vq, X, Rest] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkTT (env := [P, Xr, Vq, X, Rest]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 16) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dOk0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.SINC (1 :: (j ++ (1 :: s))) []) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 14) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP11 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (1 :: Fu)))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (1 :: Fu)) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad1E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (1 :: Fu))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0 (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP10 [1] (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: Fu))))))))
      (hd Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: [1]))))) (3 :: (1 :: Fu))) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem dBad0E (j : List Nat) (s : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: [2]))))) (3 :: (1 :: Fu)))
      (hd Q.JINC (1 :: j) [1]) := by
  have hV : Valid [bits, bits, NB] [j, s, Fu] := Valid.cons hj (Valid.cons hs (Valid.cons hFu (Valid.nil _)))
  exact checkFT (env := [j, s, Fu]) (E := []) (k := 11) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 3, .sym 1, .blk 2 .id])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR Q.GRB (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR Q.GRB (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR Q.GRB (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR Q.GRB (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zbppLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)



theorem copyLoop (P T : List Nat) (hP : NoB P) (hT : ∀ a ∈ T, a ∈ NB) :
    ∀ v u, Bits u → Bits v →
      zbppLogic.Reach (hdR Q.COPY (P ++ u) (v ++ 1 :: (T ++ 1 :: List.replicate u.length 3)))
        (hdR Q.COPY (P ++ (u ++ v)) (1 :: (T ++ 1 :: List.replicate (u ++ v).length 3)))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := copyBody P u v T b hP hu hv.tail hT hv.head
    have h2 := copyLoop P T hP hT v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.of_eq (by simp [List.replicate_succ']) (by simp only [List.append_assoc, List.singleton_append]))


theorem o13_nb {T : List Nat} (h : ∀ a ∈ T, a ∈ O13) : ∀ a ∈ T, a ∈ NB := fun a ha => by
  have := h a ha; simp [O13] at this; rcases this with rfl | rfl <;> simp [NB]

/-- `BLK` up to the end of the `COPY` loop. -/
theorem blkCopy (Jl Jr s T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s)
    (hT : ∀ a ∈ T, a ∈ NB) :
    zbppLogic.Reach (hdR Q.GRB (Jl ++ 1 :: (Jr ++ 1 :: (s ++ 1 :: T))) [])
      (hdR Q.COPY (Jl ++ 1 :: (Jr ++ 1 :: s)) (1 :: (T ++ 1 :: List.replicate s.length 3))) := by
  have hP : NoB (Jl ++ 1 :: (Jr ++ [1])) := hJl.noB.app (NoB.cons one_nb (hJr.noB.app (NoB.cons one_nb NoB.nil)))
  exact (blkStart Jl Jr s T hJl hJr hs hT).trans
    ((copyLoop _ T hP hT s [] Bits.nil hs).of_eq (by simp) (by simp))


theorem gcLoop (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ v u, Bits u → Bits v →
      zbppLogic.Reach (hdR Q.GC (u.reverse ++ 1 :: (V ++ (P ++ 1 :: u))) (v ++ 1 :: Rest))
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
      zbppLogic.Reach (hd Q.QC (Qc ++ 1 :: (Xr ++ 1 :: (V ++ vr.reverse))) (Qc ++ 1 :: (X ++ 1 :: Rest)))
        (hd Q.QC (vr.reverse ++ (Qc ++ 1 :: (Xr ++ 1 :: V))) (vr.reverse ++ (Qc ++ 1 :: (X ++ 1 :: Rest))))
  | [], Qc, _, _ => by
    simp only [List.reverse_nil, List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: vr, Qc, hv, hQ => by
    have h1 := qcBody Qc Xr V vr.reverse X Rest b hQ hXr hV hv.tail.rev hX hR hv.head
    have h2 := qcLoop Xr V X Rest hXr hV hX hR vr (b :: Qc) hv.tail (Bits.cons hv.head hQ)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


theorem wbLoop : ∀ (jr Y : List Nat), Bits jr → Sym4 Y →
    zbppLogic.Reach (hd Q.WB1 (jr.reverse ++ [1]) Y) (hd Q.WB1 [1] (jr.reverse ++ Y))
  | [], Y, _, _ => LTM.Reach.refl _ _
  | b :: jr, Y, hj, hY => by
    have h1 := wbBody jr.reverse Y b hj.tail.rev hY hj.head
    have h2 := wbLoop jr (b :: Y) hj.tail (Sym4.cons (bits_all hj.head) hY)
    exact (h1.of_eq (by simp) rfl).trans (h2.of_eq rfl (by simp))


/-- The decider fuel: one block per position of the walker. -/
theorem decFuel (s t : List Nat) (n : Nat) (hn : s.length = n) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) :
    ∀ Jr Jl i, Bits Jl → Bits Jr →
      zbppLogic.Reach
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
    have hA := blkCopy Jl [] s _ hJl Bits.nil hs (o13_nb hT)
    have hL := blkDecLast Jl s t (FWr n (List.replicate i (n + 1))) hJl hs ht (o13_nb hBl)
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
    have hA := blkCopy Jl (b :: Jr') s _ hJl hJr hs (o13_nb hT)
    have hS := blkDecStep Jl Jr' s t (FWr n (List.replicate i (n + 1))) b hJl hJr.tail hs ht (o13_nb hBl) hJr.head
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
    ∃ g, 1 ≤ g ∧ zbppLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  have hB0 := hA.trans (zpBase_ext_zbppLogic.reach (hr.of_eq (by rw [hcode]) rfl))
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
    refine ⟨k + 1, by omega, hB0.trans (zpBase_ext_zbppLogic.reach (hB.of_eq ?_ ?_))⟩
    · rw [eT, eV, hk]
      simp [List.replicate_succ, rep_cons_comm, bitsOf]
    · unfold Bd Zp.Lw Zp.Rw
      rw [hrr, ← eV]
      simp [cellN, bitsOf, List.replicate_succ, rep_cons_comm]
  | cons x xt =>
    have hB := segB R'.reverse (bitsOf xt.reverse) X' (k + 1) 0 p (bn x) b (bn_cases x) hb hRr
      (Bits.ofB _) hX'
    refine ⟨k + 1 + 1, by omega, hB0.trans (zpBase_ext_zbppLogic.reach (hB.of_eq ?_ ?_))⟩
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
      zbppLogic.Reach (hdR Q.GC (1 :: (1 :: W1 ++ (bitsOf Pb ++ [1]))) (bitsOf Xb ++ 1 :: Rest))
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
  exact ⟨ds', hd', hl', h1.trans (zpBase_ext_zbppLogic.reach h2)⟩



/-- Decider fuel, run of `J` on `s` with the clock, up to the dispatch state. -/
theorem dPhase (Jb Sb : List Bool) (b : Bool) :
    ∃ Fu, NoB Fu ∧ zbppLogic.Reach (TR (bitsOf Jb) Sb b)
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
    zbppLogic.Reach (hd Q.SINC (A ++ 1 :: bitsOf r.reverse) (List.replicate k 2))
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
    zbppLogic.Reach (hd Q.JINC (1 :: bitsOf r.reverse) (List.replicate k 2 ++ [1]))
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
    zbppLogic.zstep (hd Q.BEEP (1 :: (j ++ 1 :: (s ++ 1 :: [1]))) Y) =
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

/-! ## Verdict segments: accept / reject / outside the promise -/

/-- Accepted, `A = 0`, `|C| = 1`: truth flag `1`. -/
theorem accTrue1 (j : List Nat) (s : List Nat) (Za : List Nat) (R : List Nat) (Fu : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hZa : ∀ a ∈ Za, a ∈ Z2) (hR : Bits R) (hFu : NoB Fu) (hc : c ∈ bits) :
    zbppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (1 :: (Za ++ (1 :: (R ++ (1 :: (Fu))))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: [1]))))))) []) := by
  have hV : Valid [bits, bits, Z2, bits, NB] [j, s, Za, R, Fu] := (Valid.cons hj (Valid.cons hs (Valid.cons hZa (Valid.cons hR (Valid.cons hFu (Valid.nil _))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Za, R, Fu]) (E := []) (k := 28) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Za, R, Fu]) (E := []) (k := 28) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Accepted, `A = 0`, `|C| ≥ 2`: truth flag `1`. -/
theorem accTrue2 (j : List Nat) (s : List Nat) (Cq : List Nat) (Za : List Nat) (R : List Nat) (Fu : List Nat) (c : Nat) (y : Nat) (hj : Bits j) (hs : Bits s) (hCq : Bits Cq) (hZa : ∀ a ∈ Za, a ∈ Z2) (hR : Bits R) (hFu : NoB Fu) (hc : c ∈ bits) (hy : y ∈ bits) :
    zbppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (y :: (Cq ++ (1 :: (Za ++ (1 :: (R ++ (1 :: (Fu))))))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: [1]))))))) []) := by
  have hV : Valid [bits, bits, bits, Z2, bits, NB] [j, s, Cq, Za, R, Fu] := (Valid.cons hj (Valid.cons hs (Valid.cons hCq (Valid.cons hZa (Valid.cons hR (Valid.cons hFu (Valid.nil _)))))))
  rcases mem_bits hc with rfl | rfl <;> rcases mem_bits hy with rfl | rfl
  · exact checkFF (env := [j, s, Cq, Za, R, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, R, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, R, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cq, Za, R, Fu]) (E := []) (k := 36) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Rejected, `R = 0`: truth flag `0`. -/
theorem rejTrue (j : List Nat) (s : List Nat) (Cp : List Nat) (A : List Nat) (Zr : List Nat) (Fu : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCp : Bits Cp) (hA : Bits A) (hZr : ∀ a ∈ Zr, a ∈ Z2) (hFu : NoB Fu) (hc : c ∈ bits) :
    zbppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (1 :: (A ++ (1 :: (Zr ++ (1 :: (Fu)))))))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: [1])))))) []) := by
  have hV : Valid [bits, bits, bits, bits, Z2, NB] [j, s, Cp, A, Zr, Fu] := (Valid.cons hj (Valid.cons hs (Valid.cons hCp (Valid.cons hA (Valid.cons hZr (Valid.cons hFu (Valid.nil _)))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Cp, A, Zr, Fu]) (E := []) (k := 37) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, A, Zr, Fu]) (E := []) (k := 37) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Accepted, `A > 0`, `C = 1 0^k`: `A -= 1`, `C -= 1`, refill. -/
theorem accDecE (j : List Nat) (s : List Nat) (Z : List Nat) (Ul : List Nat) (Za : List Nat) (R : List Nat) (D : List Nat) (E : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hR : Bits R) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) :
    zbppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (3 :: (Z ++ (1 :: (Ul ++ (3 :: (Za ++ (1 :: (R ++ (1 :: (1 :: (D ++ (E)))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (2 :: (List.replicate Z.length 3 ++ (1 :: (Ul ++ (2 :: (List.replicate Za.length 3 ++ (1 :: (R ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))))))) := by
  have hV : Valid [bits, bits, Z2, bits, Z2, bits, T3, Z2] [j, s, Z, Ul, Za, R, D, E] := (Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hUl (Valid.cons hZa (Valid.cons hR (Valid.cons hD (Valid.cons hE (Valid.nil _)))))))))
  exact checkFF (env := [j, s, Z, Ul, Za, R, D, E]) (E := []) (k := 52) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .blk 7 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 (.const 3), .sym 1, .blk 3 .id, .sym 2, .blk 4 (.const 3), .sym 1, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .blk 7 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Accepted, `A > 0`, `C = c C' 1 0^k`. -/
theorem accDecC (j : List Nat) (s : List Nat) (Cp : List Nat) (Z : List Nat) (Ul : List Nat) (Za : List Nat) (R : List Nat) (D : List Nat) (E : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCp : Bits Cp) (hZ : ∀ a ∈ Z, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hR : Bits R) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hc : c ∈ bits) :
    zbppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (3 :: (Z ++ (1 :: (Ul ++ (3 :: (Za ++ (1 :: (R ++ (1 :: (1 :: (D ++ (E)))))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (c :: (Cp ++ (2 :: (List.replicate Z.length 3 ++ (1 :: (Ul ++ (2 :: (List.replicate Za.length 3 ++ (1 :: (R ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))))))))) := by
  have hV : Valid [bits, bits, bits, Z2, bits, Z2, bits, T3, Z2] [j, s, Cp, Z, Ul, Za, R, D, E] := (Valid.cons hj (Valid.cons hs (Valid.cons hCp (Valid.cons hZ (Valid.cons hUl (Valid.cons hZa (Valid.cons hR (Valid.cons hD (Valid.cons hE (Valid.nil _))))))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Cp, Z, Ul, Za, R, D, E]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 4 .id, .sym 2, .blk 5 (.const 3), .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, Ul, Za, R, D, E]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 4 .id, .sym 2, .blk 5 (.const 3), .sym 1, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Rejected, `R > 0`, `C = 1 0^k`: `R -= 1`, `C -= 1`, refill. -/
theorem rejDecE (j : List Nat) (s : List Nat) (Z : List Nat) (A : List Nat) (Ur : List Nat) (Zr : List Nat) (D : List Nat) (E : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hA : Bits A) (hUr : Bits Ur) (hZr : ∀ a ∈ Zr, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) :
    zbppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (3 :: (Z ++ (1 :: (A ++ (1 :: (Ur ++ (3 :: (Zr ++ (1 :: (1 :: (D ++ (E)))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (2 :: (List.replicate Z.length 3 ++ (1 :: (A ++ (1 :: (Ur ++ (2 :: (List.replicate Zr.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))))))) := by
  have hV : Valid [bits, bits, Z2, bits, bits, Z2, T3, Z2] [j, s, Z, A, Ur, Zr, D, E] := (Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hA (Valid.cons hUr (Valid.cons hZr (Valid.cons hD (Valid.cons hE (Valid.nil _)))))))))
  exact checkFF (env := [j, s, Z, A, Ur, Zr, D, E]) (E := []) (k := 56) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .sym 1, .blk 6 .id, .blk 7 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 (.const 3), .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 2, .blk 5 (.const 3), .sym 1, .sym 1, .blk 6 .id, .blk 7 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Rejected, `R > 0`, `C = c C' 1 0^k`. -/
theorem rejDecC (j : List Nat) (s : List Nat) (Cp : List Nat) (Z : List Nat) (A : List Nat) (Ur : List Nat) (Zr : List Nat) (D : List Nat) (E : List Nat) (c : Nat) (hj : Bits j) (hs : Bits s) (hCp : Bits Cp) (hZ : ∀ a ∈ Z, a ∈ Z2) (hA : Bits A) (hUr : Bits Ur) (hZr : ∀ a ∈ Zr, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hc : c ∈ bits) :
    zbppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (3 :: (Z ++ (1 :: (A ++ (1 :: (Ur ++ (3 :: (Zr ++ (1 :: (1 :: (D ++ (E)))))))))))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (c :: (Cp ++ (2 :: (List.replicate Z.length 3 ++ (1 :: (A ++ (1 :: (Ur ++ (2 :: (List.replicate Zr.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))))))))) := by
  have hV : Valid [bits, bits, bits, Z2, bits, bits, Z2, T3, Z2] [j, s, Cp, Z, A, Ur, Zr, D, E] := (Valid.cons hj (Valid.cons hs (Valid.cons hCp (Valid.cons hZ (Valid.cons hA (Valid.cons hUr (Valid.cons hZr (Valid.cons hD (Valid.cons hE (Valid.nil _))))))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [j, s, Cp, Z, A, Ur, Zr, D, E]) (E := []) (k := 60) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 3, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 2, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 2, .blk 6 (.const 3), .sym 1, .sym 1, .blk 7 .id, .blk 8 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [j, s, Cp, Z, A, Ur, Zr, D, E]) (E := []) (k := 60) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 3, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id, .blk 8 .id])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 2, .blk 3 (.const 3), .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 2, .blk 6 (.const 3), .sym 1, .sym 1, .blk 7 .id, .blk 8 (.const 3)])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Accepted, `A > 0`, `C = 0`: `A -= 1`, then `C` underflows: outside the promise. -/
theorem accOut (j : List Nat) (s : List Nat) (Z : List Nat) (Ul : List Nat) (Za : List Nat) (R : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hUl : Bits Ul) (hZa : ∀ a ∈ Za, a ∈ Z2) (hR : Bits R) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (2 :: (Z ++ (1 :: (Ul ++ (3 :: (Za ++ (1 :: (R ++ (1 :: (Fu)))))))))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: (s)))) []) := by
  have hV : Valid [bits, bits, Z2, bits, Z2, bits, NB] [j, s, Z, Ul, Za, R, Fu] := (Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hUl (Valid.cons hZa (Valid.cons hR (Valid.cons hFu (Valid.nil _))))))))
  exact checkFT (env := [j, s, Z, Ul, Za, R, Fu]) (E := []) (k := 40) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .blk 6 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Rejected, `R > 0`, `C = 0`: outside the promise. -/
theorem rejOut (j : List Nat) (s : List Nat) (Z : List Nat) (A : List Nat) (Ur : List Nat) (Zr : List Nat) (Fu : List Nat) (hj : Bits j) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hA : Bits A) (hUr : Bits Ur) (hZr : ∀ a ∈ Zr, a ∈ Z2) (hFu : NoB Fu) :
    zbppLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (2 :: (Z ++ (1 :: (A ++ (1 :: (Ur ++ (3 :: (Zr ++ (1 :: (Fu)))))))))))))))
      (hd Q.SINC (1 :: (j ++ (1 :: (s)))) []) := by
  have hV : Valid [bits, bits, Z2, bits, bits, Z2, NB] [j, s, Z, A, Ur, Zr, Fu] := (Valid.cons hj (Valid.cons hs (Valid.cons hZ (Valid.cons hA (Valid.cons hUr (Valid.cons hZr (Valid.cons hFu (Valid.nil _))))))))
  exact checkFT (env := [j, s, Z, A, Ur, Zr, Fu]) (E := []) (k := 44) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 3, .blk 5 .id, .sym 1, .blk 6 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-! ## Building `C`, `A` and the verifier fuel -/

/-- The block `A` (`n ≥ 2`) is built: fix its second cell, start the block `R`. -/
theorem blkA2 (j : List Nat) (s : List Nat) (C : List Nat) (u : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hu : ∀ a ∈ u, a ∈ T3) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (3 :: (3 :: (u))))))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (3 :: (2 :: (u ++ (3 :: [1])))))))))) := by
  have hV : Valid [bits, bits, T3, T3] [j, s, C, u] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hu (Valid.nil _)))))
  exact checkFF (env := [j, s, C, u]) (E := []) (k := 53) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 3 .id, .sym 3, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The block `A` (`n = 1`) is built. -/
theorem blkA1 (j : List Nat) (s : List Nat) (C : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: [3])))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (3 :: (2 :: [1])))))))) := by
  have hV : Valid [bits, bits, T3] [j, s, C] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.nil _))))
  exact checkFF (env := [j, s, C]) (E := []) (k := 45) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The block `A` (`n = 0`) is built. -/
theorem blkA0 (j : List Nat) (s : List Nat) (C : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ [1]))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (3 :: [1]))))))) := by
  have hV : Valid [bits, bits, T3] [j, s, C] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.nil _))))
  exact checkFF (env := [j, s, C]) (E := []) (k := 41) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The block `R` (`n ≥ 2`) is built: fix its second cell, start the fuel block. -/
theorem blkR2 (j : List Nat) (s : List Nat) (C : List Nat) (A : List Nat) (u : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hA : Bits A) (hu : ∀ a ∈ u, a ∈ T3) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (3 :: (3 :: (u))))))))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (3 :: (2 :: (u ++ (3 :: (1 :: [1]))))))))))))) := by
  have hV : Valid [bits, bits, T3, bits, T3] [j, s, C, A, u] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hA (Valid.cons hu (Valid.nil _))))))
  exact checkFF (env := [j, s, C, A, u]) (E := []) (k := 69) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .sym 3, .blk 4 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .sym 2, .blk 4 .id, .sym 3, .sym 1, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The block `R` (`n = 1`) is built. -/
theorem blkR1 (j : List Nat) (s : List Nat) (C : List Nat) (A : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hA : Bits A) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: [3])))))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (3 :: (2 :: (1 :: [1]))))))))))) := by
  have hV : Valid [bits, bits, T3, bits] [j, s, C, A] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hA (Valid.nil _)))))
  exact checkFF (env := [j, s, C, A]) (E := []) (k := 57) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .sym 2, .sym 1, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The block `R` (`n = 0`) is built. -/
theorem blkR0 (j : List Nat) (s : List Nat) (C : List Nat) (A : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hA : Bits A) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (A ++ [1]))))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (3 :: (1 :: [1])))))))))) := by
  have hV : Valid [bits, bits, T3, bits] [j, s, C, A] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hA (Valid.nil _)))))
  exact checkFF (env := [j, s, C, A]) (E := []) (k := 51) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
      (ls' := [.sym 1, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .sym 1, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Fuel block done: write `H`, go to the guest source `C`. -/
theorem blkVerBPP (j : List Nat) (s : List Nat) (C : List Nat) (A : List Nat) (R : List Nat) (hj : Bits j) (hs : Bits s) (hC : ∀ a ∈ C, a ∈ T3) (hA : Bits A) (hR : Bits R) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (3 :: (C ++ (1 :: (A ++ (1 :: (R ++ (1 :: (1 :: (List.replicate s.length 3)))))))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ [1]))))) (3 :: (C ++ (1 :: (A ++ (1 :: (R ++ (1 :: (1 :: (List.replicate s.length 3 ++ [3])))))))))) := by
  have hV : Valid [bits, bits, T3, bits, bits] [j, s, C, A, R] := (Valid.cons hj (Valid.cons hs (Valid.cons hC (Valid.cons hA (Valid.cons hR (Valid.nil _))))))
  exact checkFF (env := [j, s, C, A, R]) (E := []) (k := 55) hV trivial
      (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .sym 1, .blk 1 (.const 3)])
      (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .sym 1, .blk 1 (.const 3), .sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- `BLK` for `A`: starts like the `GRB` step, from `BD6` on the blank after `C`. -/
theorem blkStart2 (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) :
    zbppLogic.Reach (hdR Q.BD6 (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: T)))))) [])
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
    zbppLogic.Reach1 (L0.den [j, s]) (P1pre.den [j, s]) := by
  have hA : zbppLogic.Reach1 (L0.den [j, s]) (F1.den [j, [], s]) :=
    check1 (sets := [bits, bits]) (E := []) (ρ := [[0], [], [1]]) (k := 9)
      (Valid.cons hj (Valid.cons hs (Valid.nil _))) trivial (by decide +kernel)
  have hL : zbppLogic.Reach (F1.den [j, [], s]) (F1.den [j, [] ++ s, []]) := by
    refine LTM.Reach.fold (S := bits) (fun u v => F1.den [j, u, v]) ?_ s [] (nil_valid _) hs
    intro u b v hb hu hv
    have hval : Valid [bits, bits, bits] [j, u, v] :=
      Valid.cons hj (Valid.cons hu (Valid.cons hv (Valid.nil _)))
    rcases mem_bits hb with rfl | rfl
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
    · exact body (E := []) (i := 2) (i' := 1) (k := 9) hval trivial
        (by show 2 < 3; decide) (by show 1 < 3; decide) (by decide +kernel)
  have hB : zbppLogic.Reach (F1.den [j, s, []]) (P1pre.den [j, s]) :=
    check (sets := [bits, bits, bits]) (E := [2]) (ρ := [[0], [1]]) (k := 18)
      (Valid.cons hj (Valid.cons hs (Valid.cons (nil_valid _) (Valid.nil _)))) ⟨rfl, trivial⟩
      (by decide +kernel)
  exact (hA.trans hL).trans hB

theorem P1pre_hdR (j s : List Nat) :
    P1pre.den [j, s] = hdR Q.BD6 (1 :: (j ++ 1 :: (s ++ 1 :: (List.replicate s.length 3 ++ [3])))) [] :=
  den_tapeR (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 1 (.const 3), .sym 3])
    (by osimp) (by osimp)


/-- Threshold counters: `⌈3N/4⌉ - 1` with `N = 2^(n+1)`, least significant bit first. -/
def thrL : Nat → List Bool
  | 0 => [true]
  | k + 1 => List.replicate k true ++ [false, true]

/-- The same counter on the tape (most significant bit first). -/
def thrW : Nat → List Nat
  | 0 => [3]
  | k + 1 => 3 :: 2 :: List.replicate k 3

theorem bitsOf_rep_false (n : Nat) : bitsOf (List.replicate n false) = List.replicate n 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, bitsOf] using ih

theorem bitsOf_rep_true (n : Nat) : bitsOf (List.replicate n true) = List.replicate n 3 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, bitsOf] using ih

theorem bitsOf_thrL (n : Nat) : bitsOf (thrL n).reverse = thrW n := by
  cases n with
  | zero => rfl
  | succ k => simp [thrL, thrW, bitsOf, List.reverse_append, List.reverse_replicate, bitsOf_rep_true]

theorem length_thrL (n : Nat) : (thrL n).length = n + 1 := by
  cases n <;> simp [thrL]

theorem thrW_bits (n : Nat) : Bits (thrW n) := by
  rw [← bitsOf_thrL]; exact Bits.ofB _

/-- The block `A` is built (any `n`). -/
theorem blkAany (j s : List Nat) (hj : Bits j) (hs : Bits s) :
    zbppLogic.Reach (hdR Q.COPY (1 :: (j ++ 1 :: s)) (1 :: ((List.replicate s.length 3 ++ [3]) ++ 1 :: List.replicate s.length 3)))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ 1 :: (3 :: (List.replicate s.length 3 ++ 1 :: (thrW s.length ++ [1]))))) := by
  rcases hn : s.length with _ | _ | m
  · have h := blkA0 j s [] hj hs (fun a ha => by cases ha)
    exact h.of_eq (by simp) (by simp [thrW])
  · have h := blkA1 j s [3] hj hs (fun a ha => by simp at ha; simp [T3, ha])
    exact h.of_eq (by simp) (by simp [thrW])
  · have h := blkA2 j s (List.replicate (m + 2) 3) (List.replicate m 3) hj hs (rep_t3 _) (rep_t3 _)
    refine h.of_eq ?_ ?_
    · simp [List.replicate_succ, rep_cons_comm, rep_snoc_eq]
    · simp [thrW, List.replicate_succ, rep_cons_comm, rep_snoc_eq]

/-- The block `R` is built (any `n`). -/
theorem blkRany (j s : List Nat) (hj : Bits j) (hs : Bits s) :
    zbppLogic.Reach
      (hdR Q.COPY (1 :: (j ++ 1 :: s)) (1 :: (3 :: (List.replicate s.length 3 ++ 1 :: (thrW s.length ++ 1 :: List.replicate s.length 3)))))
      (hdR Q.COPY (1 :: (j ++ [1])) (s ++ 1 :: (3 :: (List.replicate s.length 3 ++ 1 :: (thrW s.length ++ 1 :: (thrW s.length ++ [1, 1])))))) := by
  rcases hn : s.length with _ | _ | m
  · have h := blkR0 j s [] (thrW 0) hj hs (fun a ha => by cases ha) (thrW_bits 0)
    exact h.of_eq (by simp [thrW]) (by simp [thrW])
  · have h := blkR1 j s [3] (thrW 1) hj hs (fun a ha => by simp at ha; simp [T3, ha]) (thrW_bits 1)
    exact h.of_eq (by simp [thrW]) (by simp [thrW])
  · have h := blkR2 j s (List.replicate (m + 2) 3) (thrW (m + 2)) (List.replicate m 3) hj hs (rep_t3 _) (thrW_bits _) (rep_t3 _)
    refine h.of_eq ?_ ?_
    · simp [thrW, List.replicate_succ, rep_cons_comm, rep_snoc_eq]
    · simp [thrW, List.replicate_succ, rep_cons_comm, rep_snoc_eq]

/-- The verifier run starts: guest source `C` (counter `cl`), then `M_3`, the counters `A` and `R`,
and the fuel. -/
def GCvBPP (j : List Nat) (Sb cl a r : List Bool) : ZC :=
  hdR Q.GC (1 :: (1 :: (j ++ [1]) ++ (bitsOf Sb ++ [1])))
    (bitsOf cl.reverse ++ 1 :: (bitsOf a.reverse ++ 1 :: (bitsOf r.reverse ++ 1 :: blkW Sb.length (Sb.length + 1))))

theorem vStartBPP (J S : Nat) :
    zbppLogic.Reach1 (lay J S)
      (GCvBPP (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)
        (thrL (str S).length) (thrL (str S).length)) := by
  have hj := Bits.ofB (str J)
  have hs := Bits.ofB (str S)
  have h1 := phase1PP _ _ hj hs
  rw [← lay_den, P1pre_hdR] at h1
  have hT0 : ∀ a ∈ List.replicate (bitsOf (str S)).length 3 ++ [3], a ∈ O13 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rw [List.eq_of_mem_replicate h]; simp [O13]
    · simp at h; rw [h]; simp [O13]
  have hP : NoB (1 :: (bitsOf (str J) ++ [1])) := NoB.cons one_nb (hj.noB.app (NoB.cons one_nb NoB.nil))
  have h2 := blkStart2 [] (bitsOf (str J)) (bitsOf (str S)) _ Bits.nil hj hs hT0
  have h3 := copyLoop (1 :: (bitsOf (str J) ++ [1])) (List.replicate (bitsOf (str S)).length 3 ++ [3])
    hP (o13_nb hT0) (bitsOf (str S)) [] Bits.nil hs
  have h4 := blkAany (bitsOf (str J)) (bitsOf (str S)) hj hs
  have hW1 : NoB (thrW (bitsOf (str S)).length) := (thrW_bits _).noB
  have hT1 : NoB (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: thrW (bitsOf (str S)).length)) :=
    NoB.cons (by simp [NB]) ((t3_noB (rep_t3 _)).app (NoB.cons one_nb hW1))
  have h5 := copyLoop (1 :: (bitsOf (str J) ++ [1])) _ hP hT1 (bitsOf (str S)) [] Bits.nil hs
  have h6 := blkRany (bitsOf (str J)) (bitsOf (str S)) hj hs
  have hT2 : NoB (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++
      1 :: (thrW (bitsOf (str S)).length ++ [1])))) :=
    NoB.cons (by simp [NB]) ((t3_noB (rep_t3 _)).app (NoB.cons one_nb (hW1.app (NoB.cons one_nb
      (hW1.app (NoB.cons one_nb NoB.nil))))))
  have h7 := copyLoop (1 :: (bitsOf (str J) ++ [1])) _ hP hT2 (bitsOf (str S)) [] Bits.nil hs
  have h8 := blkVerBPP (bitsOf (str J)) (bitsOf (str S)) (List.replicate (bitsOf (str S)).length 3)
    (thrW (bitsOf (str S)).length) (thrW (bitsOf (str S)).length) hj hs (rep_t3 _) (thrW_bits _) (thrW_bits _)
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
  have a4 := h5.of_eq
    (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ [1]))
      (bitsOf (str S) ++ 1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++ [1])))))
    (c4 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: List.replicate (bitsOf (str S)).length 3))))) (by simp) (by simp)
  have a6 := h7.of_eq
    (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ [1]))
      (bitsOf (str S) ++ 1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: (thrW (bitsOf (str S)).length ++ [1, 1]))))))
    (c4 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: 1 :: List.replicate (bitsOf (str S)).length 3))))))
    (by simp) (by simp)
  have a8 := h8.of_eq (c3 := hdR Q.COPY (1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S)))
      (1 :: (3 :: (List.replicate (bitsOf (str S)).length 3 ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: (thrW (bitsOf (str S)).length ++ 1 :: 1 :: List.replicate (bitsOf (str S)).length 3))))))
    (c4 := GCvBPP (bitsOf (str J)) (str S) (List.replicate ((str S).length + 1) true)
        (thrL (str S).length) (thrL (str S).length)) (by simp) (by
      unfold GCvBPP
      simp only [bitsOf_thrL]
      simp [bitsOf, blkW, List.replicate_succ, rep_cons_comm, List.reverse_replicate])
  exact h1.trans (a1.trans (a2.trans (h4.trans (a4.trans (h6.trans (a6.trans a8))))))

/-! ## One verifier pass -/

/-- The run of the verifier from `GCvBPP`: `A` and `R` are just more of the work area. -/
theorem runBPP (j : List Nat) (hj : Bits j) (Sb cl al rl : List Bool) :
    ∃ d, d ≤ Sb.length + 1 ∧
      zbppLogic.Reach (GCvBPP j Sb cl al rl)
        (hdR (dpOf (bn (run Sb cl.reverse (Sb.length + 1)))) [1]
          (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: (bitsOf al.reverse ++
            1 :: (bitsOf rl.reverse ++ 1 :: FWr Sb.length [d])))))) := by
  have hW : NoB (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: (bitsOf al.reverse ++
      1 :: bitsOf rl.reverse)))) :=
    hj.noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb ((Bits.ofB _).noB.app
      (NoB.cons one_nb ((Bits.ofB _).noB.app (NoB.cons one_nb (Bits.ofB _).noB)))))))
  have hR : Sym4 (bitsOf al.reverse ++ 1 :: (bitsOf rl.reverse ++ 1 :: blkW Sb.length (Sb.length + 1))) :=
    (Bits.ofB _).sym4.app (Sym4.cons (by simp [ALL]) ((Bits.ofB _).sym4.app
      (Sym4.cons (by simp [ALL]) (blkW_noB _ _).sym4)))
  obtain ⟨ds', hd', hl', h⟩ := runFrom Sb.length (j ++ [1]) (1 :: j) Sb cl.reverse
    (bitsOf al.reverse ++ 1 :: (bitsOf rl.reverse ++ 1 :: blkW Sb.length (Sb.length + 1)))
    (j ++ 1 :: (bitsOf Sb ++ 1 :: (bitsOf cl.reverse ++ 1 :: (bitsOf al.reverse ++ 1 :: bitsOf rl.reverse))))
    [Sb.length + 1]
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
  unfold GCvBPP
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

theorem length_decA : ∀ al : List Bool, (decA al).length = al.length
  | [] => rfl
  | false :: l => by simp [decA, length_decA l]
  | true :: l => rfl

theorem bitsOf_rev_pos (k : Nat) (r : List Bool) :
    bitsOf (List.replicate k false ++ true :: r).reverse = bitsOf r.reverse ++ 3 :: List.replicate k 2 := by
  simp [bitsOf, List.reverse_append, List.reverse_replicate, List.map_append, List.map_reverse,
    bitsOf_rep_false]

theorem bitsOf_rev_dec (k : Nat) (r : List Bool) :
    bitsOf (List.replicate k true ++ false :: r).reverse = bitsOf r.reverse ++ 2 :: List.replicate k 3 := by
  simp [bitsOf, List.reverse_append, List.reverse_replicate, List.map_append, List.map_reverse]

theorem bitsOf_rev_zero (k : Nat) : bitsOf (List.replicate k false).reverse = List.replicate k 2 := by
  simp [bitsOf_rep_false, List.reverse_replicate]

theorem FWr_one (n d : Nat) : FWr n [d] = 1 :: (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) := by
  simp [FWr, blkW]

/-- Outside the promise: the machine is about to increment `s`. -/
def outS (j : List Nat) (Sb : List Bool) : ZC := hd Q.SINC (1 :: (j ++ 1 :: bitsOf Sb)) []

/-- One verifier pass of the promise-BPP machine. -/
theorem vStepBPP (j : List Nat) (hj : Bits j) (Sb cl al rl : List Bool) (hcl : cl.length = Sb.length + 1) :
    (run Sb cl.reverse (Sb.length + 1) = true → ∀ k, al = List.replicate k false →
      zbppLogic.Reach (GCvBPP j Sb cl al rl) (TR j Sb true)) ∧
    (run Sb cl.reverse (Sb.length + 1) = false → ∀ k, rl = List.replicate k false →
      zbppLogic.Reach (GCvBPP j Sb cl al rl) (TR j Sb false)) ∧
    (run Sb cl.reverse (Sb.length + 1) = true → ∀ k r, al = List.replicate k false ++ true :: r →
      cl = List.replicate (Sb.length + 1) false → zbppLogic.Reach (GCvBPP j Sb cl al rl) (outS j Sb)) ∧
    (run Sb cl.reverse (Sb.length + 1) = false → ∀ k r, rl = List.replicate k false ++ true :: r →
      cl = List.replicate (Sb.length + 1) false → zbppLogic.Reach (GCvBPP j Sb cl al rl) (outS j Sb)) ∧
    (run Sb cl.reverse (Sb.length + 1) = true → ∀ k0 r0, al = List.replicate k0 false ++ true :: r0 →
      ∀ k r, cl = List.replicate k false ++ true :: r →
      zbppLogic.Reach (GCvBPP j Sb cl al rl) (GCvBPP j Sb (List.replicate k true ++ false :: r) (decA al) rl)) ∧
    (run Sb cl.reverse (Sb.length + 1) = false → ∀ k0 r0, rl = List.replicate k0 false ++ true :: r0 →
      ∀ k r, cl = List.replicate k false ++ true :: r →
      zbppLogic.Reach (GCvBPP j Sb cl al rl) (GCvBPP j Sb (List.replicate k true ++ false :: r) al (decA rl))) := by
  obtain ⟨d, hdd, h⟩ := runBPP j hj Sb cl al rl
  have hF := FWr_one Sb.length d
  have hne : cl.reverse ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [hcl] at this
  have hDE : List.replicate d 3 ++ List.replicate (Sb.length + 1 - d) 3 = List.replicate (Sb.length + 1) 3 := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  have hBl : blkW Sb.length (Sb.length + 1) = 1 :: List.replicate (Sb.length + 1) 3 := by
    simp [blkW]
  have hb : Bits (bitsOf Sb) := Bits.ofB _
  have hAl : Bits (bitsOf al.reverse) := Bits.ofB _
  have hRl : Bits (bitsOf rl.reverse) := Bits.ofB _
  refine ⟨fun ho k hk => ?_, fun ho k hk => ?_, fun ho k r hk hz => ?_, fun ho k r hk hz => ?_,
    fun ho k0 r0 hal k r hc => ?_, fun ho k0 r0 hrl k r hc => ?_⟩
  · -- accept, `A = 0`
    rw [ho] at h
    have hAr : bitsOf al.reverse = List.replicate k 2 := by rw [hk]; exact bitsOf_rev_zero k
    cases hr : cl.reverse with
    | nil => exact absurd hr hne
    | cons c rest =>
      cases rest with
      | nil =>
        have hT := accTrue1 j (bitsOf Sb) (List.replicate k 2) (bitsOf rl.reverse) (FWr Sb.length [d]) (bn c)
          hj hb (rep_z2 k) hRl (FWr_noB _ _) (bn_bits c)
        refine h.trans (hT.of_eq ?_ (by simp [TR, tflag]))
        rw [hr, hAr]
        simp [dpOf, bn, bitsOf]
      | cons y Cq =>
        have hT := accTrue2 j (bitsOf Sb) (bitsOf Cq) (List.replicate k 2) (bitsOf rl.reverse)
          (FWr Sb.length [d]) (bn c) (bn y) hj hb (Bits.ofB _) (rep_z2 k) hRl (FWr_noB _ _) (bn_bits c) (bn_bits y)
        refine h.trans (hT.of_eq ?_ (by simp [TR, tflag]))
        rw [hr, hAr]
        simp [dpOf, bn, bitsOf]
  · -- reject, `R = 0`
    rw [ho] at h
    have hRr : bitsOf rl.reverse = List.replicate k 2 := by rw [hk]; exact bitsOf_rev_zero k
    cases hr : cl.reverse with
    | nil => exact absurd hr hne
    | cons c Cp =>
      have hT := rejTrue j (bitsOf Sb) (bitsOf Cp) (bitsOf al.reverse) (List.replicate k 2)
        (FWr Sb.length [d]) (bn c) hj hb (Bits.ofB _) hAl (rep_z2 k) (FWr_noB _ _) (bn_bits c)
      refine h.trans (hT.of_eq ?_ (by simp [TR, tflag]))
      rw [hr, hRr]
      simp [dpOf, bn, bitsOf]
  · -- accept, `A > 0`, `C = 0`
    rw [ho] at h
    have hAr : bitsOf al.reverse = bitsOf r.reverse ++ 3 :: List.replicate k 2 := by
      rw [hk]; exact bitsOf_rev_pos k r
    have hCr : bitsOf cl.reverse = 2 :: List.replicate Sb.length 2 := by
      rw [hz, List.reverse_replicate, List.replicate_succ]
      simp [bitsOf, bitsOf_rep_false]
    have hT := accOut j (bitsOf Sb) (List.replicate Sb.length 2) (bitsOf r.reverse) (List.replicate k 2)
      (bitsOf rl.reverse) (FWr Sb.length [d]) hj hb (rep_z2 _) (Bits.ofB _) (rep_z2 _) hRl (FWr_noB _ _)
    refine h.trans (hT.of_eq ?_ (by simp [outS]))
    rw [hCr, hAr]
    simp [dpOf, bn]
  · -- reject, `R > 0`, `C = 0`
    rw [ho] at h
    have hRr : bitsOf rl.reverse = bitsOf r.reverse ++ 3 :: List.replicate k 2 := by
      rw [hk]; exact bitsOf_rev_pos k r
    have hCr : bitsOf cl.reverse = 2 :: List.replicate Sb.length 2 := by
      rw [hz, List.reverse_replicate, List.replicate_succ]
      simp [bitsOf, bitsOf_rep_false]
    have hT := rejOut j (bitsOf Sb) (List.replicate Sb.length 2) (bitsOf al.reverse) (bitsOf r.reverse)
      (List.replicate k 2) (FWr Sb.length [d]) hj hb (rep_z2 _) hAl (Bits.ofB _) (rep_z2 _) (FWr_noB _ _)
    refine h.trans (hT.of_eq ?_ (by simp [outS]))
    rw [hCr, hRr]
    simp [dpOf, bn]
  · -- accept, `A > 0`, `C > 0`
    rw [ho] at h
    have hcr : cl.reverse = r.reverse ++ true :: List.replicate k false := by rw [hc]; simp
    have hAr : bitsOf al.reverse = bitsOf r0.reverse ++ 3 :: List.replicate k0 2 := by
      rw [hal]; exact bitsOf_rev_pos k0 r0
    have hAr' : bitsOf (decA al).reverse = bitsOf r0.reverse ++ 2 :: List.replicate k0 3 := by
      rw [hal, decA_spec]; exact bitsOf_rev_dec k0 r0
    have hcr' : (List.replicate k true ++ false :: r).reverse = r.reverse ++ false :: List.replicate k true := by
      simp
    cases hr : r.reverse with
    | nil =>
      have hE := accDecE j (bitsOf Sb) (List.replicate k 2) (bitsOf r0.reverse) (List.replicate k0 2)
        (bitsOf rl.reverse) (List.replicate d 3) (List.replicate (Sb.length + 1 - d) 2) hj hb (rep_z2 _)
        (Bits.ofB _) (rep_z2 _) hRl (rep_t3 _) (rep_z2 _)
      refine h.trans (hE.of_eq ?_ ?_)
      · rw [hF, hcr, hr, hAr]
        simp [dpOf, bn, bitsOf]
      · unfold GCvBPP
        rw [hcr', hr, hAr']
        simp only [List.length_replicate]
        rw [hDE, hBl]
        simp [bitsOf]
    | cons x rr =>
      have hE := accDecC j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (bitsOf r0.reverse)
        (List.replicate k0 2) (bitsOf rl.reverse) (List.replicate d 3) (List.replicate (Sb.length + 1 - d) 2)
        (bn x) hj hb (Bits.ofB _) (rep_z2 _) (Bits.ofB _) (rep_z2 _) hRl (rep_t3 _) (rep_z2 _) (bn_bits x)
      refine h.trans (hE.of_eq ?_ ?_)
      · rw [hF, hcr, hr, hAr]
        simp [dpOf, bn, bitsOf]
      · unfold GCvBPP
        rw [hcr', hr, hAr']
        simp only [List.length_replicate]
        rw [hDE, hBl]
        simp [bitsOf, bn]
  · -- reject, `R > 0`, `C > 0`
    rw [ho] at h
    have hcr : cl.reverse = r.reverse ++ true :: List.replicate k false := by rw [hc]; simp
    have hRr : bitsOf rl.reverse = bitsOf r0.reverse ++ 3 :: List.replicate k0 2 := by
      rw [hrl]; exact bitsOf_rev_pos k0 r0
    have hRr' : bitsOf (decA rl).reverse = bitsOf r0.reverse ++ 2 :: List.replicate k0 3 := by
      rw [hrl, decA_spec]; exact bitsOf_rev_dec k0 r0
    have hcr' : (List.replicate k true ++ false :: r).reverse = r.reverse ++ false :: List.replicate k true := by
      simp
    cases hr : r.reverse with
    | nil =>
      have hE := rejDecE j (bitsOf Sb) (List.replicate k 2) (bitsOf al.reverse) (bitsOf r0.reverse)
        (List.replicate k0 2) (List.replicate d 3) (List.replicate (Sb.length + 1 - d) 2) hj hb (rep_z2 _)
        hAl (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _)
      refine h.trans (hE.of_eq ?_ ?_)
      · rw [hF, hcr, hr, hRr]
        simp [dpOf, bn, bitsOf]
      · unfold GCvBPP
        rw [hcr', hr, hRr']
        simp only [List.length_replicate]
        rw [hDE, hBl]
        simp [bitsOf]
    | cons x rr =>
      have hE := rejDecC j (bitsOf Sb) (bitsOf rr) (List.replicate k 2) (bitsOf al.reverse)
        (bitsOf r0.reverse) (List.replicate k0 2) (List.replicate d 3) (List.replicate (Sb.length + 1 - d) 2)
        (bn x) hj hb (Bits.ofB _) (rep_z2 _) hAl (Bits.ofB _) (rep_z2 _) (rep_t3 _) (rep_z2 _) (bn_bits x)
      refine h.trans (hE.of_eq ?_ ?_)
      · rw [hF, hcr, hr, hRr]
        simp [dpOf, bn, bitsOf]
      · unfold GCvBPP
        rw [hcr', hr, hRr']
        simp only [List.length_replicate]
        rw [hDE, hBl]
        simp [bitsOf, bn]

end ZP.BPP
