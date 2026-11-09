module

public import ZP.ConpRun
public import ZP.DefsConp

@[expose] public section

/-!
# Z_coNP: outer-loop segments for `zconpLogic` (generated with `scripts/symexec.py`)

The tape to the right of the fuel is `0 :: Dw` (the separator and the choice string); the segments take an
arbitrary tail `Y` that they never read.
-/

namespace ZP.Conp

open ZP

def O13 : List Nat := [1, 3]
def T3 : List Nat := [3]
def Z2 : List Nat := [2]

macro "osimp" : tactic =>
  `(tactic| simp [dR, Item.den, List.getD, map_id_app, map_const_len, Fn.app])

/-- `BLK` starts: `M` at the end, back to the first bit of `s`. -/
theorem blkStartY (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (Y : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : NoB T) (hY : Sym4 Y) :
    zconpLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: (T))))))) (0 :: (0 :: (List.replicate s.length 0 ++ (Y)))))
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ ([1])))) (s ++ (1 :: (T ++ (1 :: (0 :: (List.replicate s.length 0 ++ (Y)))))))) := by
  have hV : Valid [bits, bits, bits, NB, ALL] [Jl, Jr, s, T, Y] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.cons hY (Valid.nil _)))))
  exact checkFF (env := [Jl, Jr, s, T, Y]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 0, .sym 0, .blk 2 (.const 0), .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 0, .blk 2 (.const 0), .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One `COPY` round. -/
theorem copyBodyY (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (Y : List Nat) (c : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : NoB T) (hY : Sym4 Y) (hc : c ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (P ++ (u)) (c :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ (0 :: (0 :: (List.replicate v.length 0 ++ (Y)))))))))))
      (hdR Q.COPY (P ++ (u ++ ([c]))) (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ (3 :: (0 :: (List.replicate v.length 0 ++ (Y)))))))))) := by
  have hV : Valid [NB, bits, bits, NB, ALL] [P, u, v, T, Y] := Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hT (Valid.cons hY (Valid.nil _)))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [P, u, v, T, Y]) (E := []) (k := 13) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 0, .sym 0, .blk 2 (.const 0), .blk 4 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3, .sym 0, .blk 2 (.const 0), .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, u, v, T, Y]) (E := []) (k := 13) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 0, .sym 0, .blk 2 (.const 0), .blk 4 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .blk 1 (.const 3), .sym 3, .sym 0, .blk 2 (.const 0), .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier fuel block done: go to the guest source. -/
theorem blkVerY (j : List Nat) (s : List Nat) (Y : List Nat) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zconpLogic.Reach (hdR Q.COPY (1 :: (j ++ (1 :: (s)))) (1 :: (1 :: (1 :: (List.replicate s.length 3 ++ (0 :: (Y)))))))
      (hdR Q.GC (1 :: (1 :: (j ++ (1 :: (s ++ ([1])))))) (1 :: (1 :: (List.replicate s.length 3 ++ (3 :: (Y)))))) := by
  have hV : Valid [bits, bits, ALL] [j, s, Y] := Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _)))
  exact checkFF (env := [j, s, Y]) (E := []) (k := 19) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 1, .sym 1, .blk 1 (.const 3), .sym 0, .blk 2 .id])
    (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.sym 1, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- Decider fuel block done, the walker steps right. -/
theorem blkDecStepYe (Jl : List Nat) (Jr : List Nat) (s : List Nat) (Y : List Nat) (c : Nat) (t : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hY : Sym4 Y) (hc : c ∈ bits) (ht : t ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (c :: (Jr ++ (1 :: (s)))))) (1 :: (t :: (1 :: (1 :: (List.replicate s.length 3 ++ (0 :: (Y))))))))
      (hdR Q.GRB (Jl ++ (c :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (t :: (1 :: (1 :: (List.replicate s.length 3 ++ ([3])))))))))))) (Y)) := by
  have hV : Valid [bits, bits, bits, ALL] [Jl, Jr, s, Y] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hY (Valid.nil _))))
  rcases mem_bits hc with rfl | rfl <;> rcases mem_bits ht with rfl | rfl
  · exact checkFF (env := [Jl, Jr, s, Y]) (E := []) (k := 32) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 2, .sym 1, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 1, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y]) (E := []) (k := 32) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .sym 1, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y]) (E := []) (k := 32) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 2, .sym 1, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 1, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y]) (E := []) (k := 32) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .sym 1, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider fuel block done, the walker steps right. -/
theorem blkDecStepYn (Jl : List Nat) (Jr : List Nat) (s : List Nat) (Y : List Nat) (Bp : List Nat) (c : Nat) (t : Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hY : Sym4 Y) (hBp : ∀ a ∈ Bp, a ∈ O13) (hc : c ∈ bits) (ht : t ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (c :: (Jr ++ (1 :: (s)))))) (1 :: (t :: (1 :: (Bp ++ (3 :: (1 :: (List.replicate s.length 3 ++ (0 :: (Y))))))))))
      (hdR Q.GRB (Jl ++ (c :: (1 :: (Jr ++ (1 :: (s ++ (1 :: (t :: (1 :: (Bp ++ (3 :: (1 :: (List.replicate s.length 3 ++ ([3])))))))))))))) (Y)) := by
  have hV : Valid [bits, bits, bits, ALL, O13] [Jl, Jr, s, Y, Bp] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hY (Valid.cons hBp (Valid.nil _)))))
  rcases mem_bits hc with rfl | rfl <;> rcases mem_bits ht with rfl | rfl
  · exact checkFF (env := [Jl, Jr, s, Y, Bp]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 2, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y, Bp]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y, Bp]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 2, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Jl, Jr, s, Y, Bp]) (E := []) (k := 38) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 0, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1, .blk 4 .id, .sym 3, .sym 1, .blk 2 (.const 3), .sym 3]) (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Last decider fuel block: the walker goes home. -/
theorem blkDecLastYe (Jl : List Nat) (s : List Nat) (Y : List Nat) (t : Nat) (hJl : Bits Jl) (hs : Bits s) (hY : Sym4 Y) (ht : t ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: (s)))) (1 :: (t :: (1 :: (1 :: (List.replicate s.length 3 ++ (0 :: (Y))))))))
      (hd Q.WB1 (Jl ++ ([1])) (1 :: (s ++ (1 :: (t :: (1 :: (1 :: (List.replicate s.length 3 ++ (3 :: (Y)))))))))) := by
  have hV : Valid [bits, bits, ALL] [Jl, s, Y] := Valid.cons hJl (Valid.cons hs (Valid.cons hY (Valid.nil _)))
  rcases mem_bits ht with rfl | rfl
  · exact checkFT (env := [Jl, s, Y]) (E := []) (k := 19) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 2, .sym 1, .sym 1, .blk 1 (.const 3), .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Jl, s, Y]) (E := []) (k := 19) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .sym 1, .sym 1, .blk 1 (.const 3), .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Last decider fuel block: the walker goes home. -/
theorem blkDecLastYn (Jl : List Nat) (s : List Nat) (Y : List Nat) (Bp : List Nat) (t : Nat) (hJl : Bits Jl) (hs : Bits s) (hY : Sym4 Y) (hBp : ∀ a ∈ Bp, a ∈ O13) (ht : t ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (Jl ++ (1 :: (1 :: (s)))) (1 :: (t :: (1 :: (Bp ++ (3 :: (1 :: (List.replicate s.length 3 ++ (0 :: (Y))))))))))
      (hd Q.WB1 (Jl ++ ([1])) (1 :: (s ++ (1 :: (t :: (1 :: (Bp ++ (3 :: (1 :: (List.replicate s.length 3 ++ (3 :: (Y)))))))))))) := by
  have hV : Valid [bits, bits, ALL, O13] [Jl, s, Y, Bp] := Valid.cons hJl (Valid.cons hs (Valid.cons hY (Valid.cons hBp (Valid.nil _))))
  rcases mem_bits ht with rfl | rfl
  · exact checkFT (env := [Jl, s, Y, Bp]) (E := []) (k := 23) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 2, .sym 1, .blk 3 .id, .sym 3, .sym 1, .blk 1 (.const 3), .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 3 .id, .sym 3, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [Jl, s, Y, Bp]) (E := []) (k := 23) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id]) (rs := [.sym 1, .sym 3, .sym 1, .blk 3 .id, .sym 3, .sym 1, .blk 1 (.const 3), .sym 0, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 3 .id, .sym 3, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Code copy: one bit into `Q` (skipped trailing ones `S` stay). -/
theorem qcBodyS (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (S : List Nat) (c : Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hS : ∀ a ∈ S, a ∈ T3) (hc : c ∈ bits) :
    zconpLogic.Reach (hd Q.QC (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ ([c]))))))) (Qc ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))
      (hd Q.QC (c :: (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v))))))) (c :: (Qc ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))) := by
  have hV : Valid [bits, bits, NB, bits, bits, ALL, T3] [Qc, Xr, V, v, X, Rest, S] := Valid.cons hQc (Valid.cons hXr (Valid.cons hV (Valid.cons hv (Valid.cons hX (Valid.cons hRest (Valid.cons hS (Valid.nil _)))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkTT (env := [Qc, Xr, V, v, X, Rest, S]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id, .sym 2]) (rs := [.blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 2, .blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Qc, Xr, V, v, X, Rest, S]) (E := []) (k := 15) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id, .sym 3]) (rs := [.blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (ls' := [.sym 3, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 3, .blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The last `0` of the code. -/
theorem qsBody0 (Qc : List Nat) (Xr : List Nat) (V : List Nat) (v : List Nat) (X : List Nat) (Rest : List Nat) (S : List Nat) (hQc : Bits Qc) (hXr : Bits Xr) (hV : NoB V) (hv : Bits v) (hX : Bits X) (hRest : Sym4 Rest) (hS : ∀ a ∈ S, a ∈ T3) :
    zconpLogic.Reach (hd QConp.QS (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v ++ ([2]))))))) (Qc ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))
      (hd Q.QC (2 :: (Qc ++ (1 :: (Xr ++ (1 :: (V ++ (v))))))) (2 :: (Qc ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))) := by
  have hV : Valid [bits, bits, NB, bits, bits, ALL, T3] [Qc, Xr, V, v, X, Rest, S] := Valid.cons hQc (Valid.cons hXr (Valid.cons hV (Valid.cons hv (Valid.cons hX (Valid.cons hRest (Valid.cons hS (Valid.nil _)))))))
  exact checkTT (env := [Qc, Xr, V, v, X, Rest, S]) (E := []) (k := 15) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id, .sym 2]) (rs := [.blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
    (ls' := [.sym 2, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .blk 3 .id]) (rs' := [.sym 2, .blk 0 .id, .blk 6 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Code copied: the sentinel `0`, one rotation. -/
theorem qsEndS (P : List Nat) (Xr : List Nat) (Vq : List Nat) (X : List Nat) (Rest : List Nat) (S : List Nat) (hP : Bits P) (hXr : Bits Xr) (hVq : NoB Vq) (hX : Bits X) (hRest : Sym4 Rest) (hS : ∀ a ∈ S, a ∈ T3) :
    zconpLogic.Reach (hd QConp.QS (P ++ (1 :: (Xr ++ (1 :: (Vq ++ ([1])))))) (P ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))
      (hd Q.TW (2 :: (P)) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL, T3] [P, Xr, Vq, X, Rest, S] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.cons hS (Valid.nil _))))))
  exact checkTT (env := [P, Xr, Vq, X, Rest, S]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .blk 5 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .blk 5 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Code copied: the sentinel `0`, one rotation. -/
theorem qcEndS (P : List Nat) (Xr : List Nat) (Vq : List Nat) (X : List Nat) (Rest : List Nat) (S : List Nat) (hP : Bits P) (hXr : Bits Xr) (hVq : NoB Vq) (hX : Bits X) (hRest : Sym4 Rest) (hS : ∀ a ∈ S, a ∈ T3) :
    zconpLogic.Reach (hd Q.QC (P ++ (1 :: (Xr ++ (1 :: (Vq ++ ([1])))))) (P ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))
      (hd Q.TW (2 :: (P)) (0 :: (Xr ++ (1 :: (Vq ++ (1 :: (P ++ (S ++ (1 :: (X ++ (1 :: (Rest)))))))))))) := by
  have hV : Valid [bits, bits, NB, bits, ALL, T3] [P, Xr, Vq, X, Rest, S] := Valid.cons hP (Valid.cons hXr (Valid.cons hVq (Valid.cons hX (Valid.cons hRest (Valid.cons hS (Valid.nil _))))))
  exact checkTT (env := [P, Xr, Vq, X, Rest, S]) (E := []) (k := 9) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs := [.blk 0 .id, .blk 5 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 0 .id, .blk 5 .id, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Drop a trailing `1` of the code. -/
theorem qsSkip (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.QS (A ++ ([3])) (R))
      (hd QConp.QS (A) (3 :: (R))) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Input copied: the code scan starts. -/
theorem gcEndS (Xr : List Nat) (V : List Nat) (P : List Nat) (X : List Nat) (Rest : List Nat) (hXr : Bits Xr) (hV : NoB V) (hP : Bits P) (hX : Bits X) (hRest : Sym4 Rest) :
    zconpLogic.Reach (hdR Q.GC (Xr ++ (1 :: (V ++ (P ++ (1 :: (X)))))) (1 :: (Rest)))
      (hd QConp.QS (1 :: (Xr ++ (1 :: (V ++ (P))))) (1 :: (X ++ (1 :: (Rest))))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Xr, V, P, X, Rest] := Valid.cons hXr (Valid.cons hV (Valid.cons hP (Valid.cons hX (Valid.cons hRest (Valid.nil _)))))
  exact checkFT (env := [Xr, V, P, X, Rest]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .blk 4 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .blk 2 .id]) (rs' := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EX1` erases a block (to its `M`). -/
theorem exA (L : List Nat) (Bk : List Nat) (R : List Nat) (hL : Sym4 L) (hBk : Bits Bk) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.EX1 (L ++ (1 :: (Bk))) (R))
      (hd QConp.EX2 (L) (List.replicate Bk.length 0 ++ (0 :: (R)))) := by
  have hV : Valid [ALL, bits, ALL] [L, Bk, R] := Valid.cons hL (Valid.cons hBk (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [L, Bk, R]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `ER3` erases a block (to its `M`). -/
theorem erA (L : List Nat) (Bk : List Nat) (R : List Nat) (hL : Sym4 L) (hBk : Bits Bk) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.ER3 (L ++ (1 :: (Bk))) (R))
      (hd QConp.ER4 (L) (List.replicate Bk.length 0 ++ (0 :: (R)))) := by
  have hV : Valid [ALL, bits, ALL] [L, Bk, R] := Valid.cons hL (Valid.cons hBk (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [L, Bk, R]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Next block, from its last bit. -/
theorem exB (L : List Nat) (Bk : List Nat) (R : List Nat) (c : Nat) (hL : Sym4 L) (hBk : Bits Bk) (hR : Sym4 R) (hc : c ∈ bits) :
    zconpLogic.Reach (hd QConp.EX2 (L ++ (1 :: (Bk ++ ([c])))) (R))
      (hd QConp.EX2 (L) (List.replicate Bk.length 0 ++ (0 :: (0 :: (R))))) := by
  have hV : Valid [ALL, bits, ALL] [L, Bk, R] := Valid.cons hL (Valid.cons hBk (Valid.cons hR (Valid.nil _)))
  rcases mem_bits hc with rfl | rfl
  · exact checkTT (env := [L, Bk, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .sym 0, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [L, Bk, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .sym 0, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Next block, from its last bit. -/
theorem erB (L : List Nat) (Bk : List Nat) (R : List Nat) (c : Nat) (hL : Sym4 L) (hBk : Bits Bk) (hR : Sym4 R) (hc : c ∈ bits) :
    zconpLogic.Reach (hd QConp.ER4 (L ++ (1 :: (Bk ++ ([c])))) (R))
      (hd QConp.ER4 (L) (List.replicate Bk.length 0 ++ (0 :: (0 :: (R))))) := by
  have hV : Valid [ALL, bits, ALL] [L, Bk, R] := Valid.cons hL (Valid.cons hBk (Valid.cons hR (Valid.nil _)))
  rcases mem_bits hc with rfl | rfl
  · exact checkTT (env := [L, Bk, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .sym 0, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [L, Bk, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .sym 0, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EX2` at `M_3`. -/
theorem exEnd (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.EX2 (L ++ ([1])) (R))
      (hd QConp.EX3 (L) (1 :: (R))) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `ER4` at `M_3`. -/
theorem erEnd (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.ER4 (L ++ ([1])) (R))
      (hdR Q.GRB (L ++ ([1])) (R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier accepted: truth bit `1`. -/
theorem vAccA (j : List Nat) (s : List Nat) (F : List Nat) (Dw : List Nat) (hj : Bits j) (hs : Bits s) (hF : NoB F) (hDw : NoB Dw) :
    zconpLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (1 :: (F ++ (0 :: (Dw)))))))))
      (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: ([3])))))) (F ++ (0 :: (Dw)))) := by
  have hV : Valid [bits, bits, NB, NB] [j, s, F, Dw] := Valid.cons hj (Valid.cons hs (Valid.cons hF (Valid.cons hDw (Valid.nil _))))
  exact checkFF (env := [j, s, F, Dw]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider accepted, `s ∉ L`: correct. -/
theorem dAcc2A (j : List Nat) (s : List Nat) (F : List Nat) (Dw : List Nat) (hj : Bits j) (hs : Bits s) (hF : NoB F) (hDw : NoB Dw) :
    zconpLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (2 :: (1 :: (F ++ (0 :: (Dw))))))))))
      (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: ([0])))))) (1 :: (F ++ (0 :: (Dw))))) := by
  have hV : Valid [bits, bits, NB, NB] [j, s, F, Dw] := Valid.cons hj (Valid.cons hs (Valid.cons hF (Valid.cons hDw (Valid.nil _))))
  exact checkFF (env := [j, s, F, Dw]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 0]) (rs' := [.sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider accepted, `s ∈ L`: beep. -/
theorem dAcc3 (j : List Nat) (s : List Nat) (F : List Nat) (Dw : List Nat) (hj : Bits j) (hs : Bits s) (hF : NoB F) (hDw : NoB Dw) :
    zconpLogic.Reach (hdR Q.DP11 ([1]) (j ++ (1 :: (s ++ (1 :: (3 :: (1 :: (F ++ (0 :: (Dw))))))))))
      (hdR Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: ([2])))))) (1 :: (F ++ (0 :: (Dw))))) := by
  have hV : Valid [bits, bits, NB, NB] [j, s, F, Dw] := Valid.cons hj (Valid.cons hs (Valid.cons hF (Valid.cons hDw (Valid.nil _))))
  exact checkFF (env := [j, s, F, Dw]) (E := []) (k := 5) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier rejected: to the end of `D`. -/
theorem dp0v (j : List Nat) (s : List Nat) (F : List Nat) (Dw : List Nat) (hj : Bits j) (hs : Bits s) (hF : NoB F) (hDw : NoB Dw) :
    zconpLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (1 :: (F ++ (0 :: (Dw)))))))))
      (hd QConp.BT (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (F ++ (0 :: (Dw))))))))) ([])) := by
  have hV : Valid [bits, bits, NB, NB] [j, s, F, Dw] := Valid.cons hj (Valid.cons hs (Valid.cons hF (Valid.cons hDw (Valid.nil _))))
  exact checkFT (env := [j, s, F, Dw]) (E := []) (k := 9) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider rejected: to the end of `D`. -/
theorem dp0d (j : List Nat) (s : List Nat) (F : List Nat) (Dw : List Nat) (t : Nat) (hj : Bits j) (hs : Bits s) (hF : NoB F) (hDw : NoB Dw) (ht : t ∈ bits) :
    zconpLogic.Reach (hdR Q.DP10 ([1]) (j ++ (1 :: (s ++ (1 :: (t :: (1 :: (F ++ (0 :: (Dw))))))))))
      (hd QConp.BT (1 :: (j ++ (1 :: (s ++ (1 :: (t :: (1 :: (F ++ (0 :: (Dw)))))))))) ([])) := by
  have hV : Valid [bits, bits, NB, NB] [j, s, F, Dw] := Valid.cons hj (Valid.cons hs (Valid.cons hF (Valid.cons hDw (Valid.nil _))))
  rcases mem_bits ht with rfl | rfl
  · exact checkFT (env := [j, s, F, Dw]) (E := []) (k := 10) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [j, s, F, Dw]) (E := []) (k := 10) hV trivial
      (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id])
      (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 1, .blk 2 .id, .sym 0, .blk 3 .id]) (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier exhausted: `t = 0`. -/
theorem vExh (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zconpLogic.Reach (hd QConp.EX3 (1 :: (j ++ (1 :: (s ++ ([1]))))) ([1]))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (2 :: ([1]))))))) ([])) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkTF (env := [j, s]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs := [.sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider exhausted with `t = 1`: correct. -/
theorem dExh3A (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zconpLogic.Reach (hd QConp.EX3 (1 :: (j ++ (1 :: (s ++ (1 :: ([3])))))) ([1]))
      (hdR Q.EAs (1 :: (j ++ (1 :: (s ++ (1 :: ([0])))))) ([1])) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkTF (env := [j, s]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3]) (rs := [.sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 0]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider exhausted with `t = 0`: beep. -/
theorem dExh2 (j : List Nat) (s : List Nat) (hj : Bits j) (hs : Bits s) :
    zconpLogic.Reach (hd QConp.EX3 (1 :: (j ++ (1 :: (s ++ (1 :: ([2])))))) ([1]))
      (hdR Q.BEEP (1 :: (j ++ (1 :: (s ++ (1 :: ([2])))))) ([1])) := by
  have hV : Valid [bits, bits] [j, s] := Valid.cons hj (Valid.cons hs (Valid.nil _))
  exact checkTF (env := [j, s]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs := [.sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EAs` erases a block. -/
theorem eaF (L : List Nat) (F : List Nat) (R : List Nat) (hL : Sym4 L) (hF : NoB F) (hR : Sym4 R) :
    zconpLogic.Reach (hdR Q.EAs (L) (F ++ (R)))
      (hdR Q.EAs (L ++ (List.replicate F.length 0)) (R)) := by
  have hV : Valid [ALL, NB, ALL] [L, F, R] := Valid.cons hL (Valid.cons hF (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [L, F, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 0)]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EAs` at a blank. -/
theorem eaSep (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zconpLogic.Reach (hdR Q.EAs (L) (0 :: (R)))
      (hdR QConp.EAs2 (L ++ ([0])) (R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EAs2` on `M`. -/
theorem ea2M (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zconpLogic.Reach (hdR QConp.EAs2 (L) (1 :: (R)))
      (hdR Q.EAs (L ++ ([0])) (R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [L, R]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
    (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EAs2` on a bit. -/
theorem ea2b (L : List Nat) (R : List Nat) (c : Nat) (hL : Sym4 L) (hR : Sym4 R) (hc : c ∈ bits) :
    zconpLogic.Reach (hdR QConp.EAs2 (L) (c :: (R)))
      (hdR Q.EAs (L ++ ([0])) (R)) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [L, R]) (E := []) (k := 1) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [L, R]) (E := []) (k := 1) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EAs2` at the end. -/
theorem ea2End (L : List Nat) (hL : Sym4 L) :
    zconpLogic.Reach (hdR QConp.EAs2 (L) ([]))
      (hd Q.EBs (L) ([])) := by
  have hV : Valid [ALL] [L] := Valid.cons hL (Valid.nil _)
  exact checkFT (env := [L]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EBs` finds `t = 1`: decider phase. -/
theorem ebs3 (A : List Nat) (K : List Nat) (hA : Sym4 A) (hK : Bits K) :
    zconpLogic.Reach (hd Q.EBs (A ++ (3 :: (List.replicate K.length 0 ++ ([0])))) ([]))
      (hdR Q.GRB (A ++ (3 :: ([1]))) ([])) := by
  have hV : Valid [ALL, bits] [A, K] := Valid.cons hA (Valid.cons hK (Valid.nil _))
  exact checkTF (env := [A, K]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 (.const 0), .sym 0]) (rs := [])
    (ls' := [.blk 0 .id, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EBs` finds `M_2`: `s`++. -/
theorem ebsM (A : List Nat) (K : List Nat) (hA : Sym4 A) (hK : Bits K) :
    zconpLogic.Reach (hd Q.EBs (A ++ (1 :: (List.replicate K.length 0 ++ ([0])))) ([]))
      (hd Q.SINC (A) ([])) := by
  have hV : Valid [ALL, bits] [A, K] := Valid.cons hA (Valid.cons hK (Valid.nil _))
  exact checkTT (env := [A, K]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 (.const 0), .sym 0]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `EBs` finds the beep mark: `J`++. -/
theorem ebs0 (j : List Nat) (s : List Nat) (K : List Nat) (hj : Bits j) (hs : Bits s) (hK : Bits K) :
    zconpLogic.Reach (hd Q.EBs (1 :: (j ++ (1 :: (s ++ (1 :: (2 :: (List.replicate K.length 0 ++ ([0])))))))) ([]))
      (hd Q.JINC (1 :: (j)) ([1])) := by
  have hV : Valid [bits, bits, bits] [j, s, K] := Valid.cons hj (Valid.cons hs (Valid.cons hK (Valid.nil _)))
  exact checkTT (env := [j, s, K]) (E := []) (k := 6) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 2, .blk 2 (.const 0), .sym 0]) (rs := [])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Backtrack: the last `1` of `D` becomes the pointer. -/
theorem btOk (L : List Nat) (A : List Nat) (Z : List Nat) (hL : Sym4 L) (hA : Bits A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd QConp.BT (L ++ (A ++ (3 :: (Z ++ ([1]))))) ([]))
      (hd QConp.RS2 (L ++ (A ++ ([1]))) ([2])) := by
  have hV : Valid [ALL, bits, Z2] [L, A, Z] := Valid.cons hL (Valid.cons hA (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [L, A, Z]) (E := []) (k := 5) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id, .sym 3, .blk 2 .id, .sym 1]) (rs := [])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.sym 2])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` exhausted (only `0`s). -/
theorem btEx1 (L : List Nat) (Z : List Nat) (hL : Sym4 L) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd QConp.BT (L ++ (0 :: (Z ++ ([1])))) ([]))
      (hd QConp.EX1 (L) (0 :: (List.replicate Z.length 0 ++ ([0])))) := by
  have hV : Valid [ALL, Z2] [L, Z] := Valid.cons hL (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [L, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 0, .blk 1 .id, .sym 1]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .blk 1 (.const 0), .sym 0])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` empty: exhausted. -/
theorem btEx0 (L : List Nat) (hL : Sym4 L) :
    zconpLogic.Reach (hd QConp.BT (L ++ ([0])) ([]))
      (hd QConp.EX1 (L) ([0])) := by
  have hV : Valid [ALL] [L] := Valid.cons hL (Valid.nil _)
  exact checkTT (env := [L]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 0]) (rs := [])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The pointer moves one bit to the front. -/
theorem rsStep (L : List Nat) (R : List Nat) (c : Nat) (hL : Sym4 L) (hR : Sym4 R) (hc : c ∈ bits) :
    zconpLogic.Reach (hd QConp.RS2 (L ++ (c :: ([1]))) (R))
      (hd QConp.RS2 (L ++ ([1])) (c :: (R))) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  rcases mem_bits hc with rfl | rfl
  · exact checkTT (env := [L, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 2, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 2, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [L, R]) (E := []) (k := 3) hV trivial
      (ls := [.blk 0 .id, .sym 3, .sym 1]) (rs := [.blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The pointer is at the front: to the fuel. -/
theorem rsEnd (L : List Nat) (R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zconpLogic.Reach (hd QConp.RS2 (L ++ (0 :: ([1]))) (R))
      (hd QConp.ER3 (L) (0 :: (1 :: (R)))) := by
  have hV : Valid [ALL, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [L, R]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 0, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 0, .sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sincE (A : List Nat) (Z : List Nat) (hA : NoB A) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.SINC (A ++ [1]) Z)
      (hdR QConp.W1 (A ++ (1 :: (Z ++ [2]))) []) := by
  have hV : Valid [NB, Z2] [A, Z] := Valid.cons hA (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [A, Z]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [2]))) Z)
      (hdR QConp.W1 (A ++ (1 :: (r ++ (3 :: Z)))) []) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 2) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ [3]))) Z)
      (hd Q.SINC (A ++ (1 :: r)) (2 :: Z)) := by
  have hV : Valid [NB, bits, Z2] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem jincE (Z : List Nat) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.JINC [1] (Z ++ [1]))
      (hdR QConp.W1 (1 :: (Z ++ (2 :: [1]))) []) := by
  have hV : Valid [Z2] [Z] := Valid.cons hZ (Valid.nil _)
  exact checkTF (env := [Z]) (E := []) (k := 4) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 2, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem jinc0 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.JINC (1 :: (r ++ [2])) (Z ++ [1]))
      (hdR QConp.W1 (1 :: (r ++ (3 :: (Z ++ [1])))) []) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [r, Z]) (E := []) (k := 3) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 2]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id, .sym 3, .blk 1 .id, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem jinc1 (r : List Nat) (Z : List Nat) (hr : Bits r) (hZ : ∀ a ∈ Z, a ∈ Z2) :
    zconpLogic.Reach (hd Q.JINC (1 :: (r ++ [3])) (Z ++ [1]))
      (hd Q.JINC (1 :: r) (2 :: (Z ++ [1]))) := by
  have hV : Valid [bits, Z2] [r, Z] := Valid.cons hr (Valid.cons hZ (Valid.nil _))
  exact checkTT (env := [r, Z]) (E := []) (k := 1) hV trivial
    (ls := [.sym 1, .blk 0 .id, .sym 3]) (rs := [.blk 1 .id, .sym 1])
    (ls' := [.sym 1, .blk 0 .id]) (rs' := [.sym 2, .blk 1 .id, .sym 1])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## Blank padding -/

theorem hd_eq' (q : Nat) (A R : List Nat) :
    hd q A R = ⟨q, stail (sapp A.reverse blank), scons (sapp A.reverse blank 0) (sapp R blank)⟩ := by
  show (⟨q, stail (sapp (dL [A, R] [.blk 0 .id]) blank),
    scons (sapp (dL [A, R] [.blk 0 .id]) blank 0) (sapp (dR [A, R] [.blk 1 .id]) blank)⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem hdR_eq' (q : Nat) (A R : List Nat) :
    hdR q A R = ⟨q, sapp A.reverse blank, sapp R blank⟩ := by
  show (⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩ : ZC) = _
  rw [dW_blk0, dW_blk1]

theorem sapp_zeros' (g : Nat) : sapp (List.replicate g 0) blank = blank := by
  induction g with
  | zero => rfl
  | succ g ih =>
    show scons 0 (sapp (List.replicate g 0) blank) = blank
    rw [ih, scons_blank]

theorem hd_pad (q : Nat) (A R : List Nat) (z : Nat) : hd q A (R ++ List.replicate z 0) = hd q A R := by
  rw [hd_eq', hd_eq', sapp_append, sapp_zeros']

theorem hdR_pad (q : Nat) (A R : List Nat) (z : Nat) : hdR q A (R ++ List.replicate z 0) = hdR q A R := by
  rw [hdR_eq', hdR_eq', sapp_append, sapp_zeros']

theorem zeros_eq {l l' : List Nat} (h : ∀ x ∈ l, x = 0) (h' : ∀ x ∈ l', x = 0) (hl : l.length = l'.length) :
    l = l' := by
  rw [List.eq_replicate_iff.mpr ⟨rfl, h⟩, List.eq_replicate_iff.mpr ⟨rfl, h'⟩, hl]

/-- Erase to the right: the head ends on `EBs`, over blanks. -/
theorem eaAll (L F Dw : List Nat) (hL : Sym4 L) (hF : NoB F) (hD : NoB Dw) :
    ∃ k, zconpLogic.Reach (hdR Q.EAs L (F ++ 0 :: Dw)) (hd Q.EBs (L ++ (List.replicate k 0 ++ [0])) []) := by
  have h0 : Sym4 (0 :: Dw) := Sym4.cons (by simp [ALL]) hD.sym4
  have h1 := eaF L F (0 :: Dw) hL hF h0
  have hL1 : Sym4 (L ++ List.replicate F.length 0) := hL.app (Sym4.rep _ _ (by simp [ALL]))
  have h2 := eaSep (L ++ List.replicate F.length 0) Dw hL1 hD.sym4
  have hL2 : Sym4 (L ++ List.replicate F.length 0 ++ [0]) := hL1.app (Sym4.cons (by simp [ALL]) Sym4.nil)
  cases Dw with
  | nil =>
    refine ⟨F.length, h1.trans (h2.trans ((ea2End _ hL2).ofEq rfl (by simp)))⟩
  | cons x Dw' =>
    have hx : x ∈ NB := hD x (List.mem_cons_self ..)
    have hD' : NoB Dw' := fun y hy => hD y (List.mem_cons_of_mem _ hy)
    have h3 : zconpLogic.Reach (hdR QConp.EAs2 (L ++ List.replicate F.length 0 ++ [0]) (x :: Dw'))
        (hdR Q.EAs (L ++ List.replicate F.length 0 ++ [0] ++ [0]) Dw') := by
      by_cases hx1 : x = 1
      · subst hx1; exact ea2M _ _ hL2 hD'.sym4
      · exact ea2b _ _ x hL2 hD'.sym4 (by simp [NB] at hx; simp [bits]; omega)
    have hL3 : Sym4 (L ++ List.replicate F.length 0 ++ [0] ++ [0]) :=
      hL2.app (Sym4.cons (by simp [ALL]) Sym4.nil)
    have h4 := eaF _ Dw' [] hL3 hD' Sym4.nil
    have hL4 : Sym4 (L ++ List.replicate F.length 0 ++ [0] ++ [0] ++ List.replicate Dw'.length 0) :=
      hL3.app (Sym4.rep _ _ (by simp [ALL]))
    have h4' : zconpLogic.Reach (hdR Q.EAs (L ++ List.replicate F.length 0 ++ [0] ++ [0]) Dw')
        (hdR Q.EAs (L ++ List.replicate F.length 0 ++ [0] ++ [0] ++ List.replicate Dw'.length 0) []) := h4.ofEq (by simp) rfl
    have h5 := eaSep _ [] hL4 Sym4.nil
    have hL5 : Sym4 (L ++ List.replicate F.length 0 ++ [0] ++ [0] ++ List.replicate Dw'.length 0 ++ [0]) :=
      hL4.app (Sym4.cons (by simp [ALL]) Sym4.nil)
    have h6 := ea2End _ hL5
    have e0 : ∀ q A, hdR q A ([] : List Nat) = hdR q A [0] := fun q A => by
      simpa using (hdR_pad q A [] 1).symm
    have h56 := (h5.ofEq (e0 _ _).symm rfl).trans h6
    refine ⟨F.length + Dw'.length + 2, h1.trans (h2.trans (h3.trans ((h4'.ofEq rfl rfl).trans
      (h56.ofEq rfl ?_))))⟩
    congr 1
    simp only [List.append_assoc]
    congr 1
    apply zeros_eq
    · intro x hx; simp at hx; omega
    · intro x hx; simp at hx; omega
    · simp; omega

/-! ## Loops over the fuel and over `D` -/

theorem bits_all {b : Nat} (h : b ∈ bits) : b ∈ ALL := by
  simp [bits, ALL] at *; omega

theorem rep0_cons (b : Nat) (X : List Nat) : List.replicate b 0 ++ 0 :: X = List.replicate (b + 1) 0 ++ X := by
  rw [← List.replicate_append_replicate]; simp

theorem rep0_app (a b : Nat) (X : List Nat) :
    List.replicate a 0 ++ (List.replicate b 0 ++ X) = List.replicate (a + b) 0 ++ X := by
  rw [← List.append_assoc, List.replicate_append_replicate]

theorem rsLoop (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    ∀ Ar : List Nat, Bits Ar →
      zconpLogic.Reach (hd QConp.RS2 (L ++ (Ar.reverse ++ [1])) R)
        (hd QConp.RS2 (L ++ [1]) (Ar.reverse ++ R))
  | [], _ => by simpa using LTM.Reach.refl _ _
  | c :: Ar, h => by
    have hAr : Bits Ar := h.tail
    have hrev : Sym4 (L ++ Ar.reverse) := hL.app (fun a ha => bits_all (hAr a (List.mem_reverse.mp ha)))
    have h1 := rsStep (L ++ Ar.reverse) R c hrev hR h.head
    have h2 := rsLoop L (c :: R) hL (Sym4.cons (bits_all h.head) hR) Ar hAr
    exact (h1.ofEq (by simp) rfl).trans (h2.ofEq (by simp) (by simp))

theorem blkW_cons (n d : Nat) : blkW n d = 1 :: (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) := rfl

theorem blkB_bits (n d : Nat) : Bits (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) := by
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with h | h
  · rw [List.eq_of_mem_replicate h]; simp [bits]
  · rw [List.eq_of_mem_replicate h]; simp [bits]

theorem blkB_ne (n d : Nat) : List.replicate d 3 ++ List.replicate (n + 1 - d) 2 ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem blkB_snoc (n d : Nat) : ∃ B0 c, List.replicate d 3 ++ List.replicate (n + 1 - d) 2 = B0 ++ [c] ∧ Bits B0 ∧ c ∈ bits := by
  have hb := blkB_bits n d
  rcases List.eq_nil_or_concat (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) with h | ⟨B0, c, h⟩
  · exact absurd h (blkB_ne n d)
  · refine ⟨B0, c, by rw [h]; simp, ?_, ?_⟩
    · intro a ha; exact hb a (by rw [h]; simp [ha])
    · exact hb c (by rw [h]; simp)

theorem FWr_sym4 (n : Nat) (ds : List Nat) : Sym4 (FWr n ds) := (FWr_noB n ds).sym4

theorem erLoop4 (n : Nat) (L X : List Nat) (hL : Sym4 L) (hX : Sym4 X) :
    ∀ ds : List Nat, zconpLogic.Reach (hd QConp.ER4 (L ++ 1 :: FWr n ds) X)
      (hdR Q.GRB (L ++ [1]) (List.replicate (FWr n ds).length 0 ++ X))
  | [] => by simpa [FWr] using erEnd L X hL hX
  | d :: ds => by
    obtain ⟨B0, c, hB, hB0, hc⟩ := blkB_snoc n d
    have hL' : Sym4 (L ++ 1 :: FWr n ds) := hL.app (Sym4.cons (by simp [ALL]) (FWr_sym4 n ds))
    have h1 := erB (L ++ 1 :: FWr n ds) B0 X c hL' hB0 hX hc
    have hX' : Sym4 (List.replicate B0.length 0 ++ 0 :: 0 :: X) :=
      (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hX))
    have h2 := erLoop4 n L _ hL hX' ds
    have e : FWr n (d :: ds) = FWr n ds ++ 1 :: (B0 ++ [c]) := by
      show FWr n ds ++ blkW n d = _
      rw [blkW_cons, hB]
    rw [e]
    refine (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl ?_)
    rw [rep0_cons, rep0_cons, rep0_app]
    congr 2
    simp

theorem exLoop4 (n : Nat) (L X : List Nat) (hL : Sym4 L) (hX : Sym4 X) :
    ∀ ds : List Nat, zconpLogic.Reach (hd QConp.EX2 (L ++ 1 :: FWr n ds) X)
      (hd QConp.EX3 L (1 :: (List.replicate (FWr n ds).length 0 ++ X)))
  | [] => by simpa [FWr] using exEnd L X hL hX
  | d :: ds => by
    obtain ⟨B0, c, hB, hB0, hc⟩ := blkB_snoc n d
    have hL' : Sym4 (L ++ 1 :: FWr n ds) := hL.app (Sym4.cons (by simp [ALL]) (FWr_sym4 n ds))
    have h1 := exB (L ++ 1 :: FWr n ds) B0 X c hL' hB0 hX hc
    have hX' : Sym4 (List.replicate B0.length 0 ++ 0 :: 0 :: X) :=
      (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) hX))
    have h2 := exLoop4 n L _ hL hX' ds
    have e : FWr n (d :: ds) = FWr n ds ++ 1 :: (B0 ++ [c]) := by
      show FWr n ds ++ blkW n d = _
      rw [blkW_cons, hB]
    rw [e]
    refine (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl ?_)
    rw [rep0_cons, rep0_cons, rep0_app]
    congr 3
    simp

theorem exLoop3 (n : Nat) (L X : List Nat) (hL : Sym4 L) (hX : Sym4 X) (d : Nat) (ds : List Nat) :
    zconpLogic.Reach (hd QConp.EX1 (L ++ 1 :: FWr n (d :: ds)) X)
      (hd QConp.EX3 L (1 :: (List.replicate (FWr n (d :: ds)).length 0 ++ X))) := by
  have hL' : Sym4 (L ++ 1 :: FWr n ds) := hL.app (Sym4.cons (by simp [ALL]) (FWr_sym4 n ds))
  have h1 := exA (L ++ 1 :: FWr n ds) _ X hL' (blkB_bits n d) hX
  have hX' : Sym4 (List.replicate (List.replicate d 3 ++ List.replicate (n + 1 - d) 2).length 0 ++ 0 :: X) :=
    (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hX)
  have h2 := exLoop4 n L _ hL hX' ds
  have e : FWr n (d :: ds) = FWr n ds ++ 1 :: (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) := rfl
  rw [e]
  refine (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl ?_)
  rw [rep0_cons, rep0_app]
  congr 3
  simp

theorem erLoop3 (n : Nat) (L X : List Nat) (hL : Sym4 L) (hX : Sym4 X) (d : Nat) (ds : List Nat) :
    zconpLogic.Reach (hd QConp.ER3 (L ++ 1 :: FWr n (d :: ds)) X)
      (hdR Q.GRB (L ++ [1]) (List.replicate (FWr n (d :: ds)).length 0 ++ X)) := by
  have hL' : Sym4 (L ++ 1 :: FWr n ds) := hL.app (Sym4.cons (by simp [ALL]) (FWr_sym4 n ds))
  have h1 := erA (L ++ 1 :: FWr n ds) _ X hL' (blkB_bits n d) hX
  have hX' : Sym4 (List.replicate (List.replicate d 3 ++ List.replicate (n + 1 - d) 2).length 0 ++ 0 :: X) :=
    (Sym4.rep _ _ (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hX)
  have h2 := erLoop4 n L _ hL hX' ds
  have e : FWr n (d :: ds) = FWr n ds ++ 1 :: (List.replicate d 3 ++ List.replicate (n + 1 - d) 2) := rfl
  rw [e]
  refine (h1.ofEq (by simp) rfl).trans (h2.ofEq rfl ?_)
  rw [rep0_cons, rep0_app]
  congr 3
  simp

end ZP.Conp
