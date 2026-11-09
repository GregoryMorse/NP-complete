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
theorem blkStartY (Jl : List Nat) (Jr : List Nat) (s : List Nat) (T : List Nat) (Y : List Nat) (hJl : Bits Jl) (hJr : Bits Jr) (hs : Bits s) (hT : ∀ a ∈ T, a ∈ O13) (hY : Sym4 Y) :
    zconpLogic.Reach (hdR Q.GRB (Jl ++ (1 :: (Jr ++ (1 :: (s ++ (1 :: (T))))))) (0 :: (0 :: (List.replicate s.length 0 ++ (Y)))))
      (hdR Q.COPY (Jl ++ (1 :: (Jr ++ ([1])))) (s ++ (1 :: (T ++ (1 :: (0 :: (List.replicate s.length 0 ++ (Y)))))))) := by
  have hV : Valid [bits, bits, bits, O13, ALL] [Jl, Jr, s, T, Y] := Valid.cons hJl (Valid.cons hJr (Valid.cons hs (Valid.cons hT (Valid.cons hY (Valid.nil _)))))
  exact checkFF (env := [Jl, Jr, s, T, Y]) (E := []) (k := 13) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 0, .sym 0, .blk 2 (.const 0), .blk 4 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 0, .blk 2 (.const 0), .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One `COPY` round. -/
theorem copyBodyY (P : List Nat) (u : List Nat) (v : List Nat) (T : List Nat) (Y : List Nat) (c : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hT : ∀ a ∈ T, a ∈ O13) (hY : Sym4 Y) (hc : c ∈ bits) :
    zconpLogic.Reach (hdR Q.COPY (P ++ (u)) (c :: (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ (0 :: (0 :: (List.replicate v.length 0 ++ (Y)))))))))))
      (hdR Q.COPY (P ++ (u ++ ([c]))) (v ++ (1 :: (T ++ (1 :: (List.replicate u.length 3 ++ (3 :: (0 :: (List.replicate v.length 0 ++ (Y)))))))))) := by
  have hV : Valid [NB, bits, bits, O13, ALL] [P, u, v, T, Y] := Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.cons hT (Valid.cons hY (Valid.nil _)))))
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


end ZP.Conp
