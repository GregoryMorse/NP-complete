/-- Wrong answer: `s := 0^n`, back to the last cell of `a`. -/
theorem zsSweep (Z : List Nat) (s : List Nat) (hZ : Sym4 Z) (hs : Bits s) :
    zppolyLogic.Reach (hd QPoly.ZS (Z ++ (1 :: (s))) ([])) (hd Q.SINC (Z) (1 :: (List.replicate s.length 2))) := by
  have hV : Valid [ALL, bits] [Z, s] := Valid.cons hZ (Valid.cons hs (Valid.nil _))
  exact checkTT (env := [Z, s]) (E := []) (k := 2) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [])
        (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 2)])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Correct, `s` all ones: the carry reaches `M_a`, a `0` is appended, back to `a`. -/
theorem cOvA (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N)) (hd QPoly.DL1 (Z) (1 :: (N ++ ([2])))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTT (env := [Z, N]) (E := []) (k := 5) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id])
        (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .sym 2])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Overflow: one cell of `a` moves to `s`. -/
theorem dlStep (Z : List Nat) (N : List Nat) (b : Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) (hb : b ∈ bits) :
    zppolyLogic.Reach (hd QPoly.DL1 (Z ++ ([b])) (1 :: (N ++ ([2])))) (hd QPoly.DL1 (Z) (1 :: (2 :: (N)))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [Z, N]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .sym 2]) (rs := [.sym 1, .blk 1 .id, .sym 2])
          (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 2, .blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [Z, N]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id, .sym 2])
          (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 2, .blk 1 .id])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Overflow: `a` is empty. -/
theorem dlEnd (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd QPoly.DL1 (Z ++ ([1])) (1 :: (N ++ ([2])))) (hdR Q.GRB (Z ++ ([1])) (1 :: (N ++ ([2])))) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTF (env := [Z, N]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 1, .blk 1 .id, .sym 2])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 2])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Wrong, `a` all ones: `a` grows, `s` empty. -/
theorem wOv0 (Z : List Nat) (N : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N ++ ([1]))) (hdR Q.GRB (Z ++ (1 :: (N ++ (2 :: ([1]))))) ([])) := by
  have hV : Valid [ALL, Z2] [Z, N] := Valid.cons hZ (Valid.cons hN (Valid.nil _))
  exact checkTF (env := [Z, N]) (E := []) (k := 4) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 1]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Wrong, `a` all ones: `a` grows, `s` is kept at length `n`. -/
theorem wOv1 (Z : List Nat) (N : List Nat) (S : List Nat) (hZ : Sym4 Z) (hN : ∀ a ∈ N, a ∈ Z2) (hS : ∀ a ∈ S, a ∈ Z2) :
    zppolyLogic.Reach (hd Q.SINC (Z ++ ([1])) (N ++ (1 :: (2 :: (S))))) (hdR Q.GRB (Z ++ (1 :: (N ++ (2 :: (1 :: (S ++ ([2]))))))) ([])) := by
  have hV : Valid [ALL, Z2, Z2] [Z, N, S] := Valid.cons hZ (Valid.cons hN (Valid.cons hS (Valid.nil _)))
  exact checkTF (env := [Z, N, S]) (E := []) (k := 6) hV trivial
        (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .sym 1, .blk 2 .id, .sym 2]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
