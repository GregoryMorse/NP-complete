/-- First `BLK` (the certificate counter): `M_2` at the end, back to the first bit of `s`. -/
theorem blk1Start (Kr : List Nat) (a : List Nat) (s : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) :
    zppolyLogic.Reach (hdR Q.GRB (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) (hdR Q.COPY (1 :: (Kr ++ (1 :: (a ++ ([1]))))) (s ++ ([1]))) := by
  have hV : Valid [bits, bits, bits] [Kr, a, s] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.nil _)))
  exact checkFF (env := [Kr, a, s]) (E := []) (k := 13) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 1])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One `COPY` round of the first `BLK`. -/
theorem copyBody1 (P : List Nat) (u : List Nat) (v : List Nat) (b : Nat) (hP : NoB P) (hu : Bits u) (hv : Bits v) (hb : b ∈ bits) :
    zppolyLogic.Reach (hdR Q.COPY (P ++ (u)) (b :: (v ++ (1 :: (List.replicate u.length 3))))) (hdR Q.COPY (P ++ (u ++ ([b]))) (v ++ (1 :: (List.replicate u.length 3 ++ ([3]))))) := by
  have hV : Valid [NB, bits, bits] [P, u, v] := Valid.cons hP (Valid.cons hu (Valid.cons hv (Valid.nil _)))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [P, u, v]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 2, .blk 2 .id, .sym 1, .blk 1 (.const 3)])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id, .sym 1, .blk 1 (.const 3), .sym 3])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, u, v]) (E := []) (k := 9) hV trivial
          (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 1 (.const 3)])
          (ls' := [.blk 0 .id, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id, .sym 1, .blk 1 (.const 3), .sym 3])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- First `BLK` done, `s = []`: `C = 1`, `M_3`. -/
theorem blk1End0 (Kr : List Nat) (a : List Nat) (s : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) :
    zppolyLogic.Reach (hdR Q.COPY (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([1])) (hdR Q.GRB (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (3 :: ([1]))))))))) ([])) := by
  have hV : Valid [bits, bits, bits] [Kr, a, s] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.nil _)))
  exact checkFF (env := [Kr, a, s]) (E := []) (k := 3) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- First `BLK` done, `s` nonempty: `C`, `M_3`. -/
theorem blk1End1 (Kr : List Nat) (a : List Nat) (s : List Nat) (C0 : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hC0 : ∀ a ∈ C0, a ∈ T3) :
    zppolyLogic.Reach (hdR Q.COPY (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) (1 :: (3 :: (C0)))) (hdR Q.GRB (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (3 :: (C0 ++ (3 :: ([1]))))))))))) ([])) := by
  have hV : Valid [bits, bits, bits, T3] [Kr, a, s, C0] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hC0 (Valid.nil _))))
  exact checkFF (env := [Kr, a, s, C0]) (E := []) (k := 5) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 3, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 3, .sym 1]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Decider fuel block done, the walker steps right. -/
theorem blkDecStep (Kl : List Nat) (Kr : List Nat) (a : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (b : Nat) (hKl : Bits Kl) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) (hb : b ∈ bits) :
    zppolyLogic.Reach (hdR Q.COPY (Kl ++ (1 :: (b :: (Kr ++ (1 :: (a ++ (1 :: (s)))))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3)))))))) (hdR Q.GRB (Kl ++ ([b])) (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ ([3]))))))))))))))) := by
  have hV : Valid [bits, bits, bits, bits, T3, O13] [Kl, Kr, a, s, t, Bl] := Valid.cons hKl (Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _))))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Kl, Kr, a, s, t, Bl]) (E := []) (k := 28) hV trivial
          (ls := [.blk 0 .id, .sym 1, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .blk 3 (.const 3)])
          (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .blk 3 (.const 3), .sym 3])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kl, Kr, a, s, t, Bl]) (E := []) (k := 28) hV trivial
          (ls := [.blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id]) (rs := [.sym 1, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .blk 3 (.const 3)])
          (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id, .sym 1, .blk 3 (.const 3), .sym 3])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Last decider fuel block: the walker goes home. -/
theorem blkDecLast (Kl : List Nat) (a : List Nat) (s : List Nat) (t : List Nat) (Bl : List Nat) (hKl : Bits Kl) (ha : Bits a) (hs : Bits s) (ht : ∀ a ∈ t, a ∈ T3) (hBl : ∀ a ∈ Bl, a ∈ O13) :
    zppolyLogic.Reach (hdR Q.COPY (Kl ++ (1 :: (1 :: (a ++ (1 :: (s)))))) (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3)))))))) (hd Q.WB1 (Kl ++ ([1])) (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (t ++ (1 :: (Bl ++ (1 :: (List.replicate s.length 3 ++ ([3]))))))))))))) := by
  have hV : Valid [bits, bits, bits, T3, O13] [Kl, a, s, t, Bl] := Valid.cons hKl (Valid.cons ha (Valid.cons hs (Valid.cons ht (Valid.cons hBl (Valid.nil _)))))
  exact checkFT (env := [Kl, a, s, t, Bl]) (E := []) (k := 25) hV trivial
        (ls := [.blk 0 .id, .sym 1, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3)])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 2 (.const 3), .sym 3])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The walker is home: `H`, start of the charge. -/
theorem wbEnd (K : List Nat) (Y : List Nat) (hK : Bits K) (hY : Sym4 Y) :
    zppolyLogic.Reach (hd Q.WB1 ([1]) (K ++ (1 :: (Y)))) (hdR QPoly.CHS ([1]) (1 :: (K ++ (1 :: (Y))))) := by
  have hV : Valid [bits, ALL] [K, Y] := Valid.cons hK (Valid.cons hY (Valid.nil _))
  exact checkTF (env := [K, Y]) (E := []) (k := 2) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id])
        (ls' := [.sym 1]) (rs' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment: a `0` becomes `1`. -/
theorem sinc0 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : NoB Z) :
    zppolyLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ ([2])))) (Z)) (hdR Q.GRB (A ++ (1 :: (r ++ ([3])))) (Z)) := by
  have hV : Valid [NB, bits, NB] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [A, r, Z]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2]) (rs := [.blk 2 .id])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Increment: a `1` becomes `0`, carry. -/
theorem sinc1 (A : List Nat) (r : List Nat) (Z : List Nat) (hA : NoB A) (hr : Bits r) (hZ : NoB Z) :
    zppolyLogic.Reach (hd Q.SINC (A ++ (1 :: (r ++ ([3])))) (Z)) (hd Q.SINC (A ++ (1 :: (r))) (2 :: (Z))) := by
  have hV : Valid [NB, bits, NB] [A, r, Z] := Valid.cons hA (Valid.cons hr (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [A, r, Z]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3]) (rs := [.blk 2 .id])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 2, .blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
