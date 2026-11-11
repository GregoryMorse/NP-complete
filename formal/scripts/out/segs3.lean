/-- Verifier accepted: truth flag `1`. -/
theorem vAcc (Kr : List Nat) (a : List Nat) (s : List Nat) (Y : List Nat) (c : Nat) (y : Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hY : NoB Y) (hc : c ∈ bits) (hy : y ∈ NB) :
    zppolyLogic.Reach (hdR Q.DP11 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (c :: (y :: (Y)))))))))) (hdR Q.GRB (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Y] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hY (Valid.nil _))))
  rcases mem_bits hc with rfl | rfl <;> rcases (show y = 1 ∨ y = 2 ∨ y = 3 by simpa [NB] using hy) with rfl | rfl | rfl
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 1, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 2, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .sym 3, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 1, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Y]) (E := []) (k := 14) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 3 .id])
          (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier rejected: `C -= 1`, refill the fuel, run again. -/
theorem vRejE (Kr : List Nat) (a : List Nat) (s : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) :
    zppolyLogic.Reach (hdR Q.DP10 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (3 :: (Z ++ (1 :: (1 :: (D ++ (E))))))))))))) (hdR Q.GC (1 :: (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ ([1])))))))) (2 :: (List.replicate Z.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))) := by
  have hV : Valid [bits, bits, bits, Z2, T3, Z2] [Kr, a, s, Z, D, E] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.nil _))))))
  exact checkFF (env := [Kr, a, s, Z, D, E]) (E := []) (k := 38) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id, .blk 5 .id])
        (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.sym 2, .blk 3 (.const 3), .sym 1, .sym 1, .blk 4 .id, .blk 5 (.const 3)])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier rejected, `C` has more bits. -/
theorem vRejC (Kr : List Nat) (a : List Nat) (s : List Nat) (Cp : List Nat) (Z : List Nat) (D : List Nat) (E : List Nat) (c : Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hCp : Bits Cp) (hZ : ∀ a ∈ Z, a ∈ Z2) (hD : ∀ a ∈ D, a ∈ T3) (hE : ∀ a ∈ E, a ∈ Z2) (hc : c ∈ bits) :
    zppolyLogic.Reach (hdR Q.DP10 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (c :: (Cp ++ (3 :: (Z ++ (1 :: (1 :: (D ++ (E))))))))))))))) (hdR Q.GC (1 :: (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ ([1])))))))) (c :: (Cp ++ (2 :: (List.replicate Z.length 3 ++ (1 :: (1 :: (D ++ (List.replicate E.length 3))))))))) := by
  have hV : Valid [bits, bits, bits, bits, Z2, T3, Z2] [Kr, a, s, Cp, Z, D, E] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hCp (Valid.cons hZ (Valid.cons hD (Valid.cons hE (Valid.nil _)))))))
  rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [Kr, a, s, Cp, Z, D, E]) (E := []) (k := 42) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .sym 1, .blk 5 .id, .blk 6 .id])
          (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.sym 2, .blk 3 .id, .sym 2, .blk 4 (.const 3), .sym 1, .sym 1, .blk 5 .id, .blk 6 (.const 3)])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Kr, a, s, Cp, Z, D, E]) (E := []) (k := 42) hV trivial
          (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 3, .blk 4 .id, .sym 1, .sym 1, .blk 5 .id, .blk 6 .id])
          (ls' := [.sym 1, .sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.sym 3, .blk 3 .id, .sym 2, .blk 4 (.const 3), .sym 1, .sym 1, .blk 5 .id, .blk 6 (.const 3)])
          (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Verifier rejected at `C = 0`: truth flag `0`. -/
theorem vUnder (Kr : List Nat) (a : List Nat) (s : List Nat) (Z : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hZ : ∀ a ∈ Z, a ∈ Z2) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.DP10 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (2 :: (Z ++ (1 :: (Fu))))))))))) (hdR Q.GRB (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: ([1]))))))))) ([])) := by
  have hV : Valid [bits, bits, bits, Z2, NB] [Kr, a, s, Z, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hZ (Valid.cons hFu (Valid.nil _)))))
  exact checkFF (env := [Kr, a, s, Z, Fu]) (E := []) (k := 23) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- dok1 -/
theorem dOk1 (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.DP11 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: (Fu))))))))))) (hd Q.SINC (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 18) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- dok0 -/
theorem dOk0 (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.DP10 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (1 :: (Fu)))))))))) (hd Q.SINC (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 16) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- dbad1 -/
theorem dBad1 (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.DP11 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (1 :: (Fu)))))))))) (hd Q.BEEP (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: ([1])))))))) (1 :: (Fu))) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 8) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1]) (rs' := [.sym 1, .blk 3 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- dbad0 -/
theorem dBad0 (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.DP10 ([1]) (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: (1 :: (3 :: (1 :: (Fu))))))))))) (hd Q.BEEP (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: ([1])))))))) (3 :: (1 :: (Fu)))) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 8) hV trivial
        (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1]) (rs' := [.sym 3, .sym 1, .blk 3 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- dbad1E -/
theorem dBad1E (Kr : List Nat) (a : List Nat) (s : List Nat) (Fu : List Nat) (hKr : Bits Kr) (ha : Bits a) (hs : Bits s) (hFu : NoB Fu) :
    zppolyLogic.Reach (hdR Q.EAs (1 :: (Kr ++ (1 :: (a ++ (1 :: (s ++ (1 :: ([2])))))))) (1 :: (Fu))) (hd QPoly.ZS (1 :: (Kr ++ (1 :: (a ++ (1 :: (s)))))) ([])) := by
  have hV : Valid [bits, bits, bits, NB] [Kr, a, s, Fu] := Valid.cons hKr (Valid.cons ha (Valid.cons hs (Valid.cons hFu (Valid.nil _))))
  exact checkFT (env := [Kr, a, s, Fu]) (E := []) (k := 7) hV trivial
        (ls := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 2]) (rs := [.sym 1, .blk 3 .id])
        (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id]) (rs' := [])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
