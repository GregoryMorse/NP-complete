module

public import ZP.MainN
public import ZP.PairG

@[expose] public section

/-! # The pair lemma of the NTT machine: layout, start configuration and the ruler `P += n` -/

namespace ZP.N

open ZP ZP.G

/-- The pair start: `P = 1`, the head on the `M` after it, then `K = 111`, `C = 1^c`, `Nn = 1^n`. -/
def layN (c n : Nat) : ZC :=
  hdR QN.PA0 [3] (1 :: [3, 3, 3] ++ 1 :: List.replicate c 3 ++ 1 :: List.replicate n 3)

theorem znttConf_k0 : znttLogic.zconf 20 = some (layN 1 1) := by
  rfl

/-! ## `P += n`: for each cell of `Nn` (marked from the right) one cell is added at the left edge -/

theorem pa0Sweep (A X Z : List Nat) (hA : NoB A) (hX : NoB X) (hZ : Sym4 Z) :
    znttLogic.Reach (hdR QN.PA0 A (X ++ 0 :: Z)) (hd QN.PA1 (A ++ X) (0 :: Z)) := by
  have hV : Valid [NB, NB, ALL] [A, X, Z] := Valid.cons hA (Valid.cons hX (Valid.cons hZ (Valid.nil _)))
  exact checkFT (env := [A, X, Z]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One unmarked cell is marked and `P` grows by one cell. -/
theorem paMark (W0 Z : List Nat) (j : Nat) (hW : NoB W0) (hZ : Sym4 Z) :
    znttLogic.Reach (hd QN.PA1 (W0 ++ 3 :: List.replicate j 2) (0 :: Z))
      (hdR QN.PA0 [3] (W0 ++ 2 :: List.replicate j 2 ++ 0 :: Z)) := by
  have hV : Valid [NB, Mk, ALL] [W0, List.replicate j 2, Z] :=
    Valid.cons hW (Valid.cons (rep2_mk j) (Valid.cons hZ (Valid.nil _)))
  exact checkTF (env := [W0, List.replicate j 2, Z]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 .id]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.sym 3]) (rs' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- All cells of `Nn` are marked: unmark them and start the primality test. -/
theorem paDone (W0 Z : List Nat) (n : Nat) (hW : NoB W0) (hZ : Sym4 Z) :
    znttLogic.Reach (hd QN.PA1 (W0 ++ 1 :: List.replicate n 2) (0 :: Z))
      (hd QN.PT0 (W0 ++ 1 :: List.replicate n 3) (0 :: Z)) := by
  have hV : Valid [NB, Mk, ALL] [W0, List.replicate n 2, Z] :=
    Valid.cons hW (Valid.cons (rep2_mk n) (Valid.cons hZ (Valid.nil _)))
  exact checkTT (env := [W0, List.replicate n 2, Z]) (E := []) (k := 8) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 0, .blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 (.const 3)]) (rs' := [.sym 0, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Everything between `P` and `Nn`: `M K M C`. -/
def Hd0 (c : Nat) : List Nat := 1 :: [3, 3, 3] ++ 1 :: List.replicate c 3

theorem noB_Hd0 (c : Nat) : NoB (Hd0 c) := by simp [Hd0, NB]

theorem paLoop (c p : Nat) (Z : List Nat) (hZ : Sym4 Z) (n : Nat) : ∀ d j, j + d = n →
    znttLogic.Reach
      (hd QN.PA1 (List.replicate (p + j) 3 ++ Hd0 c ++ 1 :: (List.replicate (n - j) 3 ++ List.replicate j 2)) (0 :: Z))
      (hd QN.PT0 (List.replicate (p + n) 3 ++ Hd0 c ++ 1 :: List.replicate n 3) (0 :: Z)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    obtain rfl : j = n := by omega
    have h := paDone (List.replicate (p + j) 3 ++ Hd0 c) Z j (by simp [NB, noB_Hd0]) hZ
    refine h.of_eq (by simp) ?_
    simp
  | succ d ih =>
    intro j hj
    obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
    have h1 := paMark (List.replicate (p + j) 3 ++ Hd0 c ++ 1 :: List.replicate m 3) Z j
      (by simp [NB, noB_Hd0]) hZ
    have h2 := pa0Sweep [3] (List.replicate (p + j) 3 ++ Hd0 c ++ 1 :: List.replicate m 3 ++ 2 :: List.replicate j 2)
      Z (by simp [NB]) (by simp [NB, noB_Hd0]) hZ
    have h3 := ih (j + 1) (by omega)
    have e : n - (j + 1) = m := by omega
    refine (h1.of_eq (by rw [hm, List.replicate_succ']; simp [List.append_assoc]) rfl).trans
      ((h2.of_eq rfl rfl).trans (h3.of_eq ?_ rfl))
    rw [e, ← Nat.add_assoc, List.replicate_succ]
    simp [List.replicate_succ, List.append_assoc]

/-! ## Primality test: copy `P` into `D` (left of the separator `M`) -/

/-- `PT0`: go to the left edge, write the separator `M`, step onto `P`. -/
theorem pt0Start (W Z : List Nat) (hW : NoB W) (hZ : Sym4 Z) :
    znttLogic.Reach (hd QN.PT0 W (0 :: Z)) (hdR QN.DC1 [1] (W ++ 0 :: Z)) := by
  have hV : Valid [NB, ALL] [W, Z] := Valid.cons hW (Valid.cons hZ (Valid.nil _))
  exact checkTF (env := [W, Z]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 0, .blk 1 .id])
    (ls' := [.sym 1]) (rs' := [.blk 0 .id, .sym 0, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- One copy round: a cell of `P` is marked and a cell is added to `D`. -/
theorem dcRound (j m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QN.DC1 (List.replicate j 3 ++ [1]) (List.replicate j 2 ++ 3 :: List.replicate m 3 ++ 1 :: R))
      (hdR QN.DC1 (List.replicate (j + 1) 3 ++ [1]) (List.replicate (j + 1) 2 ++ List.replicate m 3 ++ 1 :: R)) := by
  have hV : Valid [T3, Mk, T3, ALL] [List.replicate j 3, List.replicate j 2, List.replicate m 3, R] :=
    Valid.cons (rep_t3 j) (Valid.cons (rep2_mk j) (Valid.cons (rep_t3 m) (Valid.cons hR (Valid.nil _))))
  have : znttLogic.Reach (hdR QN.DC1 (List.replicate j 3 ++ [1]) (List.replicate j 2 ++ 3 :: List.replicate m 3 ++ 1 :: R))
      (hdR QN.DC1 (3 :: List.replicate j 3 ++ [1]) (List.replicate j 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)) :=
    checkFF (env := [List.replicate j 3, List.replicate j 2, List.replicate m 3, R]) (E := []) (k := 40) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
      (ls' := [.sym 3, .blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ]) ?_
  have e2 : List.replicate (j + 1) 2 = List.replicate j 2 ++ [2] := List.replicate_succ'
  have e3 : List.replicate (j + 1) 3 = 3 :: List.replicate j 3 := List.replicate_succ ..
  simp only [e2, e3, List.append_assoc, List.cons_append, List.nil_append]

theorem dcEnd (p : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QN.DC1 (List.replicate p 3 ++ [1]) (List.replicate p 2 ++ 1 :: R))
      (hd QN.XS1 (List.replicate p 3) (1 :: List.replicate p 3 ++ 1 :: R)) := by
  have hV : Valid [T3, Mk, ALL] [List.replicate p 3, List.replicate p 2, R] :=
    Valid.cons (rep_t3 p) (Valid.cons (rep2_mk p) (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [List.replicate p 3, List.replicate p 2, R]) (E := []) (k := 40) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 3), .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dcLoop (p : Nat) (R : List Nat) (hR : Sym4 R) : ∀ d j, j + d = p →
    znttLogic.Reach (hdR QN.DC1 (List.replicate j 3 ++ [1]) (List.replicate j 2 ++ List.replicate (p - j) 3 ++ 1 :: R))
      (hd QN.XS1 (List.replicate p 3) (1 :: List.replicate p 3 ++ 1 :: R)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    obtain rfl : j = p := by omega
    have h := dcEnd j R hR
    exact h.of_eq (by simp) rfl
  | succ d ih =>
    intro j hj
    obtain ⟨m, hm⟩ : ∃ m, p - j = m + 1 := ⟨p - j - 1, by omega⟩
    have h1 := dcRound j m R hR
    have h2 := ih (j + 1) (by omega)
    have e : p - (j + 1) = m := by omega
    rw [e] at h2
    refine (h1.of_eq (by rw [hm]; simp [List.replicate_succ, List.append_assoc]) rfl).trans h2

/-! ## `d := d - 1`: erase the first cell of `D`, restore the others -/

theorem rep_eq_map (D : List Nat) : List.replicate D.length 3 = D.map (fun _ => 3) := (List.map_const' ..).symm

theorem xsDec2 (a b : Nat) (R : List Nat) (ha : a ∈ bits) (hb : b ∈ bits) (hR : Sym4 R) :
    znttLogic.Reach (hd QN.XS1 [a, b] (1 :: R)) (hd QN.WX [0, 3] (1 :: R)) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  rcases mem_bits ha with rfl | rfl <;> rcases mem_bits hb with rfl | rfl
  · exact checkTT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 2, .sym 2]) (rs := [.sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 2, .sym 3]) (rs := [.sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 3, .sym 2]) (rs := [.sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 3, .sym 3]) (rs := [.sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xsDecN (a b c : Nat) (Dt R : List Nat) (ha : a ∈ bits) (hb : b ∈ bits) (hc : c ∈ bits)
    (hD : Bits Dt) (hR : Sym4 R) :
    znttLogic.Reach (hd QN.XS1 (a :: b :: c :: Dt) (1 :: R))
      (hdR QN.X4 (0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) R) := by
  have hV : Valid [bits, ALL] [Dt, R] := Valid.cons hD (Valid.cons hR (Valid.nil _))
  rcases mem_bits ha with rfl | rfl <;> rcases mem_bits hb with rfl | rfl <;> rcases mem_bits hc with rfl | rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 2, .sym 2, .sym 2, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 2, .sym 2, .sym 3, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 2, .sym 3, .sym 2, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 2, .sym 3, .sym 3, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 3, .sym 2, .sym 2, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 3, .sym 2, .sym 3, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 3, .sym 3, .sym 2, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl
  · exact (checkTF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := 0 :: 3 :: 3 :: List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 3, .sym 3, .sym 3, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl rfl

/-! ## Divisibility test by marking: `D` counts `a` modulo `d` -/

/-- One cell of `P` is marked; one cell of `D` is marked (`D` has at least two unmarked cells). -/
theorem xIterA (r k a m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QN.X4 ([0] ++ List.replicate r 2 ++ 3 :: 3 :: List.replicate k 3 ++ [1])
        (List.replicate a 2 ++ 3 :: List.replicate m 3 ++ 1 :: R))
      (hdR QN.X4 ([0] ++ List.replicate r 2 ++ 2 :: 3 :: List.replicate k 3 ++ [1])
        (List.replicate a 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)) := by
  have hV : Valid [Mk, T3, Mk, T3, ALL] [List.replicate r 2, List.replicate k 3, List.replicate a 2, List.replicate m 3, R] :=
    Valid.cons (rep2_mk r) (Valid.cons (rep_t3 k) (Valid.cons (rep2_mk a) (Valid.cons (rep_t3 m) (Valid.cons hR (Valid.nil _)))))
  exact checkFF (env := [List.replicate r 2, List.replicate k 3, List.replicate a 2, List.replicate m 3, R]) (E := []) (k := 200) hV trivial
    (ls := [.sym 0, .blk 0 .id, .sym 3, .sym 3, .blk 1 .id, .sym 1])
    (rs := [.blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 0, .blk 0 .id, .sym 2, .sym 3, .blk 1 .id, .sym 1])
    (rs' := [.blk 2 .id, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `D` is full after the mark: it is reset. -/
theorem xIterB (r a m : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QN.X4 ([0] ++ List.replicate r 2 ++ 3 :: [1]) (List.replicate a 2 ++ 3 :: List.replicate m 3 ++ 1 :: R))
      (hdR QN.X4 ([0] ++ List.replicate (r + 1) 3 ++ [1]) (List.replicate a 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)) := by
  have hV : Valid [Mk, Mk, T3, ALL] [List.replicate r 2, List.replicate a 2, List.replicate m 3, R] :=
    Valid.cons (rep2_mk r) (Valid.cons (rep2_mk a) (Valid.cons (rep_t3 m) (Valid.cons hR (Valid.nil _))))
  have : znttLogic.Reach
      (hdR QN.X4 ([0] ++ List.replicate r 2 ++ 3 :: [1]) (List.replicate a 2 ++ 3 :: List.replicate m 3 ++ 1 :: R))
      (hdR QN.X4 ([0] ++ List.replicate r 3 ++ 3 :: [1]) (List.replicate a 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)) :=
    checkFF (env := [List.replicate r 2, List.replicate a 2, List.replicate m 3, R]) (E := []) (k := 200) hV trivial
      (ls := [.sym 0, .blk 0 .id, .sym 3, .sym 1])
      (rs := [.blk 1 .id, .sym 3, .blk 2 .id, .sym 1, .blk 3 .id])
      (ls' := [.sym 0, .blk 0 (.const 3), .sym 3, .sym 1])
      (rs' := [.blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq rfl ?_
  simp [List.replicate_succ', List.append_assoc]

/-- `D` after `a` cells of `P` have been counted: `a % d` marks. -/
def Dm (d a : Nat) : List Nat := [0] ++ List.replicate (a % d) 2 ++ List.replicate (d - a % d) 3 ++ [1]

theorem s2 (r : Nat) : List.replicate (r + 1) 2 = List.replicate r 2 ++ [2] := List.replicate_succ'
theorem s3 (k : Nat) : List.replicate (k + 1) 3 = 3 :: List.replicate k 3 := List.replicate_succ ..

theorem xLoop (d p : Nat) (hd : 2 ≤ d) (R : List Nat) (hR : Sym4 R) : ∀ g a, a + g = p →
    znttLogic.Reach
      (hdR QN.X4 (Dm d a) (List.replicate a 2 ++ List.replicate (p - a) 3 ++ 1 :: R))
      (hdR QN.X4 (Dm d p) (List.replicate p 2 ++ 1 :: R)) := by
  intro g
  induction g with
  | zero =>
    intro a ha
    obtain rfl : a = p := by omega
    exact (LTM.Reach.refl _ _).of_eq (by simp) rfl
  | succ g ih =>
    intro a ha
    obtain ⟨m, hm⟩ : ∃ m, p - a = m + 1 := ⟨p - a - 1, by omega⟩
    have hlt : a % d < d := Nat.mod_lt _ (by omega)
    have hsm := ZP.F.succ_mod a d hd
    have h2 := ih (a + 1) (by omega)
    have e : p - (a + 1) = m := by omega
    rw [e] at h2
    by_cases hc : a % d + 1 < d
    · obtain ⟨k, hk⟩ : ∃ k, d - a % d = k + 2 := ⟨d - a % d - 2, by omega⟩
      have h1 := xIterA (a % d) k a m R hR
      have e2 : (a + 1) % d = a % d + 1 := by rw [hsm]; simp [hc]
      have e3 : d - (a % d + 1) = k + 1 := by omega
      have eA : hdR QN.X4 (Dm d a) (List.replicate a 2 ++ List.replicate (p - a) 3 ++ 1 :: R)
          = hdR QN.X4 ([0] ++ List.replicate (a % d) 2 ++ 3 :: 3 :: List.replicate k 3 ++ [1])
            (List.replicate a 2 ++ 3 :: List.replicate m 3 ++ 1 :: R) := by
        unfold Dm
        rw [hk, hm]
        simp [List.replicate_succ, List.append_assoc]
      have eB : hdR QN.X4 ([0] ++ List.replicate (a % d) 2 ++ 2 :: 3 :: List.replicate k 3 ++ [1])
            (List.replicate a 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)
          = hdR QN.X4 (Dm d (a + 1)) (List.replicate (a + 1) 2 ++ List.replicate m 3 ++ 1 :: R) := by
        unfold Dm
        rw [e2, e3]
        simp only [s2, s3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
      rw [eA]
      refine h1.trans ?_
      rw [eB]
      exact h2
    · have hd1 : d - a % d = 1 := by omega
      have h1 := xIterB (a % d) a m R hR
      have e2 : (a + 1) % d = 0 := by rw [hsm]; simp [hc]
      have eA : hdR QN.X4 (Dm d a) (List.replicate a 2 ++ List.replicate (p - a) 3 ++ 1 :: R)
          = hdR QN.X4 ([0] ++ List.replicate (a % d) 2 ++ 3 :: [1])
            (List.replicate a 2 ++ 3 :: List.replicate m 3 ++ 1 :: R) := by
        unfold Dm
        rw [hd1, hm]
        simp [List.replicate_succ, List.append_assoc]
      have ed : a % d + 1 = d := by omega
      have eB : hdR QN.X4 ([0] ++ List.replicate (a % d + 1) 3 ++ [1])
            (List.replicate a 2 ++ 2 :: List.replicate m 3 ++ 1 :: R)
          = hdR QN.X4 (Dm d (a + 1)) (List.replicate (a + 1) 2 ++ List.replicate m 3 ++ 1 :: R) := by
        unfold Dm
        rw [e2, ed]
        simp only [s2, s3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, Nat.sub_self, Nat.sub_zero, List.replicate_zero]
      rw [eA]
      refine h1.trans ?_
      rw [eB]
      exact h2

/-- `P` is used up: unmark it and look at `D`. -/
theorem xEnd (r s p : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hdR QN.X4 ([0] ++ List.replicate r 2 ++ List.replicate s 3 ++ [1]) (List.replicate p 2 ++ 1 :: R))
      (hd QN.XD ([0] ++ List.replicate r 2 ++ List.replicate s 3) (1 :: List.replicate p 3 ++ 1 :: R)) := by
  have hV : Valid [Mk, T3, Mk, ALL] [List.replicate r 2, List.replicate s 3, List.replicate p 2, R] :=
    Valid.cons (rep2_mk r) (Valid.cons (rep_t3 s) (Valid.cons (rep2_mk p) (Valid.cons hR (Valid.nil _))))
  exact checkFT (env := [List.replicate r 2, List.replicate s 3, List.replicate p 2, R]) (E := []) (k := 200) hV trivial
    (ls := [.sym 0, .blk 0 .id, .blk 1 .id, .sym 1]) (rs := [.blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 0, .blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 1, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- No mark in `D`: `d` divides `p`, the candidate is composite; erase `D` and its separator. -/
theorem xComposite (s p : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QN.XD ([0] ++ List.replicate s 3) (1 :: List.replicate p 3 ++ 1 :: R))
      (hdR QN.PA0 (0 :: List.replicate s 0 ++ [0]) (List.replicate p 3 ++ 1 :: R)) := by
  have hV : Valid [T3, T3, ALL] [List.replicate s 3, List.replicate p 3, R] :=
    Valid.cons (rep_t3 s) (Valid.cons (rep_t3 p) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [List.replicate s 3, List.replicate p 3, R]) (E := []) (k := 200) hV trivial
    (ls := [.sym 0, .blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.sym 0, .blk 0 (.const 0), .sym 0]) (rs' := [.blk 1 .id, .sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## The decrement of `d`, entered from `XD` -/

theorem xs2Dec2 (a b : Nat) (R : List Nat) (ha : a ∈ bits) (hb : b ∈ bits) (hR : Sym4 R) :
    znttLogic.Reach (hdR QN.XS2 [0] ([a, b] ++ 1 :: R)) (hd QN.WX [0, 0, 3] (1 :: R)) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  rcases mem_bits ha with rfl | rfl <;> rcases mem_bits hb with rfl | rfl
  · exact checkFT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 2, .sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 3, .sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 2, .sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFT (env := [R]) (E := []) (k := 12) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 3, .sym 1, .blk 0 .id])
      (ls' := [.sym 0, .sym 0, .sym 3]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xs2DecN (a b c : Nat) (Dt R : List Nat) (ha : a ∈ bits) (hb : b ∈ bits) (hc : c ∈ bits)
    (hD : Bits Dt) (hR : Sym4 R) :
    znttLogic.Reach (hdR QN.XS2 [0] (a :: b :: c :: Dt ++ 1 :: R))
      (hdR QN.X4 ([0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) R) := by
  have hV : Valid [bits, ALL] [Dt, R] := Valid.cons hD (Valid.cons hR (Valid.nil _))
  rcases mem_bits ha with rfl | rfl <;> rcases mem_bits hb with rfl | rfl <;> rcases mem_bits hc with rfl | rfl
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 2, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 2, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 3, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .sym 3, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 2, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 2, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 3, .sym 2, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Dt, R]) (E := []) (k := 20) (q' := QN.X4) (A' := [0, 0, 3, 3] ++ List.replicate Dt.length 3 ++ [1]) (R' := R) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .sym 3, .sym 3, .blk 0 .id, .sym 1, .blk 1 .id])
      (ls' := [.sym 0, .sym 0, .sym 3, .sym 3, .blk 0 (.const 3), .sym 1]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- A mark in `D`: `d` does not divide `p`; go to the first cell of `D` and decrement. -/
theorem xdMarked (r s p : Nat) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QN.XD ([0] ++ List.replicate (r + 1) 2 ++ List.replicate s 3) (1 :: List.replicate p 3 ++ 1 :: R))
      (hdR QN.XS2 [0] (List.replicate (r + 1) 2 ++ List.replicate s 3 ++ 1 :: (List.replicate p 3 ++ 1 :: R))) := by
  have hV : Valid [Mk, T3, T3, ALL] [List.replicate r 2, List.replicate s 3, List.replicate p 3, R] :=
    Valid.cons (rep2_mk r) (Valid.cons (rep_t3 s) (Valid.cons (rep_t3 p) (Valid.cons hR (Valid.nil _))))
  have : znttLogic.Reach (hd QN.XD ([0] ++ List.replicate r 2 ++ 2 :: List.replicate s 3) (1 :: List.replicate p 3 ++ 1 :: R))
      (hdR QN.XS2 [0] (List.replicate r 2 ++ 2 :: List.replicate s 3 ++ 1 :: (List.replicate p 3 ++ 1 :: R))) :=
    checkTF (env := [List.replicate r 2, List.replicate s 3, List.replicate p 3, R]) (E := []) (k := 200) hV trivial
      (ls := [.sym 0, .blk 0 .id, .sym 2, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
      (ls' := [.sym 0]) (rs' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ', List.append_assoc]) ?_
  simp [List.replicate_succ', List.append_assoc]

theorem bits_Dl (r s : Nat) : Bits (List.replicate r 2 ++ List.replicate s 3) := fun a ha => by
  rcases List.mem_append.1 ha with ha | ha
  · rw [List.eq_of_mem_replicate ha]; simp [bits]
  · rw [List.eq_of_mem_replicate ha]; simp [bits]

theorem zeros_B0 (k : Nat) : ∀ a ∈ List.replicate k 0, a ∈ ZP.F.B0 := fun a ha => by
  rw [List.eq_of_mem_replicate ha]; simp [ZP.F.B0]

/-- The state before testing the divisor `d`: `D` is `d` unmarked cells, `P` is unmarked. -/
def TD (d p : Nat) (R : List Nat) : ZC :=
  hdR QN.X4 ([0] ++ List.replicate d 3 ++ [1]) (List.replicate p 3 ++ 1 :: R)

/-- `d` divides `p`: composite. -/
theorem dStepA (d p : Nat) (hd : 2 ≤ d) (hdv : p % d = 0) (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (TD d p R) (hdR QN.PA0 [] (List.replicate p 3 ++ 1 :: R)) := by
  have h1 := xLoop d p hd R hR p 0 (by omega)
  have h2 := xEnd (p % d) (d - p % d) p R hR
  rw [hdv] at h2
  have h3 := xComposite (d - 0) p R hR
  have e1 : hdR QN.X4 (Dm d 0) (List.replicate 0 2 ++ List.replicate (p - 0) 3 ++ 1 :: R) = TD d p R := by
    simp [Dm, TD]
  have e2 : hdR QN.X4 (Dm d p) (List.replicate p 2 ++ 1 :: R)
      = hdR QN.X4 ([0] ++ List.replicate 0 2 ++ List.replicate (d - 0) 3 ++ [1]) (List.replicate p 2 ++ 1 :: R) := by
    simp [Dm, hdv]
  rw [e1] at h1
  rw [e2] at h1
  have h4 := (h1.trans h2).trans h3
  refine h4.of_eq rfl ?_
  have := ZP.F.hdR_zeros QN.PA0 (0 :: List.replicate (d - 0) 0 ++ [0]) [] (List.replicate p 3 ++ 1 :: R)
    (fun a ha => by
      simp at ha
      rcases ha with rfl | ⟨-, rfl⟩ | rfl <;> simp [ZP.F.B0])
  simpa using this

end ZP.N
