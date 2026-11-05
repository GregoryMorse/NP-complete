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

end ZP.N
