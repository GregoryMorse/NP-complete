module

public import ZP.PairN

@[expose] public section

/-! # The pair lemma of the NTT machine, part 2: the record build -/

namespace ZP.N

open ZP ZP.G

/-- `WX..WC0`: `W := 33`, the head returns to the last cell of `C`. -/
theorem wxStart (p c' n : Nat) :
    znttLogic.Reach
      (hd QN.WX [0, 3] (1 :: List.replicate p 3 ++ 1 :: (Yc (c' + 1) n ++ [0])))
      (hd QN.RC1 ([3, 3, 1] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ List.replicate c' 3 ++ [3])
        (1 :: List.replicate n 3 ++ [0])) := by
  have hV : Valid [T3, T3, T3] [List.replicate p 3, List.replicate c' 3, List.replicate n 3] :=
    Valid.cons (rep_t3 p) (Valid.cons (rep_t3 c') (Valid.cons (rep_t3 n) (Valid.nil _)))
  have : znttLogic.Reach (hd QN.WX [0, 3] ([1] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ List.replicate c' 3 ++ [3, 1] ++ List.replicate n 3 ++ [0]))
      (hd QN.RC1 ([3, 3, 1] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ List.replicate c' 3 ++ [3])
        ([1] ++ List.replicate n 3 ++ [0])) :=
    checkTT (env := [List.replicate p 3, List.replicate c' 3, List.replicate n 3]) (E := []) (k := 60) hV trivial
    (ls := [.sym 0, .sym 3])
    (rs := [.sym 1, .blk 0 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .blk 1 .id, .sym 3, .sym 1, .blk 2 .id, .sym 0]) (A := [0,3])
    (ls' := [.sym 3, .sym 3, .sym 1, .blk 0 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .blk 1 .id, .sym 3])
    (rs' := [.sym 1, .blk 2 .id, .sym 0])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · simp [Yc, List.replicate_succ', List.append_assoc]
  · simp [List.append_assoc]

/-! ## Copying a ruler into a new field -/

theorem rep2_mk' (k : Nat) : ∀ a ∈ List.replicate k 2, a ∈ Mk := rep2_mk k

/-- One round of the copy loop: the next unmarked ruler cell is marked, a `0` is appended. -/
theorem cpIter (A B : List Nat) (hA : ∀ a ∈ A, a ∈ O13) (hB : NoB B) (j m : Nat) :
    znttLogic.Reach
      (hdR QN.CW0 (A ++ List.replicate (j + 2) 2) (List.replicate (m + 1) 3 ++ 1 :: B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.CW0 (A ++ List.replicate (j + 3) 2) (List.replicate m 3 ++ 1 :: B ++ [1, 3] ++ List.replicate (j + 1) 2)) := by
  have hV : Valid [O13, Mk, T3, NB] [A, List.replicate j 2, List.replicate m 3, B] :=
    Valid.cons hA (Valid.cons (rep2_mk j) (Valid.cons (rep_t3 m) (Valid.cons hB (Valid.nil _))))
  have : znttLogic.Reach
      (hdR QN.CW0 (A ++ [2, 2] ++ List.replicate j 2) ([3] ++ List.replicate m 3 ++ 1 :: B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.CW0 (A ++ [2, 2] ++ List.replicate j 2 ++ [2]) (List.replicate m 3 ++ 1 :: B ++ [1, 3] ++ List.replicate j 2 ++ [2])) :=
    checkFF (env := [A, List.replicate j 2, List.replicate m 3, B]) (E := []) (k := 80) hV trivial
      (ls := [.blk 0 .id, .sym 2, .sym 2, .blk 1 .id])
      (rs := [.sym 3, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 2, .sym 2, .blk 1 .id, .sym 2])
      (rs' := [.blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 3, .blk 1 .id, .sym 2])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · simp [List.replicate_succ, List.append_assoc]
  · have e1 : List.replicate (j + 1) 2 = List.replicate j 2 ++ [2] := List.replicate_succ' ..
    have e2 : List.replicate (j + 3) 2 = [2, 2] ++ List.replicate j 2 ++ [2] := by
      show List.replicate (j + 1 + 1 + 1) 2 = _
      rw [List.replicate_succ, List.replicate_succ, e1]; simp
    rw [e2, e1]
    simp [List.append_assoc]

/-- The first marked cell is copied: write the first `1` of the copy, mark the second ruler cell. -/
theorem cpStart (A B : List Nat) (hA : ∀ a ∈ A, a ∈ O13) (hB : NoB B) (m : Nat) :
    znttLogic.Reach
      (hdR QN.SW3 (A ++ [2]) (List.replicate (m + 1) 3 ++ 1 :: B ++ [1]))
      (hdR QN.CW0 (A ++ [2, 2]) (List.replicate m 3 ++ 1 :: B ++ [1, 3])) := by
  have hV : Valid [O13, T3, NB] [A, List.replicate m 3, B] :=
    Valid.cons hA (Valid.cons (rep_t3 m) (Valid.cons hB (Valid.nil _)))
  have : znttLogic.Reach
      (hdR QN.SW3 (A ++ [2]) ([3] ++ List.replicate m 3 ++ 1 :: B ++ [1]))
      (hdR QN.CW0 (A ++ [2, 2]) (List.replicate m 3 ++ 1 :: B ++ [1, 3])) :=
    checkFF (env := [A, List.replicate m 3, B]) (E := []) (k := 80) hV trivial
      (ls := [.blk 0 .id, .sym 2])
      (rs := [.sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1])
      (ls' := [.blk 0 .id, .sym 2, .sym 2])
      (rs' := [.blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 3])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl

/-- End of the copy of `P`: restore the ruler, step onto it, `KX1`. -/
theorem cpEndP (A B : List Nat) (hA : ∀ a ∈ A, a ∈ O13) (hB : NoB B) (j : Nat) :
    znttLogic.Reach
      (hdR QN.CW0 (A ++ [1] ++ List.replicate (j + 2) 2) (1 :: B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.KX1 (A ++ [1]) (List.replicate (j + 2) 3 ++ 1 :: B ++ [1, 3] ++ List.replicate (j + 1) 2)) := by
  have hV : Valid [O13, Mk, NB] [A, List.replicate j 2, B] :=
    Valid.cons hA (Valid.cons (rep2_mk j) (Valid.cons hB (Valid.nil _)))
  have : znttLogic.Reach
      (hdR QN.CW0 (A ++ [1, 2, 2] ++ List.replicate j 2) ([1] ++ B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.KX1 (A ++ [1]) (List.replicate j 3 ++ [3, 3] ++ [1] ++ B ++ [1, 3] ++ List.replicate j 2 ++ [2])) :=
    checkFF (env := [A, List.replicate j 2, B]) (E := []) (k := 80) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 2, .sym 2, .blk 1 .id])
      (rs := [.sym 1, .blk 2 .id, .sym 1, .sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1])
      (rs' := [.blk 1 (.const 3), .sym 3, .sym 3, .sym 1, .blk 2 .id, .sym 1, .sym 3, .blk 1 .id, .sym 2])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  have e1 : List.replicate (j + 1) 2 = List.replicate j 2 ++ [2] := List.replicate_succ' ..
  have e2 : List.replicate (j + 2) 3 = List.replicate j 3 ++ [3, 3] := by
    show List.replicate (j + 1 + 1) 3 = _
    rw [List.replicate_succ', List.replicate_succ']; simp
  rw [e2, e1]
  simp [List.append_assoc]

/-- End of the copy of `W`: restore the ruler, and add the new cell at the left edge. -/
theorem cpEndW (B : List Nat) (hB : NoB B) (j : Nat) :
    znttLogic.Reach
      (hdR QN.CW0 (List.replicate (j + 2) 2) (1 :: B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.RN0 [3] (List.replicate (j + 2) 3 ++ 1 :: B ++ [1, 3] ++ List.replicate (j + 1) 2)) := by
  have hV : Valid [Mk, NB] [List.replicate j 2, B] :=
    Valid.cons (rep2_mk j) (Valid.cons hB (Valid.nil _))
  have : znttLogic.Reach
      (hdR QN.CW0 ([2, 2] ++ List.replicate j 2) ([1] ++ B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.RN0 [3] (List.replicate j 3 ++ [3, 3] ++ [1] ++ B ++ [1, 3] ++ List.replicate j 2 ++ [2])) :=
    checkFF (env := [List.replicate j 2, B]) (E := []) (k := 80) hV trivial
      (ls := [.sym 2, .sym 2, .blk 0 .id])
      (rs := [.sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 0 .id])
      (ls' := [.sym 3])
      (rs' := [.blk 0 (.const 3), .sym 3, .sym 3, .sym 1, .blk 1 .id, .sym 1, .sym 3, .blk 0 .id, .sym 2])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  have e1 : List.replicate (j + 1) 2 = List.replicate j 2 ++ [2] := List.replicate_succ' ..
  have e2 : List.replicate (j + 2) 3 = List.replicate j 3 ++ [3, 3] := by
    show List.replicate (j + 1 + 1) 3 = _
    rw [List.replicate_succ', List.replicate_succ']; simp
  rw [e2, e1]
  simp [List.append_assoc]

theorem cpLoop (A B : List Nat) (hA : ∀ a ∈ A, a ∈ O13) (hB : NoB B) : ∀ d j,
    znttLogic.Reach
      (hdR QN.CW0 (A ++ List.replicate (j + 2) 2) (List.replicate d 3 ++ 1 :: B ++ [1, 3] ++ List.replicate j 2))
      (hdR QN.CW0 (A ++ List.replicate (j + d + 2) 2) (1 :: B ++ [1, 3] ++ List.replicate (j + d) 2)) := by
  intro d
  induction d with
  | zero => intro j; exact LTM.Reach.refl _ _
  | succ d ih =>
    intro j
    have h1 := cpIter A B hA hB j d
    have h2 := ih (j + 1)
    refine (h1.of_eq rfl rfl).trans (h2.of_eq ?_ ?_)
    · rw [show j + 1 + 2 = j + 3 by omega]
    · rw [show j + 1 + d + 2 = j + (d + 1) + 2 by omega, show j + 1 + d = j + (d + 1) by omega]

/-- Copy of the ruler `P` (size `s + 2`) behind the partial record. -/
theorem copyP (A0 B : List Nat) (hA0 : ∀ a ∈ A0, a ∈ O13) (hB : NoB B) (s : Nat) :
    znttLogic.Reach
      (hdR QN.SW3 (A0 ++ [1] ++ [2]) (List.replicate (s + 1) 3 ++ 1 :: B ++ [1]))
      (hdR QN.KX1 (A0 ++ [1]) (List.replicate (s + 2) 3 ++ 1 :: B ++ [1, 3] ++ List.replicate (s + 1) 2)) := by
  have hA : ∀ a ∈ A0 ++ [1], a ∈ O13 := fun a ha => by
    rcases List.mem_append.1 ha with h | h
    · exact hA0 a h
    · simp at h; subst h; simp [O13]
  have h1 := cpStart (A0 ++ [1]) B hA hB s
  have h2 : znttLogic.Reach
      (hdR QN.CW0 (A0 ++ [1] ++ [2, 2]) (List.replicate s 3 ++ 1 :: B ++ [1, 3]))
      (hdR QN.CW0 (A0 ++ [1] ++ List.replicate (s + 2) 2) (1 :: B ++ [1, 3] ++ List.replicate s 2)) :=
    (cpLoop (A0 ++ [1]) B hA hB s 0).of_eq (by simp) (by simp [Nat.zero_add])
  have h3 := cpEndP A0 B hA0 hB s
  exact h1.trans (h2.trans h3)

/-- Copy of the ruler `W` (size `s + 2`) behind the partial record; `W` grows. -/
theorem copyW (B : List Nat) (hB : NoB B) (s : Nat) :
    znttLogic.Reach
      (hdR QN.SW3 [2] (List.replicate (s + 1) 3 ++ 1 :: B ++ [1]))
      (hdR QN.RN0 [3] (List.replicate (s + 2) 3 ++ 1 :: B ++ [1, 3] ++ List.replicate (s + 1) 2)) := by
  have h1 := cpStart [] B (by simp) hB s
  have h2 : znttLogic.Reach
      (hdR QN.CW0 ([] ++ [2, 2]) (List.replicate s 3 ++ 1 :: B ++ [1, 3]))
      (hdR QN.CW0 (List.replicate (s + 2) 2) (1 :: B ++ [1, 3] ++ List.replicate s 2)) :=
    (cpLoop [] B (by simp) hB s 0).of_eq (by simp) (by simp [Nat.zero_add])
  have h3 := cpEndW B hB s
  exact (h1.of_eq (by simp) rfl).trans (h2.trans h3)

end ZP.N
