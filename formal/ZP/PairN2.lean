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

theorem reach_trans_eq {a b c d : ZC} (h1 : znttLogic.Reach a b) (h2 : znttLogic.Reach c d) (e : b = c) :
    znttLogic.Reach a d := by
  subst e; exact h1.trans h2

theorem hd_trail (q : Nat) (A X : List Nat) : hd q A (X ++ [0]) = hd q A X := by
  rw [hd_eq', hd_eq', ZP.sapp_append]
  have h0 : sapp [0] blank = blank := ZP.F.sapp_zeros 1
  rw [h0]

/-! ## One record: header, three copies of `P`, one copy of `W` -/

/-- A new header `MM 0 1 0` is appended behind the records, the head goes to the first cell of `K`. -/
theorem recHdr (w p cA cM nA nM : Nat) (Rs : List Nat) (hRs : NoB Rs) :
    znttLogic.Reach
      (hd QN.RN2 (List.replicate w 3 ++ 1 :: List.replicate p 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ List.replicate cM 2)
        ++ 1 :: (List.replicate nA 3 ++ [3] ++ List.replicate nM 2)) Rs)
      (hdR QN.KX2 (List.replicate w 3 ++ 1 :: List.replicate p 3 ++ [1])
        ([3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ List.replicate cM 2)
        ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2) ++ Rs ++ [1, 1, 2, 3, 2])) := by
  have hV : Valid [T3, T3, T3, Mk, T3, Mk, NB]
      [List.replicate w 3, List.replicate p 3, List.replicate cA 3, List.replicate cM 2, List.replicate nA 3,
        List.replicate nM 2, Rs] :=
    Valid.cons (rep_t3 w) (Valid.cons (rep_t3 p) (Valid.cons (rep_t3 cA) (Valid.cons (rep2_mk cM)
      (Valid.cons (rep_t3 nA) (Valid.cons (rep2_mk nM) (Valid.cons hRs (Valid.nil _)))))))
  have : znttLogic.Reach
      (hd QN.RN2 (List.replicate w 3 ++ [1] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ List.replicate cA 3 ++ List.replicate cM 2
        ++ [1] ++ List.replicate nA 3 ++ [3] ++ List.replicate nM 2) Rs)
      (hdR QN.KX2 (List.replicate w 3 ++ [1] ++ List.replicate p 3 ++ [1])
        ([3, 3, 3, 1] ++ List.replicate cA 3 ++ List.replicate cM 2
        ++ [1] ++ List.replicate nA 3 ++ [2] ++ List.replicate nM 2 ++ Rs ++ [1, 1, 2, 3, 2])) :=
    checkTF (env := [List.replicate w 3, List.replicate p 3, List.replicate cA 3, List.replicate cM 2,
        List.replicate nA 3, List.replicate nM 2, Rs]) (E := []) (k := 300) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .blk 2 .id, .blk 3 .id,
        .sym 1, .blk 4 .id, .sym 3, .blk 5 .id])
      (rs := [.blk 6 .id])
      (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1])
      (rs' := [.sym 3, .sym 3, .sym 3, .sym 1, .blk 2 .id, .blk 3 .id, .sym 1, .blk 4 .id, .sym 2, .blk 5 .id,
        .blk 6 .id, .sym 1, .sym 1, .sym 2, .sym 3, .sym 2])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.append_assoc]) (by simp [List.append_assoc])

/-- Entry of one `P`-copy: mark the next cell of `K`, open a new field, mark the first cell of `P`. -/
theorem kEntry (w s k m : Nat) (T : List Nat) (hT : NoB T) :
    znttLogic.Reach
      (hdR QN.KX2 (List.replicate w 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1])
        (List.replicate k 2 ++ 3 :: List.replicate m 3 ++ 1 :: T))
      (hdR QN.SW3 (List.replicate w 3 ++ [1] ++ [2])
        (List.replicate (s + 1) 3 ++ 1 :: (List.replicate k 2 ++ 2 :: List.replicate m 3 ++ 1 :: T) ++ [1])) := by
  have hV : Valid [T3, T3, Mk, T3, NB]
      [List.replicate w 3, List.replicate s 3, List.replicate k 2, List.replicate m 3, T] :=
    Valid.cons (rep_t3 w) (Valid.cons (rep_t3 s) (Valid.cons (rep2_mk k) (Valid.cons (rep_t3 m)
      (Valid.cons hT (Valid.nil _)))))
  have : znttLogic.Reach
      (hdR QN.KX2 (List.replicate w 3 ++ [1] ++ [3, 3] ++ List.replicate s 3 ++ [1])
        (List.replicate k 2 ++ [3] ++ List.replicate m 3 ++ [1] ++ T))
      (hdR QN.SW3 (List.replicate w 3 ++ [1] ++ [2])
        ([3] ++ List.replicate s 3 ++ [1] ++ List.replicate k 2 ++ [2] ++ List.replicate m 3 ++ [1] ++ T ++ [1])) :=
    checkFF (env := [List.replicate w 3, List.replicate s 3, List.replicate k 2, List.replicate m 3, T])
      (E := []) (k := 300) hV trivial
      (ls := [.blk 0 .id, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1])
      (rs := [.blk 2 .id, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 2])
      (rs' := [.sym 3, .blk 1 .id, .sym 1, .blk 2 .id, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  simp [List.replicate_succ, List.append_assoc]

theorem skipP (w s : Nat) (X : List Nat) (hX : NoB X) :
    znttLogic.Reach
      (hdR QN.KX1 (List.replicate w 3 ++ [1]) (List.replicate (s + 2) 3 ++ 1 :: X))
      (hdR QN.KX2 (List.replicate w 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1]) X) := by
  have hV : Valid [T3, T3, NB] [List.replicate w 3, List.replicate s 3, X] :=
    Valid.cons (rep_t3 w) (Valid.cons (rep_t3 s) (Valid.cons hX (Valid.nil _)))
  have : znttLogic.Reach
      (hdR QN.KX1 (List.replicate w 3 ++ [1]) ([3, 3] ++ List.replicate s 3 ++ [1] ++ X))
      (hdR QN.KX2 (List.replicate w 3 ++ [1] ++ [3, 3] ++ List.replicate s 3 ++ [1]) X) :=
    checkFF (env := [List.replicate w 3, List.replicate s 3, X]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 3, .sym 3, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  simp [List.replicate_succ, List.append_assoc]

theorem noB_rep (k a : Nat) (h : a ∈ NB) : NoB (List.replicate k a) := fun x hx => by
  rw [List.eq_of_mem_replicate hx]; exact h

theorem noB_app {u v : List Nat} (hu : NoB u) (hv : NoB v) : NoB (u ++ v) := fun x hx => by
  rcases List.mem_append.1 hx with h | h
  · exact hu x h
  · exact hv x h

/-- One `P`-copy: the next cell of `K` is marked and a copy of `P` is appended. -/
theorem kIter (w s k m : Nat) (T : List Nat) (hT : NoB T) :
    znttLogic.Reach
      (hdR QN.KX2 (List.replicate w 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1])
        (List.replicate k 2 ++ 3 :: List.replicate m 3 ++ 1 :: T))
      (hdR QN.KX2 (List.replicate w 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1])
        (List.replicate (k + 1) 2 ++ List.replicate m 3 ++ 1 :: T ++ [1, 3] ++ List.replicate (s + 1) 2)) := by
  have hB : NoB (List.replicate k 2 ++ 2 :: List.replicate m 3 ++ 1 :: T) := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
    rcases hx with (⟨_, rfl⟩ | rfl | ⟨_, rfl⟩) | rfl | hx
    · simp [NB]
    · simp [NB]
    · simp [NB]
    · simp [NB]
    · exact hT x hx
  have h1 := kEntry w s k m T hT
  have h2 := copyP (List.replicate w 3) (List.replicate k 2 ++ 2 :: List.replicate m 3 ++ 1 :: T)
    (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [O13]) hB s
  have hX : NoB (List.replicate k 2 ++ 2 :: List.replicate m 3 ++ 1 :: T ++ [1, 3] ++ List.replicate (s + 1) 2) := by
    refine noB_app (noB_app hB (fun x hx => ?_)) (noB_rep _ _ (by simp [NB]))
    simp at hx; rcases hx with rfl | rfl <;> simp [NB]
  have h3 := skipP w s _ hX
  refine h1.trans (h2.trans (h3.of_eq ?_ ?_))
  · simp [List.append_assoc]
  · simp [List.replicate_succ', List.append_assoc]

/-- `K` has been used up: restore it, mark the first cell of `W` to copy it. -/
theorem kEnd (u s : Nat) (T : List Nat) (hT : NoB T) :
    znttLogic.Reach
      (hdR QN.KX2 (List.replicate (u + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1]) ([2, 2, 2] ++ 1 :: T))
      (hdR QN.SW3 [2]
        (List.replicate (u + 1) 3 ++ 1 :: (List.replicate (s + 2) 3 ++ [1, 3, 3, 3, 1] ++ T) ++ [1])) := by
  have hV : Valid [T3, T3, NB] [List.replicate u 3, List.replicate s 3, T] :=
    Valid.cons (rep_t3 u) (Valid.cons (rep_t3 s) (Valid.cons hT (Valid.nil _)))
  have : znttLogic.Reach
      (hdR QN.KX2 ([3, 3] ++ List.replicate u 3 ++ [1] ++ [3, 3] ++ List.replicate s 3 ++ [1]) ([2, 2, 2, 1] ++ T))
      (hdR QN.SW3 [2]
        ([3] ++ List.replicate u 3 ++ [1] ++ [3, 3] ++ List.replicate s 3 ++ [1, 3, 3, 3, 1] ++ T ++ [1])) :=
    checkFF (env := [List.replicate u 3, List.replicate s 3, T]) (E := []) (k := 300) hV trivial
      (ls := [.sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1])
      (rs := [.sym 2, .sym 2, .sym 2, .sym 1, .blk 2 .id])
      (ls' := [.sym 2])
      (rs' := [.sym 3, .blk 0 .id, .sym 1, .sym 3, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1,
        .blk 2 .id, .sym 1])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  simp [List.replicate_succ, List.append_assoc]

theorem noB_nil : NoB [] := fun x hx => by simp at hx

theorem noB_cons' {a : Nat} {l : List Nat} (ha : a ∈ NB) (h : NoB l) : NoB (a :: l) := fun x hx => by
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact h x hx

macro "noB_tac" : tactic =>
  `(tactic| repeat (first | assumption | exact noB_nil | apply noB_cons' (by simp [NB] <;> omega) | apply noB_app | apply noB_rep _ _ (by simp [NB]) | exact noB_Fld _))

/-- A copy field of width `s + 2`: `M 1 0^(s+1)`. -/
def Fld (s : Nat) : List Nat := [1, 3] ++ List.replicate (s + 1) 2

theorem noB_Fld (s : Nat) : NoB (Fld s) := by
  intro x hx
  simp only [Fld, List.mem_append, List.mem_cons, List.mem_replicate] at hx
  rcases hx with (h | h) | ⟨_, h⟩ <;> simp_all [NB]

/-- The whole record: header and four fields. -/
def Rec3 (o s u : Nat) : List Nat := [1, 1, 2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u

theorem recBuild (u s cA cM nA nM : Nat) (Rs : List Nat) (hRs : NoB Rs) :
    znttLogic.Reach
      (hd QN.RN2 (List.replicate (u + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ List.replicate cM 2)
        ++ 1 :: (List.replicate nA 3 ++ [3] ++ List.replicate nM 2)) Rs)
      (hdR QN.RN0 [3] (List.replicate (u + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ List.replicate cM 2)
        ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2) ++ Rs ++ Rec3 3 s u)) := by
  have hT0 : NoB ((List.replicate cA 3 ++ List.replicate cM 2) ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2)
      ++ Rs ++ [1, 1, 2, 3, 2]) := by noB_tac
  have hF : NoB (Fld s) := noB_Fld s
  have hT1 : NoB (((List.replicate cA 3 ++ List.replicate cM 2) ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2)
      ++ Rs ++ [1, 1, 2, 3, 2]) ++ Fld s) := by noB_tac
  have hT2 : NoB (((List.replicate cA 3 ++ List.replicate cM 2) ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2)
      ++ Rs ++ [1, 1, 2, 3, 2]) ++ Fld s ++ Fld s) := by noB_tac
  have hT3 : NoB (((List.replicate cA 3 ++ List.replicate cM 2) ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2)
      ++ Rs ++ [1, 1, 2, 3, 2]) ++ Fld s ++ Fld s ++ Fld s) := by noB_tac
  have h0 := recHdr (u + 2) (s + 2) cA cM nA nM Rs hRs
  have h1 := kIter (u + 2) s 0 2 _ hT0
  have h2 := kIter (u + 2) s 1 1 _ hT1
  have h3 := kIter (u + 2) s 2 0 _ hT2
  have h4 := kEnd u s _ hT3
  have h5 := copyW (List.replicate (s + 2) 3 ++ [1, 3, 3, 3, 1] ++ (((List.replicate cA 3 ++ List.replicate cM 2)
      ++ 1 :: (List.replicate nA 3 ++ [2] ++ List.replicate nM 2) ++ Rs ++ [1, 1, 2, 3, 2]) ++ Fld s ++ Fld s ++ Fld s))
    (by noB_tac) u
  refine reach_trans_eq (reach_trans_eq (reach_trans_eq (reach_trans_eq (reach_trans_eq h0 h1 ?_) h2 ?_) h3 ?_) h4 ?_) h5 ?_
    |>.of_eq ?_ ?_
  all_goals simp [Fld, Rec3, List.replicate_succ, List.append_assoc]

/-! ## Finding the last cell of `Nn` (`RN0`) and the flags of old records (`RO0`) -/

theorem rnFindsMr (a0 w p cM b ca a : Nat) (Y : List Nat) (hY : NoB Y) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2))) ([1, 1] ++ Y)) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk, NB] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, List.replicate a 3, List.replicate b 2, Y] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons hY (Valid.nil _)))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))) ([1, 1] ++ Y)) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, List.replicate a 3, List.replicate b 2, Y]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (rs' := [.sym 1, .sym 1, .blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem rnFindsMe (a0 w p cM b ca a : Nat) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2)))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2))) []) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, List.replicate a 3, List.replicate b 2] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.nil _))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))) []) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, List.replicate a 3, List.replicate b 2]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem rnFindsDr (a0 w p cM b ca : Nat) (Y : List Nat) (hY : NoB Y) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (b + 1) 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate (ca + 1) 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (b + 1) 2))) ([1, 1] ++ Y)) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk, NB] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, [], List.replicate b 2, Y] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons (fun x hx => by simp at hx) (Valid.cons (rep2_mk _) (Valid.cons hY (Valid.nil _)))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([2] ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([3] ++ List.replicate ca 3 ++ [2] ++ List.replicate cM 2) ++ [1] ++ ([2] ++ List.replicate b 2)))) ([1, 1] ++ Y)) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, List.replicate ca 3, List.replicate cM 2, [], List.replicate b 2, Y]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 2, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 3 .id, .sym 2, .blk 4 .id, .sym 1, .sym 2, .blk 6 .id])
      (rs' := [.sym 1, .sym 1, .blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem rnFindzMr (a0 w p cM b a : Nat) (Y : List Nat) (hY : NoB Y) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2))) ([1, 1] ++ Y)) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk, NB] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, List.replicate a 3, List.replicate b 2, Y] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (fun x hx => by simp at hx) (Valid.cons (rep2_mk _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons hY (Valid.nil _)))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))) ([1, 1] ++ Y)) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, List.replicate a 3, List.replicate b 2, Y]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (rs' := [.sym 1, .sym 1, .blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem rnFindzMe (a0 w p cM b a : Nat) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2)))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2))) []) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, List.replicate a 3, List.replicate b 2] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (fun x hx => by simp at hx) (Valid.cons (rep2_mk _) (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.nil _))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([3] ++ List.replicate a 3 ++ List.replicate b 2)))) []) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, List.replicate a 3, List.replicate b 2]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 3, .blk 5 .id, .blk 6 .id])
      (rs' := [])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem rnFindzDr (a0 w p cM b : Nat) (Y : List Nat) (hY : NoB Y) :
    znttLogic.Reach (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (b + 1) 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: ([2] ++ List.replicate cM 2) ++ 1 :: (List.replicate (b + 1) 2))) ([1, 1] ++ Y)) := by
  have hV : Valid [T3, T3, T3, T3, Mk, T3, Mk, NB] [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, [], List.replicate b 2, Y] := (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (rep_t3 _) (Valid.cons (fun x hx => by simp at hx) (Valid.cons (rep2_mk _) (Valid.cons (fun x hx => by simp at hx) (Valid.cons (rep2_mk _) (Valid.cons hY (Valid.nil _)))))))))
  have : znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3) (List.replicate w 3 ++ [1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([2] ++ List.replicate b 2) ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ ([1, 3] ++ List.replicate p 3 ++ [1, 3, 3, 3, 1] ++ ([2] ++ List.replicate cM 2) ++ [1] ++ ([2] ++ List.replicate b 2)))) ([1, 1] ++ Y)) :=
    checkFT (env := [List.replicate a0 3, List.replicate w 3, List.replicate p 3, [], List.replicate cM 2, [], List.replicate b 2, Y]) (E := []) (k := 2000) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 2, .blk 6 .id, .sym 1, .sym 1, .blk 7 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 2, .blk 4 .id, .sym 1, .sym 2, .blk 6 .id])
      (rs' := [.sym 1, .sym 1, .blk 7 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ, List.append_assoc]) (by simp [List.replicate_succ, List.append_assoc])

theorem roRec2 (A Z : List Nat) (hA : NoB A) (hZ : NoB Z) (s u : Nat) :
    znttLogic.Reach (hdR QN.RO0 A (Rec3 2 s u ++ Z)) (hdR QN.RO0 (A ++ Rec3 2 s u) Z) := by
  have hV : Valid [NB, Mk, Mk, NB] [A, List.replicate (s + 1) 2, List.replicate (u + 1) 2, Z] :=
    Valid.cons hA (Valid.cons (rep2_mk _) (Valid.cons (rep2_mk _) (Valid.cons hZ (Valid.nil _))))
  have : znttLogic.Reach
      (hdR QN.RO0 A ([1, 1, 2, 2, 2, 1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3]
        ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (u + 1) 2 ++ Z))
      (hdR QN.RO0 (A ++ ([1, 1, 2, 2, 2, 1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3]
        ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (u + 1) 2)) Z) :=
    checkFF (env := [A, List.replicate (s + 1) 2, List.replicate (u + 1) 2, Z]) (E := []) (k := 400) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 1 .id,
        .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3,
        .blk 1 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
      (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [Rec3, Fld, List.append_assoc]) (by simp [Rec3, Fld, List.append_assoc])

theorem roRec3 (A Z : List Nat) (hA : NoB A) (hZ : NoB Z) (s u : Nat) :
    znttLogic.Reach (hdR QN.RO0 A (Rec3 3 s u ++ Z)) (hdR QN.RO0 (A ++ Rec3 2 s u) Z) := by
  have hV : Valid [NB, Mk, Mk, NB] [A, List.replicate (s + 1) 2, List.replicate (u + 1) 2, Z] :=
    Valid.cons hA (Valid.cons (rep2_mk _) (Valid.cons (rep2_mk _) (Valid.cons hZ (Valid.nil _))))
  have : znttLogic.Reach
      (hdR QN.RO0 A ([1, 1, 2, 3, 2, 1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3]
        ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (u + 1) 2 ++ Z))
      (hdR QN.RO0 (A ++ ([1, 1, 2, 2, 2, 1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (s + 1) 2 ++ [1, 3]
        ++ List.replicate (s + 1) 2 ++ [1, 3] ++ List.replicate (u + 1) 2)) Z) :=
    checkFF (env := [A, List.replicate (s + 1) 2, List.replicate (u + 1) 2, Z]) (E := []) (k := 400) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.sym 1, .sym 1, .sym 2, .sym 3, .sym 2, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 1 .id,
        .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id, .blk 3 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 1, .sym 2, .sym 2, .sym 2, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3,
        .blk 1 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
      (rs' := [.blk 3 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [Rec3, Fld, List.append_assoc]) (by simp [Rec3, Fld, List.append_assoc])

def recsL (s : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (o, u) :: l => Rec3 o s u ++ recsL s l

theorem noB_Rec3 (o s u : Nat) (ho : o = 2 ∨ o = 3) : NoB (Rec3 o s u) := by
  have h1 := noB_Fld s
  have h2 := noB_Fld u
  have ho' : o ∈ NB := by rcases ho with rfl | rfl <;> simp [NB]
  unfold Rec3
  noB_tac

theorem noB_recsL (s : Nat) : ∀ l : List (Nat × Nat), (∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) → NoB (recsL s l)
  | [], _ => noB_nil
  | (o, u) :: l, h => noB_app (noB_Rec3 o s u (h _ (List.mem_cons_self ..)))
      (noB_recsL s l (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem roAll (s : Nat) : ∀ (l : List (Nat × Nat)) (A : List Nat), NoB A → (∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) →
    znttLogic.Reach (hdR QN.RO0 A (recsL s l))
      (hdR QN.RO0 (A ++ recsL s (l.map fun x => (2, x.2))) []) := by
  intro l
  induction l with
  | nil =>
    intro A _ _
    show znttLogic.Reach (hdR QN.RO0 A []) (hdR QN.RO0 (A ++ []) [])
    rw [List.append_nil]; exact LTM.Reach.refl _ _
  | cons x l ih =>
    intro A hA hl
    obtain ⟨o, u⟩ := x
    have ho := hl (o, u) (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x.1 = 2 ∨ x.1 = 3 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hZ := noB_recsL s l hl'
    have hR : NoB (A ++ Rec3 2 s u) := noB_app hA (noB_Rec3 2 s u (Or.inl rfl))
    have h2 := ih (A ++ Rec3 2 s u) hR hl'
    have h1 : znttLogic.Reach (hdR QN.RO0 A (Rec3 o s u ++ recsL s l)) (hdR QN.RO0 (A ++ Rec3 2 s u) (recsL s l)) := by
      rcases ho with rfl | rfl
      · exact roRec2 A _ hA hZ s u
      · exact roRec3 A _ hA hZ s u
    refine (h1.of_eq (by simp [recsL]) rfl).trans (h2.of_eq rfl ?_)
    simp [recsL, List.append_assoc]

theorem rnl (X : List Nat) (hX : NoB X) :
    znttLogic.Reach (hdR QN.RO0 X []) (hdR QN.RN0 [] X) := by
  have hV : Valid [NB] [X] := Valid.cons hX (Valid.nil _)
  exact checkFF (env := [X]) (E := []) (k := 40) hV trivial (ls := [.blk 0 .id]) (rs := [])
    (ls' := []) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Mark the last unmarked cell of `C`, sweep to the records. -/
theorem rc1Mark (A Zr : List Nat) (hA : NoB A) (hZ : NoB Zr) (a cM n' : Nat) :
    znttLogic.Reach
      (hd QN.RC1 (A ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate cM 2)) (1 :: 3 :: List.replicate n' 3 ++ Zr))
      (hdR QN.RO0 (A ++ 1 :: (List.replicate a 3 ++ [2] ++ List.replicate cM 2 ++ 1 :: 3 :: List.replicate n' 3)) Zr) := by
  have hV : Valid [NB, T3, Mk, T3, NB] [A, List.replicate a 3, List.replicate cM 2, List.replicate n' 3, Zr] :=
    Valid.cons hA (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons (rep_t3 _) (Valid.cons hZ (Valid.nil _)))))
  have : znttLogic.Reach
      (hd QN.RC1 (A ++ [1] ++ List.replicate a 3 ++ [3] ++ List.replicate cM 2) ([1, 3] ++ List.replicate n' 3 ++ Zr))
      (hdR QN.RO0 (A ++ [1] ++ List.replicate a 3 ++ [2] ++ List.replicate cM 2 ++ [1, 3] ++ List.replicate n' 3) Zr) :=
    checkTF (env := [A, List.replicate a 3, List.replicate cM 2, List.replicate n' 3, Zr]) (E := []) (k := 200) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 3, .blk 2 .id])
      (rs := [.sym 1, .sym 3, .blk 3 .id, .blk 4 .id])
      (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id])
      (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ', List.append_assoc]) (by simp [List.append_assoc])

/-- All cells of `Nn` are marked: unmark them, back to `C`. -/
theorem roundEnd (A Y : List Nat) (hA : NoB A) (hY : NoB Y) (a cM b : Nat) :
    znttLogic.Reach
      (hd QN.RN2 (A ++ 1 :: (List.replicate a 3 ++ [2] ++ List.replicate cM 2) ++ 1 :: List.replicate (b + 1) 2) (1 :: Y))
      (hd QN.RC1 (A ++ 1 :: (List.replicate a 3 ++ [2] ++ List.replicate cM 2))
        (1 :: List.replicate (b + 1) 3 ++ 1 :: Y)) := by
  have hV : Valid [NB, T3, Mk, Mk, NB] [A, List.replicate a 3, List.replicate cM 2, List.replicate b 2, Y] :=
    Valid.cons hA (Valid.cons (rep_t3 _) (Valid.cons (rep2_mk _) (Valid.cons (rep2_mk _) (Valid.cons hY (Valid.nil _)))))
  have : znttLogic.Reach
      (hd QN.RN2 (A ++ [1] ++ List.replicate a 3 ++ [2] ++ List.replicate cM 2 ++ [1, 2] ++ List.replicate b 2) ([1] ++ Y))
      (hd QN.RC1 (A ++ [1] ++ List.replicate a 3 ++ [2] ++ List.replicate cM 2)
        ([1, 3] ++ List.replicate b 3 ++ [1] ++ Y)) :=
    checkTT (env := [A, List.replicate a 3, List.replicate cM 2, List.replicate b 2, Y]) (E := []) (k := 200) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .blk 2 .id, .sym 1, .sym 2, .blk 3 .id])
      (rs := [.sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 2, .blk 2 .id])
      (rs' := [.sym 1, .sym 3, .blk 3 (.const 3), .sym 1, .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
  simp [List.replicate_succ, List.append_assoc]

/-- All cells of `C` are marked: unmark, on to the witness initialisation. -/
theorem rcuEnd (A X : List Nat) (hA : NoB A) (hX : NoB X) (c : Nat) :
    znttLogic.Reach
      (hd QN.RC1 (A ++ 1 :: List.replicate c 2) (1 :: X))
      (hd QN.WI0 (A ++ 1 :: List.replicate c 3) (1 :: X)) := by
  have hV : Valid [NB, Mk, NB] [A, List.replicate c 2, X] :=
    Valid.cons hA (Valid.cons (rep2_mk _) (Valid.cons hX (Valid.nil _)))
  have : znttLogic.Reach
      (hd QN.RC1 (A ++ [1] ++ List.replicate c 2) ([1] ++ X))
      (hd QN.WI0 (A ++ [1] ++ List.replicate c 3) ([1] ++ X)) :=
    checkTT (env := [A, List.replicate c 2, X]) (E := []) (k := 100) hV trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 1, .blk 1 (.const 3)]) (rs' := [.sym 1, .blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.append_assoc]) (by simp [List.append_assoc])

theorem recsL_append (s : Nat) : ∀ l1 l2 : List (Nat × Nat), recsL s (l1 ++ l2) = recsL s l1 ++ recsL s l2
  | [], l2 => by simp [recsL]
  | (o, u) :: l1, l2 => by simp [recsL, recsL_append s l1 l2, List.append_assoc]

/-- Records behind `Nn`: none, or `MM ..`. -/
theorem recsL_cases (s : Nat) (l : List (Nat × Nat)) (hl : ∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) :
    recsL s l = [] ∨ ∃ Y, recsL s l = [1, 1] ++ Y ∧ NoB Y := by
  cases l with
  | nil => left; rfl
  | cons x l =>
    right
    obtain ⟨o, u⟩ := x
    refine ⟨[2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u ++ recsL s l, ?_, ?_⟩
    · simp [recsL, Rec3, List.append_assoc]
    · have h1 := noB_Fld s
      have h2 := noB_Fld u
      have ho := hl (o, u) (List.mem_cons_self ..)
      have ho' : o = 2 ∨ o = 3 := ho
      have h3 := noB_recsL s l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      noB_tac

theorem rnFindMg (a0 w p cA cM a b : Nat) (Rs : List Nat)
    (hR : Rs = [] ∨ ∃ Y, Rs = [1, 1] ++ Y ∧ NoB Y) :
    znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3)
        (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2)
          ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2) ++ Rs))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3]
          ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2)
          ++ 1 :: (List.replicate (a + 1) 3 ++ List.replicate b 2))) Rs) := by
  rcases hR with rfl | ⟨Y, rfl, hY⟩
  · cases cA with
    | zero => exact (rnFindzMe a0 w p cM b a).of_eq (by simp) (by simp)
    | succ ca => exact (rnFindsMe a0 w p cM b ca a).of_eq (by simp) (by simp)
  · cases cA with
    | zero => exact (rnFindzMr a0 w p cM b a Y hY).of_eq (by simp) (by simp)
    | succ ca => exact (rnFindsMr a0 w p cM b ca a Y hY).of_eq (by simp) (by simp)

theorem rnFindDg (a0 w p cA cM b : Nat) (Y : List Nat) (hY : NoB Y) :
    znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3)
        (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2)
          ++ 1 :: List.replicate (b + 1) 2 ++ [1, 1] ++ Y))
      (hd QN.RN2 (List.replicate a0 3 ++ (List.replicate w 3 ++ 1 :: List.replicate (p + 1) 3 ++ 1 :: [3, 3, 3]
          ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2)
          ++ 1 :: List.replicate (b + 1) 2)) ([1, 1] ++ Y)) := by
  cases cA with
  | zero => exact (rnFindzDr a0 w p cM b Y hY).of_eq (by simp) (by simp)
  | succ ca => exact (rnFindsDr a0 w p cM b ca Y hY).of_eq (by simp) (by simp)

def newRecs : Nat → Nat → List (Nat × Nat)
  | _, 0 => []
  | u, d + 1 => (3, u) :: newRecs (u + 1) d

theorem newRecs_flags : ∀ d u, ∀ x ∈ newRecs u d, x.1 = 2 ∨ x.1 = 3
  | 0, u, x, hx => by simp [newRecs] at hx
  | d + 1, u, x, hx => by
    simp only [newRecs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · right; rfl
    · exact newRecs_flags d (u + 1) x hx

theorem recsL_ne (s : Nat) (l : List (Nat × Nat)) (hl : ∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) (hne : l ≠ []) :
    ∃ Y, recsL s l = [1, 1] ++ Y ∧ NoB Y := by
  rcases recsL_cases s l hl with h | h
  · cases l with
    | nil => exact absurd rfl hne
    | cons x l => obtain ⟨o, u⟩ := x; simp [recsL, Rec3] at h
  · exact h

theorem rep_split (a0 w m : Nat) (h : a0 + w = m) (X : List Nat) :
    List.replicate a0 3 ++ (List.replicate w 3 ++ X) = List.replicate m 3 ++ X := by
  subst h; rw [← List.append_assoc, List.replicate_append_replicate]

theorem cons_rep (a k : Nat) : a :: List.replicate k a = List.replicate k a ++ [a] := by
  rw [← List.replicate_succ, List.replicate_succ']

theorem nLoop (s cA cM : Nat) : ∀ (d b u a0 w : Nat) (l : List (Nat × Nat)), a0 + w = u + 2 →
    (∀ x ∈ l, x.1 = 2 ∨ x.1 = 3) →
    znttLogic.Reach
      (hdR QN.RN0 (List.replicate a0 3)
        (List.replicate w 3 ++ 1 :: List.replicate (s + 2) 3 ++ 1 :: [3, 3, 3] ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2)
          ++ 1 :: (List.replicate (d + 1) 3 ++ List.replicate b 2) ++ recsL s l))
      (hd QN.RC1 (List.replicate (u + d + 3) 3 ++ 1 :: List.replicate (s + 2) 3 ++ 1 :: [3, 3, 3]
          ++ 1 :: (List.replicate cA 3 ++ [2] ++ List.replicate cM 2))
        (1 :: List.replicate (d + 1 + b) 3 ++ recsL s (l ++ newRecs u (d + 1)))) := by
  intro d
  induction d with
  | zero =>
    intro b u a0 w l hW hl
    have hRs := recsL_cases s l hl
    have h1 := rnFindMg a0 w (s + 1) cA cM 0 b (recsL s l) hRs
    have h2 := recBuild u s cA (cM + 1) 0 b (recsL s l) (noB_recsL s l hl)
    have st := reach_trans_eq h1 h2 (hd_eq (by
      simp only [List.append_assoc]
      rw [rep_split a0 w (u + 2) hW]
      simp [List.replicate_succ, List.append_assoc]) rfl)
    have hl' : ∀ x ∈ l ++ [(3, u)], x.1 = 2 ∨ x.1 = 3 := fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact hl x h
      · simp at h; subst h; right; rfl
    obtain ⟨Y, hY, hYn⟩ := recsL_ne s (l ++ [(3, u)]) hl' (by simp)
    have hY' : recsL s l ++ Rec3 3 s u = [1, 1] ++ Y := by
      have := hY; rw [recsL_append] at this; simpa [recsL] using this
    have h3 := rnFindDg 1 (u + 2) (s + 1) cA cM b Y hYn
    have h4 := roundEnd (List.replicate 1 3 ++ (List.replicate (u + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1, 3, 3, 3]))
      (1 :: Y) (by noB_tac) (noB_cons' (by simp [NB]) hYn) cA cM b
    have s1 := reach_trans_eq st h3 (by
      simp [List.replicate_succ, List.append_assoc, hY'])
    have s2 := reach_trans_eq s1 h4 (by
      simp [List.replicate_succ, List.append_assoc])
    refine s2.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_
    simp [newRecs, hY, List.replicate_succ, List.append_assoc, Nat.add_comm]
  | succ d ih =>
    intro b u a0 w l hW hl
    have hRs := recsL_cases s l hl
    have h1 := rnFindMg a0 w (s + 1) cA cM (d + 1) b (recsL s l) hRs
    have h2 := recBuild u s cA (cM + 1) (d + 1) b (recsL s l) (noB_recsL s l hl)
    have st := reach_trans_eq h1 h2 (hd_eq (by
      simp only [List.append_assoc]
      rw [rep_split a0 w (u + 2) hW]
      simp [List.replicate_succ', cons_rep, List.append_assoc]) rfl)
    have hl' : ∀ x ∈ l ++ [(3, u)], x.1 = 2 ∨ x.1 = 3 := fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact hl x h
      · simp at h; subst h; right; rfl
    have h3 := ih (b + 1) (u + 1) 1 (u + 2) (l ++ [(3, u)]) (by omega) hl'
    have s1 := reach_trans_eq st h3 (by
      simp [List.replicate_succ', cons_rep, List.append_assoc, recsL_append, recsL])
    refine s1.of_eq rfl ?_
    have e1 : u + 1 + d + 3 = u + (d + 1) + 3 := by omega
    have e2 : d + 1 + (b + 1) = d + 1 + 1 + b := by omega
    rw [e1, e2]
    simp [newRecs, List.append_assoc]

end ZP.N
