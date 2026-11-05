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
  `(tactic| repeat (first | assumption | exact noB_nil | apply noB_cons' (by simp [NB]) | apply noB_app | apply noB_rep _ _ (by simp [NB]) | exact noB_Fld _))

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

end ZP.N
