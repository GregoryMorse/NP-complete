module

public import ZP.PairN2

@[expose] public section

/-! # The pair lemma of the NTT machine, part 3: witness initialisation -/

namespace ZP.N

open ZP ZP.G

/-- `WI0..WI2`: from the end of `C` sweep left, then right to the first record header. -/
theorem wiSweep (a s c' n' : Nat) (rest : List Nat) (hrest : NoB rest) :
    znttLogic.Reach
      (hd QN.WI0 ([0] ++ List.replicate (a + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1, 3, 3, 3] ++ 1 :: List.replicate (c' + 1) 3)
        ([1, 3] ++ List.replicate n' 3 ++ [1, 1] ++ rest))
      (hdR QN.WH1 ([0] ++ List.replicate (a + 2) 3 ++ 1 :: List.replicate (s + 2) 3 ++ [1, 3, 3, 3] ++ 1 :: List.replicate (c' + 1) 3
        ++ [1, 3] ++ List.replicate n' 3 ++ [1, 1]) rest) := by
  have hV : Valid [T3, T3, T3, T3, NB] [List.replicate a 3, List.replicate (s + 1) 3, List.replicate c' 3, List.replicate n' 3, rest] :=
    Valid.cons (rep_t3 a) (Valid.cons (rep_t3 (s + 1)) (Valid.cons (rep_t3 c') (Valid.cons (rep_t3 n')
      (Valid.cons hrest (Valid.nil _)))))
  have : znttLogic.Reach
      (hd QN.WI0 ([0, 3, 3] ++ List.replicate a 3 ++ [1, 3] ++ List.replicate (s + 1) 3 ++ [1, 3, 3, 3, 1, 3] ++ List.replicate c' 3)
        ([1, 3] ++ List.replicate n' 3 ++ [1, 1] ++ rest))
      (hdR QN.WH1 ([0, 3, 3] ++ List.replicate a 3 ++ [1, 3] ++ List.replicate (s + 1) 3 ++ [1, 3, 3, 3, 1, 3] ++ List.replicate c' 3
        ++ [1, 3] ++ List.replicate n' 3 ++ [1, 1]) rest) :=
    checkTF (env := [List.replicate a 3, List.replicate (s + 1) 3, List.replicate c' 3, List.replicate n' 3, rest]) (E := []) (k := 80) hV trivial
      (ls := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id])
      (rs := [.sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
      (ls' := [.sym 0, .sym 3, .sym 3, .blk 0 .id, .sym 1, .sym 3, .blk 1 .id, .sym 1, .sym 3, .sym 3, .sym 3, .sym 1, .sym 3, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1])
      (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · simp [List.replicate_succ, List.append_assoc]
  · simp [List.replicate_succ, List.append_assoc]


def U4 : List Nat := [0, 1, 2, 3]

/-- `E := 1`: first two cells `1`, the rest `0`. -/
def E1 (s : Nat) : List Nat := [1, 3, 3] ++ List.replicate s 2

theorem recInitMid0 (A : List Nat) (hA : ∀ a ∈ A, a ∈ U4) (o s u : Nat) (ho : o = 2 ∨ o = 3) (rest : List Nat) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.WH0 A ([2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u ++ [1, 1] ++ rest))
      (hdR QN.WH0 (A ++ [2, o, 2] ++ Fld s ++ E1 s ++ Fld s ++ Fld u ++ [1, 1]) rest) := by
  have hb : ∀ a ∈ [2, o], a ∈ bits := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rcases ho with rfl | rfl <;> simp [bits]
  have hV : Valid [U4, bits, Mk, Mk, NB] [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, rest] :=
    Valid.cons hA (Valid.cons hb (Valid.cons (rep2_mk s) (Valid.cons (rep2_mk (u + 1))
      (Valid.cons hrest (Valid.nil _)))))
  have : znttLogic.Reach
      (hdR QN.WH0 A ([2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [1, 1] ++ rest))
      (hdR QN.WH0 (A ++ [2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 3] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [1, 1]) rest) :=
    checkFF (env := [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, rest]) (E := []) (k := 120) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1])
      (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · simp [Fld, List.replicate_succ, List.append_assoc]
  · simp [Fld, E1, List.replicate_succ, List.append_assoc]

theorem recInitMid1 (A : List Nat) (hA : ∀ a ∈ A, a ∈ U4) (o s u : Nat) (ho : o = 2 ∨ o = 3) (rest : List Nat) (hrest : NoB rest) :
    znttLogic.Reach
      (hdR QN.WH1 A ([2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u ++ [1, 1] ++ rest))
      (hdR QN.WH0 (A ++ [2, o, 3] ++ Fld s ++ E1 s ++ Fld s ++ Fld u ++ [1, 1]) rest) := by
  have hb : ∀ a ∈ [2, o], a ∈ bits := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rcases ho with rfl | rfl <;> simp [bits]
  have hV : Valid [U4, bits, Mk, Mk, NB] [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, rest] :=
    Valid.cons hA (Valid.cons hb (Valid.cons (rep2_mk s) (Valid.cons (rep2_mk (u + 1))
      (Valid.cons hrest (Valid.nil _)))))
  have : znttLogic.Reach
      (hdR QN.WH1 A ([2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [1, 1] ++ rest))
      (hdR QN.WH0 (A ++ [2, o, 3, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 3] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [1, 1]) rest) :=
    checkFF (env := [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, rest]) (E := []) (k := 120) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 3, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 1, .sym 1])
      (rs' := [.blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · simp [Fld, List.replicate_succ, List.append_assoc]
  · simp [Fld, E1, List.replicate_succ, List.append_assoc]

theorem recInitLast0 (A : List Nat) (hA : ∀ a ∈ A, a ∈ U4) (o s u : Nat) (ho : o = 2 ∨ o = 3) :
    znttLogic.Reach
      (hdR QN.WH0 A ([2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u))
      (hd QN.RZ0 (A ++ [2, o, 2] ++ Fld s ++ E1 s ++ Fld s ++ Fld u) [0]) := by
  have hb : ∀ a ∈ [2, o], a ∈ bits := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rcases ho with rfl | rfl <;> simp [bits]
  have hV : Valid [U4, bits, Mk, Mk, NB] [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, []] :=
    Valid.cons hA (Valid.cons hb (Valid.cons (rep2_mk s) (Valid.cons (rep2_mk (u + 1))
      (Valid.cons (fun a ha => by simp at ha) (Valid.nil _)))))
  have : znttLogic.Reach
      (hdR QN.WH0 A ([2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [0]))
      (hd QN.RZ0 (A ++ [2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 3] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2) [0]) :=
    checkFT (env := [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, []]) (E := []) (k := 120) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 0])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id])
      (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · rw [hdR_trail]; simp [Fld, List.replicate_succ, List.append_assoc]
  · simp [Fld, E1, List.replicate_succ, List.append_assoc]

theorem recInitLast1 (A : List Nat) (hA : ∀ a ∈ A, a ∈ U4) (o s u : Nat) (ho : o = 2 ∨ o = 3) :
    znttLogic.Reach
      (hdR QN.WH1 A ([2, o, 2] ++ Fld s ++ Fld s ++ Fld s ++ Fld u))
      (hd QN.RZ0 (A ++ [2, o, 3] ++ Fld s ++ E1 s ++ Fld s ++ Fld u) [0]) := by
  have hb : ∀ a ∈ [2, o], a ∈ bits := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rcases ho with rfl | rfl <;> simp [bits]
  have hV : Valid [U4, bits, Mk, Mk, NB] [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, []] :=
    Valid.cons hA (Valid.cons hb (Valid.cons (rep2_mk s) (Valid.cons (rep2_mk (u + 1))
      (Valid.cons (fun a ha => by simp at ha) (Valid.nil _)))))
  have : znttLogic.Reach
      (hdR QN.WH1 A ([2, o, 2, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2 ++ [0]))
      (hd QN.RZ0 (A ++ [2, o, 3, 1, 3, 2] ++ List.replicate s 2 ++ [1, 3, 3] ++ List.replicate s 2 ++ [1, 3, 2] ++ List.replicate s 2
        ++ [1, 3] ++ List.replicate (u + 1) 2) [0]) :=
    checkFT (env := [A, [2, o], List.replicate s 2, List.replicate (u + 1) 2, []]) (E := []) (k := 120) hV trivial
      (ls := [.blk 0 .id])
      (rs := [.blk 1 .id, .sym 2, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id, .sym 0])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 3, .sym 1, .sym 3, .sym 2, .blk 2 .id, .sym 1, .sym 3, .sym 3, .blk 2 .id, .sym 1, .sym 3, .sym 2, .blk 2 .id,
        .sym 1, .sym 3, .blk 3 .id])
      (rs' := [.sym 0])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  refine this.of_eq ?_ ?_
  · rw [hdR_trail]; simp [Fld, List.replicate_succ, List.append_assoc]
  · simp [Fld, E1, List.replicate_succ, List.append_assoc]

end ZP.N
