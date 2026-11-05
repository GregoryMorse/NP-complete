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

end ZP.N
