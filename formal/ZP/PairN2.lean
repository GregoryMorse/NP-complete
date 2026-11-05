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

end ZP.N
