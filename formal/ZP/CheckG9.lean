import ZP.CheckG8

namespace ZP.G

open ZP

/-- The result 0 is reported and the left side erased. -/
theorem frPath0G (Lc : List Nat) (Mr : List Nat) (j : List Nat) (s : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hj : Bits j) (hs : Bits s) :
    zgiLogic.Reach (hdR QG.FR0 (Lc) (Mr ++ (0 :: (1 :: (j ++ (1 :: (s ++ ([1]))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: ([1]))))))) ([])) := by
  have hV : Valid [NB, NB, bits, bits] [Lc, Mr, j, s] := Valid.cons hLc (Valid.cons hMr (Valid.cons hj (Valid.cons hs (Valid.nil _))))
  exact checkFF (env := [Lc, Mr, j, s]) (E := []) (k := 16) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (ls' := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- The result 1 (via `FR1`) is reported and the left side erased. -/
theorem frPath1G (Lc : List Nat) (Mr : List Nat) (j : List Nat) (s : List Nat) (hLc : NoB Lc) (hMr : NoB Mr) (hj : Bits j) (hs : Bits s) :
    zgiLogic.Reach (hdR QG.FR1 (Lc) (Mr ++ (0 :: (1 :: (j ++ (1 :: (s ++ ([1]))))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [NB, NB, bits, bits] [Lc, Mr, j, s] := Valid.cons hLc (Valid.cons hMr (Valid.cons hj (Valid.cons hs (Valid.nil _))))
  exact checkFF (env := [Lc, Mr, j, s]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 0, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1])
    (ls' := [.sym 1, .blk 2 .id, .sym 1, .blk 3 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The result 1 (via `FE`) is reported and the left side erased. -/
theorem fePathG (Lc : List Nat) (j : List Nat) (s : List Nat) (hLc : NoB Lc) (hj : Bits j) (hs : Bits s) :
    zgiLogic.Reach (hd QG.FE (Lc) (3 :: (1 :: (j ++ (1 :: (s ++ ([1])))))))
      (hdR Q.GRB (1 :: (j ++ (1 :: (s ++ (1 :: (1 :: (3 :: ([1])))))))) ([])) := by
  have hV : Valid [NB, bits, bits] [Lc, j, s] := Valid.cons hLc (Valid.cons hj (Valid.cons hs (Valid.nil _)))
  exact checkTF (env := [Lc, j, s]) (E := []) (k := 17) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1])
    (ls' := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .sym 1, .sym 3, .sym 1]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

end ZP.G
