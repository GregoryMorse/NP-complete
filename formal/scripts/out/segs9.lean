/-- The charge is done: `H`, skip `K` and `a`, to the start of `s`. -/
theorem dgGuest (Z : List Nat) (K : List Nat) (a : List Nat) (Y : List Nat) (hZ : Sym4 Z) (hK : Bits K) (ha : Bits a) (hY : Sym4 Y) :
    zppolyLogic.Reach (hdR Q.DG2 (Z) (1 :: (K ++ (1 :: (a ++ (1 :: (Y))))))) (hdR Q.GC (Z ++ (1 :: (K ++ (1 :: (a ++ ([1])))))) (Y)) := by
  have hV : Valid [ALL, bits, bits, ALL] [Z, K, a, Y] := Valid.cons hZ (Valid.cons hK (Valid.cons ha (Valid.cons hY (Valid.nil _))))
  exact checkFF (env := [Z, K, a, Y]) (E := []) (k := 5) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
        (ls' := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1]) (rs' := [.blk 3 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
