module

public import ZP.MMDry2
public import ZP.MMRowsAll
public import ZP.MMBridge
public import ZP.MMVerdict3
public import ZP.MMExit
public import ZP.MMSetupLoop
public import ZP.MMRBLoop
public import ZP.MMRSLoop
public import ZP.MMFetch2

@[expose] public section

/-! Setup glue of the Z_MATMUL check: from the entry `mK1` to the first dry cycle. -/

namespace ZP.Mul.MM

open ZP

/-- The entry chain: `Rw 1 J 1 s 1 Y` becomes the copy loop's start (the separator `Ms` stays `M`). -/
theorem mkChain' (Rw : List Nat) (j : List Nat) (s : List Nat) (Y : List Nat) (hRw : Bits Rw) (hj : Bits j) (hs : Bits s) (hY : Sym4 Y) :
    zmmLogic.Reach (hdR QMM.mK1 ([1]) (Rw ++ (1 :: (j ++ (1 :: (s ++ (1 :: (Y))))))))
      (hdR Q.GC (1 :: (Rw ++ (1 :: (j ++ ([1]))))) (s ++ (0 :: (Y)))) := by
  have hV : Valid [bits, bits, bits, ALL] [Rw, j, s, Y] := Valid.cons hRw (Valid.cons hj (Valid.cons hs (Valid.cons hY (Valid.nil _))))
  exact checkFF (env := [Rw, j, s, Y]) (E := []) (k := 8) hV trivial
    (ls := [.sym 1]) (rs := [.blk 0 .id, .sym 1, .blk 1 .id, .sym 1, .blk 2 .id, .sym 1, .blk 3 .id])
    (ls' := [.sym 1, .blk 0 .id, .sym 1, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id, .sym 0, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Copy one bit of `s` to the far left. -/
theorem gcBodyM (Ur : List Nat) (V : List Nat) (u : List Nat) (v : List Nat) (Y : List Nat) (b : Nat) (hUr : Bits Ur) (hV : NoB V) (hu : Bits u) (hv : Bits v) (hY : Sym4 Y) (hb : b ∈ bits) :
    zmmLogic.Reach (hdR Q.GC (Ur ++ (V ++ (u))) (b :: (v ++ (0 :: (Y)))))
      (hdR Q.GC (b :: (Ur ++ (V ++ (u ++ ([b]))))) (v ++ (0 :: (Y)))) := by
  have hV : Valid [bits, NB, bits, bits, ALL] [Ur, V, u, v, Y] := Valid.cons hUr (Valid.cons hV (Valid.cons hu (Valid.cons hv (Valid.cons hY (Valid.nil _)))))
  rcases mem_bits hb with rfl | rfl
  · exact checkFF (env := [Ur, V, u, v, Y]) (E := []) (k := 9) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .blk 2 .id]) (rs := [.sym 2, .blk 3 .id, .sym 0, .blk 4 .id])
      (ls' := [.sym 2, .blk 0 .id, .blk 1 .id, .blk 2 .id, .sym 2]) (rs' := [.blk 3 .id, .sym 0, .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [Ur, V, u, v, Y]) (E := []) (k := 9) hV trivial
      (ls := [.blk 0 .id, .blk 1 .id, .blk 2 .id]) (rs := [.sym 3, .blk 3 .id, .sym 0, .blk 4 .id])
      (ls' := [.sym 3, .blk 0 .id, .blk 1 .id, .blk 2 .id, .sym 3]) (rs' := [.blk 3 .id, .sym 0, .blk 4 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gcLoopM (V Y : List Nat) (hV : NoB V) (hY : Sym4 Y) :
    ∀ v u, Bits u → Bits v →
      zmmLogic.Reach (hdR Q.GC (u.reverse ++ (V ++ u)) (v ++ 0 :: Y))
        (hdR Q.GC ((u ++ v).reverse ++ (V ++ (u ++ v))) (0 :: Y))
  | [], u, _, _ => by
    rw [List.append_nil, List.nil_append]
    exact LTM.Reach.refl _ _
  | b :: v, u, hu, hv => by
    have h1 := gcBodyM u.reverse V u v Y b hu.rev hV hu hv.tail hY hv.head
    have h2 := gcLoopM V Y hV hY v (u ++ [b]) (hu.snoc hv.head) hv.tail
    exact h1.trans (h2.of_eq (by simp) (by simp only [List.append_assoc, List.singleton_append]))

end ZP.Mul.MM

