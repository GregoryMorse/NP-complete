module

public import ZP.Defs
public import ZP.Logic
public import ZP.SymExec
public import ZP.Outer
public import ZP.Rot
public import ZP.Fuel

@[expose] public section

/-!
# Layer N3: the guest interpreter, segment by segment

Between guest steps the interpreter is in state `BK2` on the scanned cell `ch`:

    B^∞ · Q · B^(g+1) · Lw · ch · H · V,    V = Rw M_g W M_3 fuel

`Q` is the code (`reverse R`), `Lw` the guest cells right of the head (reversed), `Rw`
the cells left of it (reversed). Each segment below is one symbolic check.
-/

namespace ZP

theorem rep_rep (a b x : Nat) (l : List Nat) :
    List.replicate a x ++ (List.replicate b x ++ l) = List.replicate (a + b) x ++ l := by
  rw [← List.append_assoc, List.replicate_append_replicate]

macro "wsimp" : tactic =>
  `(tactic| simp [dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app, rep_rep])

def isets : Env := [bits, ALL, bits, bits, NB, NB]

theorem ivalid {Qw G Lw Rw W F : List Nat} (hQ : Bits Qw) (hG : Sym4 G) (hL : Bits Lw)
    (hR : Bits Rw) (hW : NoB W) (hF : NoB F) : Valid isets [Qw, G, Lw, Rw, W, F] :=
  Valid.cons hQ (Valid.cons hG (Valid.cons hL (Valid.cons hR (Valid.cons hW (Valid.cons hF
    (Valid.nil _))))))

def nsets : Env := [bits, ALL, ALL, bits, ALL, ALL]

theorem nvalid {Z A G Lw P X : List Nat} (hZ : Bits Z) (hA : Sym4 A) (hG : Sym4 G) (hL : Bits Lw)
    (hP : Sym4 P) (hX : Sym4 X) : Valid nsets [Z, A, G, Lw, P, X] :=
  Valid.cons hZ (Valid.cons hA (Valid.cons hG (Valid.cons hL (Valid.cons hP (Valid.cons hX
    (Valid.nil _))))))

theorem Bits.nil : Bits [] := fun _ h => by cases h

theorem NoB.nil : NoB [] := fun _ h => by cases h

theorem Bits.sym4 {w : List Nat} (h : Bits w) : Sym4 w := by
  intro a ha
  rcases mem_bits (h a ha) with e | e <;> rw [e] <;> simp [ALL]

theorem Bits.noB {w : List Nat} (h : Bits w) : NoB w := by
  intro a ha
  rcases mem_bits (h a ha) with e | e <;> rw [e] <;> simp [NB]

theorem zeros4 (g : Nat) : Sym4 (List.replicate g 0) := Sym4.rep g 0 (by simp [ALL])

theorem ones4 (g : Nat) : Sym4 (List.replicate g 1) := Sym4.rep g 1 (by simp [ALL])

/-- The count-down successor of the scanned cell: `1 → 0 → B`. -/
def cdn (ch : Nat) : Nat := if ch = 3 then 2 else 0

/-- The halting state with output `b`. -/
def dpOf (b : Nat) : Nat := if b = 3 then Q.DP11 else Q.DP10

/-! ## Count-down: `BK2` on a bit, to `TW` on `Q`'s right end -/

theorem segA (Qw Lw W : List Nat) (g ch : Nat) (hch : ch ∈ bits) (hQ : Bits Qw) (hL : Bits Lw)
    (hW : NoB W) :
    zpBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [ch])) (1 :: W))
      (hd Q.TW Qw (List.replicate g 0 ++ 0 :: (Lw ++ cdn ch :: 1 :: W))) := by
  have hv := ivalid hQ (zeros4 g) hL Bits.nil hW NoB.nil
  rcases mem_bits hch with rfl | rfl
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, [], W, []]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 2]) (rs := [.sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .sym 1, .blk 4 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by simp [cdn, dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app, rep_rep])
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, [], W, []]) (E := []) (k := 8) hv trivial
      (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 3]) (rs := [.sym 1, .blk 4 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 2, .sym 1, .blk 4 .id])
      (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by simp [cdn, dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app, rep_rep])

/-! ## Back from a normal rotation to `BK2` -/

theorem segB (Z Lw X : List Nat) (a g p ch b : Nat) (hch : ch = 0 ∨ ch = 2 ∨ ch = 3) (hb : b ∈ bits)
    (hZ : Bits Z) (hL : Bits Lw) (hX : Sym4 X) :
    zpBase.Reach
      (hdR Q.NAV [2] (Z ++ 0 :: (List.replicate a 0 ++ List.replicate g 0 ++ 0 :: (Lw ++ ch :: 1 ::
        (List.replicate p 1 ++ b :: X)))))
      (hd Q.BK2 (2 :: Z ++ 0 :: (List.replicate a 0 ++ List.replicate g 0 ++ 0 :: (Lw ++ [ch])))
        (1 :: (List.replicate p 1 ++ b :: X))) := by
  have hv := nvalid hZ (zeros4 a) (zeros4 g) hL (ones4 p) hX
  rcases hch with rfl | rfl | rfl <;> rcases mem_bits hb with rfl | rfl
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 0, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 0])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 0, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 0])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 2, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 2])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 2, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 2])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 3, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 3])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate g 0, Lw, List.replicate p 1, X])
        (E := []) (k := 16) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 3, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .blk 2 (.const 0), .sym 0, .blk 3 .id, .sym 3])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## `BK2` on a blank: to the last fuel cell -/

theorem segC (Qw Lw Rw W F : List Nat) (g : Nat) (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw)
    (hW : NoB W) (hF : NoB F) :
    zpBase.Reach (hd Q.BK2 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: (W ++ 1 :: F))))
      (hd Q.DEC1 (Qw ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]) ++ 1 :: (Rw ++ 1 :: W) ++ [1] ++ F) []) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW hF
  exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, F]) (E := []) (k := 12) hv trivial
    (ls := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
    (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id, .sym 1, .blk 5 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0, .sym 1, .blk 3 .id, .sym 1,
      .blk 4 .id, .sym 1, .blk 5 .id]) (rs' := [])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## Time-out: `EXH` on the blank `ch`, cleanup, result 0 -/

theorem segExh (Qw Lw Rw W : List Nat) (g r : Nat) (hr : r ∈ bits) (hQ : Bits Qw) (hL : Bits Lw)
    (hR : Bits Rw) (hW : NoB W) :
    zpBase.Reach (hd Q.EXH (Qw ++ [r] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: W)))
      (hdR Q.DP10 [1] W) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW NoB.nil
  rcases mem_bits hr with rfl | rfl
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 24) hv trivial
        (ls := [.blk 0 .id, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 24) hv trivial
        (ls := [.blk 0 .id, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## Peek: `FBACK` on the blank `ch` reads `R[0..2]` at `Q`'s right end -/

theorem segHalt (Qw Lw Rw W : List Nat) (g r0 r1 : Nat) (h0 : r0 ∈ bits) (h1 : r1 ∈ bits)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK (Qw ++ [2, r1, r0] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: (Rw ++ 1 :: W)))
      (hdR (dpOf r0) [1] W) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW NoB.nil
  rcases mem_bits h0 with rfl | rfl <;> rcases mem_bits h1 with rfl | rfl
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 40) hv trivial
        (ls := [.blk 0 .id, .sym 2, .sym 2, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 40) hv trivial
        (ls := [.blk 0 .id, .sym 2, .sym 3, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 40) hv trivial
        (ls := [.blk 0 .id, .sym 2, .sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 40) hv trivial
        (ls := [.blk 0 .id, .sym 2, .sym 3, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem segShort1 (Lw Rw W : List Nat) (g : Nat) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK ([2] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: W)))
      (hdR Q.DP10 [1] W) := by
  have hv := ivalid Bits.nil (zeros4 g) hL hR hW NoB.nil
  exact checkTF (env := [[], List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 32) hv trivial
    (ls := [.sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
    (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
    (ls' := [.sym 1]) (rs' := [.blk 4 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

theorem segShort2 (Lw Rw W : List Nat) (g r0 : Nat) (h0 : r0 ∈ bits) (hL : Bits Lw) (hR : Bits Rw)
    (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK ([2, r0] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: (Rw ++ 1 :: W)))
      (hdR (dpOf r0) [1] W) := by
  have hv := ivalid Bits.nil (zeros4 g) hL hR hW NoB.nil
  rcases mem_bits h0 with rfl | rfl
  · exact checkTF (env := [[], List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 36) hv trivial
        (ls := [.sym 2, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTF (env := [[], List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 36) hv trivial
        (ls := [.sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.sym 1]) (rs' := [.blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## Write and move, then `RTW` on `Q`'s right end -/

/-- Guest left move at cell 0: the head stays. -/
theorem segMv0e (Qw Lw W : List Nat) (g r0 : Nat) (h0 : r0 ∈ bits) (hQ : Bits Qw) (hL : Bits Lw)
    (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK (Qw ++ [3, 2, r0] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0])) (1 :: 1 :: W))
      (hd Q.RTW (Qw ++ [3, 2, r0]) (List.replicate g 0 ++ 0 :: (Lw ++ r0 :: 1 :: 1 :: W))) := by
  have hv := ivalid hQ (zeros4 g) hL Bits.nil hW NoB.nil
  rcases mem_bits h0 with rfl | rfl
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, [], W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 2])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 2, .sym 1, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, [], W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 3])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 3, .sym 1, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Guest left move onto the cell `c`. -/
theorem segMv0c (Qw Lw Rw W : List Nat) (g r0 c : Nat) (h0 : r0 ∈ bits) (hc : c ∈ bits)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK (Qw ++ [3, 2, r0] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: c :: (Rw ++ 1 :: W)))
      (hd Q.RTW (Qw ++ [3, 2, r0]) (List.replicate g 0 ++ 0 :: (Lw ++ r0 :: c :: 1 :: (Rw ++ 1 :: W)))) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW NoB.nil
  rcases mem_bits h0 with rfl | rfl <;> rcases mem_bits hc with rfl | rfl
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 2])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 2, .sym 2, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 2])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 2, .sym 3, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 3])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 3, .sym 2, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 26) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 2, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 2, .sym 3])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 3, .sym 3, .sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Guest right move. -/
theorem segMv1 (Qw Lw Rw W : List Nat) (g r0 : Nat) (h0 : r0 ∈ bits)
    (hQ : Bits Qw) (hL : Bits Lw) (hR : Bits Rw) (hW : NoB W) :
    zpBase.Reach (hd Q.FBACK (Qw ++ [3, 3, r0] ++ List.replicate g 0 ++ 0 :: (Lw ++ [0]))
        (1 :: (Rw ++ 1 :: W)))
      (hd Q.RTW (Qw ++ [3, 3, r0]) (List.replicate g 0 ++ 0 :: (Lw ++ 1 :: r0 :: (Rw ++ 1 :: W)))) := by
  have hv := ivalid hQ (zeros4 g) hL hR hW NoB.nil
  rcases mem_bits h0 with rfl | rfl
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 22) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 3, .sym 2, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 3, .sym 2])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 1, .sym 2, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkTT (env := [Qw, List.replicate g 0, Lw, Rw, W, []]) (E := []) (k := 22) hv trivial
        (ls := [.blk 0 .id, .sym 3, .sym 3, .sym 3, .blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 0])
        (rs := [.sym 1, .blk 3 .id, .sym 1, .blk 4 .id])
        (ls' := [.blk 0 .id, .sym 3, .sym 3, .sym 3])
        (rs' := [.blk 1 (.const 0), .sym 0, .blk 2 .id, .sym 1, .sym 3, .blk 3 .id, .sym 1, .blk 4 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-! ## Consuming jump tokens -/

/-- Two tokens left: consume one, then a normal rotation starts. -/
theorem segE1a (Z X : List Nat) (a y : Nat) (hZ : Bits Z) (hX : Sym4 X) :
    zpBase.Reach
      (hdR Q.NAV [2] (Z ++ 0 :: (List.replicate a 0 ++ [1, 1] ++ List.replicate y 0 ++ 0 :: X)))
      (hd Q.TW (2 :: Z) (0 :: (List.replicate a 0 ++ [1, 0] ++ List.replicate y 0 ++ 0 :: X))) := by
  have hv := nvalid hZ (zeros4 a) (zeros4 y) Bits.nil Sym4.nil hX
  exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, [], [], X]) (E := []) (k := 14) hv trivial
    (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .sym 1, .blk 2 (.const 0), .sym 0,
      .blk 5 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 (.const 0), .sym 1, .sym 0, .blk 2 (.const 0),
      .sym 0, .blk 5 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- Three or more tokens left. -/
theorem segE1b (Z X : List Nat) (a y p : Nat) (hZ : Bits Z) (hX : Sym4 X) :
    zpBase.Reach
      (hdR Q.NAV [2] (Z ++ 0 :: (List.replicate a 0 ++ 1 :: (List.replicate p 1 ++ [1]) ++
        List.replicate y 0 ++ 0 :: X)))
      (hd Q.TW (2 :: Z) (0 :: (List.replicate a 0 ++ 1 :: (List.replicate p 1 ++ [0]) ++
        List.replicate y 0 ++ 0 :: X))) := by
  have hv := nvalid hZ (zeros4 a) (zeros4 y) Bits.nil (ones4 p) hX
  exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, [], List.replicate p 1, X]) (E := [])
    (k := 18) hv trivial
    (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 4 (.const 1), .sym 1,
      .blk 2 (.const 0), .sym 0, .blk 5 .id])
    (ls' := [.sym 2, .blk 0 .id]) (rs' := [.sym 0, .blk 1 (.const 0), .sym 1, .blk 4 (.const 1), .sym 0,
      .blk 2 (.const 0), .sym 0, .blk 5 .id])
    (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

/-- The last token: back to `BK2` on the new scanned cell. -/
theorem segE2 (Z Lw X : List Nat) (a y p ch b : Nat) (hch : ch = 0 ∨ ch = 2 ∨ ch = 3) (hb : b ∈ bits)
    (hZ : Bits Z) (hL : Bits Lw) (hX : Sym4 X) :
    zpBase.Reach
      (hdR Q.NAV [2] (Z ++ 0 :: (List.replicate a 0 ++ [1] ++ List.replicate y 0 ++ 0 :: (Lw ++ ch :: 1 ::
        (List.replicate p 1 ++ b :: X)))))
      (hd Q.BK2 (2 :: Z ++ 0 :: (List.replicate a 0 ++ [0] ++ List.replicate y 0 ++ 0 :: (Lw ++ [ch])))
        (1 :: (List.replicate p 1 ++ b :: X))) := by
  have hv := nvalid hZ (zeros4 a) (zeros4 y) hL (ones4 p) hX
  rcases hch with rfl | rfl | rfl <;> rcases mem_bits hb with rfl | rfl
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 0, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 0])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 0, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 0])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 2, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 2])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 2, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 2])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 3, .sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 3])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 2, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)
  · exact checkFT (env := [Z, List.replicate a 0, List.replicate y 0, Lw, List.replicate p 1, X])
        (E := []) (k := 22) hv trivial
        (ls := [.sym 2]) (rs := [.blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 1, .blk 2 (.const 0), .sym 0,
          .blk 3 .id, .sym 3, .sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (ls' := [.sym 2, .blk 0 .id, .sym 0, .blk 1 (.const 0), .sym 0, .blk 2 (.const 0), .sym 0, .blk 3 .id,
          .sym 3])
        (rs' := [.sym 1, .blk 4 (.const 1), .sym 3, .blk 5 .id])
        (by decide +kernel) (by wsimp) (by wsimp) (by wsimp) (by wsimp)

end ZP
