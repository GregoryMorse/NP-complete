module

public import ZP.Defs

@[expose] public section

/-!
# The multihead read-only guest (`ref/zmh_ref.py`, `run_mh`)

Shared by the L = P machine (`native/zlp.py`) and the L = NL machine (`native/zlnl.py`).

A code `P` is rotated and parsed as in `ZP/Defs.lean` (`rot`, `rotN`, `entryOnes`, `iota`).
The input `x` is read only. Positions are `0 … |x| + 1`; position `0` is the left end
marker and `|x| + 1` the right one, and both read as blank (`none`); position `p` in
`1 … |x|` reads `x[p-1]`. There are `|P| + 1` heads, all at position 0, and head 0 is
current. One step reads `a` under the current head, rotates `iota a` times and then
(unless the time is out) peeks `w d t` at the front of the code. `t = 0` halts, accepting
iff `w = 1`. Otherwise `w = 1` moves the current head right (`d = 1`, stopping at `|x|+1`)
or left (stopping at 0), and `w = 0` makes the next (`d = 1`) or previous (`d = 0`)
head current (stopping at the last and the first head). Then the code is rotated past the
entry and `k + 1` more rotations follow.
-/

namespace ZP

/-- The symbol at position `p` of `⊢x⊣`: blank at both end markers. -/
def mhRead (x : List Bool) (p : Nat) : Option Bool :=
  if p = 0 ∨ p = x.length + 1 then none else x[p - 1]?

/-- `np` is `|P|`; `pos` holds the head positions, `c` is the current head. -/
def runMHAux (np : Nat) (x : List Bool) : Nat → List Bool → List Nat → Nat → Bool
  | 0, _, _, _ => false
  | T + 1, R0, pos, c =>
    let p := pos.getD c 0
    let R := rotN (iota (mhRead x p)) R0
    if R.getD 2 false then
      if R.getD 0 false then
        runMHAux np x T (rotN (entryOnes R + 1) (rot R))
          (pos.set c (if R.getD 1 false then min (p + 1) (x.length + 1) else p - 1)) c
      else
        runMHAux np x T (rotN (entryOnes R + 1) (rot R)) pos
          (if R.getD 1 false then min (c + 1) np else c - 1)
    else R.getD 0 false

/-- Guest program `P` on read-only input `x` with `|P| + 1` heads for at most `T` steps
(a time-out rejects). -/
def runMH (P x : List Bool) (T : Nat) : Bool :=
  runMHAux P.length x T (rot (P.reverse ++ [false])) (List.replicate (P.length + 1) 0) 0

end ZP
