module

public import ZP.Defs
public import ZP.DefsF

@[expose] public section

/-!
# Definitions for the multiplication machine (`native/zmul.py`, `ref/zmul_ref.py`)

The guest model is `zp2` plus a queue of stacks. The guest tape is a `List Bool` (its support is always
an initial segment, and the head is at most one past its end).
-/

namespace ZP

/-- `zmul_ref.run`: at most `T` steps; `some out` iff the run halts properly. -/
def runMulAux : Nat → List Bool → List Bool → Nat → List (List Bool) → Option (List Bool)
  | 0, _, _, _, _ => none
  | T + 1, R0, tape, h, queue =>
    let R := rotN (iota tape[h]?) R0
    let w := R.getD 0 false
    let d := R.getD 1 false
    let t := R.getD 2 false
    if t then
      runMulAux T (rotN (entryOnes R + 1) (rot R)) (tape.take h ++ w :: tape.drop (h + 1))
        (if d then h + 1 else h - 1) queue
    else if d then
      let st := tape.drop (h + 1)
      let q2 := queue ++ [st]
      runMulAux T (rotN (entryOnes R + 1) (rot R)) (tape.take h ++ (q2.headD []).reverse) h q2.tail
    else if w then some (tape.take h) else none

def runMul (P x : List Bool) (T r : Nat) : Option (List Bool) :=
  runMulAux T (rot (P.reverse ++ [false])) x 0 (List.replicate r [])

def clockMul (J s : List Bool) : Nat := (s.length + 2) * 2 ^ J.length - 1

end ZP
