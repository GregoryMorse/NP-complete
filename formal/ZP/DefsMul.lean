module

public import ZP.Defs
public import ZP.DefsF
public import ZP.DefsTwin

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

def checkMul (out s : List Bool) : Bool :=
  let N := numbers (out ++ false :: s) ++ [0, 0]
  N.getD 0 0 == N.getD 1 0 * N.getD 2 0

def correctMulB (J S : Nat) : Bool :=
  match runMul (str J) (str S) (clockMul (str J) (str S)) (str J).length with
  | some out => checkMul out (str S)
  | none => false

def CorrectMul (J S : Nat) : Prop := correctMulB J S = true

instance (J S : Nat) : Decidable (CorrectMul J S) := inferInstanceAs (Decidable (correctMulB J S = true))

def SentenceMul : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectMul J S

/-! Sanity checks against `ref/zmul_ref.py`. -/

-- first refutations: (J, s) = ('', ''), ('0', ''), ('1', '11011'), ('00', '')
example : ¬ CorrectMul 1 1 := by decide
example : ¬ CorrectMul 2 1 := by decide
example : ¬ CorrectMul 3 59 := by decide
example : CorrectMul 3 1 := by decide
example : runMul [] [] (clockMul [] []) 0 = none := by decide
example : checkMul [] [false] = true := by decide
example : checkMul [true, false] [true, true, false] = true := by decide

example : ¬ CorrectMul 4 1 := by decide
example : (List.range 58).all (fun i => correctMulB 3 (i + 1)) = true := by decide +kernel

end ZP
