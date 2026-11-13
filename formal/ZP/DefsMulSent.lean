module

public import ZP.DefsMul

@[expose] public section

/-! The (retired) multiplication sentence; not part of the Challenge. See `README.md`. -/

namespace ZP

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
