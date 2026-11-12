module

public import ZP.Defs
public import ZP.DefsMul

@[expose] public section

/-!
# Definitions for the GF(2) matrix-product machine (`native/zmm.py`, `ref/zmm_ref.py`)

The guest model, fuel and clock are those of `zmul` (`runMul`, `clockMul`).  Only the truth of a
proper halt changes: the output, padded with `0`s, must start with `C = A B` over GF(2), where
`s = 1^m 0 w`, `B` is the first `m²` cells of `w` (padded) as an `m × m` matrix, and `A` is the
rest of `w` cut into rows of length `m` (the last row padded).
-/

namespace ZP

/-- `m`, the number of leading `1`s of `s`. -/
def mmM (s : List Bool) : Nat := (s.takeWhile id).length

/-- `w`: what follows the first `0` of `s`. -/
def mmW (s : List Bool) : List Bool := s.drop (mmM s + 1)

/-- The first `n` entries of `l`, padded with `false`. -/
def padTo (n : Nat) (l : List Bool) : List Bool := (l ++ List.replicate n false).take n

/-- `B[k][j]`. -/
def mmB (s : List Bool) (k j : Nat) : Bool :=
  (padTo (mmM s ^ 2) (mmW s)).getD (k * mmM s + j) false

/-- The number of rows of `A`. -/
def mmRows (s : List Bool) : Nat :=
  if mmM s = 0 then 0 else ((mmW s).length - mmM s ^ 2 + mmM s - 1) / mmM s

/-- `A[i][k]`. -/
def mmA (s : List Bool) (i k : Nat) : Bool :=
  ((mmW s).drop (mmM s ^ 2)).getD (i * mmM s + k) false

/-- `C = A B` over GF(2), row-major. -/
def mmC (s : List Bool) : List Bool :=
  (List.range (mmRows s)).flatMap fun i => (List.range (mmM s)).map fun j =>
    (List.range (mmM s)).foldl (fun acc k => xor acc (mmA s i k && mmB s k j)) false

def checkMM (out s : List Bool) : Bool := padTo (mmC s).length out == mmC s

def correctMMB (J S : Nat) : Bool :=
  match runMul (str J) (str S) (clockMul (str J) (str S)) (str J).length with
  | some out => checkMM out (str S)
  | none => false

def CorrectMM (J S : Nat) : Prop := correctMMB J S = true

instance (J S : Nat) : Decidable (CorrectMM J S) := inferInstanceAs (Decidable (correctMMB J S = true))

def SentenceMM : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectMM J S

/-! Sanity checks against `ref/zmm_ref.py`. -/

-- `s = 110 1011 0110 1`: `m = 2`, `B = [[1,0],[1,1]]`, `A` has three rows `01, 10, 10`
example : mmM [true, true, false, true, false, true, true, false, true, true, false, true] = 2 := by decide
example : mmRows [true, true, false, true, false, true, true, false, true, true, false, true] = 3 := by decide
example : mmC [true, true, false, true, false, true, true, false, true, true, false, true] =
    [true, true, true, false, true, false] := by decide
example : checkMM [true, true, true, false, true, false]
    [true, true, false, true, false, true, true, false, true, true, false, true] = true := by decide
example : checkMM [true, true, true, false, true, false, true, true]
    [true, true, false, true, false, true, true, false, true, true, false, true] = true := by decide
example : checkMM [true, true, true, false, true, true]
    [true, true, false, true, false, true, true, false, true, true, false, true] = false := by decide
-- missing output cells read as `0`
example : checkMM [] [true, true, false, false, false, false, false, false, false] = true := by decide
-- `m = 0`: `C` is empty
example : mmC [false, true, true] = [] := by decide
example : mmC [] = [] := by decide
example : checkMM [] [] = true := by decide
-- `|w| ≤ m²`: `C` is empty
example : mmC [true, false, true] = [] := by decide
example : mmC [true, true, false, true, true] = [] := by decide
-- a short last row of `A` is padded: `m = 1`, `B = 1`, `A = 1 0 1`
example : mmC [true, false, true, true, false, true] = [true, false, true] := by decide

-- first beeps: `('', '')`, `('0', '')`, `('1', '1011')`, `('00', '')`
example : ¬ CorrectMM 1 1 := by decide
example : ¬ CorrectMM 2 1 := by decide
example : ¬ CorrectMM 3 27 := by decide
example : ¬ CorrectMM 4 1 := by decide
example : CorrectMM 3 1 := by decide
example : (List.range 26).all (fun i => correctMMB 3 (i + 1)) = true := by decide +kernel

end ZP
