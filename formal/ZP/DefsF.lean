module

public import ZP.Defs
public import ZP.TableF
public import ZP.DefsPS

@[expose] public section

/-!
# Definitions for the FACTOR machine (`native/zfac.py`, `ref/zfac_ref.py`)

The instance `s` is parsed left to right into numbers: a pair `1b` appends the binary digit
`b` to the current number, a `0` starts the next number (a trailing lone `1` is ignored).
`s ∈ L_F` iff there are at least two numbers `k, a` and some `d` with `2 ≤ d ≤ k` divides `a`.
-/

namespace ZP

/-- Fuel-structured parser (one step consumes one or two bits, so `s.length` fuel suffices). -/
def numsAux : Nat → List Bool → Nat → List Nat
  | 0, _, cur => [cur]
  | _ + 1, [], cur => [cur]
  | _ + 1, [true], cur => [cur]
  | f + 1, true :: b :: r, cur => numsAux f r (2 * cur + if b then 1 else 0)
  | f + 1, false :: r, cur => cur :: numsAux f r 0

/-- `ref/zfac_ref.numbers`. -/
def numbers (s : List Bool) : List Nat := numsAux s.length s 0

def inLF (s : List Bool) : Bool :=
  match numbers s with
  | k :: a :: _ => (List.range (k + 1)).any fun d => decide (2 ≤ d) && a % d == 0
  | _ => false

def CorrectF (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inLF (str S)

instance (J S : Nat) : Decidable (CorrectF J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inLF (str S)))

def SentenceF : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectF J S

end ZP
