module

public import ZP.DefsMH
public import ZP.TableLNL

@[expose] public section

/-!
# Definitions for the L = NL machine (`native/zlnl.py`, `ref/znl_ref.py`)

`run1` is `run` of `ZP/Defs.lean` with a one-way head: a left move (`d = 0`) leaves the head in
place. `L_NL = { s : some certificate c of length |s|+1 has run1 s c (|s|+1) accepting }`.
A candidate `J` is correct on `s` if the multihead run of `J` on `s` within the clock agrees
with `L_NL`. The enumeration and the clock are those of `ZP/Defs.lean`.
-/

namespace ZP

/-- `runAux` with a one-way head: `d = 0` leaves the head in place. -/
def run1Aux : Nat → List Bool → (Nat → Option Bool) → Nat → Bool
  | 0, _, _, _ => false
  | T + 1, R0, tape, h =>
    let R := rotN (iota (tape h)) R0
    if R.getD 2 false then
      run1Aux T (rotN (entryOnes R + 1) (rot R))
        (fun i => if i = h then some (R.getD 0 false) else tape i)
        (if R.getD 1 false then h + 1 else h)
    else R.getD 0 false

/-- Guest program `P` on input `x` with a one-way head, at most `T` steps. -/
def run1 (P x : List Bool) (T : Nat) : Bool :=
  run1Aux T (rot (P.reverse ++ [false])) (fun i => x[i]?) 0

/-- `s ∈ L_NL`: some certificate of length `|s|+1` makes the one-way program `s` accept
within `|s|+1` steps. -/
def inLNL (s : List Bool) : Bool :=
  (strings (s.length + 1)).any fun c => run1 s c (s.length + 1)

def CorrectLNL (J S : Nat) : Prop :=
  runMH (str J) (str S) (clock (str J) (str S)) = inLNL (str S)

instance (J S : Nat) : Decidable (CorrectLNL J S) :=
  inferInstanceAs (Decidable (runMH (str J) (str S) (clock (str J) (str S)) = inLNL (str S)))

def SentenceLNL : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectLNL J S

end ZP
