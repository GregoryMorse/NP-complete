module

public import ZP.Defs

@[expose] public section

/-!
# Definitions for the NP = coNP machine (`native/zconp.py`, `ref/zconp_ref.py`)

The guest is `zp2` with nondeterminism at fresh cells: whenever the head moves right onto a cell beyond
everything visited so far (beyond the input, and beyond `top`), a choice bit is consumed. Choice `1` puts a `1`
in the cell, choice `0` leaves it blank. The start cell is not a choice. `runND` is existential over the
choice string; the machine searches the choice strings depth first (that this agrees is a theorem).
-/

namespace ZP

/-- `P.rstrip('1')`. -/
def core (P : List Bool) : List Bool := (P.reverse.dropWhile (· == true)).reverse

/-- `zconp_ref.run_choice`: at most `T` steps; the choice string `D` is extended lazily with `1`s.
`used` is the list of choices consumed so far; the result is `(accepted, choices used)`. -/
def runChoiceAux : Nat → List Bool → (Nat → Option Bool) → Nat → Nat → List Bool → List Bool →
    Bool × List Bool
  | 0, _, _, _, _, _, used => (false, used)
  | T + 1, R0, tape, h, top, D, used =>
    let R := rotN (iota (tape h)) R0
    if R.getD 2 false then
      let tape' := fun i => if i = h then some (R.getD 0 false) else tape i
      let R' := rotN (entryOnes R + 1) (rot R)
      if R.getD 1 false then
        if top < h + 1 then
          let c := D.getD used.length true
          runChoiceAux T R' (fun i => if i = h + 1 ∧ c = true then some true else tape' i) (h + 1) (h + 1) D
            (used ++ [c])
        else runChoiceAux T R' tape' (h + 1) top D used
      else runChoiceAux T R' tape' (h - 1) top D used
    else (R.getD 0 false, used)

/-- One run of `P` on `x` for at most `T` steps with the choices `D`. -/
def runChoice (P x : List Bool) (T : Nat) (D : List Bool) : Bool × List Bool :=
  runChoiceAux T (rot (P.reverse ++ [false])) (fun i => x[i]?) 0 (x.length - 1) D []

/-- `run_nd`: some choice string makes the run of `core P` accept. -/
def runND (P x : List Bool) (T : Nat) : Prop := ∃ D : List Bool, (runChoice (core P) x T D).1 = true

/-- `s ∈ L`: the program `s` accepts the empty input within `|s| + 1` steps, for some choices. -/
def inLC (s : List Bool) : Prop := runND s [] (s.length + 1)

/-- Candidate `J` is a nondeterministic verifier for the complement of `L` on `s`. -/
def CorrectConp (J S : Nat) : Prop := runND (str J) (str S) (clock (str J) (str S)) ↔ ¬ inLC (str S)

open Classical in
noncomputable instance (J S : Nat) : Decidable (CorrectConp J S) := Classical.propDecidable _

def SentenceConp : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectConp J S

end ZP
