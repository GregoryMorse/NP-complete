module

public import ZP.Defs
public import ZP.TablePP

@[expose] public section

/-!
# Definitions for the P = PP machine (`native/zpp.py`, `ref/zpp_ref.py`)

`L_PP = { s : at least half of the c in {0,1}^(|s|+1) have run(s, c, |s|+1) = ACC }`.
The candidate/instance enumeration, the guest semantics and the clock are those of
`ZP/Defs.lean`; only the truth function changes.
-/

namespace ZP

/-- The number of certificates of length `|s|+1` that the guest `s` accepts. -/
def accCount (s : List Bool) : Nat :=
  ((strings (s.length + 1)).filter fun c => run s c (s.length + 1)).length

/-- `s ∈ L_PP`: at least half of the certificates are accepted. -/
def inPP (s : List Bool) : Bool := decide (2 ^ (s.length + 1) ≤ 2 * accCount s)

def CorrectPP (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inPP (str S)

instance (J S : Nat) : Decidable (CorrectPP J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inPP (str S)))

def SentencePP : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectPP J S

end ZP
