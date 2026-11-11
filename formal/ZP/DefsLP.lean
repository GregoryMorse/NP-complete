module

public import ZP.DefsMH
public import ZP.TableLP

@[expose] public section

/-!
# Definitions for the L = P machine (`native/zlp.py`, `ref/zmh_ref.py`)

`L_P = { s : runMH s s (|s|+1) accepts }`: the program `s` run on its own text with
`|s| + 1` heads. A candidate `J` is correct on `s` if the multihead run of `J` on `s`
within the clock agrees with `L_P`. The enumeration and the clock are those of
`ZP/Defs.lean`.
-/

namespace ZP

def inLP (s : List Bool) : Bool := runMH s s (s.length + 1)

def CorrectLP (J S : Nat) : Prop :=
  runMH (str J) (str S) (clock (str J) (str S)) = inLP (str S)

instance (J S : Nat) : Decidable (CorrectLP J S) :=
  inferInstanceAs (Decidable (runMH (str J) (str S) (clock (str J) (str S)) = inLP (str S)))

def SentenceLP : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectLP J S

end ZP
