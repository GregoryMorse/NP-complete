module

public import ZP.Defs
public import ZP.TablePS

@[expose] public section

/-!
# Definitions for the P = PSPACE machine (`native/zps.py`, `ref/zps_ref.py`)

`G(s) = Q_0 c_0 … Q_n c_n : run(s, c, n+1) = ACC` with `Q_n = ∃` and alternating quantifiers.
-/

namespace ZP

/-- Value of the game node with certificate prefix `p` and `d` levels below it
(`ref/zps_ref.val`): the player is ∃ iff `d` is even, and a dominant first child
(value `= player`) short-circuits. -/
def gval (s : List Bool) : Nat → List Bool → Bool
  | 0, p => run s p (s.length + 1)
  | d + 1, p =>
    let ex := d % 2 == 0
    let a := gval s d (p ++ [true])
    if a == ex then a else gval s d (p ++ [false])

def inPS (s : List Bool) : Bool := gval s (s.length + 1) []

def CorrectPS (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inPS (str S)

instance (J S : Nat) : Decidable (CorrectPS J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inPS (str S)))

def SentencePS : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectPS J S

end ZP
