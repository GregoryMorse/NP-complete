module

public import ZP.Defs
public import ZP.TablePoly

@[expose] public section

/-!
# Definitions for the NP ⊆ P/poly machine (`native/zppoly.py`, `ref/zppoly_ref.py`)

A degree `K` (only `|K|` matters) fixes the budget `T(K, n) = (n+2)^(|K|+1) - 1`. An advice
program `a` is charged `|a|` steps up front. `K` is good on length `n` if some `a` of length
at most `T(K, n)` decides `L` (`inL`, `run` of `ZP/Defs.lean`) on all of `{0,1}^n` within the
budget. `SentencePoly` says that some degree is good on every length.
-/

namespace ZP

def budget (K : List Bool) (n : Nat) : Nat := (n + 2) ^ (K.length + 1) - 1

/-- Charged run: `|a|` steps up front, then `run a s` with the rest of the budget. -/
def prun (a s : List Bool) (t : Nat) : Bool := if a.length ≤ t then run a s (t - a.length) else false

/-- `a` decides `L` on all of `{0,1}^n` within the budget of degree `K`. -/
def advOK (K a : List Bool) (n : Nat) : Prop :=
  ∀ s ∈ strings n, prun a s (budget K n) = inL s

instance (K a : List Bool) (n : Nat) : Decidable (advOK K a n) := by
  unfold advOK; infer_instance

def goodLen (K : List Bool) (n : Nat) : Prop := ∃ a, a.length ≤ budget K n ∧ advOK K a n

def SentencePoly : Prop := ∃ K : List Bool, ∀ n, goodLen K n

end ZP
