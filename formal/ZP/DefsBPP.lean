module

public import ZP.DefsPP
public import ZP.TableBPP

@[expose] public section

/-!
# Definitions for the promise-BPP machine (`native/zbpp.py`, `ref/zbpp_ref.py`)

For `s` with `N = 2^(|s|+1)` certificates and `acc = accCount s` accepted ones, the promise
problem is `YES` if `4 acc ≥ 3 N`, `NO` if `4 (N - acc) ≥ 3 N`, and `s` is outside the promise
otherwise. A candidate `J` is correct on `s` if `s` is outside the promise or `J` decides
`s` within the clock. The enumeration, guest semantics and clock are those of `ZP/Defs.lean`.
-/

namespace ZP

/-- `some true` (YES), `some false` (NO) or `none` (outside the promise). -/
def capp (s : List Bool) : Option Bool :=
  if 3 * 2 ^ (s.length + 1) ≤ 4 * accCount s then some true
  else if 3 * 2 ^ (s.length + 1) ≤ 4 * (2 ^ (s.length + 1) - accCount s) then some false
  else none

def CorrectBPP (J S : Nat) : Prop :=
  match capp (str S) with
  | none => True
  | some t => run (str J) (str S) (clock (str J) (str S)) = t

instance (J S : Nat) : Decidable (CorrectBPP J S) := by
  unfold CorrectBPP
  cases capp (str S) with
  | none => exact isTrue trivial
  | some t => exact inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = t))

def SentenceBPP : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectBPP J S

end ZP
