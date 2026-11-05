module

public import ZP.DefsF
public import ZP.TableD

@[expose] public section

/-!
# Definitions for the DLOG machine (`native/zdl.py`, `ref/zdl_ref.py`)

The last four numbers of the instance (parsed as for FACTOR) are `(k, h, g, p)`; with three
numbers `k = 0`. `s ∈ L_D` iff `p` is prime and `g^e mod p = h` for some `0 ≤ e ≤ k`.
-/

namespace ZP

def isPrime (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || p % d != 0

/-- `ref/zdl_ref.in_LD`'s loop: `f` more tries; `y` is the current power. -/
def dlogLoop : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => false
  | f + 1, y, g, h, p => if y = h then true else dlogLoop f (y * g % p) g h p

def inLD (s : List Bool) : Bool :=
  match (numbers s).reverse with
  | p :: g :: h :: r => isPrime p && dlogLoop (r.headD 0 + 1) 1 g h p
  | _ => false

def CorrectD (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inLD (str S)

instance (J S : Nat) : Decidable (CorrectD J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inLD (str S)))

def SentenceD : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → CorrectD J S

end ZP
