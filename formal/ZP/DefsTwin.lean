module

@[expose] public section

/-!
# Twin primes: the trusted statement

Core Lean has no `Nat.Prime`, so primality is defined plainly.
-/

namespace ZP

/-- `p` is prime. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime
  exact inferInstance

/-- There are infinitely many twin primes. -/
def TwinPrimes : Prop := ∀ n, ∃ p, n ≤ p ∧ IsPrime p ∧ IsPrime (p + 2)

end ZP
