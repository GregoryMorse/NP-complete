module

public import ZP.CompileN
public import ZP.AbstractNTT

@[expose] public section

/-!
# The NTT machine: from the pair lemma to the top theorem

`nttProg pr` is the abstract program of `ZP/AbstractNTT.lean` as an `AbsProg`. A `PairDataA` for
`znttLogic` (the one machine-level lemma, still to be proved) gives `Quasihalts znttMachine ↔ SentenceN pr`.
-/

namespace ZP

def nttProg (pr : Nat → Nat) : AbsProg where
  σ := Nat × Nat
  init := (1, 1)
  next := stepN pr
  good s := hasCircuit pr s.1 s.2 = true
  inv s := 1 ≤ s.1 ∧ 1 ≤ s.2
  inv_init := ⟨Nat.le_refl _, Nat.le_refl _⟩
  inv_next s h := by
    unfold stepN
    split <;> simp <;> omega

theorem nttProg_st (pr : Nat → Nat) (k : Nat) : (nttProg pr).st k = absN pr k := by
  induction k with
  | zero => rfl
  | succ k ih => show stepN pr ((nttProg pr).st k) = stepN pr (absN pr k); rw [ih]

theorem nttProg_Q (pr : Nat → Nat) : (nttProg pr).Q ↔ AbstractQN pr := by
  unfold AbsProg.Q AbstractQN
  simp only [nttProg_st]
  rfl

/-- The one machine-level lemma, given as pair data, yields the top theorem. -/
theorem zntt_quasihalts_of_pair (pr : Nat → Nat) (hp : NPrime pr) (P : PairDataA znttLogic (nttProg pr)) :
    Quasihalts znttMachine ↔ SentenceN pr :=
  match P.macroSim with
  | ⟨S⟩ => ((quasihalts_iff_of_macroSimA (znttMacroSimA S)).trans (nttProg_Q pr)).trans (abstractQN_iff pr hp)

theorem zntt_quasihalts_iff_sentence (h : PrimeEx) (P : PairDataA znttLogic (nttProg primeN)) :
    Quasihalts znttMachine ↔ SentenceN primeN :=
  zntt_quasihalts_of_pair primeN (nprime_primeN h) P

end ZP
