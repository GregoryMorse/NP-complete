module

public import ZP.DefsG

@[expose] public section

/-!
# Definitions for the NTT machine (`native/zntt.py`, `ref/zntt_ref.py`)

`evalC n p recs` mirrors `zntt_ref.evaluate` literally. The prime `p` is a parameter here;
the prime function `primeN` is introduced separately.
-/

namespace ZP

/-- A record: pointer `u` (`none` or an earlier index) and coefficient `b`. -/
abbrev Rec := Option Nat × Nat

/-- The contribution of a pointer. -/
def ptrVal (u : Option Nat) (j b : Nat) (vs : List Nat) : Nat :=
  match u with
  | some u => if u < j then b * vs.getD u 0 else 0
  | none => 0

/-- Node values of pass `t`: `valsAux t p j recs vs` appends the values of `recs` (starting at
index `j`) to `vs`. -/
def valsAux (t p : Nat) : Nat → List Rec → List Nat → List Nat
  | _, [], vs => vs
  | j, (u, b) :: rs, vs =>
    let v := ((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p
    valsAux t p (j + 1) rs (vs ++ [v])

/-- One pass `t`: compare outputs with `E`, update `E`, check the power sum. -/
def evalPass (n p : Nat) (recs : List Rec) (t : Nat) (E : List Nat) : Option (List Nat) :=
  let N := recs.length
  let zs := (recs.drop (N - n)).map Prod.snd
  let val := valsAux t p 0 recs []
  if (List.range n).all (fun k => val.getD (N - n + k) 0 == E.getD k 0) then
    let E' := (List.range n).map fun k => E.getD k 0 * zs.getD k 0 % p
    if ((E'.foldl (· + ·) 0 % p == 0) == (t == n - 1)) then none else some E'
  else none

def evalC (n p : Nat) (recs : List Rec) : Bool :=
  ((List.range n).foldl (fun st t => st.bind fun E => evalPass n p recs t E) (some (List.replicate n 1))).isSome

/-- The choices for the record at index `j`. -/
def recChoices (j p : Nat) : List Rec :=
  (List.range p).map (fun b => ((none : Option Nat), b)) ++
    (List.range j).flatMap fun u => (List.range p).map fun b => (some u, b)

/-- All record lists of length `k` starting at index `j`. -/
def allRecs (p : Nat) : Nat → Nat → List (List Rec)
  | 0, _ => [[]]
  | k + 1, j => (recChoices j p).flatMap fun r => (allRecs p k (j + 1)).map (r :: ·)

/-- `pr n` is the prime used for `n`. -/
def hasCircuit (pr : Nat → Nat) (c n : Nat) : Bool :=
  (allRecs (pr n) (c * n) 0).any (evalC n (pr n))

/-- The sentence: some `c` gives a circuit for every `n ≥ 1`. -/
def SentenceN (pr : Nat → Nat) : Prop := ∃ c, ∀ n, 1 ≤ n → hasCircuit pr c n = true

def isPrimeN (p : Nat) : Bool := decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || decide (p % d ≠ 0)

/-- The hypothesis: every `n ≥ 1` has a prime `1 + n i` with `i ≥ 1` (Dirichlet for `≡ 1 (mod n)`). -/
def PrimeEx : Prop := ∀ n, 1 ≤ n → ∃ i, 1 ≤ i ∧ isPrimeN (1 + n * i) = true

theorem exists_least (P : Nat → Prop) (h : ∃ i, P i) : ∃ i, P i ∧ ∀ j, P j → i ≤ j := by
  obtain ⟨i0, hi0⟩ := h
  induction i0 using Nat.strongRecOn with
  | _ i ih =>
    by_cases hl : ∃ j, j < i ∧ P j
    · obtain ⟨j, hj, hpj⟩ := hl
      exact ih j hj hpj
    · refine ⟨i, hi0, fun j hj => ?_⟩
      exact Nat.le_of_not_lt fun hlt => hl ⟨j, hlt, hj⟩

open Classical in
/-- `ref.prime`: the least prime `1 + n i`, `i ≥ 1`. -/
noncomputable def primeN (n : Nat) : Nat :=
  if h : ∃ i, 1 ≤ i ∧ isPrimeN (1 + n * i) = true then
    1 + n * Classical.choose (exists_least (fun i => 1 ≤ i ∧ isPrimeN (1 + n * i) = true) h)
  else 0

end ZP
