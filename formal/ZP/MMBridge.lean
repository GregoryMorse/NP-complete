module

public import ZP.MMRowsAll

@[expose] public section

/-! The GF(2) meaning of the accumulator: column `j` of `accFold As Rws C` is `C[j] xor sum_k A[k] B[k][j]`. -/

namespace ZP.Mul.MM

open ZP

/-- Symbol of a bit (`2` = bit `0`, `3` = bit `1`). -/
def sy (b : Bool) : Nat := if b then 3 else 2

/-- Bit of a symbol. -/
def bt (x : Nat) : Bool := decide (x = 3)

def prodCol : List Nat → List (List Nat) → Nat → Bool
  | s :: As, V :: Rws, j => xor (bt s && bt (V.getD j 2)) (prodCol As Rws j)
  | _, _, _ => false

theorem bt_jc (s v x : Nat) (hs : s = 2 ∨ s = 3) (hx : x = 2 ∨ x = 3) :
    bt (jc (aOf s) v x) = xor (bt x) (bt s && bt v) := by
  rcases hs with rfl | rfl <;> rcases hx with rfl | rfl <;> by_cases hv : v = 3 <;> simp [jc, aOf, bt, hv]

theorem accFold_col : ∀ (As : List Nat) (Rws : List (List Nat)) (C : List Nat), (∀ s ∈ As, s = 2 ∨ s = 3) →
    Bits C → (∀ r ∈ Rws, Bits r ∧ r.length = C.length) → ∀ j, j < C.length →
    bt ((accFold As Rws C).getD j 2) = xor (bt (C.getD j 2)) (prodCol As Rws j)
  | [], Rws, C, _, _, _, j, _ => by simp [accFold, prodCol]
  | s :: As, [], C, _, _, _, j, _ => by simp [accFold, prodCol]
  | s :: As, V :: Rws, C, hA, hC, hR, j, hj => by
    obtain ⟨hVb, hVl⟩ := hR V (by simp)
    have h1 := bits_zipWith (aOf s) V C hVb hC
    have h2 := len_zipWith (aOf s) V C hVl
    have ih := accFold_col As Rws (List.zipWith (jc (aOf s)) V C) (fun t ht => hA t (by simp [ht])) h1
      (fun r hr => ⟨(hR r (by simp [hr])).1, by rw [h2]; exact (hR r (by simp [hr])).2⟩) j (by rw [h2]; exact hj)
    simp only [accFold, prodCol]
    rw [ih]
    have hjV : j < V.length := by omega
    have e : (List.zipWith (jc (aOf s)) V C).getD j 2 = jc (aOf s) (V.getD j 2) (C.getD j 2) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, hjV, hj]
    rw [e, bt_jc s _ _ (hA s (by simp))]
    · cases bt (C.getD j 2) <;> cases bt s <;> cases bt (V.getD j 2) <;> cases prodCol As Rws j <;> rfl
    · have : C.getD j 2 ∈ C := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rcases mem_bits (hC _ this) with h | h
      · exact Or.inl h
      · exact Or.inr h

end ZP.Mul.MM
