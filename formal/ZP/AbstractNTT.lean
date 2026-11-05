module

public import ZP.PadNTT

@[expose] public section

/-! # The abstract program of the NTT machine -/

namespace ZP

theorem valsAux_ones : ∀ (k j : Nat) (vs : List Nat), vs.length = j → (j = 0 ∨ vs.getLastD 0 = 1) →
    valsAux 0 2 j (List.replicate k ((none : Option Nat), 1)) vs = vs ++ List.replicate k 1
  | 0, j, vs, _, _ => by simp [valsAux]
  | k + 1, j, vs, hl, hj => by
    simp only [List.replicate_succ, valsAux]
    have hv : ((if j = 0 then 1 else 0) + vs.getLastD 0 + ptrVal none j 1 vs) % 2 = 1 := by
      rcases hj with h | h
      · subst h
        have : vs = [] := List.length_eq_zero_iff.1 hl
        subst this; simp [ptrVal]
      · by_cases h0 : j = 0
        · subst h0
          have : vs = [] := List.length_eq_zero_iff.1 hl
          subst this; simp [ptrVal]
        · have e : (if j = 0 then 1 else 0) = 0 := by simp [h0]
          rw [e, h]; simp [ptrVal]
    simp only [hv]
    rw [valsAux_ones k (j + 1) _ (by simp [hl]) (Or.inr (by simp [getLastD_append]))]
    simp [List.replicate_succ', List.append_assoc]

theorem evalC_ones (c : Nat) (hc : 1 ≤ c) : evalC 1 2 (List.replicate c ((none : Option Nat), 1)) = true := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hv := valsAux_ones (c + 1) 0 [] rfl (Or.inl rfl)
  simp only [List.nil_append] at hv
  have hg : (List.replicate (c + 1) 1).getD c 0 = 1 := getD_rep _ _ _ (by omega)
  unfold evalC evalPass
  simp only [List.length_replicate, show c + 1 - 1 = c by omega, List.range_one, List.foldl_cons,
    List.foldl_nil, Option.bind_some]
  simp only [hv]
  simp [hg]

end ZP
