module

public import ZP.Pair
public import ZP.GuestCompile

@[expose] public section

/-!
# The sentence and P = NP: one direction

* `sentence_iff`: `Sentence` says exactly that one guest code `J` decides `L`
  within `clock J`, on every input.
* `sentence_of_InP`: if `L ∈ P` then `Sentence` (compile the decider, padded so
  that `clock` exceeds its time bound).
* `sentence_of_PeqNP`: hence `P = NP → Sentence`, given `L ∈ NP`.

`L ∈ NP` is `Lp_InNP` (`ZP/Verif.lean`); the converse `Sentence → P = NP` and the
equivalence `sentence_iff_PeqNP` are in `ZP/Hard.lean`.
-/

namespace ZP.Cx

/-- The language `L` of `docs/native.md`. -/
def Lp (s : List Bool) : Prop := inL s = true

theorem str_surj (s : List Bool) : ∃ N, 1 ≤ N ∧ str N = s :=
  ⟨numR s.reverse, by have := numR_gt s.reverse; omega, by rw [str_numR, List.reverse_reverse]⟩

theorem sentence_iff : Sentence ↔ ∃ J : List Bool, ∀ s, run J s (clock J s) = inL s := by
  constructor
  · rintro ⟨J, -, hJ⟩
    refine ⟨str J, fun s => ?_⟩
    obtain ⟨S, hS, rfl⟩ := str_surj s
    exact hJ S hS
  · rintro ⟨J, hJ⟩
    obtain ⟨N, hN, rfl⟩ := str_surj J
    exact ⟨N, hN, fun S _ => hJ (str S)⟩

theorem pow_le_clock (n k m : Nat) (h : k ≤ m) : (n + 2) ^ k ≤ (n + 2) ^ (m + 1) - 1 := by
  have h1 : (n + 2) ^ k ≤ (n + 2) ^ m := Nat.pow_le_pow_right (by omega) h
  have h2 : (n + 2) ^ (m + 1) = (n + 2) ^ m * n + (n + 2) ^ m * 2 := by
    rw [Nat.pow_succ, Nat.mul_add]
  have h3 : 1 ≤ (n + 2) ^ m := Nat.pow_pos (by omega : 0 < n + 2)
  omega

theorem sentence_of_InP (h : InP Lp) : Sentence := by
  obtain ⟨D, k, hD⟩ := h
  obtain ⟨P, hP, hrun⟩ := compile D k
  refine sentence_iff.mpr ⟨P, fun s => ?_⟩
  obtain ⟨b, hb, hiff⟩ := hD s
  rw [hrun]
  unfold clock
  rw [exec_mono D _ 0 _ 0 b hb _ (pow_le_clock s.length k P.length hP)]
  exact bool_eq_of_iff (by simpa [Lp] using hiff)

theorem sentence_of_PeqNP (hL : InNP Lp) (h : PeqNP) : Sentence :=
  sentence_of_InP ((h Lp).mpr hL)

end ZP.Cx
