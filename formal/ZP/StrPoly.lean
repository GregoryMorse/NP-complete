module

public import ZP.AllDefs
public import ZP.Count

@[expose] public section

/-! Facts about `str` (the shortlex enumeration) and about bit strings used by plan 12. -/

namespace ZP

theorem strAux_spec : ∀ f N acc, 1 ≤ N → N ≤ f →
    ∃ k, 2 ^ k ≤ N ∧ N < 2 ^ (k + 1) ∧ (strAux f N acc).length = acc.length + k
  | 0, N, acc, h1, h2 => by omega
  | f + 1, N, acc, h1, h2 => by
    by_cases hN : N ≤ 1
    · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [strAux, hN] <;> omega
    · obtain ⟨k, hk1, hk2, hk3⟩ := strAux_spec f (N / 2) ((N % 2 == 1) :: acc) (by omega) (by omega)
      refine ⟨k + 1, ?_, ?_, ?_⟩
      · have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
        omega
      · have e1 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := Nat.pow_succ _ _
        have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ _ _
        omega
      · simp only [strAux, hN, if_false]; rw [hk3]; simp; omega

theorem str_spec {N : Nat} (h : 1 ≤ N) :
    2 ^ (str N).length ≤ N ∧ N < 2 ^ ((str N).length + 1) := by
  obtain ⟨k, h1, h2, h3⟩ := strAux_spec N N [] h (Nat.le_refl _)
  have : (str N).length = k := by simpa [str] using h3
  rw [this]; exact ⟨h1, h2⟩

theorem str_len_eq {N k : Nat} (h1 : 2 ^ k ≤ N) (h2 : N < 2 ^ (k + 1)) : (str N).length = k := by
  have hN : 1 ≤ N := Nat.le_trans (Nat.one_le_two_pow) h1
  obtain ⟨s1, s2⟩ := str_spec hN
  rcases Nat.lt_trichotomy (str N).length k with h | h | h
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) (show (str N).length + 1 ≤ k by omega)
    omega
  · exact h
  · have := Nat.pow_le_pow_right (by decide : 0 < 2) (show k + 1 ≤ (str N).length by omega)
    omega

theorem str_len_mono {A B : Nat} (hA : 1 ≤ A) (h : A ≤ B) : (str A).length ≤ (str B).length := by
  obtain ⟨a1, a2⟩ := str_spec hA
  obtain ⟨b1, b2⟩ := str_spec (Nat.le_trans hA h)
  refine Classical.byContradiction fun hc => ?_
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (show (str B).length + 1 ≤ (str A).length by omega)
  omega

theorem str_len_pow2 (k : Nat) : (str (2 ^ k)).length = k :=
  str_len_eq (Nat.le_refl _) (by rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := k); omega)

theorem strAux_fuel : ∀ f g N acc, 1 ≤ N → N ≤ f → N ≤ g → strAux f N acc = strAux g N acc
  | 0, g, N, acc, h1, h2, h3 => by omega
  | f + 1, 0, N, acc, h1, h2, h3 => by omega
  | f + 1, g + 1, N, acc, h1, h2, h3 => by
    by_cases hN : N ≤ 1
    · simp [strAux, hN]
    · simp only [strAux, hN, if_false]
      exact strAux_fuel f g (N / 2) _ (by omega) (by omega) (by omega)

theorem strAux_acc : ∀ f N acc, 1 ≤ N → N ≤ f → strAux f N acc = strAux f N [] ++ acc
  | 0, N, acc, h1, h2 => by omega
  | f + 1, N, acc, h1, h2 => by
    by_cases hN : N ≤ 1
    · simp [strAux, hN]
    · simp only [strAux, hN, if_false]
      rw [strAux_acc f (N / 2) _ (by omega) (by omega), strAux_acc f (N / 2) [_] (by omega) (by omega)]
      simp

theorem str_double {N : Nat} (b : Bool) (hN : 1 ≤ N) :
    str (2 * N + (if b then 1 else 0)) = str N ++ [b] := by
  have hM : 2 * N + (if b then 1 else 0) = (2 * N + (if b then 1 else 0) - 1) + 1 := by
    cases b <;> simp <;> omega
  have hne : ¬ (2 * N + (if b then 1 else 0) ≤ 1) := by cases b <;> simp <;> omega
  unfold str
  rw [hM]
  simp only [strAux]
  rw [← hM]
  simp only [hne, if_false]
  rw [strAux_acc _ _ _ (by omega) (by cases b <;> simp <;> omega)]
  have h2 : (2 * N + (if b then 1 else 0)) / 2 = N := by cases b <;> simp <;> omega
  have h3 : ((2 * N + (if b then 1 else 0)) % 2 == 1) = b := by cases b <;> simp <;> omega
  rw [h2, h3, strAux_fuel _ N _ _ (by omega) (by cases b <;> simp <;> omega) (Nat.le_refl _)]

theorem str_surj : ∀ l : List Bool, ∃ N, 1 ≤ N ∧ str N = l := by
  intro l
  suffices h : ∀ n, ∀ l : List Bool, l.length = n → ∃ N, 1 ≤ N ∧ str N = l from h _ l rfl
  intro n
  induction n with
  | zero => intro l hl; cases l with
    | nil => exact ⟨1, Nat.le_refl _, rfl⟩
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l hl
    obtain ⟨l', b, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left (by rintro rfl; simp at hl)
    obtain ⟨N, hN, hs⟩ := ih l' (by simpa using hl)
    exact ⟨2 * N + (if b then 1 else 0), by cases b <;> simp <;> omega, by rw [str_double b hN, hs, List.concat_eq_append]⟩

end ZP
