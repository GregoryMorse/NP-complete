module

public import ZP.PairPolyPair
public import ZP.AbstractPoly

@[expose] public section

/-!
# One abstract step, simulated

`layPoly st` is the configuration of the state `st = (K, n, A, v)`; one `polyStep` is one
run of the logical machine, visiting the beep state iff `polyOver st`, and then once.
-/

namespace ZP.Poly

open ZP

/-- The configuration of the abstract state `st`: `M_g rev(K) M_1 a M_a s`. -/
def layPoly (st : PSt) : ZC :=
  layP (bitsOf (str st.K).reverse) (bitsOf (str st.A)) (bitsOf (svec st.n st.v))

theorem layP_q (Kr a s : List Nat) : (layP Kr a s).q = Q.GRB := by
  unfold layP
  rw [hdR_eqP]

theorem LTM.Reach.seg_pos {L : LTM} {c m d : ZC} (h1 : L.Reach c m) (hq : c.q ≠ m.q)
    (h2 : L.Reach m d) : ∃ n, 0 < n ∧ L.zrun n c = some d := by
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  cases n1 with
  | zero =>
    have : c = m := Option.some.inj hn1
    exact absurd (by rw [this]) hq
  | succ n1 =>
    refine ⟨n1 + 1 + n2, by omega, ?_⟩
    rw [LTM.zrun_add, hn1]
    exact hn2


/-! ## Counters -/

theorem ofBv_next : ∀ n v : Nat, v + 1 < 2 ^ n →
    false ∈ ofBv n v ∧ incR (ofBv n v) = ofBv n (v + 1)
  | 0, v, h => by simp at h
  | n + 1, v, h => by
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ _ _
    by_cases hm : v % 2 = 1
    · have hlt : v / 2 + 1 < 2 ^ n := by omega
      obtain ⟨h1, h2⟩ := ofBv_next n (v / 2) hlt
      have e1 : (v + 1) % 2 = 0 := by omega
      have e2 : (v + 1) / 2 = v / 2 + 1 := by omega
      refine ⟨?_, ?_⟩
      · simp [ofBv, hm, h1]
      · simp [ofBv, hm, incR, h2, e1, e2]
    · have hm0 : v % 2 = 0 := by omega
      have e1 : (v + 1) % 2 = 1 := by omega
      have e2 : (v + 1) / 2 = v / 2 := by omega
      refine ⟨?_, ?_⟩
      · simp [ofBv, hm]
      · simp [ofBv, hm, incR, e1, e2]

theorem ofBv_carry : ∀ n v : Nat, v + 1 = 2 ^ n → ∀ x ∈ ofBv n v, x = true
  | 0, v, _ => by simp [ofBv]
  | n + 1, v, h => by
    have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ _ _
    have hm : v % 2 = 1 := by omega
    have hd : v / 2 + 1 = 2 ^ n := by omega
    have := ofBv_carry n (v / 2) hd
    intro x hx
    simp only [ofBv, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [hm]
    · exact this x hx

theorem ofBv_zero : ∀ n, ofBv n 0 = List.replicate n false
  | 0 => rfl
  | n + 1 => by simp [ofBv, ofBv_zero n, List.replicate_succ]

theorem svec_zero (n : Nat) : svec n 0 = List.replicate n false := by
  simp [svec, ofBv_zero]

theorem svec_succ_eq (n v : Nat) : svec n v = (ofBv n v).reverse := rfl

/-! ## Numerals -/

theorem nums (st : PSt) (hK : 1 ≤ st.K) (hA : 1 ≤ st.A) :
    ∃ rK rA : List Bool, str st.K = rK.reverse ∧ str st.A = rA.reverse ∧
      str (st.K + 1) = (incR rK).reverse ∧ str (st.A + 1) = (incR rA).reverse := by
  obtain ⟨rK, hrK⟩ := numR_surj st.K hK
  obtain ⟨rA, hrA⟩ := numR_surj st.A hA
  refine ⟨rK, rA, ?_, ?_, ?_, ?_⟩
  · rw [← hrK, str_numR]
  · rw [← hrA, str_numR]
  · rw [← hrK, ← numR_inc, str_numR]
  · rw [← hrA, ← numR_inc, str_numR]

end ZP.Poly
