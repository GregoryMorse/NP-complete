module

@[expose] public section

namespace ZP

/-- proper divisors of n, as a list (increasing) -/
def divs (n : Nat) : List Nat := (List.range n).filter (fun e => 0 < e && n % e == 0)

/-- Euler's totient -/
def phi (n : Nat) : Nat := ((List.range n).filter (fun k => Nat.gcd k n == 1)).length

theorem mem_divs {n e : Nat} : e ∈ divs n ↔ 0 < e ∧ e < n ∧ e ∣ n := by
  simp only [divs, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, Nat.dvd_of_mod_eq_zero h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, Nat.mod_eq_zero_of_dvd h3⟩

theorem divs_nodup (n : Nat) : (divs n).Nodup := List.nodup_range.filter _

theorem phi_pos {n : Nat} (hn : 1 ≤ n) : 1 ≤ phi n := by
  unfold phi
  apply List.length_pos_of_mem (a := if n = 1 then 0 else 1)
  rw [List.mem_filter, List.mem_range]
  by_cases h : n = 1
  · subst h; simp
  · simp only [h, ite_false]
    simp
    omega

theorem count_split {α : Type} (f : α → Nat) : ∀ (D : List Nat) (l : List α), D.Nodup →
    (∀ x ∈ l, f x ∈ D) →
    l.length = (D.map fun g => (l.filter (fun x => f x == g)).length).sum
  | [], l, _, h => by
    cases l with
    | nil => rfl
    | cons x t => exact absurd (h x (by simp)) (by simp)
  | g :: D, l, hD, h => by
    have hnd := List.nodup_cons.1 hD
    have ih := count_split f D (l.filter (fun x => f x != g)) hnd.2 (by
      intro x hx
      rw [List.mem_filter] at hx
      rcases List.mem_cons.1 (h x hx.1) with h1 | h1
      · simp [h1] at hx
      · exact h1)
    simp only [List.map_cons, List.sum_cons]
    have hs : (D.map fun g' => (l.filter (fun x => f x == g')).length) =
        (D.map fun g' => ((l.filter (fun x => f x != g)).filter (fun x => f x == g')).length) := by
      apply List.map_congr_left
      intro g' hg'
      rw [List.filter_filter]
      congr 1
      apply List.filter_congr
      intro x _
      by_cases e : f x == g'
      · have : f x ≠ g := by
          have e' := beq_iff_eq.1 e
          intro h2; exact hnd.1 (by rw [← h2, e']; exact hg')
        simp [e, this]
      · simp [e]
    rw [hs, ← ih]
    have := List.length_eq_countP_add_countP (fun x => f x == g) (l := l)
    simp only [List.countP_eq_length_filter] at this
    refine this.trans ?_
    congr 2

theorem fiber_len {n e : Nat} (hn : 1 ≤ n) (he : e ∣ n) :
    ((List.range n).filter (fun k => n / Nat.gcd k n == e)).length = phi e := by
  obtain ⟨g, rfl⟩ := he
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hn
    · exact h
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hn
    · exact h
  unfold phi
  have hinj : Function.Injective (fun j => g * j) := fun a b h => Nat.eq_of_mul_eq_mul_left hg h
  rw [← List.length_map (f := fun j => g * j)
    (as := (List.range e).filter (fun k => Nat.gcd k e == 1))]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup]
  · intro k
    have key : ∀ k, e * g / Nat.gcd k (e * g) = e ↔ Nat.gcd k (e * g) = g := by
      intro k
      have hd : Nat.gcd k (e * g) ∣ e * g := Nat.gcd_dvd_right _ _
      constructor
      · intro h
        have := Nat.div_mul_cancel hd
        rw [h] at this
        exact Nat.eq_of_mul_eq_mul_left he this
      · intro h
        rw [h]; exact Nat.mul_div_cancel e hg
    simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq, key]
    rw [iff_comm]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have : g * j < g * e := (Nat.mul_lt_mul_left hg).2 hj1
        rw [Nat.mul_comm e g]; exact this
      · rw [Nat.mul_comm e g, Nat.gcd_mul_left, hj2, Nat.mul_one]
    · rintro ⟨hk, hgk⟩
      have hdv : g ∣ k := hgk ▸ Nat.gcd_dvd_left k (e * g)
      obtain ⟨j, rfl⟩ := hdv
      rw [Nat.mul_comm e g, Nat.gcd_mul_left] at hgk
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rw [Nat.mul_comm e g] at hk
        exact (Nat.mul_lt_mul_left hg).1 hk
      · have : g * Nat.gcd j e = g * 1 := by rw [hgk, Nat.mul_one]
        exact Nat.eq_of_mul_eq_mul_left hg this
  · exact List.nodup_range.filter _
  · exact List.Pairwise.map (fun j => g * j) (fun a b h e => h (hinj e))
      (List.nodup_range.filter _)

theorem phi_sum {n : Nat} (hn : 1 ≤ n) : phi n + ((divs n).map phi).sum = n := by
  have hnd : (divs n ++ [n]).Nodup := by
    rw [List.nodup_append]
    refine ⟨divs_nodup n, by simp, ?_⟩
    intro a ha b hb
    simp at hb; subst hb
    intro h; subst h
    have := (mem_divs.1 ha).2.1
    omega
  have hc := count_split (fun k => n / Nat.gcd k n) (divs n ++ [n]) (List.range n) hnd (by
    intro k hk
    have hk' := List.mem_range.1 hk
    have hgp : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_right _ hn
    have hdv : Nat.gcd k n ∣ n := Nat.gcd_dvd_right _ _
    generalize Nat.gcd k n = d at hgp hdv ⊢
    obtain ⟨m, hm⟩ := hdv
    have hq : n / d = m := by
      rw [hm]; exact Nat.mul_div_cancel_left m hgp
    simp only [hq, List.mem_append, List.mem_singleton]
    by_cases hmn : m = n
    · exact Or.inr hmn
    · left
      rw [mem_divs]
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hm; omega
        · exact h
      have hmd : m ∣ n := ⟨d, by rw [hm, Nat.mul_comm]⟩
      have hmle : m ≤ n := Nat.le_of_dvd hn hmd
      exact ⟨hm0, by omega, hmd⟩)
  rw [List.length_range] at hc
  rw [List.map_append, List.sum_append] at hc
  have h1 : ((divs n).map fun g => ((List.range n).filter (fun x => n / Nat.gcd x n == g)).length)
      = (divs n).map phi := by
    apply List.map_congr_left
    intro e he
    exact fiber_len hn (mem_divs.1 he).2.2
  rw [h1] at hc
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc
  rw [fiber_len hn (Nat.dvd_refl n)] at hc
  omega

end ZP
