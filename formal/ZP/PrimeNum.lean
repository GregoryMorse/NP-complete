module

public import ZP.AllDefs

@[expose] public section

namespace ZP

def IsP (q : Nat) : Prop := 2 ≤ q ∧ ∀ d, d ∣ q → d = 1 ∨ d = q

theorem IsP.coprime_of_not_dvd {q x : Nat} (h : IsP q) (hx : ¬ q ∣ x) : Nat.Coprime q x := by
  have := h.2 _ (Nat.gcd_dvd_left q x)
  rcases this with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ Nat.gcd_dvd_right q x) hx

theorem IsP.dvd_mul {q x y : Nat} (h : IsP q) (hd : q ∣ x * y) : q ∣ x ∨ q ∣ y := by
  by_cases hx : q ∣ x
  · exact Or.inl hx
  · exact Or.inr ((h.coprime_of_not_dvd hx).dvd_of_dvd_mul_left hd)

theorem IsP.dvd_pow {q x k : Nat} (h : IsP q) (hd : q ∣ x ^ k) : q ∣ x := by
  induction k with
  | zero =>
    rw [Nat.pow_zero] at hd
    have := Nat.le_of_dvd (by decide) hd
    have := h.1
    omega
  | succ k ih =>
    rw [Nat.pow_succ] at hd
    rcases h.dvd_mul hd with h1 | h1
    · exact ih h1
    · exact h1

theorem IsP.eq_of_dvd {p q : Nat} (hp : IsP p) (hq : IsP q) (h : q ∣ p) : q = p := by
  rcases hp.2 q h with h1 | h1
  · have := hq.1; omega
  · exact h1

theorem exists_isP_dvd {m : Nat} (hm : 2 ≤ m) : ∃ q, IsP q ∧ q ∣ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hp : IsP m
    · exact ⟨m, hp, Nat.dvd_refl m⟩
    · have : ∃ d, d ∣ m ∧ d ≠ 1 ∧ d ≠ m := by
        refine Classical.byContradiction fun hc => ?_
        apply hp
        refine ⟨hm, fun d hd => ?_⟩
        by_cases h1 : d = 1
        · exact Or.inl h1
        · by_cases h2 : d = m
          · exact Or.inr h2
          · exact absurd ⟨d, hd, h1, h2⟩ hc
      obtain ⟨d, hd, h1, h2⟩ := this
      have hm0 : 0 < m := by omega
      have hdl := Nat.le_of_dvd hm0 hd
      have hd0 : d ≠ 0 := by
        intro h0; subst h0
        have := Nat.eq_zero_of_zero_dvd hd
        omega
      obtain ⟨q, hq, hqd⟩ := ih d (by omega) (by omega)
      exact ⟨q, hq, Nat.dvd_trans hqd hd⟩

theorem isPrimeN_of_isP {q : Nat} (h : IsP q) : isPrimeN q = true := by
  unfold isPrimeN
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  refine ⟨h.1, fun d hd => ?_⟩
  by_cases h2 : d < 2
  · exact Or.inl h2
  · right
    intro h0
    have hdv : d ∣ q := Nat.dvd_of_mod_eq_zero h0
    rcases h.2 d hdv with h1 | h1 <;> omega

/-! ### Fermat -/

theorem prod_map_mod (a q : Nat) (l : List Nat) :
    (l.map (fun x => a * x % q)).prod % q = (a ^ l.length * l.prod) % q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, List.prod_cons, Nat.mul_mod, ih,
      Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ]
    congr 1
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem not_dvd_prod {q : Nat} (h : IsP q) (l : List Nat) (hl : ∀ x ∈ l, ¬ q ∣ x) :
    ¬ q ∣ l.prod := by
  induction l with
  | nil =>
    simp only [List.prod_nil]
    intro hd
    have := Nat.le_of_dvd (by decide) hd
    have := h.1
    omega
  | cons x l ih =>
    rw [List.prod_cons]
    intro hd
    rcases h.dvd_mul hd with h1 | h1
    · exact hl x (List.mem_cons_self) h1
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) h1

theorem mul_inj {q a x y : Nat} (h : IsP q) (ha : ¬ q ∣ a) (hy : y < q) (hxy : x ≤ y)
    (he : a * x % q = a * y % q) : x = y := by
  have h1 : (a * y - a * x) % q = 0 := Nat.sub_mod_eq_zero_of_mod_eq he.symm
  have h2 : q ∣ a * (y - x) := by
    rw [Nat.mul_sub]; exact Nat.dvd_of_mod_eq_zero h1
  rcases h.dvd_mul h2 with h3 | h3
  · exact absurd h3 ha
  · have := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega

theorem fermat {q a : Nat} (hq : IsP q) (ha : ¬ q ∣ a) : a ^ (q - 1) % q = 1 := by
  have hq2 := hq.1
  let L := List.range' 1 (q - 1)
  let f : Nat → Nat := fun x => a * x % q
  have hmem : ∀ x, x ∈ L ↔ 1 ≤ x ∧ x < q := by
    intro x
    show x ∈ List.range' 1 (q - 1) ↔ _
    rw [List.mem_range'_1]; omega
  have hLnd : L.Nodup := List.nodup_range'
  have hnd : (L.map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hLnd
    intro x y hx hy hne he
    have hx' := (hmem x).1 hx
    have hy' := (hmem y).1 hy
    apply hne
    by_cases hle : x ≤ y
    · exact mul_inj hq ha hy'.2 hle he
    · exact (mul_inj hq ha hx'.2 (by omega) he.symm).symm
  have hsub : ∀ y, y ∈ L.map f → y ∈ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have hx' := (hmem x).1 hx
    rw [hmem]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    apply Nat.pos_of_ne_zero
    intro h0
    rcases hq.dvd_mul (Nat.dvd_of_mod_eq_zero h0) with h1 | h1
    · exact ha h1
    · have := Nat.le_of_dvd (by omega) h1
      omega
  have hlen : (L.map f).length = L.length := List.length_map ..
  have hperm : (L.map f).Perm L := by
    rw [List.perm_ext_iff_of_nodup hnd hLnd]
    refine fun y => ⟨hsub y, fun hy => ?_⟩
    refine Classical.byContradiction fun hn => ?_
    have hnd' : (y :: L.map f).Nodup := List.nodup_cons.2 ⟨hn, hnd⟩
    have hs : (y :: L.map f) ⊆ L := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact hsub z hz
    have := hnd'.length_le_of_subset hs
    simp only [List.length_cons] at this
    omega
  have hprod : (L.map f).prod = L.prod := List.Perm.prod_nat hperm
  have hL : L.length = q - 1 := List.length_range'
  have hnl : ¬ q ∣ L.prod := by
    apply not_dvd_prod hq
    intro x hx hd
    have hx' := (hmem x).1 hx
    have := Nat.le_of_dvd (by omega) hd
    omega
  have key := prod_map_mod a q L
  rw [hprod, hL] at key
  have hapos : 0 < a := Nat.pos_of_ne_zero (fun h0 => ha (h0 ▸ Nat.dvd_zero q))
  have hpos : 1 ≤ a ^ (q - 1) := Nat.pow_pos hapos
  have h3 : (a ^ (q - 1) * L.prod - L.prod) % q = 0 := Nat.sub_mod_eq_zero_of_mod_eq key.symm
  have h4 : q ∣ (a ^ (q - 1) - 1) * L.prod := by
    rw [Nat.sub_mul, Nat.one_mul]; exact Nat.dvd_of_mod_eq_zero h3
  rcases hq.dvd_mul h4 with h5 | h5
  · obtain ⟨c, hc⟩ := h5
    have : a ^ (q - 1) = q * c + 1 := by omega
    rw [this, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · exact absurd h5 hnl

/-! ### gcd -/

theorem pow_gcd_mod {q a m k : Nat} (hq : 2 ≤ q) (hm : a ^ m % q = 1) (hk : a ^ k % q = 1) :
    a ^ Nat.gcd m k % q = 1 := by
  have gen : ∀ m k : Nat, a ^ m % q = 1 → a ^ k % q = 1 → a ^ Nat.gcd m k % q = 1 := by
    intro m k
    induction m, k using Nat.gcd.induction with
    | H0 n => intro _ h; simpa using h
    | H1 m n hm ih =>
      intro h1 h2
      rw [Nat.gcd_rec]
      apply ih _ h1
      have hdiv : a ^ n = (a ^ m) ^ (n / m) * a ^ (n % m) := by
        rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
      have hp : (a ^ m) ^ (n / m) % q = 1 := by
        rw [Nat.pow_mod, h1, Nat.one_pow]; exact Nat.mod_eq_of_lt (by omega)
      rw [hdiv, Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod] at h2
      exact h2
  exact gen m k hm hk

theorem dvd_pred_of_primitive {q a n : Nat} (hq : IsP q) (ha : ¬ q ∣ a) (hn : 1 ≤ n)
    (h1 : a ^ n % q = 1)
    (hprim : ∀ g, 1 ≤ g → g < n → g ∣ n → a ^ g % q ≠ 1) : n ∣ q - 1 := by
  have hf := fermat hq ha
  have hg := pow_gcd_mod hq.1 h1 hf
  have hgpos : 0 < Nat.gcd n (q - 1) := Nat.gcd_pos_of_pos_left _ hn
  have hgd : Nat.gcd n (q - 1) ∣ n := Nat.gcd_dvd_left _ _
  have hle := Nat.le_of_dvd hn hgd
  have heq : Nat.gcd n (q - 1) = n := by
    refine Classical.byContradiction fun hne => ?_
    exact hprim _ hgpos (by omega) hgd hg
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

end ZP
