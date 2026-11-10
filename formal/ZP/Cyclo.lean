module

public import ZP.PrimeNum
public import ZP.Totient
public import ZP.AllDefs

@[expose] public section

/-!
# `PrimeEx` in core Lean

For `n ≥ 1` there is a prime `q ≡ 1 (mod n)`.  We follow the cyclotomic route without polynomials:
for `a` a multiple of `n`, `cycv a d` is the quotient of `a^d - 1` by the product of `cycv a e` over the
proper divisors `e` of `d`.  Every prime factor `q` of `cycv a d` is primitive (`a^g ≢ 1 mod q` for
proper divisors `g`), and size bounds (with Gauss's `Σ φ(e) = d`) show `cycv a n ≥ 2` once `a` is large.
-/

namespace ZP

def pr (f : Nat → Nat) (P : Nat → Bool) : Nat → Nat
  | 0 => 1
  | k + 1 => pr f P k * (if P k = true then f k else 1)

theorem pr_succ (f : Nat → Nat) (P : Nat → Bool) (k : Nat) :
    pr f P (k + 1) = pr f P k * (if P k = true then f k else 1) := rfl

theorem pr_list (f : Nat → Nat) (P : Nat → Bool) (k : Nat) :
    (((List.range k).filter P).map f).prod = pr f P k := by
  induction k with
  | zero => simp [pr]
  | succ k ih =>
    rw [List.range_succ, List.filter_append, pr_succ, ← ih]
    by_cases h : P k = true <;> simp [h, List.prod_append]

theorem pr_dvd_pred (f : Nat → Nat) (P Q : Nat → Bool) :
    ∀ k, (∀ e, e < k → P e = true → Q e = true) → pr f P k ∣ pr f Q k
  | 0, _ => by simp [pr]
  | k + 1, h => by
    have ih := pr_dvd_pred f P Q k (fun e he => h e (by omega))
    rw [pr_succ, pr_succ]
    by_cases hp : P k = true
    · have hq := h k (by omega) hp
      rw [if_pos hp, if_pos hq]; exact Nat.mul_dvd_mul_right ih _
    · rw [if_neg hp, Nat.mul_one]; exact Nat.dvd_trans ih (Nat.dvd_mul_right _ _)

theorem pr_ext (f : Nat → Nat) (P : Nat → Bool) (k : Nat) :
    ∀ j, (∀ e, k ≤ e → e < k + j → P e = false) → pr f P k = pr f P (k + j)
  | 0, _ => rfl
  | j + 1, h => by
    have h1 := h (k + j) (by omega) (by omega)
    rw [← Nat.add_assoc, pr_succ, ← pr_ext f P k j (fun e h1 h2 => h e h1 (by omega)), h1]; simp

theorem pr_congr (f : Nat → Nat) (P Q : Nat → Bool) :
    ∀ k, (∀ e, e < k → P e = Q e) → pr f P k = pr f Q k
  | 0, _ => rfl
  | k + 1, h => by
    rw [pr_succ, pr_succ, pr_congr f P Q k (fun e he => h e (by omega)), h k (by omega)]

theorem pr_congr_f (f g : Nat → Nat) (P : Nat → Bool) :
    ∀ k, (∀ e, e < k → P e = true → f e = g e) → pr f P k = pr g P k
  | 0, _ => rfl
  | k + 1, h => by
    rw [pr_succ, pr_succ, pr_congr_f f g P k (fun e he => h e (by omega))]
    by_cases hp : P k = true
    · rw [if_pos hp, if_pos hp, h k (by omega) hp]
    · rw [if_neg hp, if_neg hp]

theorem pr_mul (f g : Nat → Nat) (P : Nat → Bool) :
    ∀ k, pr (fun e => f e * g e) P k = pr f P k * pr g P k
  | 0 => by simp [pr]
  | k + 1 => by
    rw [pr_succ, pr_succ, pr_succ, pr_mul f g P k]
    by_cases hp : P k = true
    · rw [if_pos hp, if_pos hp, if_pos hp]; exact Nat.mul_mul_mul_comm _ _ _ _
    · rw [if_neg hp, if_neg hp, if_neg hp]; simp

theorem pr_le (f g : Nat → Nat) (P : Nat → Bool) :
    ∀ k, (∀ e, e < k → P e = true → f e ≤ g e) → pr f P k ≤ pr g P k
  | 0, _ => Nat.le_refl _
  | k + 1, h => by
    rw [pr_succ, pr_succ]
    have ih := pr_le f g P k (fun e he => h e (by omega))
    by_cases hp : P k = true
    · rw [if_pos hp, if_pos hp]; exact Nat.mul_le_mul ih (h k (by omega) hp)
    · rw [if_neg hp, if_neg hp]; exact Nat.mul_le_mul ih (Nat.le_refl _)

theorem pr_pos (f : Nat → Nat) (P : Nat → Bool) :
    ∀ k, (∀ e, e < k → P e = true → 1 ≤ f e) → 1 ≤ pr f P k
  | 0, _ => by simp [pr]
  | k + 1, h => by
    rw [pr_succ]
    have ih := pr_pos f P k (fun e he => h e (by omega))
    by_cases hp : P k = true
    · rw [if_pos hp]; exact Nat.mul_pos ih (h k (by omega) hp)
    · rw [if_neg hp, Nat.mul_one]; exact ih

theorem pr_coprime (f : Nat → Nat) (P : Nat → Bool) (x : Nat) :
    ∀ k, (∀ e, e < k → P e = true → Nat.Coprime x (f e)) → Nat.Coprime x (pr f P k)
  | 0, _ => by simp [pr]
  | k + 1, h => by
    rw [pr_succ]
    have ih := pr_coprime f P x k (fun e he => h e (by omega))
    by_cases hp : P k = true
    · rw [if_pos hp]; exact Nat.Coprime.mul_right ih (h k (by omega) hp)
    · rw [if_neg hp, Nat.mul_one]; exact ih

theorem pr_dvd_cop (f : Nat → Nat) (P : Nat → Bool) (N : Nat) :
    ∀ k, (∀ e, e < k → P e = true → f e ∣ N) →
      (∀ e e', e < k → e' < k → e ≠ e' → P e = true → P e' = true → Nat.Coprime (f e) (f e')) →
      pr f P k ∣ N
  | 0, _, _ => by simp [pr]
  | k + 1, h, hc => by
    rw [pr_succ]
    have ih := pr_dvd_cop f P N k (fun e he => h e (by omega))
      (fun e e' he he' hne => hc e e' (by omega) (by omega) hne)
    by_cases hp : P k = true
    · rw [if_pos hp]
      have hcop : Nat.Coprime (pr f P k) (f k) := by
        apply Nat.Coprime.symm
        apply pr_coprime
        intro e he hpe
        exact hc k e (by omega) (by omega) (by omega) hp hpe
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ih (h k (by omega) hp)
    · rw [if_neg hp, Nat.mul_one]; exact ih

def dv (d e : Nat) : Bool := 0 < e && d % e == 0

theorem divs_eq (d : Nat) : divs d = (List.range d).filter (dv d) := rfl

def cycv (a : Nat) (d : Nat) : Nat :=
  (a ^ d - 1) / (((divs d).attach).map fun e => cycv a e.1).prod
termination_by d
decreasing_by exact (mem_divs.1 e.2).2.1

theorem cycv_eq (a d : Nat) : cycv a d = (a ^ d - 1) / pr (cycv a) (dv d) d := by
  rw [cycv, ← pr_list, ← divs_eq]
  congr 1
  rw [List.attach_map_val (l := divs d) (f := cycv a)]

def geo (x : Nat) : Nat → Nat
  | 0 => 0
  | p + 1 => geo x p + x ^ p

theorem geo_mul (y : Nat) : ∀ p, y * geo (y + 1) p + 1 = (y + 1) ^ p
  | 0 => by simp [geo]
  | p + 1 => by
    have ih := geo_mul y p
    rw [geo, Nat.pow_succ, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm ((y + 1) ^ p) y]
    omega

theorem geo_mod (x q : Nat) (hq : 2 ≤ q) (hx : x % q = 1) : ∀ p, geo x p % q = p % q
  | 0 => by simp [geo]
  | p + 1 => by
    have ih := geo_mod x q hq hx p
    have h1 : x ^ p % q = 1 := by
      rw [Nat.pow_mod, hx]; simp; exact Nat.mod_eq_of_lt (by omega)
    have h1q : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
    rw [geo, Nat.add_mod, ih, h1, Nat.add_mod p 1 q, h1q]

theorem mod_one_of_dvd {q x : Nat} (hq : 2 ≤ q) (hx : 1 ≤ x) (h : q ∣ x - 1) : x % q = 1 := by
  obtain ⟨c, hc⟩ := h
  have : x = q * c + 1 := by omega
  rw [this, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)

theorem pow_sub_dvd (a e s : Nat) (ha : 1 ≤ a) : a ^ e - 1 ∣ a ^ (e * s) - 1 := by
  have h1 : 1 ≤ a ^ e := Nat.one_le_pow _ _ ha
  obtain ⟨y, hy⟩ : ∃ y, a ^ e = y + 1 := ⟨a ^ e - 1, by omega⟩
  have := geo_mul y s
  rw [Nat.pow_mul, hy, Nat.add_sub_cancel]
  exact ⟨geo (y + 1) s, by omega⟩

theorem cycv_pkg (a : Nat) (ha : 2 ≤ a) : ∀ d, 1 ≤ d → d ∣ a →
    (cycv a d * pr (cycv a) (dv d) d = a ^ d - 1) ∧
    (∀ q, IsP q → q ∣ cycv a d → ∀ g, 1 ≤ g → g < d → g ∣ d → a ^ g % q ≠ 1) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd1 hda
  have hdv : ∀ e, dv d e = true ↔ 0 < e ∧ e ∣ d := by
    intro e
    simp only [dv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.dvd_of_mod_eq_zero h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.mod_eq_zero_of_dvd h2⟩
  have hapos : ∀ e, 1 ≤ a ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  -- facts about smaller divisors
  have hsm : ∀ e, 0 < e → e < d → e ∣ d →
      (cycv a e * pr (cycv a) (dv e) e = a ^ e - 1) ∧
      (∀ q, IsP q → q ∣ cycv a e → ∀ g, 1 ≤ g → g < e → g ∣ e → a ^ g % q ≠ 1) :=
    fun e he1 he2 he3 => ih e he2 he1 (Nat.dvd_trans he3 hda)
  have hcdvd : ∀ e, 0 < e → e < d → e ∣ d → cycv a e ∣ a ^ e - 1 :=
    fun e h1 h2 h3 => ⟨_, by rw [← (hsm e h1 h2 h3).1, Nat.mul_comm]⟩
  have hcpos : ∀ e, 0 < e → e < d → e ∣ d → 1 ≤ cycv a e := by
    intro e h1 h2 h3
    have h := (hsm e h1 h2 h3).1
    have := hapos e
    have hne : a ^ e - 1 ≠ 0 := by
      have : a ^ e ≠ 1 := by
        intro h1'
        have : a ≤ a ^ e := Nat.le_self_pow (by omega) a
        omega
      omega
    rcases Nat.eq_zero_or_pos (cycv a e) with h0 | h0
    · rw [h0] at h; simp at h; omega
    · exact h0
  -- coprimality
  have hcop : ∀ e e', e < d → e' < d → e ≠ e' → dv d e = true → dv d e' = true →
      Nat.Coprime (cycv a e) (cycv a e') := by
    intro e e' he he' hne h1 h2
    obtain ⟨he0, hed⟩ := (hdv e).1 h1
    obtain ⟨he0', hed'⟩ := (hdv e').1 h2
    apply Classical.byContradiction
    intro hnc
    have hc1 := hcpos e he0 he hed
    have hge : 2 ≤ Nat.gcd (cycv a e) (cycv a e') := by
      have : 0 < Nat.gcd (cycv a e) (cycv a e') := Nat.gcd_pos_of_pos_left _ hc1
      have : Nat.gcd (cycv a e) (cycv a e') ≠ 1 := hnc
      omega
    obtain ⟨q, hq, hqd⟩ := exists_isP_dvd hge
    have hq1 : q ∣ cycv a e := Nat.dvd_trans hqd (Nat.gcd_dvd_left _ _)
    have hq2 : q ∣ cycv a e' := Nat.dvd_trans hqd (Nat.gcd_dvd_right _ _)
    have hm1 : a ^ e % q = 1 :=
      mod_one_of_dvd hq.1 (hapos e) (Nat.dvd_trans hq1 (hcdvd e he0 he hed))
    have hm2 : a ^ e' % q = 1 :=
      mod_one_of_dvd hq.1 (hapos e') (Nat.dvd_trans hq2 (hcdvd e' he0' he' hed'))
    have hg := pow_gcd_mod hq.1 hm1 hm2
    have hgpos : 0 < Nat.gcd e e' := Nat.gcd_pos_of_pos_left _ he0
    have hg1 : Nat.gcd e e' ∣ e := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd e e' ∣ e' := Nat.gcd_dvd_right _ _
    have hl1 := Nat.le_of_dvd he0 hg1
    have hl2 := Nat.le_of_dvd he0' hg2
    by_cases hlt : Nat.gcd e e' < e
    · exact (hsm e he0 he hed).2 q hq hq1 _ hgpos hlt hg1 hg
    · have : Nat.gcd e e' < e' := by omega
      exact (hsm e' he0' he' hed').2 q hq hq2 _ hgpos this hg2 hg
  -- P1
  have hP1 : cycv a d * pr (cycv a) (dv d) d = a ^ d - 1 := by
    have hdiv : pr (cycv a) (dv d) d ∣ a ^ d - 1 := by
      apply pr_dvd_cop _ _ _ d
      · intro e he hv
        obtain ⟨he0, hed⟩ := (hdv e).1 hv
        obtain ⟨s, hs⟩ := hed
        refine Nat.dvd_trans (hcdvd e he0 he ⟨s, hs⟩) ?_
        rw [hs]; exact pow_sub_dvd a e s (by omega)
      · exact hcop
    rw [cycv_eq a d]
    exact Nat.div_mul_cancel hdiv
  refine ⟨hP1, ?_⟩
  -- P3
  have hP3 : ∀ p, IsP p → p ∣ d → ∃ r, a ^ d - 1 = (a ^ (d / p) - 1) * (cycv a d * r) := by
    intro p hp hpd
    obtain ⟨m, hm⟩ := hpd
    have hp2 := hp.1
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    have hmd : m < d := by
      rw [hm]; calc m = 1 * m := by omega
        _ < p * m := Nat.mul_lt_mul_of_pos_right (by omega) hm0
    have hmdvd : m ∣ d := ⟨p, by rw [hm, Nat.mul_comm]⟩
    have hdp : d / p = m := by rw [hm]; exact Nat.mul_div_cancel_left _ (by omega)
    rw [hdp]
    have hPm := (hsm m hm0 hmd hmdvd).1
    -- A_m divides the divisor product at d
    have h1 : pr (cycv a) (dv m) (m + 1) = a ^ m - 1 := by
      rw [pr_succ, if_pos (by simp [dv, hm0]), Nat.mul_comm]; exact hPm
    obtain ⟨j, hj⟩ : ∃ j, d = m + 1 + j := ⟨d - (m + 1), by omega⟩
    have h2 : pr (cycv a) (dv m) (m + 1) = pr (cycv a) (dv m) d := by
      rw [hj]; apply pr_ext
      intro e he _
      have : ¬ (0 < e ∧ e ∣ m) := by
        rintro ⟨h0, h3⟩; have := Nat.le_of_dvd hm0 h3; omega
      have : dv m e = false := by
        apply Classical.byContradiction; intro hc
        have : dv m e = true := by simpa using hc
        exact ‹¬ _› ((by simp only [dv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
                         exact ⟨this.1, Nat.dvd_of_mod_eq_zero this.2⟩ : 0 < e ∧ e ∣ m))
      exact this
    have h3 : pr (cycv a) (dv m) d ∣ pr (cycv a) (dv d) d := by
      apply pr_dvd_pred
      intro e _ hv
      have hv' : 0 < e ∧ e ∣ m := by
        simp only [dv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
        exact ⟨hv.1, Nat.dvd_of_mod_eq_zero hv.2⟩
      exact (hdv e).2 ⟨hv'.1, Nat.dvd_trans hv'.2 hmdvd⟩
    have h4 : a ^ m - 1 ∣ pr (cycv a) (dv d) d := by rw [← h1, h2]; exact h3
    obtain ⟨r1, hr1⟩ := h4
    exact ⟨r1, by rw [← hP1, hr1]; exact Nat.mul_left_comm _ _ _⟩
  -- P2
  intro q hq hqc g hg1 hgd hgdvd hga
  obtain ⟨c, hc⟩ := hgdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  obtain ⟨p, hp, hpc⟩ := exists_isP_dvd hc2
  obtain ⟨s, hs⟩ := hpc
  have hpd : p ∣ d := ⟨g * s, by rw [hc, hs]; exact (Nat.mul_left_comm _ _ _)⟩
  obtain ⟨r, hr⟩ := hP3 p hp hpd
  obtain ⟨m, hm⟩ := hpd
  have hp0 : 0 < p := by have := hp.1; omega
  have hdp : d / p = m := by rw [hm]; exact Nat.mul_div_cancel_left _ hp0
  rw [hdp] at hr
  have hmgs : m = g * s := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    rw [← hm, hc, hs]; exact Nat.mul_left_comm _ _ _
  have ham : a ^ m % q = 1 := by
    rw [hmgs, Nat.pow_mul, Nat.pow_mod, hga]
    simp
    exact Nat.mod_eq_of_lt (by have := hq.1; omega)
  have hm1 : 1 ≤ a ^ m := hapos m
  obtain ⟨y, hy⟩ : ∃ y, a ^ m = y + 1 := ⟨a ^ m - 1, by omega⟩
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; omega
    · exact h
  have hypos : 0 < y := by
    have : a ≤ a ^ m := Nat.le_self_pow (by omega) a
    omega
  have hgeo := geo_mul y p
  have had : a ^ d = (y + 1) ^ p := by rw [← hy, ← Nat.pow_mul, hm, Nat.mul_comm]
  rw [hy, Nat.add_sub_cancel] at hr
  have hgeo2 : geo (y + 1) p = cycv a d * r := by
    apply Nat.eq_of_mul_eq_mul_left hypos
    rw [← hr]; omega
  have hmodg := geo_mod (y + 1) q hq.1 (by rw [← hy]; exact ham) p
  have hqg : q ∣ geo (y + 1) p := by rw [hgeo2]; exact Nat.dvd_mul_right_of_dvd hqc _
  have hqp : q ∣ p := by
    have : p % q = 0 := by rw [← hmodg]; exact Nat.mod_eq_zero_of_dvd hqg
    exact Nat.dvd_of_mod_eq_zero this
  have hqeq : q = p := IsP.eq_of_dvd hp hq hqp
  have hqa : q ∣ a := by
    refine Nat.dvd_trans hqp (Nat.dvd_trans ⟨m, hm⟩ hda)
  have hqad : q ∣ a ^ d := by
    obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [hk, Nat.pow_succ]; exact Nat.dvd_trans hqa (Nat.dvd_mul_left a _)
  have hmod : a ^ d % q = 1 :=
    mod_one_of_dvd hq.1 (hapos d) (by rw [← hP1]; exact Nat.dvd_mul_right_of_dvd hqc _)
  have := Nat.mod_eq_zero_of_dvd hqad
  omega

def Kc (d : Nat) : Nat :=
  2 * (((divs d).attach).map fun e => Kc e.1).prod
termination_by d
decreasing_by exact (mem_divs.1 e.2).2.1

theorem Kc_eq (d : Nat) : Kc d = 2 * pr Kc (dv d) d := by
  rw [Kc, ← pr_list, ← divs_eq]
  rw [List.attach_map_val (l := divs d) (f := Kc)]

theorem Kc_pos : ∀ d, 1 ≤ Kc d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    rw [Kc_eq]
    have : 1 ≤ pr Kc (dv d) d := by
      apply pr_pos
      intro e he hv
      exact ih e he
    omega

theorem prod_pow_sum (a : Nat) : ∀ l : List Nat,
    (l.map fun e => a ^ phi e).prod = a ^ ((l.map phi).sum)
  | [] => by simp
  | e :: l => by
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [prod_pow_sum a l, Nat.pow_add]

theorem pr_pow_phi (a d : Nat) (hd : 1 ≤ d) :
    pr (fun e => a ^ phi e) (dv d) d = a ^ (d - phi d) := by
  rw [← pr_list, ← divs_eq, prod_pow_sum]
  have := phi_sum hd
  congr 1; omega

theorem cycv_size (a : Nat) (ha : 2 ≤ a) : ∀ d, 1 ≤ d → d ∣ a →
    a ^ phi d ≤ Kc d * cycv a d ∧ cycv a d ≤ Kc d * a ^ phi d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd1 hda
  have hdv : ∀ e, dv d e = true → 0 < e ∧ e ∣ d := by
    intro e
    simp only [dv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rintro ⟨h1, h2⟩; exact ⟨h1, Nat.dvd_of_mod_eq_zero h2⟩
  have hapos : ∀ e, 1 ≤ a ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  have hP1 := (cycv_pkg a ha d hd1 hda).1
  have hX : pr (cycv a) (dv d) d ≤ pr Kc (dv d) d * a ^ (d - phi d) := by
    rw [← pr_pow_phi a d hd1]
    have : pr (fun e => Kc e * a ^ phi e) (dv d) d = pr Kc (dv d) d * pr (fun e => a ^ phi e) (dv d) d :=
      pr_mul Kc (fun e => a ^ phi e) (dv d) d
    rw [← this]
    apply pr_le
    intro e he hv
    obtain ⟨h0, h1⟩ := hdv e hv
    exact (ih e he h0 (Nat.dvd_trans h1 hda)).2
  have hW : a ^ (d - phi d) ≤ pr Kc (dv d) d * pr (cycv a) (dv d) d := by
    rw [← pr_pow_phi a d hd1, ← pr_mul]
    apply pr_le
    intro e he hv
    obtain ⟨h0, h1⟩ := hdv e hv
    exact (ih e he h0 (Nat.dvd_trans h1 hda)).1
  have hs := phi_sum hd1
  have hdW : a ^ d = a ^ phi d * a ^ (d - phi d) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hWpos : 0 < a ^ (d - phi d) := hapos _
  have hK : Kc d = 2 * pr Kc (dv d) d := Kc_eq d
  have hge : 2 ≤ a ^ d := by
    have : a ≤ a ^ d := Nat.le_self_pow (by omega) a
    omega
  constructor
  · apply Nat.le_of_mul_le_mul_right _ hWpos
    calc a ^ phi d * a ^ (d - phi d) = a ^ d := hdW.symm
      _ ≤ 2 * (a ^ d - 1) := by omega
      _ = 2 * (cycv a d * pr (cycv a) (dv d) d) := by rw [hP1]
      _ ≤ 2 * (cycv a d * (pr Kc (dv d) d * a ^ (d - phi d))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
      _ = Kc d * cycv a d * a ^ (d - phi d) := by rw [hK]; ac_rfl
  · apply Nat.le_of_mul_le_mul_right _ hWpos
    calc cycv a d * a ^ (d - phi d) ≤ cycv a d * (pr Kc (dv d) d * pr (cycv a) (dv d) d) :=
          Nat.mul_le_mul_left _ hW
      _ = pr Kc (dv d) d * (cycv a d * pr (cycv a) (dv d) d) := by ac_rfl
      _ = pr Kc (dv d) d * (a ^ d - 1) := by rw [hP1]
      _ ≤ pr Kc (dv d) d * a ^ d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = pr Kc (dv d) d * a ^ phi d * a ^ (d - phi d) := by rw [hdW]; ac_rfl
      _ ≤ Kc d * a ^ phi d * a ^ (d - phi d) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

theorem exists_prime_one_mod (n : Nat) (hn : 1 ≤ n) : ∃ q, IsP q ∧ n ∣ q - 1 := by
  have hK := Kc_pos n
  have hK2 : 2 ≤ Kc n := by
    rw [Kc_eq]
    have : 1 ≤ pr Kc (dv n) n := pr_pos _ _ _ (fun e _ _ => Kc_pos e)
    omega
  obtain ⟨a, ha⟩ : ∃ a, a = n * (2 * Kc n) := ⟨_, rfl⟩
  have ha2 : 2 * Kc n ≤ a := by
    rw [ha]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hna : n ∣ a := by rw [ha]; exact Nat.dvd_mul_right _ _
  have hsz := (cycv_size a (by omega) n hn hna).1
  have hphi := phi_pos hn
  have hale : a ≤ a ^ phi n := Nat.le_self_pow (by omega) a
  have hc2 : 2 ≤ cycv a n := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < Kc n)
    calc Kc n * 2 = 2 * Kc n := Nat.mul_comm _ _
      _ ≤ a := ha2
      _ ≤ a ^ phi n := hale
      _ ≤ Kc n * cycv a n := hsz
  obtain ⟨q, hq, hqd⟩ := exists_isP_dvd hc2
  obtain ⟨hP1, hP2⟩ := cycv_pkg a (by omega) n hn hna
  have hapos : ∀ e, 1 ≤ a ^ e := fun e => Nat.one_le_pow _ _ (by omega)
  have h1 : a ^ n % q = 1 :=
    mod_one_of_dvd hq.1 (hapos n) (by rw [← hP1]; exact Nat.dvd_mul_right_of_dvd hqd _)
  have hqa : ¬ q ∣ a := by
    intro hqa
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have : q ∣ a ^ n := by
      rw [hk, Nat.pow_succ]; exact Nat.dvd_trans hqa (Nat.dvd_mul_left a _)
    have := Nat.mod_eq_zero_of_dvd this
    omega
  exact ⟨q, hq, dvd_pred_of_primitive hq hqa hn h1 (fun g hg1 hg2 hg3 => hP2 q hq hqd g hg1 hg2 hg3)⟩

theorem primeEx_proof (n : Nat) (hn : 1 ≤ n) : ∃ i, 1 ≤ i ∧ isPrimeN (1 + n * i) = true := by
  obtain ⟨q, hq, ⟨i, hi⟩⟩ := exists_prime_one_mod n hn
  have h2 := hq.1
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h] at hi; simp at hi; omega
    · exact h
  refine ⟨i, hi1, ?_⟩
  have : 1 + n * i = q := by omega
  rw [this]; exact isPrimeN_of_isP hq

theorem primeEx : PrimeEx := primeEx_proof

end ZP
