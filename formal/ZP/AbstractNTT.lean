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


/-- The facts about the prime function that the abstract program needs. -/
structure NPrime (pr : Nat → Nat) : Prop where
  pos : ∀ n, 1 ≤ n → 0 < pr n
  one : pr 1 = 2
  two : pr 2 = 3

theorem hasCircuit_one (pr : Nat → Nat) (h : NPrime pr) (c : Nat) (hc : 1 ≤ c) : hasCircuit pr c 1 = true := by
  rw [hasCircuit_iff]
  refine ⟨List.replicate c ((none : Option Nat), 1), by simp, ?_, ?_⟩
  · rw [h.one]
    have : ∀ (k j : Nat), wfAux 2 j (List.replicate k ((none : Option Nat), 1)) := by
      intro k
      induction k with
      | zero => intro j; simp [wfAux]
      | succ k ih => intro j; simp only [List.replicate_succ, wfAux]; exact ⟨fun x hx => (by cases hx), by omega, ih _⟩
    exact this _ _
  · rw [h.one]; exact evalC_ones c hc

theorem hasCircuit_zero_two (pr : Nat → Nat) (h : NPrime pr) : hasCircuit pr 0 2 = false := by
  have : hasCircuit pr 0 2 = hasCircuit (fun _ => 3) 0 2 := by unfold hasCircuit; rw [h.two]
  rw [this]; decide +kernel

set_option maxRecDepth 100000 in
theorem hasCircuit_one_two (pr : Nat → Nat) (h : NPrime pr) : hasCircuit pr 1 2 = false := by
  have : hasCircuit pr 1 2 = hasCircuit (fun _ => 3) 1 2 := by unfold hasCircuit; rw [h.two]
  rw [this]; decide +kernel

set_option maxRecDepth 100000 in
theorem hasCircuit_two_two (pr : Nat → Nat) (h : NPrime pr) : hasCircuit pr 2 2 = false := by
  have : hasCircuit pr 2 2 = hasCircuit (fun _ => 3) 2 2 := by unfold hasCircuit; rw [h.two]
  rw [this]; decide +kernel

theorem hasCircuit_mono (pr : Nat → Nat) (h : NPrime pr) (n : Nat) (hn : 1 ≤ n) (c : Nat) (hc : 2 ≤ c)
    (hh : hasCircuit pr c n = true) : ∀ d, hasCircuit pr (c + d) n = true := by
  intro d
  induction d with
  | zero => exact hh
  | succ d ih => exact hasCircuit_pad pr (c + d) n (by omega) hn (h.pos n hn) ih

/-- `c ≥ 3` whenever `n = 2` has a circuit. -/
theorem three_le (pr : Nat → Nat) (h : NPrime pr) (c : Nat) (hh : hasCircuit pr c 2 = true) : 3 ≤ c := by
  by_cases h3 : 3 ≤ c
  · exact h3
  · exfalso
    have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [hasCircuit_zero_two pr h] at hh; cases hh
    · rw [hasCircuit_one_two pr h] at hh; cases hh
    · rw [hasCircuit_two_two pr h] at hh; cases hh

def stepN (pr : Nat → Nat) (s : Nat × Nat) : Nat × Nat :=
  if hasCircuit pr s.1 s.2 = true then (s.1, s.2 + 1) else (s.1 + 1, s.2)

def absN (pr : Nat → Nat) : Nat → Nat × Nat
  | 0 => (1, 1)
  | k + 1 => stepN pr (absN pr k)

def AbstractQN (pr : Nat → Nat) : Prop := ∃ N, ∀ k, N ≤ k → hasCircuit pr (absN pr k).1 (absN pr k).2 = true

theorem absN_inv (pr : Nat → Nat) (k : Nat) : 1 ≤ (absN pr k).1 ∧ 1 ≤ (absN pr k).2 := by
  induction k with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ k ih =>
    show 1 ≤ (stepN pr (absN pr k)).1 ∧ 1 ≤ (stepN pr (absN pr k)).2
    unfold stepN
    split <;> simp <;> omega

theorem absN_c_mono (pr : Nat → Nat) (k m : Nat) : (absN pr k).1 ≤ (absN pr (k + m)).1 := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    show (absN pr k).1 ≤ (stepN pr (absN pr (k + m))).1
    unfold stepN
    split <;> simp <;> omega


theorem absN_succ (pr : Nat → Nat) (k : Nat) : absN pr (k + 1) = stepN pr (absN pr k) := rfl

theorem absN_ok (pr : Nat → Nat) (k : Nat) (h : hasCircuit pr (absN pr k).1 (absN pr k).2 = true) :
    absN pr (k + 1) = ((absN pr k).1, (absN pr k).2 + 1) := by
  rw [absN_succ]; unfold stepN; simp [h]

theorem absN_bad (pr : Nat → Nat) (k : Nat) (h : ¬ hasCircuit pr (absN pr k).1 (absN pr k).2 = true) :
    absN pr (k + 1) = ((absN pr k).1 + 1, (absN pr k).2) := by
  rw [absN_succ]; unfold stepN; simp [h]

theorem sentence_to_abstract (pr : Nat → Nat) (hp : NPrime pr) : SentenceN pr → AbstractQN pr := by
  rintro ⟨cs, hcs⟩
  have hle : ∀ k, (absN pr k).1 ≤ cs := by
    intro k
    induction k with
    | zero =>
      have := hcs 2 (by omega)
      have h3 := three_le pr hp cs (hcs 2 (by omega))
      show 1 ≤ cs; omega
    | succ k ih =>
      by_cases h : hasCircuit pr (absN pr k).1 (absN pr k).2 = true
      · rw [absN_ok pr k h]; exact ih
      · rw [absN_bad pr k h]
        have hne : (absN pr k).1 ≠ cs := by
          intro he
          apply h
          rw [he]
          exact hcs _ (absN_inv pr k).2
        show (absN pr k).1 + 1 ≤ cs
        omega
  apply Classical.byContradiction
  intro hno
  have key : ∀ m, ∃ k, m + 1 ≤ (absN pr k).1 := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.le_refl _⟩
    | succ m ih =>
      obtain ⟨k0, hk0⟩ := ih
      have : ∃ k, k0 ≤ k ∧ ¬ hasCircuit pr (absN pr k).1 (absN pr k).2 = true := by
        apply Classical.byContradiction
        intro hh
        exact hno ⟨k0, fun k hk => Classical.byContradiction fun hb => hh ⟨k, hk, hb⟩⟩
      obtain ⟨k, hk, hb⟩ := this
      have hm := absN_c_mono pr k0 (k - k0)
      rw [show k0 + (k - k0) = k by omega] at hm
      refine ⟨k + 1, ?_⟩
      rw [absN_bad pr k hb]
      show m + 1 + 1 ≤ (absN pr k).1 + 1
      omega
  obtain ⟨k, hk⟩ := key cs
  have := hle k
  omega


theorem passed (pr : Nat → Nat) : ∀ k n, 1 ≤ n → n < (absN pr k).2 →
    ∃ k', k' < k ∧ (absN pr k').2 = n ∧ hasCircuit pr (absN pr k').1 (absN pr k').2 = true := by
  intro k
  induction k with
  | zero => intro n hn h; simp [absN] at h; omega
  | succ k ih =>
    intro n hn h
    by_cases hc : hasCircuit pr (absN pr k).1 (absN pr k).2 = true
    · rw [absN_ok pr k hc] at h
      simp at h
      by_cases hlt : n < (absN pr k).2
      · obtain ⟨k', hk', e⟩ := ih n hn hlt
        exact ⟨k', by omega, e⟩
      · have : n = (absN pr k).2 := by omega
        exact ⟨k, by omega, this.symm, hc⟩
    · rw [absN_bad pr k hc] at h
      simp at h
      obtain ⟨k', hk', e⟩ := ih n hn h
      exact ⟨k', by omega, e⟩

theorem passed_two (pr : Nat → Nat) : ∀ k, 3 ≤ (absN pr k).2 →
    ∃ k', k' < k ∧ (absN pr k').2 = 2 ∧ hasCircuit pr (absN pr k').1 (absN pr k').2 = true := by
  intro k
  induction k with
  | zero => intro h; simp [absN] at h
  | succ k ih =>
    intro h
    by_cases hc : hasCircuit pr (absN pr k).1 (absN pr k).2 = true
    · rw [absN_ok pr k hc] at h
      simp at h
      by_cases h3 : 3 ≤ (absN pr k).2
      · obtain ⟨k', hk', e⟩ := ih h3
        exact ⟨k', by omega, e⟩
      · exact ⟨k, by omega, by omega, hc⟩
    · rw [absN_bad pr k hc] at h
      simp at h
      obtain ⟨k', hk', e⟩ := ih h
      exact ⟨k', by omega, e⟩

theorem tail_run (pr : Nat → Nat) (N : Nat) (h : ∀ k, N ≤ k → hasCircuit pr (absN pr k).1 (absN pr k).2 = true) :
    ∀ i, absN pr (N + i) = ((absN pr N).1, (absN pr N).2 + i) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    have hc := h (N + i) (by omega)
    rw [← Nat.add_assoc, absN_ok pr (N + i) hc, ih]
    simp [Nat.add_assoc]

theorem abstract_to_sentence (pr : Nat → Nat) (hp : NPrime pr) : AbstractQN pr → SentenceN pr := by
  rintro ⟨N, hN⟩
  refine ⟨(absN pr N).1, fun n hn => ?_⟩
  by_cases hge : (absN pr N).2 ≤ n
  · have hrun := tail_run pr N hN (n - (absN pr N).2)
    have := hN (N + (n - (absN pr N).2)) (by omega)
    rw [hrun] at this
    simpa [show (absN pr N).2 + (n - (absN pr N).2) = n by omega] using this
  · obtain ⟨k', hk', hn', hc'⟩ := passed pr N n hn (by omega)
    have hmono := absN_c_mono pr k' (N - k')
    rw [show k' + (N - k') = N by omega] at hmono
    by_cases h1 : n = 1
    · subst h1
      exact hasCircuit_one pr hp _ (absN_inv pr N).1
    · have h2 : 3 ≤ (absN pr k').1 := by
        by_cases h2' : n = 2
        · rw [hn', h2'] at hc'
          exact three_le pr hp _ hc'
        · have h3 : 3 ≤ (absN pr k').2 := by omega
          obtain ⟨k'', hk'', e, hc''⟩ := passed_two pr k' h3
          rw [e] at hc''
          have := three_le pr hp _ hc''
          have hm2 := absN_c_mono pr k'' (k' - k'')
          rw [show k'' + (k' - k'') = k' by omega] at hm2
          omega
      rw [hn'] at hc'
      have := hasCircuit_mono pr hp n hn _ (by omega) hc' ((absN pr N).1 - (absN pr k').1)
      rwa [show (absN pr k').1 + ((absN pr N).1 - (absN pr k').1) = (absN pr N).1 by omega] at this

theorem abstractQN_iff (pr : Nat → Nat) (hp : NPrime pr) : AbstractQN pr ↔ SentenceN pr :=
  ⟨abstract_to_sentence pr hp, sentence_to_abstract pr hp⟩


/-! ## The prime `p ≡ 1 (mod n)`, under the existence hypothesis -/

theorem primeN_spec (n : Nat) (h : ∃ i, 1 ≤ i ∧ isPrimeN (1 + n * i) = true) :
    ∃ i, 1 ≤ i ∧ isPrimeN (1 + n * i) = true ∧ primeN n = 1 + n * i ∧
      ∀ j, 1 ≤ j → isPrimeN (1 + n * j) = true → i ≤ j := by
  unfold primeN
  rw [dif_pos h]
  have hm := Classical.choose_spec (exists_least (fun i => 1 ≤ i ∧ isPrimeN (1 + n * i) = true) h)
  exact ⟨_, hm.1.1, hm.1.2, rfl, fun j hj hp => hm.2 j ⟨hj, hp⟩⟩

theorem nprime_primeN (h : PrimeEx) : NPrime primeN := by
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hp, e, -⟩ := primeN_spec n (h n hn)
    rw [e]; omega
  · obtain ⟨i, hi, hp, e, hmin⟩ := primeN_spec 1 (h 1 (Nat.le_refl _))
    have : i ≤ 1 := hmin 1 (Nat.le_refl _) (by decide)
    have : i = 1 := by omega
    subst this; rw [e]
  · obtain ⟨i, hi, hp, e, hmin⟩ := primeN_spec 2 (h 2 (by omega))
    have : i ≤ 1 := hmin 1 (Nat.le_refl _) (by decide)
    have : i = 1 := by omega
    subst this; rw [e]

theorem sentenceN_iff (h : PrimeEx) : AbstractQN primeN ↔ SentenceN primeN :=
  abstractQN_iff primeN (nprime_primeN h)

end ZP
