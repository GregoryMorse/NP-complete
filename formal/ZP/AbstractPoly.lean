module

public import ZP.AllDefs
public import ZP.StrPoly

@[expose] public section

/-!
# The abstract program of Z_PPOLY beeps finitely often iff `SentencePoly`

State `(K, n, A, v)`: degree number `K`, length `n`, advice number `A` (program `str A`), and the
instance counter `v < 2^n` (the string `svec n v`). A step beeps (and moves to the next degree) when the
advice is longer than the budget; otherwise it compares the charged run with `inL`.
-/

namespace ZP

/-- The budget of the degree number `K` (the `K`-th string in shortlex order). -/
def bud (K n : Nat) : Nat := budget (str K) n

/-- Binary counter of width `n` with value `v`, most significant bit first. -/
def svec (n v : Nat) : List Bool := (ofBv n v).reverse

structure PSt where
  K : Nat
  n : Nat
  A : Nat
  v : Nat

def polyOver (st : PSt) : Prop := bud st.K st.n < (str st.A).length

instance (st : PSt) : Decidable (polyOver st) := inferInstanceAs (Decidable (_ < _))

def okv (K n A v : Nat) : Prop :=
  prun (str A) (svec n v) (bud K n) = inL (svec n v)

instance (K n A v : Nat) : Decidable (okv K n A v) := inferInstanceAs (Decidable (_ = _))

def polyStep (st : PSt) : PSt :=
  if polyOver st then ⟨st.K + 1, 0, 1, 0⟩
  else if okv st.K st.n st.A st.v then
    (if st.v + 1 < 2 ^ st.n then ⟨st.K, st.n, st.A, st.v + 1⟩ else ⟨st.K, st.n + 1, 1, 0⟩)
  else ⟨st.K, st.n, st.A + 1, 0⟩

def polyIter (st : PSt) : Nat → PSt
  | 0 => st
  | m + 1 => polyStep (polyIter st m)

def polyState (k : Nat) : PSt := polyIter ⟨1, 0, 1, 0⟩ k

/-- The abstract program beeps at step `k` iff `polyOver (polyState k)`. -/
def AbstractQuasihaltsPoly : Prop := ∃ N, ∀ k, N ≤ k → ¬ polyOver (polyState k)

theorem polyIter_add (st : PSt) (a b : Nat) : polyIter st (a + b) = polyIter (polyIter st a) b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg polyStep ih

/-! ## Bit strings -/

theorem bv_lt : ∀ l : List Bool, bv l < 2 ^ l.length
  | [] => by simp [bv]
  | b :: l => by
    have := bv_lt l
    have h2 : 2 ^ (l.length + 1) = 2 ^ l.length * 2 := Nat.pow_succ _ _
    have := bitN_le b
    show bitN b + 2 * bv l < 2 ^ (l.length + 1)
    omega

theorem svec_length (n v : Nat) : (svec n v).length = n := by simp [svec, length_ofBv]

theorem svec_surj (s : List Bool) : ∃ v, v < 2 ^ s.length ∧ svec s.length v = s := by
  refine ⟨bv s.reverse, by simpa using bv_lt s.reverse, ?_⟩
  have := ofBv_bv s.reverse
  simp only [List.length_reverse] at this
  simp [svec, this]

theorem advOK_iff (K a : List Bool) (n : Nat) :
    advOK K a n ↔ ∀ v, v < 2 ^ n → prun a (svec n v) (budget K n) = inL (svec n v) := by
  constructor
  · intro h v _
    exact h _ ((mem_strings _ _).2 (svec_length n v))
  · intro h s hs
    have hl := (mem_strings _ _).1 hs
    obtain ⟨v, hv, hsv⟩ := svec_surj s
    rw [hl] at hv hsv
    rw [← hsv]
    exact h v hv

def GoodA (K n A : Nat) : Prop := (str A).length ≤ bud K n ∧ ∀ v, v < 2 ^ n → okv K n A v

theorem sentencePoly_iff :
    SentencePoly ↔ ∃ K, 1 ≤ K ∧ ∀ n, ∃ A, 1 ≤ A ∧ GoodA K n A := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨2 ^ K.length, Nat.one_le_two_pow, fun n => ?_⟩
    obtain ⟨a, ha1, ha2⟩ := hK n
    obtain ⟨A, hA, hAa⟩ := str_surj a
    have hb : bud (2 ^ K.length) n = budget K n := by
      simp [bud, str_len_pow2, budget]
    refine ⟨A, hA, ?_, fun v hv => ?_⟩
    · rw [hb, hAa]; exact ha1
    · have := (advOK_iff K a n).1 ha2 v hv
      simpa [okv, hb, hAa] using this
  · rintro ⟨K, hK, h⟩
    refine ⟨str K, fun n => ?_⟩
    obtain ⟨A, hA, h1, h2⟩ := h n
    exact ⟨str A, h1, (advOK_iff _ _ _).2 h2⟩

/-! ## Dynamics -/

theorem polyStep_over {st : PSt} (h : polyOver st) : polyStep st = ⟨st.K + 1, 0, 1, 0⟩ := by
  simp [polyStep, h]

theorem polyStep_next {st : PSt} (h : ¬ polyOver st) (hok : okv st.K st.n st.A st.v)
    (hv : st.v + 1 < 2 ^ st.n) : polyStep st = ⟨st.K, st.n, st.A, st.v + 1⟩ := by
  simp [polyStep, h, hok, hv]

theorem polyStep_carry {st : PSt} (h : ¬ polyOver st) (hok : okv st.K st.n st.A st.v)
    (hv : ¬ st.v + 1 < 2 ^ st.n) : polyStep st = ⟨st.K, st.n + 1, 1, 0⟩ := by
  simp [polyStep, h, hok, hv]

theorem polyStep_wrong {st : PSt} (h : ¬ polyOver st) (hok : ¬ okv st.K st.n st.A st.v) :
    polyStep st = ⟨st.K, st.n, st.A + 1, 0⟩ := by
  simp [polyStep, h, hok]

/-- The invariant of the reachable states. -/
structure PInv (st : PSt) : Prop where
  hK : 1 ≤ st.K
  hA : 1 ≤ st.A
  hv : st.v < 2 ^ st.n
  hgood : ∀ n', n' < st.n → ∃ A, 1 ≤ A ∧ GoodA st.K n' A
  hA' : ∀ A', 1 ≤ A' → A' < st.A → ¬ GoodA st.K st.n A'
  hv' : ∀ v', v' < st.v → okv st.K st.n st.A v'

theorem PInv_init : PInv ⟨1, 0, 1, 0⟩ where
  hK := Nat.le_refl _
  hA := Nat.le_refl _
  hv := by decide
  hgood := fun n' h => absurd h (Nat.not_lt_zero _)
  hA' := fun A' h1 h2 => absurd h2 (by simp only; omega)
  hv' := fun v' h => absurd h (Nat.not_lt_zero _)

theorem PInv_step {st : PSt} (h : PInv st) : PInv (polyStep st) := by
  by_cases ho : polyOver st
  · rw [polyStep_over ho]
    exact ⟨by simp only; omega, Nat.le_refl _, by show 0 < 2 ^ 0; decide,
      fun n' h => absurd h (Nat.not_lt_zero _),
      fun A' h1 h2 => absurd h2 (by simp only; omega), fun v' h => absurd h (Nat.not_lt_zero _)⟩
  · by_cases hok : okv st.K st.n st.A st.v
    · by_cases hv : st.v + 1 < 2 ^ st.n
      · rw [polyStep_next ho hok hv]
        refine ⟨h.hK, h.hA, hv, h.hgood, h.hA', fun v' hv' => ?_⟩
        show okv st.K st.n st.A v'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv' with h1 | h1
        · exact h.hv' v' h1
        · rw [h1]; exact hok
      · rw [polyStep_carry ho hok hv]
        refine ⟨h.hK, Nat.le_refl _, Nat.two_pow_pos _, ?_, ?_,
          fun v' h => absurd h (Nat.not_lt_zero _)⟩
        · intro n' hn'
          show ∃ A, 1 ≤ A ∧ GoodA st.K n' A
          rcases Nat.lt_succ_iff_lt_or_eq.1 hn' with h1 | h1
          · exact h.hgood n' h1
          · refine ⟨st.A, h.hA, ?_⟩
            rw [h1]
            refine ⟨Nat.not_lt.1 ho, fun v' hv' => ?_⟩
            rcases Nat.lt_or_ge v' st.v with h2 | h2
            · exact h.hv' v' h2
            · have : v' = st.v := by omega
              rw [this]; exact hok
        · intro A' h1 h2
          exact absurd h2 (by simp only; omega)
      
    · rw [polyStep_wrong ho hok]
      refine ⟨h.hK, by simp only; omega, Nat.two_pow_pos _, h.hgood, ?_,
        fun v' h => absurd h (Nat.not_lt_zero _)⟩
      · intro A' h1 h2 hg
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | h3
        · exact h.hA' A' h1 h3 hg
        · rw [h3] at hg
          exact hok (hg.2 _ h.hv)

theorem PInv_iter {st : PSt} (h : PInv st) : ∀ m, PInv (polyIter st m)
  | 0 => h
  | m + 1 => PInv_step (PInv_iter h m)


theorem polyStep_K_ge (st : PSt) : st.K ≤ (polyStep st).K := by
  by_cases ho : polyOver st
  · rw [polyStep_over ho]; show st.K ≤ st.K + 1; omega
  · by_cases hok : okv st.K st.n st.A st.v
    · by_cases hv : st.v + 1 < 2 ^ st.n
      · rw [polyStep_next ho hok hv]; exact Nat.le_refl _
      · rw [polyStep_carry ho hok hv]; exact Nat.le_refl _
    · rw [polyStep_wrong ho hok]; exact Nat.le_refl _

theorem polyStep_K_same {st : PSt} (ho : ¬ polyOver st) : (polyStep st).K = st.K := by
  by_cases hok : okv st.K st.n st.A st.v
  · by_cases hv : st.v + 1 < 2 ^ st.n
    · rw [polyStep_next ho hok hv]
    · rw [polyStep_carry ho hok hv]
  · rw [polyStep_wrong ho hok]

theorem polyStep_n_ge {st : PSt} (ho : ¬ polyOver st) : st.n ≤ (polyStep st).n := by
  by_cases hok : okv st.K st.n st.A st.v
  · by_cases hv : st.v + 1 < 2 ^ st.n
    · rw [polyStep_next ho hok hv]; exact Nat.le_refl _
    · rw [polyStep_carry ho hok hv]; show st.n ≤ st.n + 1; omega
  · rw [polyStep_wrong ho hok]; exact Nat.le_refl _

theorem stabilize (f : Nat → Nat) (hm : ∀ m, f m ≤ f (m + 1)) (B : Nat) (hb : ∀ m, f m ≤ B) :
    ∃ m0, ∀ m, m0 ≤ m → f m = f m0 := by
  have hall : ∀ m j, f m ≤ f (m + j) := by
    intro m j
    induction j with
    | zero => exact Nat.le_refl _
    | succ j ih => exact Nat.le_trans ih (hm (m + j))
  refine Classical.byContradiction fun hs => ?_
  have hex : ∀ m0, ∃ m, m0 ≤ m ∧ f m ≠ f m0 := fun m0 =>
    Classical.byContradiction fun hc => hs ⟨m0, fun m hm' => Classical.byContradiction fun hne => hc ⟨m, hm', hne⟩⟩
  have hbig : ∀ j, ∃ m, j ≤ f m := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨m, hm1⟩ := ih
      obtain ⟨m', hm2, hm3⟩ := hex m
      have h1 := hall m (m' - m)
      rw [show m + (m' - m) = m' by omega] at h1
      exact ⟨m', by omega⟩
  obtain ⟨m, hm1⟩ := hbig (B + 1)
  have := hb m
  omega

theorem polyIter_K_const {st : PSt} (hno : ∀ m, ¬ polyOver (polyIter st m)) :
    ∀ m, (polyIter st m).K = st.K
  | 0 => rfl
  | m + 1 => by
    show (polyStep (polyIter st m)).K = st.K
    rw [polyStep_K_same (hno m), polyIter_K_const hno m]

theorem poly_stab {st0 : PSt} (hI : PInv st0) (hno : ∀ m, ¬ polyOver (polyIter st0 m)) (B : Nat)
    (hB : ∀ m, (polyIter st0 m).n ≤ B) : False := by
  obtain ⟨m0, hm0⟩ := stabilize (fun m => (polyIter st0 m).n)
    (fun m => polyStep_n_ge (hno m)) B hB
  have hn : ∀ j, (polyIter st0 (m0 + j)).n = (polyIter st0 m0).n := fun j => hm0 _ (Nat.le_add_right _ _)
  have hK : ∀ j, (polyIter st0 (m0 + j)).K = (polyIter st0 m0).K := by
    intro j
    rw [polyIter_add]
    have := polyIter_K_const (st := polyIter st0 m0) (fun m => by rw [← polyIter_add]; exact hno _) j
    exact this
  let P := 2 ^ (polyIter st0 m0).n
  let Q := 2 ^ (bud (polyIter st0 m0).K (polyIter st0 m0).n + 1)
  let pot : Nat → Nat := fun j => (polyIter st0 (m0 + j)).A * P + (polyIter st0 (m0 + j)).v
  have hpot : ∀ j, j ≤ pot j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hI' := PInv_iter hI (m0 + j)
      have ho := hno (m0 + j)
      have hnj := hn j
      have hnj1 := hn (j + 1)
      have hstep : polyIter st0 (m0 + (j + 1)) = polyStep (polyIter st0 (m0 + j)) := rfl
      have ih' : j ≤ (polyIter st0 (m0 + j)).A * P + (polyIter st0 (m0 + j)).v := ih
      show j + 1 ≤ (polyIter st0 (m0 + (j + 1))).A * P + (polyIter st0 (m0 + (j + 1))).v
      rw [hstep]
      rw [hstep] at hnj1
      generalize polyIter st0 (m0 + j) = s at hI' ho hnj hnj1 ih'
      have hvP : s.v < P := by show s.v < 2 ^ (polyIter st0 m0).n; rw [← hnj]; exact hI'.hv
      by_cases hok : okv s.K s.n s.A s.v
      · by_cases hv : s.v + 1 < 2 ^ s.n
        · rw [polyStep_next ho hok hv]
          show j + 1 ≤ s.A * P + (s.v + 1)
          omega
        · rw [polyStep_carry ho hok hv] at hnj1
          have h5 : s.n + 1 = (polyIter st0 m0).n := hnj1
          omega
      · rw [polyStep_wrong ho hok]
        show j + 1 ≤ (s.A + 1) * P + 0
        rw [Nat.succ_mul]
        omega
  have hbound : ∀ j, pot j < Q * P := by
    intro j
    have ho := hno (m0 + j)
    have hI' := PInv_iter hI (m0 + j)
    have h1 : ¬ _ := ho
    unfold polyOver at h1
    rw [hn j, hK j] at h1
    have hlen : (str (polyIter st0 (m0 + j)).A).length ≤ bud (polyIter st0 m0).K (polyIter st0 m0).n :=
      Nat.not_lt.1 h1
    have hAq : (polyIter st0 (m0 + j)).A < Q := by
      have := (str_spec hI'.hA).2
      have h3 := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ hlen)
      exact Nat.lt_of_lt_of_le this h3
    have hvP : (polyIter st0 (m0 + j)).v < P := by
      show _ < 2 ^ (polyIter st0 m0).n; rw [← hn j]; exact hI'.hv
    show (polyIter st0 (m0 + j)).A * P + (polyIter st0 (m0 + j)).v < Q * P
    have h4 : ((polyIter st0 (m0 + j)).A + 1) * P ≤ Q * P := Nat.mul_le_mul_right _ hAq
    rw [Nat.succ_mul] at h4
    omega
  have h1 : Q * P ≤ pot (Q * P) := hpot _
  have h2 : pot (Q * P) < Q * P := hbound _
  exact absurd h1 (Nat.not_le.2 h2)

theorem abstractPoly_to_sentence : AbstractQuasihaltsPoly → SentencePoly := by
  rintro ⟨N, hN⟩
  have hI : PInv (polyState N) := PInv_iter PInv_init N
  have hno : ∀ m, ¬ polyOver (polyIter (polyState N) m) := by
    intro m
    have : polyIter (polyState N) m = polyState (N + m) := (polyIter_add _ N m).symm
    rw [this]; exact hN _ (Nat.le_add_right _ _)
  have hK := polyIter_K_const hno
  refine sentencePoly_iff.2 ⟨(polyState N).K, hI.hK, fun n => ?_⟩
  have hex : ∃ m, n < (polyIter (polyState N) m).n :=
    Classical.byContradiction fun hc =>
      poly_stab hI hno n fun m => Nat.not_lt.1 fun h => hc ⟨m, h⟩
  obtain ⟨m, hm⟩ := hex
  obtain ⟨A, hA, hg⟩ := (PInv_iter hI m).hgood n hm
  rw [hK m] at hg
  exact ⟨A, hA, hg⟩

theorem sentence_to_abstractPoly : SentencePoly → AbstractQuasihaltsPoly := by
  intro hS
  obtain ⟨K0, hK0, hg⟩ := sentencePoly_iff.1 hS
  have hat : ∀ st : PSt, PInv st → st.K = K0 → ¬ polyOver st := by
    intro st hI hK
    obtain ⟨As, hAs, hAg⟩ := hg st.n
    rw [← hK] at hAg
    have hle : st.A ≤ As := Classical.byContradiction fun hc =>
      hI.hA' As hAs (Nat.not_le.1 hc) hAg
    exact Nat.not_lt.2 (Nat.le_trans (str_len_mono hI.hA hle) hAg.1)
  have hbd : ∀ k, (polyState k).K ≤ K0 := by
    intro k
    induction k with
    | zero => exact hK0
    | succ k ih =>
      have hI := PInv_iter PInv_init k
      show (polyStep (polyState k)).K ≤ K0
      by_cases ho : polyOver (polyState k)
      · rw [polyStep_over ho]
        have : (polyState k).K ≠ K0 := fun he => hat _ hI he ho
        show (polyState k).K + 1 ≤ K0
        omega
      · rw [polyStep_K_same ho]; exact ih
  obtain ⟨m0, hm0⟩ := stabilize (fun k => (polyState k).K) (fun k => polyStep_K_ge _) K0 hbd
  refine ⟨m0, fun k hk ho => ?_⟩
  have h1 := hm0 k hk
  have h2 := hm0 (k + 1) (Nat.le_succ_of_le hk)
  have : (polyState (k + 1)).K = (polyState k).K + 1 := by
    show (polyStep (polyState k)).K = _
    rw [polyStep_over ho]
  have h1' : (polyState k).K = (polyState m0).K := h1
  have h2' : (polyState (k + 1)).K = (polyState m0).K := h2
  omega

theorem abstractPoly_quasihalts_iff : AbstractQuasihaltsPoly ↔ SentencePoly :=
  ⟨abstractPoly_to_sentence, sentence_to_abstractPoly⟩

end ZP
