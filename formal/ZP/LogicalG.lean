module

public import ZP.AllDefs
public import ZP.Abstract
public import ZP.Bridge
public import ZP.LTM
public import ZP.Zip

@[expose] public section

/-!
# The logical machine simulates the abstract program, from one lemma per pair

Generic in the machine `L` and the correctness predicate `C`. A `PairData` says: the start
configuration is `lay 1 1` after `k0` steps, and from `lay J S` the machine reaches
`lay` of the next pair, visiting the beep state iff `C J S` fails, and then exactly once.
`PairData.macroSim` turns that into a macro simulation (`LMacroSimC`).
-/

namespace ZP

/-- A run of `n` steps from `z` to `z'`. It visits the beep state iff `b`, and then once. -/
def LTM.Seg (L : LTM) (z : ZC) (n : Nat) (z' : ZC) (b : Prop) : Prop :=
  (¬ b → L.zrun n z = some z') ∧
  (b → ∃ a c1 c2, a < n ∧ L.zrun a z = some c1 ∧ c1.q = L.beep ∧
      L.zstep c1 = some c2 ∧ L.zrun (n - a - 1) c2 = some z')

structure PairData (L : LTM) (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] where
  lay : Nat → Nat → ZC
  k0 : Nat
  h0 : L.zconf k0 = some (lay 1 1)
  step : ∀ J S, 1 ≤ J → 1 ≤ S → ∃ n, 0 < n ∧
    L.Seg (lay J S) n (lay (absStepC C (J, S)).1 (absStepC C (J, S)).2) (¬ C J S)

namespace PairData

variable {L : LTM} {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)] (P : PairData L C)

/-- A run of `n` steps from `z` to `z'`. It visits the beep state iff `b`, and then once. -/
def Seg (z : ZC) (n : Nat) (z' : ZC) (b : Prop) : Prop :=
  (¬ b → L.zrun n z = some z') ∧
  (b → ∃ a c1 c2, a < n ∧ L.zrun a z = some c1 ∧ c1.q = L.beep ∧
      L.zstep c1 = some c2 ∧ L.zrun (n - a - 1) c2 = some z')

theorem pair_step' (p : Nat × Nat) : ∃ n, 0 < n ∧ (1 ≤ p.1 → 1 ≤ p.2 →
    L.Seg (P.lay p.1 p.2) n (P.lay (absStepC C p).1 (absStepC C p).2) (¬ C p.1 p.2)) := by
  by_cases h : 1 ≤ p.1 ∧ 1 ≤ p.2
  · obtain ⟨n, hn, hs⟩ := P.step p.1 p.2 h.1 h.2
    exact ⟨n, hn, fun _ _ => hs⟩
  · exact ⟨1, Nat.one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

/-- Length of the run for pair `p`. -/
noncomputable def plen (p : Nat × Nat) : Nat := Classical.choose (P.pair_step' p)

theorem plen_spec (p : Nat × Nat) : 0 < P.plen p ∧ (1 ≤ p.1 → 1 ≤ p.2 →
    L.Seg (P.lay p.1 p.2) (P.plen p) (P.lay (absStepC C p).1 (absStepC C p).2) (¬ C p.1 p.2)) :=
  Classical.choose_spec (P.pair_step' p)

/-- The time at which abstract step `n` starts. -/
noncomputable def ztime : Nat → Nat
  | 0 => P.k0
  | n + 1 => ztime n + P.plen (absStateC C n)

theorem ztime_mono (n : Nat) : P.ztime n < P.ztime (n + 1) := by
  have := (P.plen_spec (absStateC C n)).1
  show P.ztime n < P.ztime n + P.plen (absStateC C n)
  omega

theorem ztime_lay (n : Nat) :
    L.zconf (P.ztime n) = some (P.lay (absStateC C n).1 (absStateC C n).2) := by
  induction n with
  | zero => exact P.h0
  | succ n ih =>
    obtain ⟨hJ, hS, -⟩ := absStateC_inv (C := C) n
    have hs := (P.plen_spec (absStateC C n)).2 hJ hS
    show L.zconf (P.ztime n + P.plen (absStateC C n)) =
      some (P.lay (absStepC C (absStateC C n)).1 (absStepC C (absStateC C n)).2)
    by_cases hc : C (absStateC C n).1 (absStateC C n).2
    · exact (zconf_add L _ _ ih (hs.1 (fun h => h hc))).1
    · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
      have e1 := (zconf_add L _ _ ih h1).1
      have e2 := zconf_step L e1 h2
      have e3 := (zconf_add L _ _ e2 h3).1
      rw [show P.ztime n + a + 1 + (P.plen (absStateC C n) - a - 1) = P.ztime n + P.plen (absStateC C n) by
        omega] at e3
      exact e3

theorem interval_conf (n j : Nat) (hj : j < P.plen (absStateC C n)) :
    ∃ y, L.zconf (P.ztime n + j) = some y ∧
      (y.q = L.beep → ¬ C (absStateC C n).1 (absStateC C n).2) := by
  obtain ⟨hJ, hS, -⟩ := absStateC_inv (C := C) n
  have hs := (P.plen_spec (absStateC C n)).2 hJ hS
  have ih := P.ztime_lay n
  by_cases hc : C (absStateC C n).1 (absStateC C n).2
  · obtain ⟨-, h2⟩ := zconf_add L _ _ ih (hs.1 (fun h => h hc))
    obtain ⟨y, hy, hyq⟩ := h2 j hj
    exact ⟨y, hy, fun h => absurd h hyq⟩
  · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
    obtain ⟨e1, m1⟩ := zconf_add L _ _ ih h1
    have e2 := zconf_step L e1 h2
    obtain ⟨-, m3⟩ := zconf_add L _ _ e2 h3
    by_cases hja : j < a
    · obtain ⟨y, hy, -⟩ := m1 j hja
      exact ⟨y, hy, fun _ => hc⟩
    · by_cases hja' : j = a
      · subst hja'
        exact ⟨c1, e1, fun _ => hc⟩
      · obtain ⟨y, hy, -⟩ := m3 (j - a - 1) (by omega)
        rw [show P.ztime n + a + 1 + (j - a - 1) = P.ztime n + j by omega] at hy
        exact ⟨y, hy, fun _ => hc⟩

theorem beep_in (n : Nat) (hc : ¬ C (absStateC C n).1 (absStateC C n).2) :
    ∃ j, j < P.plen (absStateC C n) ∧ ∃ y, L.zconf (P.ztime n + j) = some y ∧
      y.q = L.beep := by
  obtain ⟨hJ, hS, -⟩ := absStateC_inv (C := C) n
  have hs := (P.plen_spec (absStateC C n)).2 hJ hS
  obtain ⟨a, c1, c2, ha, h1, hb, -, -⟩ := hs.2 hc
  exact ⟨a, ha, c1, (zconf_add L _ _ (P.ztime_lay n) h1).1, hb⟩

theorem zconf_pre (L : LTM) (k : Nat) : ∀ m y, L.zconf (k + m) = some y → ∃ y', L.zconf k = some y' := by
  intro m
  induction m with
  | zero => intro y h; exact ⟨y, h⟩
  | succ m ih =>
    intro y h
    have h' : (L.zconf (k + m)).bind L.zstep = some y := h
    cases e : L.zconf (k + m) with
    | none => rw [e] at h'; cases h'
    | some z => exact ih z e

include P in
theorem ztotal (k : Nat) : ∃ y, L.zconf k = some y := by
  by_cases hk : P.k0 ≤ k
  · obtain ⟨n, -, h1, h2⟩ := time_interval P.ztime P.ztime_mono 0 k hk
    have e : P.ztime (n + 1) = P.ztime n + P.plen (absStateC C n) := rfl
    obtain ⟨y, hy, -⟩ := P.interval_conf n (k - P.ztime n) (by omega)
    rw [show P.ztime n + (k - P.ztime n) = k by omega] at hy
    exact ⟨y, hy⟩
  · exact zconf_pre L k (P.k0 - k) _ (by rw [show k + (P.k0 - k) = P.k0 by omega]; exact P.h0)

include P in
theorem macroSim : Nonempty (LMacroSimC C L) := by
  refine ⟨{ time := P.ztime, mono := P.ztime_mono, total := ?_, beeps := ?_ }⟩
  · intro k
    obtain ⟨y, hy⟩ := P.ztotal k
    obtain ⟨c, hc, -⟩ := zconf_rel L k y hy
    exact ⟨c, hc⟩
  · intro n
    have e : P.ztime (n + 1) = P.ztime n + P.plen (absStateC C n) := rfl
    constructor
    · rintro ⟨k, h1, h2, c, hc, hq⟩
      obtain ⟨y, hy, himp⟩ := P.interval_conf n (k - P.ztime n) (by omega)
      rw [show P.ztime n + (k - P.ztime n) = k by omega] at hy
      obtain ⟨c', hc', hr⟩ := zconf_rel L k y hy
      rw [hc] at hc'
      cases hc'
      apply himp
      rw [← hr.q]
      exact hq
    · intro hc
      obtain ⟨j, hj, y, hy, hyq⟩ := P.beep_in n hc
      obtain ⟨c, hc', hr⟩ := zconf_rel L _ y hy
      refine ⟨P.ztime n + j, by omega, by omega, c, hc', ?_⟩
      rw [hr.q]
      exact hyq

end PairData

end ZP
