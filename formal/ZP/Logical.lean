module

public import ZP.Defs
public import ZP.Abstract
public import ZP.Bridge
public import ZP.LTM
public import ZP.Logic
public import ZP.Zip

@[expose] public section

/-!
# Layer N3: the logical machine runs the abstract program

`zpLogic` (`native/zp2.py`, 129 states, 4 symbols) simulates the abstract program
beep for beep and never halts. Between pairs its tape reads `M_g J M_1 s` (symbols
`B = 0`, `M = 1`, `'0' = 2`, `'1' = 3`), with blanks everywhere else, and the machine
is in state `GRB` on the blank right of `s` (`lay J S`).

Everything here is proved from one open lemma, `pair_step`: from `lay J S` the
machine reaches `lay` of `absStep (J, S)`, and visits the beep state on the way iff
`J` is wrong on `S`, and then exactly once.
-/

namespace ZP

/-- Bits as logical symbols: `'0' = 2`, `'1' = 3`. -/
def bitsOf (w : List Bool) : List Nat := w.map fun b => if b then 3 else 2

/-- `M_g J M_1 s`. -/
def layWord (J S : Nat) : List Nat := 1 :: (bitsOf (str J) ++ 1 :: bitsOf (str S))

/-- The configuration at the start of pair `(J, S)`. -/
def lay (J S : Nat) : ZC := ⟨Q.GRB, sapp (layWord J S).reverse blank, blank⟩

/-- A run of `n` steps from `z` to `z'`. It visits the beep state iff `b`, and then once. -/
def Seg (z : ZC) (n : Nat) (z' : ZC) (b : Prop) : Prop :=
  (¬ b → zpLogic.zrun n z = some z') ∧
  (b → ∃ a c1 c2, a < n ∧ zpLogic.zrun a z = some c1 ∧ c1.q = zpLogic.beep ∧
      zpLogic.zstep c1 = some c2 ∧ zpLogic.zrun (n - a - 1) c2 = some z')

/-- OPEN: one pair of the outer loop. -/
theorem pair_step (J S : Nat) (hJ : 1 ≤ J) (hS : 1 ≤ S) :
    ∃ n, 0 < n ∧
      Seg (lay J S) n (lay (absStep (J, S)).1 (absStep (J, S)).2) (¬ Correct J S) := by
  sorry

theorem pair_step' (p : Nat × Nat) : ∃ n, 0 < n ∧ (1 ≤ p.1 → 1 ≤ p.2 →
    Seg (lay p.1 p.2) n (lay (absStep p).1 (absStep p).2) (¬ Correct p.1 p.2)) := by
  by_cases h : 1 ≤ p.1 ∧ 1 ≤ p.2
  · obtain ⟨n, hn, hs⟩ := pair_step p.1 p.2 h.1 h.2
    exact ⟨n, hn, fun _ _ => hs⟩
  · exact ⟨1, Nat.one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

/-- Length of the run for pair `p`. -/
noncomputable def plen (p : Nat × Nat) : Nat := Classical.choose (pair_step' p)

theorem plen_spec (p : Nat × Nat) : 0 < plen p ∧ (1 ≤ p.1 → 1 ≤ p.2 →
    Seg (lay p.1 p.2) (plen p) (lay (absStep p).1 (absStep p).2) (¬ Correct p.1 p.2)) :=
  Classical.choose_spec (pair_step' p)

/-- The time at which abstract step `n` starts. -/
noncomputable def ztime : Nat → Nat
  | 0 => 2
  | n + 1 => ztime n + plen (absState n)

/-- `I0` writes `M_g`, `JOV2` writes `M_1`: the pair `('', '')`. -/
theorem zconf_two : zpLogic.zconf 2 = some (lay 1 1) := rfl

theorem ztime_mono (n : Nat) : ztime n < ztime (n + 1) := by
  have := (plen_spec (absState n)).1
  show ztime n < ztime n + plen (absState n)
  omega

theorem ztime_lay (n : Nat) :
    zpLogic.zconf (ztime n) = some (lay (absState n).1 (absState n).2) := by
  induction n with
  | zero => exact zconf_two
  | succ n ih =>
    obtain ⟨hJ, hS, -⟩ := absState_inv n
    have hs := (plen_spec (absState n)).2 hJ hS
    show zpLogic.zconf (ztime n + plen (absState n)) =
      some (lay (absStep (absState n)).1 (absStep (absState n)).2)
    by_cases hc : Correct (absState n).1 (absState n).2
    · exact (zconf_add zpLogic _ _ ih (hs.1 (fun h => h hc))).1
    · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
      have e1 := (zconf_add zpLogic _ _ ih h1).1
      have e2 := zconf_step zpLogic e1 h2
      have e3 := (zconf_add zpLogic _ _ e2 h3).1
      rw [show ztime n + a + 1 + (plen (absState n) - a - 1) = ztime n + plen (absState n) by
        omega] at e3
      exact e3

theorem interval_conf (n j : Nat) (hj : j < plen (absState n)) :
    ∃ y, zpLogic.zconf (ztime n + j) = some y ∧
      (y.q = zpLogic.beep → ¬ Correct (absState n).1 (absState n).2) := by
  obtain ⟨hJ, hS, -⟩ := absState_inv n
  have hs := (plen_spec (absState n)).2 hJ hS
  have ih := ztime_lay n
  by_cases hc : Correct (absState n).1 (absState n).2
  · obtain ⟨-, h2⟩ := zconf_add zpLogic _ _ ih (hs.1 (fun h => h hc))
    obtain ⟨y, hy, hyq⟩ := h2 j hj
    exact ⟨y, hy, fun h => absurd h hyq⟩
  · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
    obtain ⟨e1, m1⟩ := zconf_add zpLogic _ _ ih h1
    have e2 := zconf_step zpLogic e1 h2
    obtain ⟨-, m3⟩ := zconf_add zpLogic _ _ e2 h3
    by_cases hja : j < a
    · obtain ⟨y, hy, -⟩ := m1 j hja
      exact ⟨y, hy, fun _ => hc⟩
    · by_cases hja' : j = a
      · subst hja'
        exact ⟨c1, e1, fun _ => hc⟩
      · obtain ⟨y, hy, -⟩ := m3 (j - a - 1) (by omega)
        rw [show ztime n + a + 1 + (j - a - 1) = ztime n + j by omega] at hy
        exact ⟨y, hy, fun _ => hc⟩

theorem beep_in (n : Nat) (hc : ¬ Correct (absState n).1 (absState n).2) :
    ∃ j, j < plen (absState n) ∧ ∃ y, zpLogic.zconf (ztime n + j) = some y ∧
      y.q = zpLogic.beep := by
  obtain ⟨hJ, hS, -⟩ := absState_inv n
  have hs := (plen_spec (absState n)).2 hJ hS
  obtain ⟨a, c1, c2, ha, h1, hb, -, -⟩ := hs.2 hc
  exact ⟨a, ha, c1, (zconf_add zpLogic _ _ (ztime_lay n) h1).1, hb⟩

theorem ztotal (k : Nat) : ∃ y, zpLogic.zconf k = some y := by
  by_cases hk : 2 ≤ k
  · obtain ⟨n, -, h1, h2⟩ := time_interval ztime ztime_mono 0 k hk
    have e : ztime (n + 1) = ztime n + plen (absState n) := rfl
    obtain ⟨y, hy, -⟩ := interval_conf n (k - ztime n) (by omega)
    rw [show ztime n + (k - ztime n) = k by omega] at hy
    exact ⟨y, hy⟩
  · by_cases h0 : k = 0
    · subst h0
      exact ⟨_, rfl⟩
    · have h1 : k = 1 := by omega
      subst h1
      have h : (zpLogic.zconf 1).bind zpLogic.zstep = some (lay 1 1) := zconf_two
      cases e : zpLogic.zconf 1 with
      | none =>
        rw [e] at h
        have h' : (none : Option ZC) = some (lay 1 1) := h
        cases h'
      | some y => exact ⟨y, rfl⟩

theorem zpLogic_macroSim : Nonempty (LMacroSim zpLogic) := by
  refine ⟨{ time := ztime, mono := ztime_mono, total := ?_, beeps := ?_ }⟩
  · intro k
    obtain ⟨y, hy⟩ := ztotal k
    obtain ⟨c, hc, -⟩ := zconf_rel zpLogic k y hy
    exact ⟨c, hc⟩
  · intro n
    have e : ztime (n + 1) = ztime n + plen (absState n) := rfl
    constructor
    · rintro ⟨k, h1, h2, c, hc, hq⟩
      obtain ⟨y, hy, himp⟩ := interval_conf n (k - ztime n) (by omega)
      rw [show ztime n + (k - ztime n) = k by omega] at hy
      obtain ⟨c', hc', hr⟩ := zconf_rel zpLogic k y hy
      rw [hc] at hc'
      cases hc'
      apply himp
      rw [← hr.q]
      exact hq
    · intro hc
      obtain ⟨j, hj, y, hy, hyq⟩ := beep_in n hc
      obtain ⟨c, hc', hr⟩ := zconf_rel zpLogic _ y hy
      refine ⟨ztime n + j, by omega, by omega, c, hc', ?_⟩
      rw [hr.q]
      exact hyq

end ZP
