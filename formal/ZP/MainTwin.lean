module

public import ZP.TwinRound
public import ZP.GenStep

@[expose] public section

/-!
# Twin primes: `Quasihalts twinMachine ↔ ¬ TwinPrimes`
-/

namespace ZP

/-- The walk start of candidate `n + 3`. -/
def twLay (n : Nat) : BZ := Kz 2 (n + 1)

/-- Candidate `m = n + 3` is a lesser twin prime. -/
def twBad (n : Nat) : Prop := IsPrime (n + 3) ∧ IsPrime (n + 3 + 2)

theorem tw_step (n : Nat) : ∃ pl, 0 < pl ∧ TSeg (twLay n) pl (twLay (n + 1)) (twBad n) := by
  obtain ⟨pl, hpl, hs⟩ := cand (n + 3) (by omega)
  refine ⟨pl, hpl, ?_⟩
  have e1 : n + 3 - 2 = n + 1 := by omega
  have e2 : n + 3 - 1 = n + 1 + 1 := by omega
  rw [e1, e2] at hs
  exact hs

noncomputable def twLen (k : Nat) : Nat := Classical.choose (tw_step k)

theorem twLen_spec (k : Nat) : 0 < twLen k ∧ TSeg (twLay k) (twLen k) (twLay (k + 1)) (twBad k) :=
  Classical.choose_spec (tw_step k)

theorem tw_k0 : ∃ k0, twinMachine.zconf k0 = some (twLay 0) := by
  obtain ⟨n, hn⟩ := start
  obtain ⟨h1, -⟩ := bzconf_add twinMachine 0 n (z := ⟨0, bblank, bblank⟩) rfl hn
  exact ⟨0 + n, h1⟩

noncomputable def twTime : Nat → Nat
  | 0 => Classical.choose tw_k0
  | n + 1 => twTime n + twLen n

theorem twTime_lay (n : Nat) : twinMachine.zconf (twTime n) = some (twLay n) := by
  induction n with
  | zero => exact Classical.choose_spec tw_k0
  | succ n ih =>
    have hs := (twLen_spec n).2
    show twinMachine.zconf (twTime n + twLen n) = some (twLay (n + 1))
    by_cases hc : twBad n
    · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
      have e1 := (bzconf_add twinMachine _ _ ih h1).1
      have e2 := bzconf_step twinMachine e1 h2
      have e3 := (bzconf_add twinMachine _ _ e2 h3).1
      rw [show twTime n + a + 1 + (twLen n - a - 1) = twTime n + twLen n by omega] at e3
      exact e3
    · exact (bzconf_add twinMachine _ _ ih (hs.1 hc)).1

theorem tw_interval (n j : Nat) (hj : j < twLen n) :
    ∃ y, twinMachine.zconf (twTime n + j) = some y ∧ (y.q = 5 → twBad n) := by
  have hs := (twLen_spec n).2
  have ih := twTime_lay n
  by_cases hc : twBad n
  · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
    obtain ⟨e1, m1⟩ := bzconf_add twinMachine _ _ ih h1
    have e2 := bzconf_step twinMachine e1 h2
    obtain ⟨-, m3⟩ := bzconf_add twinMachine _ _ e2 h3
    by_cases hja : j < a
    · obtain ⟨y, hy, -⟩ := m1 j hja
      exact ⟨y, hy, fun _ => hc⟩
    · by_cases hja' : j = a
      · subst hja'
        exact ⟨c1, e1, fun _ => hc⟩
      · obtain ⟨y, hy, -⟩ := m3 (j - a - 1) (by omega)
        rw [show twTime n + a + 1 + (j - a - 1) = twTime n + j by omega] at hy
        exact ⟨y, hy, fun _ => hc⟩
  · obtain ⟨-, h2⟩ := bzconf_add twinMachine _ _ ih (hs.1 hc)
    obtain ⟨y, hy, hyq⟩ := h2 j hj
    exact ⟨y, hy, fun h => absurd h hyq⟩

theorem tw_beep_in (n : Nat) (hc : twBad n) :
    ∃ j, j < twLen n ∧ ∃ y, twinMachine.zconf (twTime n + j) = some y ∧ y.q = 5 := by
  have hs := (twLen_spec n).2
  obtain ⟨a, c1, c2, ha, h1, hb, -, -⟩ := hs.2 hc
  exact ⟨a, ha, c1, (bzconf_add twinMachine _ _ (twTime_lay n) h1).1, hb⟩

noncomputable def twinMacroSim : MacroSimB twBad twinMachine where
  time := twTime
  mono n := by
    have := (twLen_spec n).1
    show twTime n < twTime n + twLen n
    omega
  beeps n := by
    have e : twTime (n + 1) = twTime n + twLen n := rfl
    constructor
    · rintro ⟨k, h1, h2, c, hc, hq⟩
      obtain ⟨y, hy, himp⟩ := tw_interval n (k - twTime n) (by omega)
      rw [show twTime n + (k - twTime n) = k by omega] at hy
      obtain ⟨c', hc', hr⟩ := bzconf_rel twinMachine k y hy
      rw [hc] at hc'
      cases hc'
      apply himp
      rw [← hr.q]
      exact hq
    · intro hc
      obtain ⟨j, hj, y, hy, hyq⟩ := tw_beep_in n hc
      obtain ⟨c, hc', hr⟩ := bzconf_rel twinMachine _ y hy
      refine ⟨twTime n + j, by omega, by omega, c, hc', ?_⟩
      rw [hr.q]
      exact hyq

theorem twinQuasihalts_iff : Quasihalts twinMachine ↔ ¬ TwinPrimes := by
  rw [quasihalts_iff_of_macroSimB twinMacroSim]
  unfold TwinPrimes
  constructor
  · rintro ⟨N, hN⟩ h
    obtain ⟨p, hp, h1, h2⟩ := h (N + 3)
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
    exact hN n (by omega) ⟨h1, h2⟩
  · intro h
    obtain ⟨n0, hn0⟩ : ∃ n, ¬ ∃ p, n ≤ p ∧ IsPrime p ∧ IsPrime (p + 2) :=
      Classical.byContradiction fun hc =>
        h (fun n => Classical.byContradiction fun hn => hc ⟨n, hn⟩)
    exact ⟨n0, fun k hk hb => hn0 ⟨k + 3, by omega, hb⟩⟩

end ZP
