module

public import ZP.Defs
public import ZP.Table
public import ZP.Abstract

@[expose] public section

/-!
# The literal table simulates the abstract program

The bridge is split in two.

* `quasihalts_iff_of_macroSim` (**proved**): if a machine has a *macro simulation*
  of the abstract program, it quasihalts iff the abstract program does. A macro
  simulation gives strictly increasing times `time n`, one per abstract step `n`
  (the moment the machine starts examining the pair `absState n`), such that the
  machine visits its beep state somewhere in `[time n, time (n+1))` iff
  `absState n` is a refutation.
* `ZP/Compile.lean` builds such a simulation for the table from one for the
  4-symbol logical machine (**proved**); `ZP/Logical.lean` holds the one open
  lemma, a simulation by the logical machine.
-/

namespace ZP

/-- A beep-exact simulation of the abstract program of `C` by `M`, one abstract step per
interval `[time n, time (n+1))`. -/
structure MacroSimC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] (M : TM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, M.conf k = some c ∧ c.q = M.beep) ↔
      ¬ C (absStateC C n).1 (absStateC C n).2

abbrev MacroSim (M : TM) : Type := MacroSimC Correct M

theorem time_ge (time : Nat → Nat) (h : ∀ n, time n < time (n + 1)) (n : Nat) :
    time 0 + n ≤ time n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => have := h n; omega

/-- Every time from `time N` on lies in an interval `[time n, time (n+1))` with `N ≤ n`. -/
theorem time_interval (time : Nat → Nat) (h : ∀ n, time n < time (n + 1)) (N k : Nat)
    (hk : time N ≤ k) : ∃ n, N ≤ n ∧ time n ≤ k ∧ k < time (n + 1) := by
  have key : ∀ d, k < time (N + d) → ∃ n, N ≤ n ∧ time n ≤ k ∧ k < time (n + 1) := by
    intro d
    induction d with
    | zero =>
      intro h0
      rw [Nat.add_zero] at h0
      omega
    | succ d ih =>
      intro hd
      by_cases hc : k < time (N + d)
      · exact ih hc
      · exact ⟨N + d, Nat.le_add_right N d, by omega, hd⟩
  have hb := time_ge time h (N + (k + 1))
  exact key (k + 1) (by omega)

/-- A macro simulation transfers quasihalting. -/
theorem quasihalts_iff_of_macroSimC {C : Nat → Nat → Prop} [∀ J S, Decidable (C J S)] {M : TM}
    (S : MacroSimC C M) : Quasihalts M ↔ AbstractQuasihaltsC C := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => Classical.byContradiction fun hbad => ?_⟩
    obtain ⟨k, hk1, _, c, hc1, hc2⟩ := (S.beeps n).2 hbad
    have := time_ge S.time S.mono n
    exact hN k (by omega) c hc1 hc2
  · rintro ⟨N, hN⟩
    refine ⟨S.time N, fun k hk c hc hq => ?_⟩
    obtain ⟨n, hn, h1, h2⟩ := time_interval S.time S.mono N k hk
    exact (S.beeps n).1 ⟨k, h1, h2, c, hc, hq⟩ (hN n hn)

theorem quasihalts_iff_of_macroSim {M : TM} (S : MacroSim M) :
    Quasihalts M ↔ AbstractQuasihalts := quasihalts_iff_of_macroSimC S

end ZP
