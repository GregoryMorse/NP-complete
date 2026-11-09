module

public import ZP.Compile
public import ZP.LogicalG

@[expose] public section

/-!
# Macro simulation for an arbitrary abstract trajectory

`Bridge`/`Compile`/`LogicalG` are stated for the step function `absStepC` of plans 02-07. The
NTT program has the step `(c, n) ↦ (c, n + 1)` or `(c + 1, n)`. Here the same results are stated for
an arbitrary beep sequence `bp : Nat → Prop` and, for logical machines, for an arbitrary
trajectory `traj` with predicate `C`: the pair lemma is only needed along the trajectory.
-/

namespace ZP

/-- A beep-exact simulation by a logical machine of an abstract run with beeps `bp`. -/
structure LMacroSimB (bp : Nat → Prop) (L : LTM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  total : ∀ k, ∃ c, L.conf k = some c
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, L.conf k = some c ∧ c.q = L.beep) ↔ bp n

/-- The same for a table machine. -/
structure MacroSimB (bp : Nat → Prop) (M : TM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, M.conf k = some c ∧ c.q = M.beep) ↔ bp n

theorem quasihalts_iff_of_macroSimB {bp : Nat → Prop} {M : TM} (S : MacroSimB bp M) :
    Quasihalts M ↔ ∃ N, ∀ n, N ≤ n → ¬ bp n := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn hbad => ?_⟩
    obtain ⟨k, hk1, _, c, hc1, hc2⟩ := (S.beeps n).2 hbad
    have := time_ge S.time S.mono n
    exact hN k (by omega) c hc1 hc2
  · rintro ⟨N, hN⟩
    refine ⟨S.time N, fun k hk c hc hq => ?_⟩
    obtain ⟨n, hn, h1, h2⟩ := time_interval S.time S.mono N k hk
    exact hN n hn ((S.beeps n).1 ⟨k, h1, h2, c, hc, hq⟩)

namespace Cert

variable (K : Cert) (hK : K.OK) {bp : Nat → Prop}

include hK in
theorem beeps_iffB (S : LMacroSimB bp K.L) (n : Nat) :
    (∃ k, htime K (S.time n) ≤ k ∧ k < htime K (S.time (n + 1)) ∧
      ∃ d, K.T.conf k = some d ∧ d.q = K.T.beep) ↔ bp n := by
  rw [← S.beeps n]
  constructor
  · rintro ⟨k, h1, h2, d, hd, hq⟩
    obtain ⟨m, hm1, hm2, hm3⟩ := time_interval (htime K) (htime_succ K hK S.total) (S.time n) k h1
    have hm4 : m < S.time (n + 1) := by
      by_cases hle : S.time (n + 1) ≤ m
      · have := htime_le K hK S.total _ _ hle
        omega
      · omega
    obtain ⟨c, hc⟩ := S.total m
    refine ⟨m, hm1, hm4, c, hc, ?_⟩
    obtain ⟨d0, hd0, henc⟩ := sim1 K hK m c hc
    by_cases hkm : k = htime K m
    · rw [hkm, hd0] at hd
      cases hd
      rw [henc.q] at hq
      exact (hK.beep _ (lq_lt K hK S.total hc)).1 hq
    · exfalso
      have hgl : htime K (m + 1) = htime K m + glenAt K m := rfl
      have hk' : k = htime K m + (k - htime K m) := by omega
      rw [hk'] at hd
      exact between K hK S.total m (k - htime K m) (by omega) (by omega) d hd hq
  · rintro ⟨m, hm1, hm2, c, hc, hq⟩
    obtain ⟨d, hd, henc⟩ := sim1 K hK m c hc
    refine ⟨htime K m, htime_le K hK S.total _ _ hm1, htime_strict K hK S.total hm2, d, hd, ?_⟩
    rw [henc.q]
    exact (hK.beep _ (lq_lt K hK S.total hc)).2 hq

/-- A macro simulation by the logical machine gives one by the table. -/
def macroSimB_of_logic (S : LMacroSimB bp K.L) : MacroSimB bp K.T where
  time n := htime K (S.time n)
  mono n := htime_strict K hK S.total (S.mono n)
  beeps n := beeps_iffB K hK S n

end Cert

/-- Pair data along a trajectory: from `lay (traj k)` the machine reaches `lay (traj (k+1))`,
visiting the beep state iff `bad k`, and then exactly once. -/
structure PairDataN (L : LTM) (bad : Nat → Prop) where
  lay : Nat → ZC
  k0 : Nat
  h0 : L.zconf k0 = some (lay 0)
  step : ∀ k, ∃ n, 0 < n ∧ L.Seg (lay k) n (lay (k + 1)) (bad k)

namespace PairDataN

variable {L : LTM} {bad : Nat → Prop} (P : PairDataN L bad)

noncomputable def plen (k : Nat) : Nat := Classical.choose (P.step k)

theorem plen_spec (k : Nat) : 0 < P.plen k ∧ L.Seg (P.lay k) (P.plen k) (P.lay (k + 1)) (bad k) :=
  Classical.choose_spec (P.step k)

noncomputable def ztime : Nat → Nat
  | 0 => P.k0
  | n + 1 => ztime n + P.plen n

theorem ztime_mono (n : Nat) : P.ztime n < P.ztime (n + 1) := by
  have := (P.plen_spec n).1
  show P.ztime n < P.ztime n + P.plen n
  omega

theorem ztime_lay (n : Nat) : L.zconf (P.ztime n) = some (P.lay n) := by
  induction n with
  | zero => exact P.h0
  | succ n ih =>
    have hs := (P.plen_spec n).2
    show L.zconf (P.ztime n + P.plen n) = some (P.lay (n + 1))
    by_cases hc : bad n
    · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
      have e1 := (zconf_add L _ _ ih h1).1
      have e2 := zconf_step L e1 h2
      have e3 := (zconf_add L _ _ e2 h3).1
      rw [show P.ztime n + a + 1 + (P.plen n - a - 1) = P.ztime n + P.plen n by omega] at e3
      exact e3
    · exact (zconf_add L _ _ ih (hs.1 hc)).1

theorem interval_conf (n j : Nat) (hj : j < P.plen n) :
    ∃ y, L.zconf (P.ztime n + j) = some y ∧ (y.q = L.beep → bad n) := by
  have hs := (P.plen_spec n).2
  have ih := P.ztime_lay n
  by_cases hc : bad n
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
  · obtain ⟨-, h2⟩ := zconf_add L _ _ ih (hs.1 hc)
    obtain ⟨y, hy, hyq⟩ := h2 j hj
    exact ⟨y, hy, fun h => absurd h hyq⟩

theorem beep_in (n : Nat) (hc : bad n) :
    ∃ j, j < P.plen n ∧ ∃ y, L.zconf (P.ztime n + j) = some y ∧ y.q = L.beep := by
  have hs := (P.plen_spec n).2
  obtain ⟨a, c1, c2, ha, h1, hb, -, -⟩ := hs.2 hc
  exact ⟨a, ha, c1, (zconf_add L _ _ (P.ztime_lay n) h1).1, hb⟩

include P in
theorem ztotal (k : Nat) : ∃ y, L.zconf k = some y := by
  by_cases hk : P.k0 ≤ k
  · obtain ⟨n, -, h1, h2⟩ := time_interval P.ztime P.ztime_mono 0 k hk
    have e : P.ztime (n + 1) = P.ztime n + P.plen n := rfl
    obtain ⟨y, hy, -⟩ := P.interval_conf n (k - P.ztime n) (by omega)
    rw [show P.ztime n + (k - P.ztime n) = k by omega] at hy
    exact ⟨y, hy⟩
  · exact (PairData.zconf_pre L k (P.k0 - k) _ (by rw [show k + (P.k0 - k) = P.k0 by omega]; exact P.h0))

include P in
theorem macroSim : Nonempty (LMacroSimB bad L) := by
  refine ⟨{ time := P.ztime, mono := P.ztime_mono, total := ?_, beeps := ?_ }⟩
  · intro k
    obtain ⟨y, hy⟩ := P.ztotal k
    obtain ⟨c, hc, -⟩ := zconf_rel L k y hy
    exact ⟨c, hc⟩
  · intro n
    have e : P.ztime (n + 1) = P.ztime n + P.plen n := rfl
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

end PairDataN

end ZP
