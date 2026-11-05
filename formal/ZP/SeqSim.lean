module

public import ZP.Defs
public import ZP.Bridge
public import ZP.LTM
public import ZP.Zip
public import ZP.LogicalG

@[expose] public section

/-!
# Macro simulation of an arbitrary abstract program

`Abstract.lean`/`Bridge.lean`/`LogicalG.lean` are written for the program `(J, S)`. The NTT machine runs
a different abstract program `(c, n)`. Here everything is stated for an abstract program with a state
type, a step, a correctness predicate (a beep iff it fails) and an invariant.
-/

namespace ZP

structure AbsProg where
  σ : Type
  init : σ
  next : σ → σ
  good : σ → Prop
  inv : σ → Prop
  inv_init : inv init
  inv_next : ∀ s, inv s → inv (next s)

namespace AbsProg

def st (A : AbsProg) : Nat → A.σ
  | 0 => A.init
  | k + 1 => A.next (A.st k)

theorem inv_st (A : AbsProg) (k : Nat) : A.inv (A.st k) := by
  induction k with
  | zero => exact A.inv_init
  | succ k ih => exact A.inv_next _ ih

/-- The program quasihalts: it refutes only finitely often. -/
def Q (A : AbsProg) : Prop := ∃ N, ∀ k, N ≤ k → A.good (A.st k)

end AbsProg

structure MacroSimA (A : AbsProg) (M : TM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, M.conf k = some c ∧ c.q = M.beep) ↔ ¬ A.good (A.st n)

theorem quasihalts_iff_of_macroSimA {A : AbsProg} {M : TM} (S : MacroSimA A M) : Quasihalts M ↔ A.Q := by
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

structure LMacroSimA (A : AbsProg) (L : LTM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  total : ∀ k, ∃ c, L.conf k = some c
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, L.conf k = some c ∧ c.q = L.beep) ↔ ¬ A.good (A.st n)


structure PairDataA (L : LTM) (A : AbsProg) where
  lay : A.σ → ZC
  k0 : Nat
  h0 : L.zconf k0 = some (lay A.init)
  step : ∀ s, A.inv s → ∃ n, 0 < n ∧ L.Seg (lay s) n (lay (A.next s)) (¬ A.good s)

namespace PairDataA

variable {L : LTM} {A : AbsProg} (P : PairDataA L A)

theorem pair_step' (s : A.σ) : ∃ n, 0 < n ∧ (A.inv s → L.Seg (P.lay s) n (P.lay (A.next s)) (¬ A.good s)) := by
  by_cases h : A.inv s
  · obtain ⟨n, hn, hs⟩ := P.step s h
    exact ⟨n, hn, fun _ => hs⟩
  · exact ⟨1, Nat.one_pos, fun h' => absurd h' h⟩

noncomputable def plen (s : A.σ) : Nat := Classical.choose (P.pair_step' s)

theorem plen_spec (s : A.σ) : 0 < P.plen s ∧ (A.inv s → L.Seg (P.lay s) (P.plen s) (P.lay (A.next s)) (¬ A.good s)) :=
  Classical.choose_spec (P.pair_step' s)

noncomputable def ztime : Nat → Nat
  | 0 => P.k0
  | n + 1 => ztime n + P.plen (A.st n)

theorem ztime_mono (n : Nat) : P.ztime n < P.ztime (n + 1) := by
  have := (P.plen_spec (A.st n)).1
  show P.ztime n < P.ztime n + P.plen (A.st n)
  omega

theorem ztime_lay (n : Nat) : L.zconf (P.ztime n) = some (P.lay (A.st n)) := by
  induction n with
  | zero => exact P.h0
  | succ n ih =>
    have hs := (P.plen_spec (A.st n)).2 (A.inv_st n)
    show L.zconf (P.ztime n + P.plen (A.st n)) = some (P.lay (A.next (A.st n)))
    by_cases hc : A.good (A.st n)
    · exact (zconf_add L _ _ ih (hs.1 (fun h => h hc))).1
    · obtain ⟨a, c1, c2, ha, h1, -, h2, h3⟩ := hs.2 hc
      have e1 := (zconf_add L _ _ ih h1).1
      have e2 := zconf_step L e1 h2
      have e3 := (zconf_add L _ _ e2 h3).1
      rw [show P.ztime n + a + 1 + (P.plen (A.st n) - a - 1) = P.ztime n + P.plen (A.st n) by omega] at e3
      exact e3

theorem interval_conf (n j : Nat) (hj : j < P.plen (A.st n)) :
    ∃ y, L.zconf (P.ztime n + j) = some y ∧ (y.q = L.beep → ¬ A.good (A.st n)) := by
  have hs := (P.plen_spec (A.st n)).2 (A.inv_st n)
  have ih := P.ztime_lay n
  by_cases hc : A.good (A.st n)
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

theorem beep_in (n : Nat) (hc : ¬ A.good (A.st n)) :
    ∃ j, j < P.plen (A.st n) ∧ ∃ y, L.zconf (P.ztime n + j) = some y ∧ y.q = L.beep := by
  have hs := (P.plen_spec (A.st n)).2 (A.inv_st n)
  obtain ⟨a, c1, c2, ha, h1, hb, -, -⟩ := hs.2 hc
  exact ⟨a, ha, c1, (zconf_add L _ _ (P.ztime_lay n) h1).1, hb⟩

theorem zconf_pre' (L : LTM) (k : Nat) : ∀ m y, L.zconf (k + m) = some y → ∃ y', L.zconf k = some y' := by
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
    have e : P.ztime (n + 1) = P.ztime n + P.plen (A.st n) := rfl
    obtain ⟨y, hy, -⟩ := P.interval_conf n (k - P.ztime n) (by omega)
    rw [show P.ztime n + (k - P.ztime n) = k by omega] at hy
    exact ⟨y, hy⟩
  · exact zconf_pre' L k (P.k0 - k) _ (by rw [show k + (P.k0 - k) = P.k0 by omega]; exact P.h0)

include P in
theorem macroSim : Nonempty (LMacroSimA A L) := by
  refine ⟨{ time := P.ztime, mono := P.ztime_mono, total := ?_, beeps := ?_ }⟩
  · intro k
    obtain ⟨y, hy⟩ := P.ztotal k
    obtain ⟨c, hc, -⟩ := zconf_rel L k y hy
    exact ⟨c, hc⟩
  · intro n
    have e : P.ztime (n + 1) = P.ztime n + P.plen (A.st n) := rfl
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

end PairDataA

end ZP
