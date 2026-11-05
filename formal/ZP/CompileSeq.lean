module

public import ZP.Compile
public import ZP.SeqSim

@[expose] public section

namespace ZP

namespace Cert

variable (K : Cert) (hK : K.OK) (A : AbsProg)

include hK in
theorem beeps_iffA (S : LMacroSimA A K.L) (n : Nat) :
    (∃ k, htime K (S.time n) ≤ k ∧ k < htime K (S.time (n + 1)) ∧
      ∃ d, K.T.conf k = some d ∧ d.q = K.T.beep) ↔
      ¬ A.good (A.st n) := by
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
def macroSimA_of_logic (S : LMacroSimA A K.L) : MacroSimA A K.T where
  time n := htime K (S.time n)
  mono n := htime_strict K hK S.total (S.mono n)
  beeps n := beeps_iffA K hK A S n


end Cert

end ZP
