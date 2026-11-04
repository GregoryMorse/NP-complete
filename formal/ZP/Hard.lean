module

public import ZP.HardB
public import ZP.PNP

@[expose] public section

/-!
# `L` is NP-hard, and `Sentence ↔ P = NP`

For `A ∈ NP` with verifier `V` (time `(n+2)^k`, certificates up to `m·(n+2)^k`), the
instance of `x` is `code (DX V k m x) pad` with `pad = (n+2)^E`, `E` large enough for
the honest certificate to fit and to finish in time (`red_iff`). `GEN` computes it,
so a decider for `L` gives one for `A` (`InP_of_InNP`). With `L ∈ NP` and
`P ⊆ NP` this gives `sentence_iff_PeqNP`.
-/

namespace ZP.Cx

theorem getD_true (o : Option Bool) : o.getD false = true ↔ o = some true := by
  cases o with
  | none => simp
  | some b => cases b <;> simp

theorem exec_in (D : Mach) (T : Nat) (c : List Bool) :
    exec D T 0 (inTape c) 0 = zexec D T 0 [] c := by
  rw [inTape_z]; exact exec_z D T 0 [] c

def padE (V : Mach) (k m : Nat) : Nat := (k + m + qm V + 30) * 5

theorem red_iff {A : List Bool → Prop} (V : Mach) (k m : Nat)
    (hV : ∀ x, A x ↔ ∃ c, c.length ≤ m * (x.length + 2) ^ k ∧
      exec V ((x.length + 2) ^ k) 0 (pairTape x c) 0 = some true) (x : List Bool) :
    inL (code (DX V k m x) ((x.length + 2) ^ padE V k m)) = true ↔ A x := by
  rw [inL_iff, hV]
  obtain ⟨hQ, hn2, hc⟩ := big_pow x.length (k + m + qm V + 30) (by omega)
  have hpad : (x.length + 2) ^ padE V k m = ((x.length + 2) ^ (k + m + qm V + 30)) ^ 5 := by
    unfold padE; rw [Nat.pow_mul]
  generalize hs : code (DX V k m x) ((x.length + 2) ^ padE V k m) = s
  have hsl : (x.length + 2) ^ padE V k m ≤ s.length := by rw [← hs]; exact code_length _ _
  have hcs : ∀ c T, run s c T = (zexec (DX V k m x) T 0 [] c).getD false := by
    intro c T; rw [← hs, compile_spec, exec_in]
  have hT : (x.length + 2) ^ k ≤ (x.length + 2) ^ (k + m + qm V + 30) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  constructor
  · rintro ⟨c, -, hr⟩
    rw [hcs, getD_true] at hr
    rcases dx_shape V k m x c with r | ⟨c0, X, rfl⟩
    · exact absurd hr (r.never _)
    · obtain ⟨t, -, b, hb, hF⟩ := dx_good V k m x c0 X
      have h1 := zexec_mono _ _ _ _ _ true hr (max (s.length + 1) (dxT x.length c0.length t + 1))
        (Nat.le_max_left _ _)
      have h2 := hF (max (s.length + 1) (dxT x.length c0.length t + 1))
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
      rw [h1] at h2
      obtain ⟨hc0, hacc⟩ := hb.mp (Option.some.inj h2).symm
      refine ⟨c0, by rw [Nat.mul_comm]; exact hc0, ?_⟩
      rw [pairTape_lay, exec_in, ← getD_true]
      exact hacc
  · rintro ⟨c0, hc0, hacc⟩
    rw [pairTape_lay, exec_in, ← getD_true] at hacc
    have hc0' : c0.length ≤ (x.length + 2) ^ k * m := by rw [Nat.mul_comm]; exact hc0
    obtain ⟨t, ht, b, hb, hF⟩ := dx_good V k m x c0
      (List.replicate (s.length + 1 - (lay [x, c0]).length) false)
    obtain ⟨hd, hl⟩ := dx_bound V k m x.length c0.length t _ hQ hn2 (hc _ (by omega))
      (hc _ (by omega)) (hc _ (by omega)) hT hc0' ht
    rw [← hpad] at hd hl
    have hlay := length_lay2 x c0
    refine ⟨lay [x, c0] ++ List.replicate (s.length + 1 - (lay [x, c0]).length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]
      omega
    · rw [hcs, hF (s.length + 1) (by omega)]
      exact hb.mpr ⟨hc0', hacc⟩

/-- Every NP language is in P once `Sentence` holds. -/
theorem InP_of_InNP (hS : Sentence) {A : List Bool → Prop} (hA : InNP A) : InP A := by
  obtain ⟨V, k, m, hV⟩ := hA
  obtain ⟨J, hJ⟩ := sentence_iff.mp hS
  refine ⟨rm 6 (.seq (GEN V k m (padE V k m)) (PD (gMach (startCode J)) (J.length + 1))),
    (padE V k m + F0 V k m + 30) * (12 * (18 * (J.length + 1 + qm (gMach (startCode J)) + 8) + 1)),
    fun x => ?_⟩
  obtain ⟨tg, htg, Eg⟩ := gen_ok V k m (padE V k m) x
  generalize hs : code (DX V k m x) ((x.length + 2) ^ padE V k m) = s at Eg
  obtain ⟨S', ⟨tp, htp, Ep⟩, hiff⟩ := pd_ok (gMach (startCode J)) (J.length + 1) s
  have hE : Exec (.seq (GEN V k m (padE V k m)) (PD (gMach (startCode J)) (J.length + 1)))
      (x :: List.replicate (6 + 1) []) S' (tg + tp) := Exec.seq Eg Ep
  have hsl : s.length ≤ x.length + tg := by
    have := Eg.tl_le
    rw [tl_WS, tl_WS] at this
    simp only [List.length_nil] at this
    omega
  refine ⟨_, rm_ok 6 ⟨ok_GEN _ _ _ _, ok_PD _ _⟩ hE _
    (dec_bound V k m (padE V k m) (gMach (startCode J)) (J.length + 1) x.length s.length tg tp
      hsl htg htp), ?_⟩
  have hr := hJ s
  rw [run_eq] at hr
  unfold clock at hr
  rw [decide_eq_true_iff, hiff, ← exec_in, hr, ← hs, red_iff V k m hV x]

/-- The sentence holds exactly when P = NP. -/
theorem sentence_iff_PeqNP : Sentence ↔ PeqNP :=
  ⟨fun h _ => ⟨InP_InNP, InP_of_InNP h⟩, sentence_of_PeqNP Lp_InNP⟩

end ZP.Cx
