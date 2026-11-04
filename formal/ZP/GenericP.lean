module

public import ZP.PNP
public import ZP.Decide

@[expose] public section

/-!
# `Sentence_f ↔ f ∈ P` for any truth function `f`

The proofs of `sentence_iff`, `sentence_of_InP` and `InP_of_Sentence` never look inside
`inL`. Here they are for an arbitrary `f : List Bool → Bool`, so each native machine whose
only change is its truth routine (PP, PSPACE, FACTOR, DLOG, GI) gets
`Quasihalts ↔ f ∈ P` from its `Quasihalts ↔ SentenceC (CorrectF f)`.
-/

namespace ZP.Cx

/-- Candidate `J` answers instance `S` as the truth function `f` says. -/
def CorrectF (f : List Bool → Bool) (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = f (str S)

instance (f : List Bool → Bool) (J S : Nat) : Decidable (CorrectF f J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = f (str S)))

theorem sentenceF_iff (f : List Bool → Bool) :
    SentenceC (CorrectF f) ↔ ∃ J : List Bool, ∀ s, run J s (clock J s) = f s := by
  constructor
  · rintro ⟨J, -, hJ⟩
    refine ⟨str J, fun s => ?_⟩
    obtain ⟨S, hS, rfl⟩ := str_surj s
    exact hJ S hS
  · rintro ⟨J, hJ⟩
    obtain ⟨N, hN, rfl⟩ := str_surj J
    exact ⟨N, hN, fun S _ => hJ (str S)⟩

theorem sentenceF_of_InP (f : List Bool → Bool) (h : InP (fun s => f s = true)) :
    SentenceC (CorrectF f) := by
  obtain ⟨D, k, hD⟩ := h
  obtain ⟨P, hP, hrun⟩ := compile D k
  refine (sentenceF_iff f).mpr ⟨P, fun s => ?_⟩
  obtain ⟨b, hb, hiff⟩ := hD s
  rw [hrun]
  unfold clock
  rw [exec_mono D _ 0 _ 0 b hb _ (pow_le_clock s.length k P.length hP)]
  exact bool_eq_of_iff hiff

theorem InP_of_sentenceF (f : List Bool → Bool) (h : SentenceC (CorrectF f)) :
    InP (fun s => f s = true) := by
  obtain ⟨J, hJ⟩ := (sentenceF_iff f).mp h
  refine ⟨rm 6 (PD (gMach (startCode J)) (J.length + 1)),
    18 * (J.length + 1 + qm (gMach (startCode J)) + 8) + 1, fun x => ?_⟩
  obtain ⟨S', ⟨t, ht, hE⟩, hiff⟩ := pd_ok (gMach (startCode J)) (J.length + 1) x
  have hE' : Exec (PD (gMach (startCode J)) (J.length + 1)) (x :: List.replicate (6 + 1) []) S' t :=
    hE
  refine ⟨_, rm_ok 6 (ok_PD _ _) hE' _ (pd_lt _ _ x.length t ht), ?_⟩
  have hr := hJ x
  rw [run_eq] at hr
  unfold clock at hr
  have hz : zexec (gMach (startCode J)) ((x.length + 2) ^ (J.length + 1) - 1) 0 [] x =
      exec (gMach (startCode J)) ((x.length + 2) ^ (J.length + 1) - 1) 0 (inTape x) 0 :=
    (exec_z _ _ 0 [] x).symm.trans (by rw [inTape_z]; rfl)
  show _ ↔ f x = true
  rw [← hr, ← hz, ← hiff]
  exact decide_eq_true_iff

theorem sentenceF_iff_InP (f : List Bool → Bool) :
    SentenceC (CorrectF f) ↔ InP (fun s => f s = true) :=
  ⟨InP_of_sentenceF f, sentenceF_of_InP f⟩

/-- The original `Sentence` is the instance `f = inL`. -/
theorem sentence_eq_sentenceF : Sentence = SentenceC (CorrectF inL) := rfl

end ZP.Cx
