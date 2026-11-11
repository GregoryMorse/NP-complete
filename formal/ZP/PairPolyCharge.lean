module

public import ZP.PairPoly

@[expose] public section

/-!
# The charge of `|a|` against the fuel

After the walker is home the machine copies `a` as tokens to the left and decrements
the fuel once per token. Either the fuel lasts (the loop ends at `DG2` with the tokens
erased) or it is exhausted (the beep: `BEEPX`, with `M_g` restored).
-/

namespace ZP.Poly

open ZP

/-- One token: `U` writes `M_t`, one decrement, `M_t` moves right. -/
theorem chargeStep (n : Nat) (g : Nat) (hg : g = 0 ∨ g = 1) (Z : List Nat) (b : Nat) (T X0 ds : List Nat)
    (hZ : Sym4 Z) (hb : b ∈ bits) (hT : Bits T) (hX : NoB X0) (hds : Dig n ds)
    (hpos : 0 < valr n ds) :
    ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧ valr n ds' + 1 = valr n ds ∧
      zppolyLogic.Reach (hdR QPoly.U Z (b :: (T ++ g :: (X0 ++ 1 :: FWr n ds))))
        (hdR QPoly.U (Z ++ [0]) (T ++ 0 :: (X0 ++ 1 :: FWr n ds'))) := by
  have hX1 : NoB (X0 ++ 1 :: FWr n ds) := hX.app (NoB.cons one_nb (FWr_noB n ds))
  have h1 : zppolyLogic.Reach (hdR QPoly.U Z (b :: (T ++ g :: (X0 ++ 1 :: FWr n ds))))
      (hd Q.DEC1 (Z ++ 1 :: (T ++ 0 :: (X0 ++ 1 :: FWr n ds))) []) := by
    rcases hg with rfl | rfl
    · exact uvFr Z T (X0 ++ 1 :: FWr n ds) b hZ hT hX1 hb
    · exact uvFrH Z T (X0 ++ 1 :: FWr n ds) b hZ hT hX1 hb
  have hL : Sym4 (Z ++ 1 :: (T ++ 0 :: X0)) :=
    hZ.app (Sym4.cons (by simp [ALL]) ((hT.sym4).app (Sym4.cons (by simp [ALL]) hX.sym4)))
  obtain ⟨ds', hd', hl', hv', h2⟩ :=
    (fuel n ds hds (Z ++ 1 :: (T ++ 0 :: X0)) [] hL Sym4.nil (Or.inl rfl)).1 hpos
  have h2' := zpolyBase_ext.reach h2
  have hX2 : NoB (X0 ++ [1]) := hX.app (NoB.cons one_nb NoB.nil)
  have hW : Sym4 (FWr n ds' ++ []) := (FWr_noB n ds').sym4.app Sym4.nil
  refine ⟨ds', hd', hl', hv', ?_⟩
  cases T with
  | nil =>
    have h3 := fbUlast Z (X0 ++ [1]) (FWr n ds' ++ []) hZ hX2 hW
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.singleton_append] at h1 h2' h3 ⊢
    exact h1.trans (h2'.trans h3)
  | cons b' T' =>
    have h3 := fbU Z T' (X0 ++ [1]) (FWr n ds' ++ []) b' hZ (Bits.tail hT) hX2 hW (Bits.head hT)
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
      List.singleton_append] at h1 h2' h3 ⊢
    exact h1.trans (h2'.trans h3)

/-- The loop: all tokens are paid, the machine ends at `DG2` with `H` restored. -/
theorem chargeLoop (n : Nat) : ∀ (T Z X0 ds : List Nat), Bits T → Sym4 Z → NoB X0 → Dig n ds →
    T.length ≤ valr n ds → ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧
      valr n ds' + T.length = valr n ds ∧
      zppolyLogic.Reach (hdR QPoly.U Z (T ++ 0 :: (X0 ++ 1 :: FWr n ds)))
        (hdR Q.DG2 (Z ++ (List.replicate T.length 0 ++ [1])) (X0 ++ 1 :: FWr n ds'))
  | [], Z, X0, ds, _, hZ, hX, hds, _ => by
    refine ⟨ds, hds, rfl, by simp, ?_⟩
    have := uEnd Z (X0 ++ 1 :: FWr n ds) hZ (hX.app (NoB.cons one_nb (FWr_noB n ds)))
    simpa using this
  | b :: T, Z, X0, ds, hT, hZ, hX, hds, hle => by
    obtain ⟨ds1, hd1, hl1, hv1, h1⟩ := chargeStep n 0 (Or.inl rfl) Z b T X0 ds hZ hT.head hT.tail hX hds
      (by simp at hle; omega)
    obtain ⟨ds2, hd2, hl2, hv2, h2⟩ := chargeLoop n T (Z ++ [0]) X0 ds1 hT.tail
      (hZ.app (Sym4.cons (by simp [ALL]) Sym4.nil)) hX hd1 (by simp at hle; omega)
    refine ⟨ds2, hd2, by omega, by simp; omega, h1.trans (h2.of_eq rfl ?_)⟩
    simp [List.replicate_succ]

end ZP.Poly
