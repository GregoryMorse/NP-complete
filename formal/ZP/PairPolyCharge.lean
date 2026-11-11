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

theorem rep0_cons (k : Nat) (l : List Nat) :
    List.replicate k 0 ++ 0 :: l = 0 :: (List.replicate k 0 ++ l) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The fuel is exhausted during the charge: the beep. -/
theorem chargeExh (n : Nat) : ∀ (g : Nat) (_ : g = 0 ∨ g = 1) (T Z Y ds : List Nat), Bits T → Sym4 Z → NoB Y → Dig n ds →
    valr n ds < T.length → ∃ ds', Dig n ds' ∧
      zppolyLogic.Reach (hdR QPoly.U Z (T ++ g :: (1 :: Y ++ 1 :: FWr n ds)))
        (hdR QPoly.BEEPX (Z ++ (List.replicate (T.length + 1) 0 ++ [1])) (Y ++ 1 :: FWr n ds'))
  | _, _, [], _, _, _, _, _, _, _, h => by simp at h
  | g, hg, b :: T, Z, Y, ds, hT, hZ, hY, hds, hlt => by
    have hX : NoB (1 :: Y) := NoB.cons one_nb hY
    rcases Nat.eq_zero_or_pos (valr n ds) with h0 | hpos
    · have h1 : zppolyLogic.Reach (hdR QPoly.U Z (b :: (T ++ g :: ((1 :: Y) ++ 1 :: FWr n ds))))
          (hd Q.DEC1 (Z ++ 1 :: (T ++ 0 :: ((1 :: Y) ++ 1 :: FWr n ds))) []) := by
        rcases hg with rfl | rfl
        · exact uvFr Z T ((1 :: Y) ++ 1 :: FWr n ds) b hZ hT.tail
            (hX.app (NoB.cons one_nb (FWr_noB n ds))) hT.head
        · exact uvFrH Z T ((1 :: Y) ++ 1 :: FWr n ds) b hZ hT.tail
            (hX.app (NoB.cons one_nb (FWr_noB n ds))) hT.head
      have hL : Sym4 (Z ++ 1 :: (T ++ 0 :: (1 :: Y))) :=
        hZ.app (Sym4.cons (by simp [ALL]) ((hT.tail.sym4).app
          (Sym4.cons (by simp [ALL]) hX.sym4)))
      have h2 := ((fuel n ds hds (Z ++ 1 :: (T ++ 0 :: (1 :: Y))) [] hL Sym4.nil (Or.inl rfl)).2 h0)
      have h2' := zpolyBase_ext.reach h2
      have hL' : Sym4 (Z ++ 1 :: (T ++ [0])) :=
        hZ.app (Sym4.cons (by simp [ALL]) ((hT.tail.sym4).app
          (Sym4.cons (by simp [ALL]) Sym4.nil)))
      have h3 := zpolyBase_ext.reach <| walkL Q.EXH (Or.inr rfl) (Z ++ 1 :: (T ++ [0])) (1 :: Y)
        (1 :: (FWr n (ds.map fun _ => n + 1) ++ [])) hL' hX
        (Sym4.cons (by simp [ALL]) ((FWr_noB n _).sym4.app Sym4.nil))
      have h4 := exhCharge Z T Y (FWr n (ds.map fun _ => n + 1) ++ []) hZ hT.tail hY
        ((FWr_noB n _).sym4.app Sym4.nil)
      refine ⟨ds.map fun _ => n + 1, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact Nat.le_refl _
      · simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append,
          List.singleton_append] at h1 h2' h3 h4 ⊢
        refine (h1.trans (h2'.trans (h3.trans h4))).of_eq rfl ?_
        simp [List.replicate_succ, rep0_cons]
    · obtain ⟨ds1, hd1, hl1, hv1, h1⟩ := chargeStep n g hg Z b T (1 :: Y) ds hZ hT.head
        hT.tail hX hds hpos
      obtain ⟨ds2, hd2, h2⟩ := chargeExh n 0 (Or.inl rfl) T (Z ++ [0]) Y ds1 hT.tail
        (hZ.app (Sym4.cons (by simp [ALL]) Sym4.nil)) hY hd1 (by simp at hlt; omega)
      refine ⟨ds2, hd2, h1.trans (h2.of_eq rfl ?_)⟩
      simp [List.replicate_succ]

/-- Charge of an empty `a`: `U` meets `H` and passes it. -/
theorem uMEnd (Z : List Nat) (X : List Nat) (hZ : Sym4 Z) (hX : NoB X) :
    zppolyLogic.Reach (hdR QPoly.U (Z) (1 :: (X))) (hdR Q.DG2 (Z ++ ([1])) (X)) := by
  have hV : Valid [ALL, NB] [Z, X] := Valid.cons hZ (Valid.cons hX (Valid.nil _))
  exact checkFF (env := [Z, X]) (E := []) (k := 1) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id])
        (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-! ## The whole charge -/

/-- The token copy of `a`. -/
theorem gcLoopC (V P Rest : List Nat) (hV : NoB V) (hP : Bits P) (hR : Sym4 Rest) :
    ∀ (v Ur u : List Nat), Bits v → Bits Ur → Bits u →
      zppolyLogic.Reach (hdR Q.GC (Ur ++ (1 :: (V ++ (P ++ (1 :: u))))) (v ++ 0 :: Rest))
        (hdR Q.GC (v.reverse ++ Ur ++ (1 :: (V ++ (P ++ (1 :: (u ++ v)))))) (0 :: Rest))
  | [], Ur, u, _, _, _ => by simp; exact LTM.Reach.refl _ _
  | b :: v, Ur, u, hv, hUr, hu => by
    have h1 := gcBodyC Ur V P u v Rest b hUr hV hP hu hv.tail hR hv.head
    have h2 := gcLoopC V P Rest hV hP hR v (b :: Ur) (u ++ [b]) hv.tail (hUr.cons hv.head)
      (hu.snoc hv.head)
    refine h1.trans (h2.of_eq rfl ?_)
    simp

/-- The charge succeeds: `|a|` decrements, back to `DG2` with `H` after `|a|` blanks. -/
theorem chargeOK (n : Nat) (K a Rm ds : List Nat) (hK : Bits K) (ha : Bits a) (hRm : NoB Rm)
    (hds : Dig n ds) (hle : a.length ≤ valr n ds) :
    ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧ valr n ds' + a.length = valr n ds ∧
      zppolyLogic.Reach (hdR QPoly.CHS [1] (1 :: (K ++ 1 :: (a ++ 1 :: (Rm ++ 1 :: FWr n ds)))))
        (hdR Q.DG2 (List.replicate a.length 0 ++ [1])
          (1 :: (K ++ 1 :: (a ++ 1 :: (Rm ++ 1 :: FWr n ds'))))) := by
  have hY : Sym4 (Rm ++ 1 :: FWr n ds) :=
    (hRm.app (NoB.cons one_nb (FWr_noB n ds))).sym4
  have h1 := chargeStart K a (Rm ++ 1 :: FWr n ds) hK ha hY
  have hV : NoB (1 :: K) := NoB.cons one_nb hK.noB
  have h2 := gcLoopC (1 :: K) [] (Rm ++ 1 :: FWr n ds) hV Bits.nil hY a [] [] ha Bits.nil Bits.nil
  have h3 := gcEndC a.reverse (1 :: K) [] a (Rm ++ 1 :: FWr n ds) ha.rev hV Bits.nil ha hY
  have hX : NoB (K ++ 1 :: (a ++ 1 :: Rm)) :=
    hK.noB.app (NoB.cons one_nb (ha.noB.app (NoB.cons one_nb hRm)))
  rcases hT : a.reverse with _ | ⟨b, T'⟩
  · have ha0 : a = [] := by
      have := congrArg List.reverse hT
      simpa using this
    subst ha0
    have h4 := uMEnd [] ((1 :: K) ++ 1 :: 1 :: (Rm ++ 1 :: FWr n ds)) Sym4.nil
      (hV.app (NoB.cons one_nb (NoB.cons one_nb (hRm.app (NoB.cons one_nb (FWr_noB n ds))))))
    refine ⟨ds, hds, rfl, by simp, ?_⟩
    simp only [List.reverse_nil, List.nil_append, List.append_nil, List.append_assoc,
      List.cons_append, List.singleton_append, List.replicate, List.length_nil] at hT h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))
  · have hT' : Bits (b :: T') := hT ▸ ha.rev
    obtain ⟨ds1, hd1, hl1, hv1, h5⟩ := chargeStep n 1 (Or.inr rfl) [] b T' (1 :: (K ++ 1 :: (a ++ 1 :: Rm))) ds
      Sym4.nil hT'.head hT'.tail (NoB.cons one_nb hX) hds
      (by
        have : (b :: T').length = a.length := by rw [← hT]; simp
        simp at this; omega)
    have hlenT : a.length = T'.length + 1 := by
      have : (a.reverse).length = a.length := by simp
      rw [hT] at this; simp at this; omega
    obtain ⟨ds2, hd2, hl2, hv2, h6⟩ := chargeLoop n T' [0] (1 :: (K ++ 1 :: (a ++ 1 :: Rm))) ds1 hT'.tail
      (Sym4.cons (by simp [ALL]) Sym4.nil) (NoB.cons one_nb hX) hd1 (by omega)
    refine ⟨ds2, hd2, by omega, by omega, ?_⟩
    rw [hT] at h2 h3
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append] at h1 h2 h3 h5 h6 ⊢
    refine (h1.trans (h2.trans (h3.trans (h5.trans h6)))).of_eq rfl ?_
    rw [hlenT]
    simp [List.replicate_succ]

/-- The charge exhausts the fuel: the beep, with `M_g` restored after `|a| + 1` blanks. -/
theorem chargeEx (n : Nat) (K a Rm ds : List Nat) (hK : Bits K) (ha : Bits a) (hRm : NoB Rm)
    (hds : Dig n ds) (hlt : valr n ds < a.length) :
    ∃ ds', Dig n ds' ∧
      zppolyLogic.Reach (hdR QPoly.CHS [1] (1 :: (K ++ 1 :: (a ++ 1 :: (Rm ++ 1 :: FWr n ds)))))
        (hdR QPoly.BEEPX (List.replicate (a.length + 1) 0 ++ [1])
          (K ++ 1 :: (a ++ 1 :: (Rm ++ 1 :: FWr n ds')))) := by
  have hY : Sym4 (Rm ++ 1 :: FWr n ds) :=
    (hRm.app (NoB.cons one_nb (FWr_noB n ds))).sym4
  have h1 := chargeStart K a (Rm ++ 1 :: FWr n ds) hK ha hY
  have hV : NoB (1 :: K) := NoB.cons one_nb hK.noB
  have h2 := gcLoopC (1 :: K) [] (Rm ++ 1 :: FWr n ds) hV Bits.nil hY a [] [] ha Bits.nil Bits.nil
  have h3 := gcEndC a.reverse (1 :: K) [] a (Rm ++ 1 :: FWr n ds) ha.rev hV Bits.nil ha hY
  have hlen : a.reverse.length = a.length := by simp
  obtain ⟨ds', hd', h4⟩ := chargeExh n 1 (Or.inr rfl) a.reverse [] (K ++ 1 :: (a ++ 1 :: Rm)) ds
    ha.rev Sym4.nil (ha.noB.app (NoB.cons one_nb hRm) |> fun h => (hK.noB.app (NoB.cons one_nb h)))
    hds (by omega)
  refine ⟨ds', hd', ?_⟩
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append,
    hlen] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

end ZP.Poly
