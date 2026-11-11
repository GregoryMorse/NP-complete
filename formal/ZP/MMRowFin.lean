module

public import ZP.MMRoundE
public import ZP.MMDry2

@[expose] public section

/-! End of a row.  After the last round `P` is next to the boundary `M`; the hole is rewound, `FA` meets the boundary and
`D0..D3` check the accumulator (stored `X`): all `2` (`rowFinOK`, on to `Q2`) or a `3` (`rowFinBad`, outcome 0 up to `DP30`). -/

namespace ZP.Mul.MM

open ZP

theorem rowFinOK (L Bd X R0 : List Nat) (hL : Sym4 L) (hBd : Bits Bd) (hX : ∀ a ∈ X, a = 2) (hXb : Bits X)
    (hR : Sym4 R0) :
    zmmLogic.Reach (hdR QMM.RS1 (L ++ 1 :: 0 :: (Bd ++ [1])) (0 :: X ++ 1 :: R0))
      (hd QMM.Q2 (L ++ 1 :: 0 :: Bd ++ [1] ++ X) (0 :: 1 :: R0)) := by
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hL1 : Sym4 (L ++ [1]) := Sym4.app hL (Sym4.cons h1 Sym4.nil)
  have t0 := rsLoop X hXb (L ++ 1 :: 0 :: (Bd ++ [1])) (by simp [sym4_app_iff, sym4_cons_iff, *, hBd.sym4, ALL]) R0 hR
  have t1 := toFA (L ++ [1]) Bd X R0 hL1 hBd hXb hR
  have t2 := rowEndOK L Bd X R0 hL hBd hX hR
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 ⊢
  exact t0.trans (t1.trans t2)

theorem rowFinBad (L Bd Z Y outr Cb J sv Y2 : List Nat) (hL : NoB L) (hBd : Bits Bd) (hZ : ∀ a ∈ Z, a = 2)
    (hY : Bits Y) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (L ++ 1 :: 0 :: (Bd ++ [1]))
        (0 :: (Z ++ 3 :: Y) ++ 1 :: outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))
      (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have hL4 : Sym4 L := fun a ha => by
    have := hL a ha
    simp only [NB, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl <;> simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hZb : Bits Z := fun a ha => by rw [hZ a ha]; simp [bits]
  have hXb : Bits (Z ++ 3 :: Y) := fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hZb a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp [bits]
      · exact hY a ha
  have hR0 : Sym4 (outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) := by
    have := houtr.sym4
    have := hJ.sym4
    have := hsv.sym4
    have := sym4_B0 hCb
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    simp [sym4_app_iff, sym4_cons_iff, *]
  have hL1 : Sym4 (L ++ [1]) := Sym4.app hL4 (Sym4.cons h1 Sym4.nil)
  have t0 := rsLoop (Z ++ 3 :: Y) hXb (L ++ 1 :: 0 :: (Bd ++ [1]))
    (by simp [sym4_app_iff, sym4_cons_iff, *, hBd.sym4, ALL]) _ hR0
  have t1 := toFA (L ++ [1]) Bd (Z ++ 3 :: Y) _ hL1 hBd hXb hR0
  have t2 := rowEndBad L Bd Z Y _ hL4 hBd hZ hY hR0
  rw [hd_snoc QMM.J1] at t2
  have hARr : Bits (Z ++ 2 :: Y) := fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hZb a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp [bits]
      · exact hY a ha
  have t3 := vEndBad L Bd (Z ++ 2 :: Y) [] outr Cb J sv Y2 hL hBd hARr Bits.nil houtr hCb hJ hsv hY2
  have t4 := vw1Bad (List.replicate L.length 0 ++ 0 :: 0 :: List.replicate Bd.length 0 ++
      0 :: List.replicate (Z ++ 2 :: Y).length 0 ++ 0 :: List.replicate ([] : List Nat).length 0)
    outr Cb J sv Y2 (by
      intro a ha
      simp [List.mem_replicate] at ha
      omega) (by simp; omega) houtr hCb hJ hsv hY2
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 t3 t4 ⊢
  exact t0.trans (t1.trans (t2.trans (t3.trans t4)))

end ZP.Mul.MM
