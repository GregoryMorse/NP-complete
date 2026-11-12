module

public import ZP.MMN2
public import ZP.MMRowEnd2

@[expose] public section

/-! The dry row (no B/A boundary yet): `FA` meets a bit of `w`, runs to the end of `w`, `D0` sweeps back to `P`,
D3 checks / marks the ruler.  `dryBad`: a ruler `1` is marked and the head returns to `J1` (next B row).
`dryOK`: the ruler is all `0`: on to `Q2`.  Ascending layout: `Wr0 ++ [b]` (rest of `w`), `P = 0`, `Bd`, `Mr = 1`,
the ruler `X`, the hole `0`, `Ms = 1`, ... -/

namespace ZP.Mul.MM

open ZP

theorem d0Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hdR QMM.D0 L (X ++ R)) (hdR QMM.D0 (L ++ X) R) :=
  kLoop QMM.D0 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact d0Step2 L R hL hR
      · exact d0Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

theorem dryBad (Wr0 Bd Z Y R0 : List Nat) (b : Nat) (hW : Bits Wr0) (hb : b ∈ bits) (hBd : Bits Bd)
    (hZ : ∀ a ∈ Z, a = 2) (hY : Bits Y) (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.FA (Wr0 ++ [b]) (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))
      (hd QMM.J1 (Wr0 ++ [b]) (0 :: Bd ++ 1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)) := by
  have hW4 := hW.sym4
  have hBd4 := hBd.sym4
  have hY4 := hY.sym4
  have hZ4 : Sym4 Z := fun a ha => by rw [hZ a ha]; simp [ALL]
  have hZb : Bits Z := fun a ha => by rw [hZ a ha]; simp [bits]
  have hWb : Bits (Wr0 ++ [b]) := fun a ha => by
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hW a ha
    · exact hb
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have h3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have hb4 : b ∈ ALL := by rcases mem_bits hb with rfl | rfl <;> simp [ALL]
  have s0 : zmmLogic.Reach (hd QMM.FA (Wr0 ++ [b]) (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))
      (hd Q.FB Wr0 (b :: (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))) := by
    rcases mem_bits hb with rfl | rfl
    · exact faBit2 _ _ hW4 (by simp [sym4_app_iff, sym4_cons_iff, *])
    · exact faBit3 _ _ hW4 (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s1 := fbLoop Wr0 hW [] (b :: (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))
    (by simp) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have e0 : ∀ R : List Nat, hd Q.FB [] R = hd Q.FB ([] ++ [0]) R := fun R => rfl
  rw [e0] at s1
  have s2 := fbB [] (Wr0 ++ b :: (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))
    (by simp) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s3 := d0Loop (Wr0 ++ [b]) hWb [0] (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s4 := d0P ([0] ++ (Wr0 ++ [b])) (Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s5 := d1Loop Bd hBd ([0] ++ (Wr0 ++ [b]) ++ [0]) (1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s6 := d1End ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd) ((Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s7 := d3Loop Z hZ ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1]) (3 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s8 := d3One ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1] ++ Z) (Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s9 := z1Loop Z hZb ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1]) (2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s10 := z1End ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd) (Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s11 := g2Loop Bd hBd ([0] ++ (Wr0 ++ [b]) ++ [0]) (1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s12 := g2End ([0] ++ (Wr0 ++ [b])) (Bd ++ 1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  rw [hd_snoc] at s4 s6 s8
  have s13 := hd_cons0 QMM.J1 Wr0 (0 :: Bd ++ 1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0) b
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 ⊢
  rw [s13] at s12
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans (s9.trans (s10.trans (s11.trans s12)))))))))))

end ZP.Mul.MM
