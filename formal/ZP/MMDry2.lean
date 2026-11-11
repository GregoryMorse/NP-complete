module

public import ZP.MMDry

@[expose] public section

/-! End of the dry phase: the ruler is all `0` (`dryOK`), and after the Q pass the boundary `M` is inserted
and `B` is shifted back into `P` (`dryN`). -/

namespace ZP.Mul.MM

open ZP

theorem dryOK (Wr0 Bd X R0 : List Nat) (b : Nat) (hW : Bits Wr0) (hb : b ∈ bits) (hBd : Bits Bd)
    (hX : ∀ a ∈ X, a = 2) (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.FA (Wr0 ++ [b]) (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))
      (hd QMM.Q2 ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1] ++ X) (0 :: 1 :: R0)) := by
  have hW4 := hW.sym4
  have hBd4 := hBd.sym4
  have hX4 : Sym4 X := fun a ha => by rw [hX a ha]; simp [ALL]
  have hWb : Bits (Wr0 ++ [b]) := fun a ha => by
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hW a ha
    · exact hb
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hb4 : b ∈ ALL := by rcases mem_bits hb with rfl | rfl <;> simp [ALL]
  have s0 : zmmLogic.Reach (hd QMM.FA (Wr0 ++ [b]) (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))
      (hd Q.FB Wr0 (b :: (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))) := by
    rcases mem_bits hb with rfl | rfl
    · exact faBit2 _ _ hW4 (by simp [sym4_app_iff, sym4_cons_iff, *])
    · exact faBit3 _ _ hW4 (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s1 := fbLoop Wr0 hW [] (b :: (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))
    (by simp) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have e0 : ∀ R : List Nat, hd Q.FB [] R = hd Q.FB ([] ++ [0]) R := fun R => rfl
  rw [e0] at s1
  have s2 := fbB [] (Wr0 ++ b :: (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))
    (by simp) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s3 := d0Loop (Wr0 ++ [b]) hWb [0] (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s4 := d0P ([0] ++ (Wr0 ++ [b])) (Bd ++ 1 :: X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s5 := d1Loop Bd hBd ([0] ++ (Wr0 ++ [b]) ++ [0]) (1 :: X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s6 := d1End ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd) (X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s7 := d3Loop X hX ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1]) (0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s8 := d3End ([0] ++ (Wr0 ++ [b]) ++ [0] ++ Bd ++ [1] ++ X) (1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  rw [hd_snoc] at s4 s6 s8
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 s4 s5 s6 s7 s8 ⊢
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8)))))))

theorem n4Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.N4 (L ++ X) R) (hd QMM.N4 L (X ++ R)) :=
  fLoop QMM.N4 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact n4Step2 L R hL hR
      · exact n4Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

/-- The RB loop through `A` (the remaining `w`), ending with the boundary `M` written into the hole. -/
theorem rbLoopA (L : List Nat) (hL : Sym4 L) :
    ∀ (X : List Nat), Bits X → ∀ (R : List Nat), Sym4 R →
      zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (X ++ 0 :: R)) (hdR QMM.RB1 (L ++ X ++ [1]) (0 :: R)) := by
  intro X
  induction X generalizing L with
  | nil =>
    intro _ R hR
    simpa using rbBnd L R hL hR
  | cons x X ih =>
    intro hX R hR
    have hx : x = 2 ∨ x = 3 := mem_bits (hX x (by simp))
    have hX' : Bits X := fun a ha => hX a (by simp [ha])
    have hL' : Sym4 (L ++ [x]) :=
      Sym4.app hL (Sym4.cons (by rcases hx with rfl | rfl <;> simp [ALL]) Sym4.nil)
    have hs : zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (x :: (X ++ 0 :: R)))
        (hd QMM.RB1 (L ++ [x] ++ [0]) (X ++ 0 :: R)) := by
      rw [hd_snoc QMM.RB1 (L ++ [x]) (X ++ 0 :: R) 0]
      have hR' : Sym4 (X ++ 0 :: R) := Sym4.app hX'.sym4 (Sym4.cons (by simp [ALL]) hR)
      rcases hx with rfl | rfl
      · exact rbStep0 L _ hL hR'
      · exact rbStep1 L _ hL hR'
    refine hs.trans ?_
    have := ih (L ++ [x]) hL' hX' R hR
    simpa using this

theorem dryN (Wr Bd R1 : List Nat) (b x : Nat) (Wt : List Nat) (hWe : Wr ++ [b] = x :: Wt) (hWr : Bits Wr)
    (hbb : b ∈ bits) (hBd : Bits Bd) (hR : Sym4 R1) :
    zmmLogic.Reach (hd QMM.Q2 ([0] ++ (Wr ++ [b]) ++ [0] ++ Bd ++ [1]) R1)
      (hdR QMM.RS1 (Wr ++ [b] ++ 1 :: Bd ++ [0, 1]) R1) := by
  have hBd4 := hBd.sym4
  have hWr4 := hWr.sym4
  have hW : Bits (Wr ++ [b]) := fun a ha => by
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hWr a ha
    · exact hbb
  have hxm : x ∈ x :: Wt := by simp
  have hx : x = 2 ∨ x = 3 := mem_bits (hW x (by rw [hWe]; exact hxm))
  have hWt : Bits Wt := fun a ha => hW a (by rw [hWe]; simp [ha])
  have hWt4 := hWt.sym4
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hx4 : x ∈ ALL := by rcases hx with rfl | rfl <;> simp [ALL]
  have hb4 : b ∈ ALL := by rcases mem_bits hbb with rfl | rfl <;> simp [ALL]
  have t0 := q2M ([0] ++ (Wr ++ [b]) ++ [0] ++ Bd) R1
    (by simp [sym4_app_iff, sym4_cons_iff, *]) hR
  have t1 := n1Loop Bd hBd ([0] ++ (Wr ++ [b]) ++ [0]) (1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t2 := n1End ([0] ++ (Wr ++ [b])) (Bd ++ 1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t3 : zmmLogic.Reach (hd QMM.N2 ([0] ++ Wr ++ [b]) (0 :: (Bd ++ 1 :: R1)))
      (hd QMM.N4 ([0] ++ Wr) (b :: 0 :: (Bd ++ 1 :: R1))) := by
    rcases mem_bits hbb with rfl | rfl
    · exact n2Bit2 _ _ (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
    · exact n2Bit3 _ _ (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t4 := n4Loop Wr hWr [0] (b :: 0 :: (Bd ++ 1 :: R1))
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have t5 := n4End [] (Wr ++ b :: 0 :: (Bd ++ 1 :: R1))
    (by simp) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have e1 : Wr ++ b :: 0 :: (Bd ++ 1 :: R1) = x :: (Wt ++ 0 :: (Bd ++ 1 :: R1)) := by
    have := congrArg (· ++ (0 :: (Bd ++ 1 :: R1))) hWe
    simpa using this
  rw [e1] at t4 t5
  have hR' : Sym4 (Wt ++ 0 :: (Bd ++ 1 :: R1)) := by simp [sym4_app_iff, sym4_cons_iff, *]
  have t6 : zmmLogic.Reach (hdR QMM.RB2 [0] (x :: (Wt ++ 0 :: (Bd ++ 1 :: R1))))
      (hdR QMM.RB1 [x] (0 :: (Wt ++ 0 :: (Bd ++ 1 :: R1)))) := by
    rcases hx with rfl | rfl
    · simpa using rb2Step0 [] _ (by simp) hR'
    · simpa using rb2Step1 [] _ (by simp) hR'
  rw [← hd_snoc] at t6
  have t7 := rbLoopA [x] (by simp [sym4_app_iff, sym4_cons_iff, *]) Wt hWt (Bd ++ 1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *])
  have hb1 : Bits Bd := hBd
  have t8 := rbLoop2 ([x] ++ Wt ++ [1]) (by simp [sym4_app_iff, sym4_cons_iff, *]) Bd hBd R1 hR
  rw [hd_snoc] at t8
  have e3 : Wr ++ [b] ++ 1 :: Bd ++ [0, 1] = x :: Wt ++ 1 :: Bd ++ [0, 1] := by rw [hWe]
  rw [e3]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at t0 t1 t2 t3 t4 t5 t6 t7 t8 ⊢
  exact t0.trans (t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans t8)))))))

end ZP.Mul.MM
