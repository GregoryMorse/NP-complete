module

public import ZP.MMRowEnd
public import ZP.MMFetch3

@[expose] public section

/-! Row end after the last B cell: `FA` meets the boundary, the check acc = 0 (D0, D1, D3).

`rowEndOK`: acc all `0` (symbol 2): to `Q2` at the top acc cell.
`rowEndBad`: acc `Z ++ 3 :: Y`: the first `1` is marked, the head returns to `J1` at the boundary. -/

namespace ZP.Mul.MM

open ZP

theorem d1Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hdR QMM.D1 L (X ++ R)) (hdR QMM.D1 (L ++ X) R) :=
  kLoop QMM.D1 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact d1Step2 L R hL hR
      · exact d1Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

theorem d3Loop (X : List Nat) (hX : ∀ a ∈ X, a = 2) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hdR QMM.D3 L (X ++ R)) (hdR QMM.D3 (L ++ X) R) :=
  kLoop QMM.D3 (fun c => c = 2)
    (fun c hc => by subst hc; simp [ALL])
    (fun L R c hL hR hc => by subst hc; exact d3Zero L R hL hR)
    X hX L R hL hR

theorem z1Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.Z1 (L ++ X) R) (hd QMM.Z1 L (X ++ R)) :=
  fLoop QMM.Z1 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact z1Step2 L R hL hR
      · exact z1Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

theorem rowEndOK (L Bd X R0 : List Nat) (hL : Sym4 L) (hBd : Bits Bd) (hX : ∀ a ∈ X, a = 2)
    (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.FA (L ++ [1]) (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0))
      (hd QMM.Q2 (L ++ 1 :: 0 :: Bd ++ [1] ++ X) (0 :: 1 :: R0)) := by
  have hBd4 := hBd.sym4
  have hX4 : Sym4 X := fun a ha => by rw [hX a ha]; simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have s0 := faM L (0 :: Bd ++ 1 :: X ++ 0 :: 1 :: R0) hL
    (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s1 := d0P (L ++ [1]) (Bd ++ 1 :: X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s2 := d1Loop Bd hBd (L ++ [1] ++ [0]) (1 :: X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s3 := d1End (L ++ [1] ++ [0] ++ Bd) (X ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s4 := d3Loop X hX (L ++ [1] ++ [0] ++ Bd ++ [1]) (0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s5 := d3End (L ++ [1] ++ [0] ++ Bd ++ [1] ++ X) (1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  rw [hd_snoc] at s1 s3 s5
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 s4 s5 ⊢
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans s5))))

theorem rowEndBad (L Bd Z Y R0 : List Nat) (hL : Sym4 L) (hBd : Bits Bd) (hZ : ∀ a ∈ Z, a = 2)
    (hY : Bits Y) (hR : Sym4 R0) :
    zmmLogic.Reach (hd QMM.FA (L ++ [1]) (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0))
      (hd QMM.J1 (L ++ [1]) (0 :: Bd ++ 1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)) := by
  have hBd4 := hBd.sym4
  have hY4 := hY.sym4
  have hZ4 : Sym4 Z := fun a ha => by rw [hZ a ha]; simp [ALL]
  have hZb : Bits Z := fun a ha => by rw [hZ a ha]; simp [bits]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have h3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have s0 := faM L (0 :: Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0) hL
    (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s1 := d0P (L ++ [1]) (Bd ++ 1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s2 := d1Loop Bd hBd (L ++ [1] ++ [0]) (1 :: (Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s3 := d1End (L ++ [1] ++ [0] ++ Bd) ((Z ++ 3 :: Y) ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s4 := d3Loop Z hZ (L ++ [1] ++ [0] ++ Bd ++ [1]) (3 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s5 := d3One (L ++ [1] ++ [0] ++ Bd ++ [1] ++ Z) (Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s6 := z1Loop Z hZb (L ++ [1] ++ [0] ++ Bd ++ [1]) (2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s7 := z1End (L ++ [1] ++ [0] ++ Bd) (Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s8 := g2Loop Bd hBd (L ++ [1] ++ [0]) (1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s9 := g2End (L ++ [1]) (Bd ++ 1 :: Z ++ 2 :: Y ++ 0 :: 1 :: R0)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  rw [hd_snoc] at s1 s3 s5
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ⊢
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans s9))))))))

end ZP.Mul.MM
