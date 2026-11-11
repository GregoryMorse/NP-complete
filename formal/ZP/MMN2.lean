module

public import ZP.MMN
public import ZP.MMQ3

@[expose] public section

/-! After the Q pass, more rows: N1..N5 and the RB shift back into `P`, ending in `RS1` (rewind). -/

namespace ZP.Mul.MM

open ZP

theorem n1Loop (X : List Nat) (hX : Bits X) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.N1 (L ++ X) R) (hd QMM.N1 L (X ++ R)) :=
  fLoop QMM.N1 (fun c => c = 2 ∨ c = 3)
    (fun c hc => by rcases hc with rfl | rfl <;> simp [ALL])
    (fun L R c hL hR hc => by
      rcases hc with rfl | rfl
      · exact n1Step2 L R hL hR
      · exact n1Step3 L R hL hR)
    X (fun a ha => by rcases mem_bits (hX a ha) with rfl | rfl <;> simp) L R hL hR

theorem n3Loop (q : Nat) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hd QMM.N3 (L ++ List.replicate q 1) R) (hd QMM.N3 L (List.replicate q 1 ++ R)) :=
  fLoop QMM.N3 (fun c => c = 1)
    (fun c hc => by subst hc; simp [ALL])
    (fun L R c hL hR hc => by subst hc; exact n3M L R hL hR)
    _ (fun a ha => List.eq_of_mem_replicate ha) L R hL hR

theorem n5Loop (q : Nat) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zmmLogic.Reach (hdR QMM.N5 L (List.replicate q 1 ++ R)) (hdR QMM.N5 (L ++ List.replicate q 1) R) :=
  kLoop QMM.N5 (fun c => c = 1)
    (fun c hc => by subst hc; simp [ALL])
    (fun L R c hL hR hc => by subst hc; exact n5M L R hL hR)
    _ (fun a ha => List.eq_of_mem_replicate ha) L R hL hR

/-- The RB loop that ends at `Mr` (no blank after the bits). -/
theorem rbLoop2 (L : List Nat) (hL : Sym4 L) :
    ∀ (X : List Nat), Bits X → ∀ (R : List Nat), Sym4 R →
      zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (X ++ 1 :: R)) (hdR QMM.RS1 (L ++ X ++ [0, 1]) R) := by
  intro X
  induction X generalizing L with
  | nil =>
    intro _ R hR
    simpa using rbEnd2 L R hL hR
  | cons x X ih =>
    intro hX R hR
    have hx : x = 2 ∨ x = 3 := mem_bits (hX x (by simp))
    have hX' : Bits X := fun a ha => hX a (by simp [ha])
    have hL' : Sym4 (L ++ [x]) :=
      Sym4.app hL (Sym4.cons (by rcases hx with rfl | rfl <;> simp [ALL]) Sym4.nil)
    have hs : zmmLogic.Reach (hd QMM.RB1 (L ++ [0]) (x :: (X ++ 1 :: R)))
        (hd QMM.RB1 (L ++ [x] ++ [0]) (X ++ 1 :: R)) := by
      rw [hd_snoc QMM.RB1 (L ++ [x]) (X ++ 1 :: R) 0]
      have hR' : Sym4 (X ++ 1 :: R) := Sym4.app hX'.sym4 (Sym4.cons (by simp [ALL]) hR)
      rcases hx with rfl | rfl
      · exact rbStep0 L _ hL hR'
      · exact rbStep1 L _ hL hR'
    refine hs.trans ?_
    have := ih (L ++ [x]) hL' hX' R hR
    simpa using this

theorem nMore (Au Bd' R1 : List Nat) (q x x1 : Nat) (hAu : Sym4 Au) (hx : x ∈ bits) (hx1 : x1 ∈ bits)
    (hBd : Bits Bd') (hR : Sym4 R1) :
    zmmLogic.Reach (hd QMM.Q2 (Au ++ x :: List.replicate q 1 ++ [1, 0] ++ x1 :: Bd' ++ [1]) R1)
      (hdR QMM.RS1 (Au ++ x :: List.replicate q 1 ++ 1 :: x1 :: Bd' ++ [0, 1]) R1) := by
  have hBd4 := hBd.sym4
  have hBd1 : Bits (x1 :: Bd') := Bits.cons hx1 hBd
  have hx4 : x ∈ ALL := by rcases mem_bits hx with rfl | rfl <;> simp [ALL]
  have hx14 : x1 ∈ ALL := by rcases mem_bits hx1 with rfl | rfl <;> simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hrep := sym4_rep q 1 h1
  have s0 := q2M (Au ++ x :: List.replicate q 1 ++ [1, 0] ++ x1 :: Bd') R1
    (by simp [sym4_app_iff, sym4_cons_iff, *]) hR
  have s1 := n1Loop (x1 :: Bd') hBd1 (Au ++ x :: List.replicate q 1 ++ [1, 0]) (1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s2 := n1End (Au ++ x :: List.replicate q 1 ++ [1]) (x1 :: Bd' ++ 1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s3 := n2M (Au ++ x :: List.replicate q 1) (0 :: (x1 :: Bd' ++ 1 :: R1))
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s4 := n3Loop q (Au ++ [x]) (1 :: 0 :: (x1 :: Bd' ++ 1 :: R1))
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s5 : zmmLogic.Reach (hd QMM.N3 (Au ++ [x]) (List.replicate q 1 ++ 1 :: 0 :: (x1 :: Bd' ++ 1 :: R1)))
      (hdR QMM.N5 (Au ++ [x]) (List.replicate q 1 ++ 1 :: 0 :: (x1 :: Bd' ++ 1 :: R1))) := by
    have hA' : Sym4 Au := hAu
    have hR' : Sym4 (List.replicate q 1 ++ 1 :: 0 :: (x1 :: Bd' ++ 1 :: R1)) := by
      simp [sym4_app_iff, sym4_cons_iff, *]
    have e : Au ++ [x] = Au ++ [x] := rfl
    rcases mem_bits hx with rfl | rfl
    · exact n3Bit2 Au _ hA' hR'
    · exact n3Bit3 Au _ hA' hR'
  have s6 := n5Loop (q + 1) (Au ++ [x]) (0 :: (x1 :: Bd' ++ 1 :: R1))
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s7 := n5End (Au ++ x :: List.replicate q 1 ++ [1]) (x1 :: Bd' ++ 1 :: R1)
    (by simp [sym4_app_iff, sym4_cons_iff, *]) (by simp [sym4_app_iff, sym4_cons_iff, *])
  have s8 : zmmLogic.Reach (hdR QMM.RB2 (Au ++ x :: List.replicate q 1 ++ [1] ++ [0]) (x1 :: (Bd' ++ 1 :: R1)))
      (hdR QMM.RB1 (Au ++ x :: List.replicate q 1 ++ [1] ++ [x1]) (0 :: (Bd' ++ 1 :: R1))) := by
    have hL : Sym4 (Au ++ x :: List.replicate q 1 ++ [1]) := by simp [sym4_app_iff, sym4_cons_iff, *]
    have hR' : Sym4 (Bd' ++ 1 :: R1) := by simp [sym4_app_iff, sym4_cons_iff, *]
    rcases mem_bits hx1 with rfl | rfl
    · exact rb2Step0 _ _ hL hR'
    · exact rb2Step1 _ _ hL hR'
  have s9 := rbLoop2 (Au ++ x :: List.replicate q 1 ++ [1] ++ [x1])
    (by simp [sym4_app_iff, sym4_cons_iff, *]) Bd' hBd R1 hR
  rw [hd_snoc] at s7 s9
  simp only [List.replicate_succ'] at s6
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ⊢
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans s9))))))))

end ZP.Mul.MM
