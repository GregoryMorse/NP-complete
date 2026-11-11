module

public import ZP.MMRowNext

@[expose] public section

/-! One full row of `A` (`m` rounds, `|As| = |Rws| = m`), followed by the row check: `rowBad` (accumulator has a `3`: outcome 0),
`rowUsed` (accumulator all `2`, `A` used up: outcome 1), `rowMore` (accumulator all `2`, more `A`: next row). -/

namespace ZP.Mul.MM

open ZP

theorem noB_app {Au0 : List Nat} (hAu : Bits Au0) (q : Nat) : NoB (Au0 ++ List.replicate q 1) := fun a ha => by
  simp only [NB, List.mem_cons, List.not_mem_nil, or_false]
  rcases List.mem_append.mp ha with h | h
  · rcases mem_bits (hAu a h) with rfl | rfl <;> simp
  · rw [List.eq_of_mem_replicate h]; simp

theorem rowBad (As : List Nat) (Rws : List (List Nat)) (C Au0 Z Y outr Cb J sv Y2 : List Nat) (q : Nat)
    (hl : As.length = Rws.length) (hAs : ∀ s ∈ As, s = 2 ∨ s = 3) (hCne : C ≠ []) (hC : Bits C)
    (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = C.length) (hAu : Bits Au0) (hZ : ∀ a ∈ Z, a = 2) (hY : Bits Y)
    (hacc : (accFold As Rws C).reverse = Z ++ 3 :: Y) (houtr : Bits outr) (hCb : ∀ a ∈ Cb, a ∈ B0)
    (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (Au0 ++ As.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
        (0 :: C.reverse ++ 1 :: (outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
      (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have hR0 : Sym4 (outr ++ Cb ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) := by
    have := houtr.sym4
    have := hJ.sym4
    have := hsv.sym4
    have := sym4_B0 hCb
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
    simp [sym4_app_iff, sym4_cons_iff, *]
  have s0 := rowsRound As Rws hl hAs C hCne hC hRws Au0 [] [] _ q hAu Bits.nil Bits.nil hR0
  rw [hacc] at s0
  have hst := bits_stor Rws (fun r hr => (hRws r hr).1)
  have s1 := rowFinBad (Au0 ++ List.replicate (q + As.length) 1) (stor Rws) Z Y outr Cb J sv Y2
    (noB_app hAu _) hst hZ hY houtr hCb hJ hsv hY2
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 ⊢
  exact s0.trans s1

theorem rowUsed (As : List Nat) (Rws : List (List Nat)) (C Os Cb0 J sv Y2 : List Nat) (q m : Nat)
    (hl : As.length = Rws.length) (hAs : ∀ s ∈ As, s = 2 ∨ s = 3) (hCne : C ≠ []) (hC : Bits C)
    (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = C.length) (hfin : accFold As Rws C = List.replicate m 2)
    (hOs : Bits Os) (hCb0 : ∀ a ∈ Cb0, a = 0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (As.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
        (0 :: C.reverse ++ 1 :: (Os ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
      (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2)) := by
  have hR0 : Sym4 (Os ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) := by
    have := hOs.sym4
    have := hJ.sym4
    have := hsv.sym4
    have hc : Sym4 Cb0 := fun a ha => by rw [hCb0 a ha]; simp [ALL]
    have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
    have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
    simp [sym4_app_iff, sym4_cons_iff, *]
  have s0 := rowsRound As Rws hl hAs C hCne hC hRws [] [] [] _ q Bits.nil Bits.nil Bits.nil hR0
  rw [hfin, List.reverse_replicate] at s0
  have hst := bits_stor Rws (fun r hr => (hRws r hr).1)
  have s1 := rowDoneUsed (q + As.length) m (stor Rws) Os Cb0 J sv Y2 hst hOs hCb0 hJ hsv hY2
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 ⊢
  exact s0.trans s1

theorem rowMore (As : List Nat) (Rws : List (List Nat)) (C Au Os Rest Bd' : List Nat) (q m x x1 e : Nat)
    (hl : As.length = Rws.length) (hAs : ∀ s ∈ As, s = 2 ∨ s = 3) (hCne : C ≠ []) (hC : Bits C)
    (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = C.length) (hfin : accFold As Rws C = List.replicate m 2)
    (hAu : Bits Au) (hx : x ∈ bits) (hx1 : x1 ∈ bits) (hB : stor Rws = x1 :: Bd') (hBd : Bits Bd')
    (hOs : Bits Os) (he : e = 0 ∨ e = 1) (hRest : Sym4 Rest) :
    zmmLogic.Reach
      (hdR QMM.RS1 (Au ++ [x] ++ As.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
        (0 :: C.reverse ++ 1 :: (Os ++ e :: Rest)))
      (hdR QMM.RS1 (Au ++ x :: List.replicate (q + As.length) 1 ++ 1 :: x1 :: Bd' ++ [0, 1])
        (0 :: ((Os.reverse ++ List.replicate m 2).take m).reverse ++ [] ++
          1 :: (Os.take (Os.length - m) ++ List.replicate (min m Os.length) 0 ++ e :: Rest))) := by
  have hOe : Sym4 (Os ++ e :: Rest) := by
    refine Sym4.app hOs.sym4 (Sym4.cons ?_ hRest)
    rcases he with rfl | rfl <;> simp [ALL]
  have hAu' : Bits (Au ++ [x]) := fun a ha => by
    rcases List.mem_append.mp ha with h | h
    · exact hAu a h
    · rw [List.mem_singleton.mp h]; exact hx
  have s0 := rowsRound As Rws hl hAs C hCne hC hRws (Au ++ [x]) [] [] _ q hAu' Bits.nil Bits.nil hOe
  rw [hfin, List.reverse_replicate] at s0
  have s1 := rowDoneMore Au Bd' Os Rest x x1 (q + As.length) m e hAu hx hx1 hBd hOs he hRest
  rw [hB] at s0
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 ⊢
  rw [hB]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
  exact s0.trans s1

end ZP.Mul.MM
