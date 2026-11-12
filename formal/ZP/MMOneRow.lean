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

theorem accFold_inv : ∀ (As : List Nat) (Rws : List (List Nat)) (C : List Nat), Bits C →
    (∀ r ∈ Rws, Bits r ∧ r.length = C.length) →
    Bits (accFold As Rws C) ∧ (accFold As Rws C).length = C.length
  | [], Rws, C, hC, _ => by simp [accFold]; exact hC
  | s :: As, [], C, hC, _ => by simp [accFold]; exact hC
  | s :: As, V :: Rws, C, hC, hR => by
    obtain ⟨hVb, hVl⟩ := hR V (by simp)
    have h1 := bits_zipWith (aOf s) V C hVb hC
    have h2 := len_zipWith (aOf s) V C hVl
    have := accFold_inv As Rws (List.zipWith (jc (aOf s)) V C) h1
      (fun r hr => ⟨(hR r (by simp [hr])).1, by rw [h2]; exact (hR r (by simp [hr])).2⟩)
    simp only [accFold]
    exact ⟨this.1, by rw [this.2, h2]⟩

theorem accFoldE_inv : ∀ (Rws : List (List Nat)) (C : List Nat), Bits C →
    (∀ r ∈ Rws, Bits r ∧ r.length = C.length) →
    Bits (accFoldE Rws C) ∧ (accFoldE Rws C).length = C.length
  | [], C, hC, _ => by simp [accFoldE]; exact hC
  | V :: Rws, C, hC, hR => by
    obtain ⟨hVb, hVl⟩ := hR V (by simp)
    have h1 := bits_zipWith 1 V C hVb hC
    have h2 := len_zipWith 1 V C hVl
    have := accFoldE_inv Rws (List.zipWith (jc 1) V C) h1
      (fun r hr => ⟨(hR r (by simp [hr])).1, by rw [h2]; exact (hR r (by simp [hr])).2⟩)
    simp only [accFoldE]
    exact ⟨this.1, by rw [this.2, h2]⟩

theorem stor_append (R1 R2 : List (List Nat)) : stor (R1 ++ R2) = stor R2 ++ stor R1 := by
  induction R1 with
  | nil => simp [stor]
  | cons V R ih => simp [stor, ih, List.append_assoc]

/-- The last row, `|As| < m` bits of `A`: the remaining rounds are padded (`a = 0`). -/
theorem rowLastUsed (As : List Nat) (Rws1 Rws2 : List (List Nat)) (C Os Cb0 J sv Y2 : List Nat) (q m : Nat)
    (hl : As.length = Rws1.length) (hAs : ∀ s ∈ As, s = 2 ∨ s = 3) (hCne : C ≠ []) (hC : Bits C)
    (hRws : ∀ r ∈ Rws1 ++ Rws2, Bits r ∧ r.length = C.length)
    (hfin : accFoldE Rws2 (accFold As Rws1 C) = List.replicate m 2)
    (hOs : Bits Os) (hCb0 : ∀ a ∈ Cb0, a = 0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (As.reverse ++ List.replicate q 1 ++ 1 :: stor (Rws1 ++ Rws2) ++ 0 :: [] ++ [1])
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
  have hR1 : ∀ r ∈ Rws1, Bits r ∧ r.length = C.length := fun r hr => hRws r (by simp [hr])
  have hR2 : ∀ r ∈ Rws2, Bits r := fun r hr => (hRws r (by simp [hr])).1
  have hst2 := bits_stor Rws2 hR2
  have hst1 := bits_stor Rws1 (fun r hr => (hR1 r hr).1)
  have hI := accFold_inv As Rws1 C hC hR1
  have hCne' : accFold As Rws1 C ≠ [] := fun h => hCne (List.length_eq_zero_iff.mp (by rw [← hI.2, h]; rfl))
  have s0 := rowsRound As Rws1 hl hAs C hCne hC hR1 [] (stor Rws2) [] _ q Bits.nil hst2 Bits.nil hR0
  have s1 := rowsRoundE Rws2 (accFold As Rws1 C) hCne' hI.1
    (fun r hr => ⟨hR2 r hr, by rw [hI.2]; exact (hRws r (by simp [hr])).2⟩) [] (stor Rws1) _ (q + As.length)
    Bits.nil hst1 hR0
  rw [hfin, List.reverse_replicate] at s1
  have hst := bits_stor (Rws1 ++ Rws2) (fun r hr => (hRws r hr).1)
  have s2 := rowDoneUsed (q + As.length) m (stor (Rws1 ++ Rws2)) Os Cb0 J sv Y2 hst hOs hCb0 hJ hsv hY2
  rw [stor_append] at s2 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 ⊢
  exact s0.trans (s1.trans s2)

theorem rowLastBad (As : List Nat) (Rws1 Rws2 : List (List Nat)) (C Z Y outr Cb J sv Y2 : List Nat) (q : Nat)
    (hl : As.length = Rws1.length) (hAs : ∀ s ∈ As, s = 2 ∨ s = 3) (hCne : C ≠ []) (hC : Bits C)
    (hRws : ∀ r ∈ Rws1 ++ Rws2, Bits r ∧ r.length = C.length) (hZ : ∀ a ∈ Z, a = 2) (hY : Bits Y)
    (hacc : (accFoldE Rws2 (accFold As Rws1 C)).reverse = Z ++ 3 :: Y) (houtr : Bits outr)
    (hCb : ∀ a ∈ Cb, a ∈ B0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (As.reverse ++ List.replicate q 1 ++ 1 :: stor (Rws1 ++ Rws2) ++ 0 :: [] ++ [1])
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
  have hR1 : ∀ r ∈ Rws1, Bits r ∧ r.length = C.length := fun r hr => hRws r (by simp [hr])
  have hR2 : ∀ r ∈ Rws2, Bits r := fun r hr => (hRws r (by simp [hr])).1
  have hst2 := bits_stor Rws2 hR2
  have hst1 := bits_stor Rws1 (fun r hr => (hR1 r hr).1)
  have hI := accFold_inv As Rws1 C hC hR1
  have hCne' : accFold As Rws1 C ≠ [] := fun h => hCne (List.length_eq_zero_iff.mp (by rw [← hI.2, h]; rfl))
  have s0 := rowsRound As Rws1 hl hAs C hCne hC hR1 [] (stor Rws2) [] _ q Bits.nil hst2 Bits.nil hR0
  have s1 := rowsRoundE Rws2 (accFold As Rws1 C) hCne' hI.1
    (fun r hr => ⟨hR2 r hr, by rw [hI.2]; exact (hRws r (by simp [hr])).2⟩) [] (stor Rws1) _ (q + As.length)
    Bits.nil hst1 hR0
  rw [hacc] at s1
  have hst := bits_stor (Rws1 ++ Rws2) (fun r hr => (hRws r hr).1)
  have s2 := rowFinBad (List.replicate (q + As.length) 1) (stor (Rws1 ++ Rws2)) Z Y outr Cb J sv Y2
    (by simpa using noB_app Bits.nil (q + As.length)) hst hZ hY houtr hCb hJ hsv hY2
  rw [stor_append] at s2 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at s0 s1 s2 ⊢
  exact s0.trans (s1.trans s2)

end ZP.Mul.MM
