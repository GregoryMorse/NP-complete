module

public import ZP.MMOneRow

@[expose] public section

/-! The rows induction: all rows of `A`, outcome `DP31` if every row of `A B` matches the loaded `out` row, else `DP30`. -/

namespace ZP.Mul.MM

open ZP

/-- The accumulator after one row of `A` with `As` (a possibly short last row: padded rounds with `a = 0`). -/
def accRow (Rws : List (List Nat)) (As C : List Nat) : List Nat :=
  accFoldE (Rws.drop As.length) (accFold As (Rws.take As.length) C)

/-- All rows match (the accumulator returns to all `2`). `Orest` is the `out` beyond the loaded row `C`. -/
def rowsOK (m : Nat) (Rws : List (List Nat)) : Nat → List Nat → List Nat → List Nat → Prop
  | 0, _, _, _ => True
  | n + 1, Atot, C, Orest =>
    Atot = [] ∨ (accRow Rws (Atot.take m) C = List.replicate m 2 ∧
      rowsOK m Rws n (Atot.drop m) ((Orest ++ List.replicate m 2).take m) (Orest.drop m))

theorem split3 : ∀ (L : List Nat), Bits L → L ≠ List.replicate L.length 2 →
    ∃ Z Y, L = Z ++ 3 :: Y ∧ (∀ a ∈ Z, a = 2) ∧ Bits Y
  | [], _, h => absurd (by simp) h
  | a :: L, hb, h => by
    rcases mem_bits (hb a (by simp)) with rfl | rfl
    · have hL : Bits L := fun c hc => hb c (by simp [hc])
      have : L ≠ List.replicate L.length 2 := fun e => h (by rw [List.length_cons, List.replicate_succ, ← e])
      obtain ⟨Z, Y, e, hZ, hY⟩ := split3 L hL this
      exact ⟨2 :: Z, Y, by rw [e]; rfl, by intro c hc; simp at hc; rcases hc with rfl | hc; rfl; exact hZ c hc, hY⟩
    · exact ⟨[], L, rfl, by simp, fun c hc => hb c (by simp [hc])⟩

theorem exists_er (Cb0 J sv Y2 : List Nat) (hCb0 : ∀ a ∈ Cb0, a = 0) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    ∃ e Rest, (e = 0 ∨ e = 1) ∧ Sym4 Rest ∧ Cb0 ++ (1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2) = e :: Rest := by
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have h1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hJ4 := hJ.sym4
  have hs4 := hsv.sym4
  cases Cb0 with
  | nil => exact ⟨1, J ++ 1 :: sv ++ 0 :: 1 :: Y2, Or.inr rfl, by simp [sym4_app_iff, sym4_cons_iff, *], by simp⟩
  | cons c Cb0 =>
    have hc : c = 0 := hCb0 c (by simp)
    subst hc
    have : Sym4 Cb0 := fun a ha => by rw [hCb0 a (by simp [ha])]; simp [ALL]
    exact ⟨0, Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2, Or.inl rfl, by simp [sym4_app_iff, sym4_cons_iff, *], by simp⟩

theorem drop_rev (O : List Nat) (m : Nat) : (O.drop m).reverse = O.reverse.take (O.length - m) := by
  rw [List.take_reverse]
  congr 1
  by_cases h : m ≤ O.length
  · congr 1; omega
  · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

theorem lastRow (m : Nat) (Rws : List (List Nat)) (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = m) (hlen : Rws.length = m)
    (hm : m ≠ 0) (Atot C Orest Cb0 J sv Y2 : List Nat) (q : Nat) (hA : ∀ s ∈ Atot, s = 2 ∨ s = 3)
    (hle : Atot.length ≤ m) (hC : Bits C) (hClen : C.length = m) (hO : Bits Orest) (hCb0 : ∀ a ∈ Cb0, a = 0)
    (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    (accRow Rws Atot C = List.replicate m 2 →
      zmmLogic.Reach
        (hdR QMM.RS1 (Atot.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
          (0 :: C.reverse ++ 1 :: (Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
        (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) ∧
    (accRow Rws Atot C ≠ List.replicate m 2 →
      zmmLogic.Reach
        (hdR QMM.RS1 (Atot.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
          (0 :: C.reverse ++ 1 :: (Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
        (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) := by
  have hCne : C ≠ [] := fun h => hm (by rw [h] at hClen; simpa using hClen.symm)
  have hAb : Bits Atot := fun t ht => by rcases hA t ht with rfl | rfl <;> simp [bits]
  have eS : stor Rws = stor (Rws.take Atot.length ++ Rws.drop Atot.length) := by rw [List.take_append_drop]
  have hl : Atot.length = (Rws.take Atot.length).length := by
    rw [List.length_take]; omega
  have hR : ∀ r ∈ Rws.take Atot.length ++ Rws.drop Atot.length, Bits r ∧ r.length = C.length := by
    rw [List.take_append_drop]; intro r hr; rw [hClen]; exact hRws r hr
  have hI := accFold_inv Atot (Rws.take Atot.length) C hC (fun r hr => hR r (List.mem_append.mpr (Or.inl hr)))
  have hI2 := accFoldE_inv (Rws.drop Atot.length) (accFold Atot (Rws.take Atot.length) C) hI.1 (fun r hr => by
    rw [hI.2]; exact hR r (List.mem_append.mpr (Or.inr hr)))
  have hacc : accRow Rws Atot C = accFoldE (Rws.drop Atot.length) (accFold Atot (Rws.take Atot.length) C) := rfl
  rw [eS]
  constructor
  · intro hf
    rw [hacc] at hf
    exact rowLastUsed Atot _ _ C Orest.reverse Cb0 J sv Y2 q m hl hA hCne hC hR hf (fun a ha => hO a (List.mem_reverse.mp ha))
      hCb0 hJ hsv hY2
  · intro hf
    have hb := hI2.1
    have hne : (accRow Rws Atot C).reverse ≠ List.replicate (accRow Rws Atot C).reverse.length 2 := by
      intro h
      apply hf
      have h' := congrArg List.reverse h
      rw [List.reverse_reverse, List.length_reverse, List.reverse_replicate] at h'
      rw [h']
      have : (accRow Rws Atot C).length = m := by rw [hacc, hI2.2, hI.2, hClen]
      rw [this]
    obtain ⟨Z, Y, e, hZ, hY⟩ := split3 _ (fun a ha => hb a (List.mem_reverse.mp ha)) hne
    exact rowLastBad Atot _ _ C Z Y Orest.reverse Cb0 J sv Y2 q hl hA hCne hC hR hZ hY e
      (fun a ha => hO a (List.mem_reverse.mp ha)) (fun a ha => by simp [B0, hCb0 a ha]) hJ hsv hY2

theorem rowsOK_nil (m : Nat) (Rws : List (List Nat)) (n : Nat) (C O : List Nat) : rowsOK m Rws n [] C O := by
  cases n <;> simp [rowsOK]

theorem rowsOK_last (m : Nat) (Rws : List (List Nat)) (n : Nat) (Atot C O : List Nat) (hne : Atot ≠ [])
    (hle : Atot.length ≤ m) : rowsOK m Rws (n + 1) Atot C O ↔ accRow Rws Atot C = List.replicate m 2 := by
  simp only [rowsOK]
  rw [List.take_of_length_le hle, List.drop_of_length_le hle]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact absurd h hne
    · exact h
  · intro h; exact Or.inr ⟨h, rowsOK_nil _ _ _ _ _⟩

theorem accRow_full (m : Nat) (Rws : List (List Nat)) (hlen : Rws.length = m) (As C : List Nat) (hAs : As.length = m) :
    accRow Rws As C = accFold As Rws C := by
  simp only [accRow, hAs]
  rw [← hlen, List.take_length, List.drop_length]
  rfl

theorem rowStep (m : Nat) (Rws : List (List Nat)) (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = m) (hlen : Rws.length = m)
    (hm : m ≠ 0) (hB : stor Rws ≠ []) (J sv Y2 : List Nat) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2)
    (Atot C Orest Cb0 : List Nat) (q : Nat) (hA : ∀ s ∈ Atot, s = 2 ∨ s = 3) (hgt : m < Atot.length)
    (hC : Bits C) (hClen : C.length = m) (hO : Bits Orest) (hCb0 : ∀ a ∈ Cb0, a = 0)
    (hok : accFold (Atot.take m) Rws C = List.replicate m 2) :
    zmmLogic.Reach
      (hdR QMM.RS1 (Atot.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
        (0 :: C.reverse ++ 1 :: (Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
      (hdR QMM.RS1 ((Atot.drop m).reverse ++ List.replicate (q + m) 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
        (0 :: ((Orest ++ List.replicate m 2).take m).reverse ++
          1 :: ((Orest.drop m).reverse ++ (List.replicate (min m Orest.length) 0 ++ Cb0) ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2))) := by
  have hAs : (Atot.take m).length = m := by rw [List.length_take]; omega
  have hCne : C ≠ [] := fun h => hm (by rw [h] at hClen; simpa using hClen.symm)
  have hAsA : ∀ s ∈ Atot.take m, s = 2 ∨ s = 3 := fun s hs => hA s (List.mem_of_mem_take hs)
  have hRl : ∀ r ∈ Rws, Bits r ∧ r.length = C.length := fun r hr => by rw [hClen]; exact hRws r hr
  have hlAs : (Atot.take m).length = Rws.length := by rw [hAs, hlen]
  have hRev : Atot.reverse = (Atot.drop m).reverse ++ (Atot.take m).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have hdropA : ∀ s ∈ Atot.drop m, s = 2 ∨ s = 3 := fun s hs => hA s (List.mem_of_mem_drop hs)
  have hdropne : Atot.drop m ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  obtain ⟨x, rest', hd⟩ : ∃ x rest', Atot.drop m = x :: rest' := by
    cases h : Atot.drop m with
    | nil => exact absurd h hdropne
    | cons x r => exact ⟨x, r, rfl⟩
  have hx : x ∈ bits := by
    rcases hdropA x (by rw [hd]; simp) with rfl | rfl <;> simp [bits]
  have hAu : Bits rest'.reverse := fun a ha => by
    rcases hdropA a (by rw [hd]; simp [List.mem_reverse.mp ha]) with rfl | rfl <;> simp [bits]
  obtain ⟨x1, Bd', hB'⟩ : ∃ x1 Bd', stor Rws = x1 :: Bd' := by
    cases h : stor Rws with
    | nil => exact absurd h hB
    | cons a r => exact ⟨a, r, rfl⟩
  have hst := bits_stor Rws (fun r hr => (hRws r hr).1)
  rw [hB'] at hst
  have hx1 : x1 ∈ bits := hst x1 (by simp)
  have hBd : Bits Bd' := fun a ha => hst a (by simp [ha])
  obtain ⟨e, Rest, he, hRest, hER⟩ := exists_er Cb0 J sv Y2 hCb0 hJ hsv hY2
  have s0 := rowMore (Atot.take m) Rws C rest'.reverse Orest.reverse Rest Bd' q m x x1 e hlAs hAsA hCne hC hRl hok
    hAu hx hx1 hB' hBd (fun a ha => hO a (List.mem_reverse.mp ha)) he hRest
  have eP1 : Atot.reverse = rest'.reverse ++ [x] ++ (Atot.take m).reverse := by rw [hRev, hd]; simp
  have eP2 : Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2 = Orest.reverse ++ e :: Rest := by
    rw [← hER]; simp
  have eQ1 : (Atot.drop m).reverse ++ List.replicate (q + m) 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1] =
      rest'.reverse ++ x :: List.replicate (q + (Atot.take m).length) 1 ++ 1 :: x1 :: Bd' ++ [0, 1] := by
    rw [hd, hB', hAs]; simp
  have eQ2 : (Orest.drop m).reverse ++ (List.replicate (min m Orest.length) 0 ++ Cb0) ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2
      = Orest.reverse.take (Orest.reverse.length - m) ++ List.replicate (min m Orest.reverse.length) 0 ++ e :: Rest := by
    rw [drop_rev, List.length_reverse, ← hER]; simp
  have eQ3 : ((Orest ++ List.replicate m 2).take m).reverse =
      ((Orest.reverse.reverse ++ List.replicate m 2).take m).reverse := by rw [List.reverse_reverse]
  rw [eP1, eP2, eQ1, eQ2, eQ3]
  simp only [List.append_nil] at s0
  exact s0

theorem rowsAll (m : Nat) (Rws : List (List Nat)) (hRws : ∀ r ∈ Rws, Bits r ∧ r.length = m) (hlen : Rws.length = m)
    (hm : m ≠ 0) (hB : stor Rws ≠ []) (J sv Y2 : List Nat) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    ∀ (n : Nat) (Atot C Orest Cb0 : List Nat) (q : Nat), (∀ s ∈ Atot, s = 2 ∨ s = 3) → Atot ≠ [] →
      Atot.length ≤ n * m → Bits C → C.length = m → Bits Orest → (∀ a ∈ Cb0, a = 0) →
      (rowsOK m Rws n Atot C Orest →
        zmmLogic.Reach
          (hdR QMM.RS1 (Atot.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
            (0 :: C.reverse ++ 1 :: (Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
          (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) ∧
      (¬ rowsOK m Rws n Atot C Orest →
        zmmLogic.Reach
          (hdR QMM.RS1 (Atot.reverse ++ List.replicate q 1 ++ 1 :: stor Rws ++ 0 :: [] ++ [1])
            (0 :: C.reverse ++ 1 :: (Orest.reverse ++ Cb0 ++ 1 :: J ++ 1 :: sv ++ 0 :: 1 :: Y2)))
          (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) := by
  intro n
  induction n with
  | zero =>
    intro Atot _ _ _ _ _ hne hle
    exact absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | succ n ih =>
    intro Atot C Orest Cb0 q hA hne hle hC hClen hO hCb0
    by_cases hlm : Atot.length ≤ m
    · have hl := lastRow m Rws hRws hlen hm Atot C Orest Cb0 J sv Y2 q hA hlm hC hClen hO hCb0 hJ hsv hY2
      rw [rowsOK_last m Rws n Atot C Orest hne hlm]
      exact hl
    · have hgt : m < Atot.length := by omega
      have hAs : (Atot.take m).length = m := by rw [List.length_take]; omega
      have hCne : C ≠ [] := fun h => hm (by rw [h] at hClen; simpa using hClen.symm)
      have hAsA : ∀ s ∈ Atot.take m, s = 2 ∨ s = 3 := fun s hs => hA s (List.mem_of_mem_take hs)
      have hRl : ∀ r ∈ Rws, Bits r ∧ r.length = C.length := fun r hr => by rw [hClen]; exact hRws r hr
      have hlAs : (Atot.take m).length = Rws.length := by rw [hAs, hlen]
      have hfull := accRow_full m Rws hlen (Atot.take m) C hAs
      have hI := accFold_inv (Atot.take m) Rws C hC hRl
      have hRev : Atot.reverse = (Atot.drop m).reverse ++ (Atot.take m).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      have hdropA : ∀ s ∈ Atot.drop m, s = 2 ∨ s = 3 := fun s hs => hA s (List.mem_of_mem_drop hs)
      have hdropne : Atot.drop m ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      have hle' : (Atot.drop m).length ≤ n * m := by
        rw [List.length_drop]
        have : (n + 1) * m = n * m + m := Nat.succ_mul n m
        generalize n * m = k at *
        omega
      have hC' : Bits ((Orest ++ List.replicate m 2).take m) := fun a ha => by
        have := List.mem_of_mem_take ha
        rcases List.mem_append.mp this with h | h
        · exact hO a h
        · rw [List.eq_of_mem_replicate h]; simp [bits]
      have hlC' : ((Orest ++ List.replicate m 2).take m).length = m := by
        rw [List.length_take, List.length_append, List.length_replicate]; omega
      have hO' : Bits (Orest.drop m) := fun a ha => hO a (List.mem_of_mem_drop ha)
      have hCb' : ∀ a ∈ List.replicate (min m Orest.length) 0 ++ Cb0, a = 0 := fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · exact List.eq_of_mem_replicate h
        · exact hCb0 a h
      have hih := ih (Atot.drop m) ((Orest ++ List.replicate m 2).take m) (Orest.drop m)
        (List.replicate (min m Orest.length) 0 ++ Cb0) (q + m) hdropA hdropne hle' hC' hlC' hO' hCb'
      rw [rowsOK]
      simp only [hne, false_or]
      rw [hfull]
      constructor
      · rintro ⟨hok, hrest⟩
        exact (rowStep m Rws hRws hlen hm hB J sv Y2 hJ hsv hY2 Atot C Orest Cb0 q hA hgt hC hClen hO hCb0 hok).trans
          (hih.1 hrest)
      · intro hn
        by_cases hok : accFold (Atot.take m) Rws C = List.replicate m 2
        · exact (rowStep m Rws hRws hlen hm hB J sv Y2 hJ hsv hY2 Atot C Orest Cb0 q hA hgt hC hClen hO hCb0 hok).trans
            (hih.2 (fun hr => hn ⟨hok, hr⟩))
        · have hb := hI.1
          have hne3 : (accFold (Atot.take m) Rws C).reverse ≠
              List.replicate (accFold (Atot.take m) Rws C).reverse.length 2 := by
            intro h
            apply hok
            have h' := congrArg List.reverse h
            rw [List.reverse_reverse, List.length_reverse, List.reverse_replicate] at h'
            rw [h', hI.2, hClen]
          obtain ⟨Z, Y, e, hZ, hY⟩ := split3 _ (fun a ha => hb a (List.mem_reverse.mp ha)) hne3
          have := rowBad (Atot.take m) Rws C (Atot.drop m).reverse Z Y Orest.reverse Cb0 J sv Y2 q hlAs hAsA hCne hC hRl
            (fun a ha => by
              have := hdropA a (List.mem_reverse.mp ha)
              rcases this with rfl | rfl <;> simp [bits])
            hZ hY e (fun a ha => hO a (List.mem_reverse.mp ha)) (fun a ha => by simp [B0, hCb0 a ha]) hJ hsv hY2
          rw [hRev]
          exact this

end ZP.Mul.MM
