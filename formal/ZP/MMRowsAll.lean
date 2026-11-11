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

end ZP.Mul.MM
