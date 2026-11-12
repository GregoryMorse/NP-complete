module

public import ZP.MMLong
public import ZP.MMEnds
public import ZP.MMBridge

@[expose] public section

/-! The whole output check `mmPhase`. -/

namespace ZP.Mul.MM

open ZP

theorem decomp : ∀ (s : List Bool), ∃ m rest, s = List.replicate m true ++ rest ∧ (rest = [] ∨ ∃ w, rest = false :: w)
  | [] => ⟨0, [], by simp, Or.inl rfl⟩
  | true :: s => by
    obtain ⟨m, rest, h, hr⟩ := decomp s
    exact ⟨m + 1, rest, by simp [h, List.replicate_succ], hr⟩
  | false :: w => ⟨0, false :: w, by simp, Or.inr ⟨w, rfl⟩⟩

theorem mmM_cons_true (l : List Bool) : mmM (true :: l) = mmM l + 1 := by
  simp [mmM, List.takeWhile_cons]

theorem mmW_cons_true (l : List Bool) : mmW (true :: l) = mmW l := by
  simp [mmW, mmM_cons_true]

theorem mmMW_zero (w : List Bool) : mmM (false :: w) = 0 ∧ mmW (false :: w) = w := by
  simp [mmM, mmW, List.takeWhile_cons]

theorem mmMW_rep (w : List Bool) : ∀ m, mmM (List.replicate m true ++ false :: w) = m ∧
    mmW (List.replicate m true ++ false :: w) = w
  | 0 => by simpa using mmMW_zero w
  | m + 1 => by
    have ih := mmMW_rep w m
    rw [List.replicate_succ, List.cons_append, mmM_cons_true, mmW_cons_true]
    exact ⟨by rw [ih.1], ih.2⟩

theorem mmMW_ones : ∀ m, mmM (List.replicate m true) = m ∧ mmW (List.replicate m true) = []
  | 0 => by simp [mmM, mmW]
  | m + 1 => by
    have ih := mmMW_ones m
    rw [List.replicate_succ, mmM_cons_true, mmW_cons_true]
    exact ⟨by rw [ih.1], ih.2⟩

theorem checkMM_of_rows0 (out s : List Bool) (h : mmRows s = 0) : checkMM out s = true := by
  simp [checkMM, mmC, h, padTo]

theorem mmRows_short (s : List Bool) (hm : mmM s ≠ 0) (h : (mmW s).length ≤ mmM s ^ 2) : mmRows s = 0 := by
  unfold mmRows
  rw [if_neg hm]
  have h1 : (mmW s).length - mmM s ^ 2 = 0 := by omega
  rw [h1]
  have : 0 + mmM s - 1 < mmM s := by omega
  exact Nat.div_eq_of_lt this

theorem mmRows_zero (s : List Bool) (hm : mmM s = 0) : mmRows s = 0 := by
  unfold mmRows; rw [if_pos hm]

theorem bitsOf_rep (m : Nat) (w : List Bool) : bitsOf (List.replicate m true ++ false :: w) =
    List.replicate m 3 ++ 2 :: bitsOf w := by
  simp [bitsOf, List.map_append, List.map_replicate]

theorem bitsOf_ones (m : Nat) : bitsOf (List.replicate m true) = List.replicate m 3 := by
  simp [bitsOf, List.map_replicate]


theorem getD_drop' (w : List Nat) (m i : Nat) : (w.drop m).getD i 0 = w.getD (m + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem rowsOf_get (m : Nat) : ∀ (t : Nat) (w : List Nat), t * m ≤ w.length →
    rowsOf m w t = (List.range t).map (fun k => (List.range m).map (fun j => w.getD (k * m + j) 0))
  | 0, w, _ => by simp [rowsOf]
  | t + 1, w, h => by
    rw [Nat.succ_mul] at h
    have ih := rowsOf_get m t (w.drop m) (by simp only [List.length_drop]; omega)
    rw [rowsOf, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · apply List.ext_getElem
      · simp only [List.length_take, List.length_map, List.length_range]; omega
      · intro i h1 h2
        have hi : i < w.length := by simp at h1; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · apply List.map_congr_left
      intro k _
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, getD_drop']
      congr 1
      rw [Nat.succ_mul]; omega


theorem padTo_getD (n : Nat) (w : List Bool) (i : Nat) (hi : i < n) (hn : n ≤ w.length) :
    (padTo n w).getD i false = w.getD i false := by
  unfold padTo
  rw [List.take_append_of_le_length hn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

theorem bitsOf_getD (w : List Bool) (i : Nat) (hi : i < w.length) :
    (bitsOf w).getD i 0 = sy (w.getD i false) := by
  have : bitsOf w = w.map sy := rfl
  rw [this]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem idx_lt (m k j : Nat) (hk : k < m) (hj : j < m) : k * m + j < m ^ 2 := by
  have : (k + 1) * m ≤ m * m := Nat.mul_le_mul_right m hk
  rw [Nat.succ_mul] at this
  rw [Nat.pow_two]; omega

theorem rowsOf_bridge (s : List Bool) (hn : mmM s ^ 2 ≤ (mmW s).length) :
    rowsOf (mmM s) (bitsOf (mmW s)) (mmM s) =
      (List.range (mmM s)).map (fun k => (List.range (mmM s)).map (fun j => sy (mmB s k j))) := by
  have hl : mmM s * mmM s ≤ (bitsOf (mmW s)).length := by
    have : (bitsOf (mmW s)).length = (mmW s).length := by simp [bitsOf]
    rw [this, ← Nat.pow_two]; exact hn
  rw [rowsOf_get _ _ _ hl]
  apply List.map_congr_left
  intro k hk
  apply List.map_congr_left
  intro j hj
  have hk' := List.mem_range.mp hk
  have hj' := List.mem_range.mp hj
  have hi := idx_lt _ _ _ hk' hj'
  have hi2 : k * mmM s + j < (mmW s).length := Nat.lt_of_lt_of_le hi hn
  rw [bitsOf_getD _ _ hi2]
  unfold mmB
  rw [padTo_getD _ _ _ hi hn]


set_option maxHeartbeats 1000000 in
theorem longPhase (out s : List Bool) (hm : mmM s ≠ 0) (hn : mmM s ^ 2 < (mmW s).length)
    (J sv Y2 : List Nat) (hJ : Bits J) (hsv : Bits sv) (hY2 : Sym4 Y2) :
    (checkMM out s = true →
      zmmLogic.Reach (hd QMM.FA (bitsOf (mmW s)).reverse (0 :: [] ++ 1 :: List.replicate (mmM s) 3 ++ 0 :: 1 ::
          (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP31 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) ∧
    (checkMM out s ≠ true →
      zmmLogic.Reach (hd QMM.FA (bitsOf (mmW s)).reverse (0 :: [] ++ 1 :: List.replicate (mmM s) 3 ++ 0 :: 1 ::
          (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (sv ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP30 (1 :: (J ++ 1 :: (sv ++ [1]))) (1 :: Y2))) := by
  have hl : (bitsOf (mmW s)).length = (mmW s).length := by simp [bitsOf]
  have hn' : mmM s * mmM s < (bitsOf (mmW s)).length := by rw [hl, ← Nat.pow_two]; exact hn
  have hfuel : ((bitsOf (mmW s)).drop (mmM s * mmM s)).length ≤ mmRows s * mmM s := by
    have := fuel_rows (((mmW s).drop (mmM s ^ 2)).length) (mmM s) hm
    rw [rows_eq s hm]
    simp only [List.length_drop, hl, ← Nat.pow_two] at this ⊢
    exact this
  have hmain := mainLong (mmM s) hm (bitsOf (mmW s)) (Bits.ofB _) hn' (bitsOf out.reverse) J sv Y2 (Bits.ofB _)
    hJ hsv hY2 (mmRows s) hfuel
  have hbr : rowsOK (mmM s) (rowsOf (mmM s) (bitsOf (mmW s)) (mmM s)) (mmRows s)
      ((bitsOf (mmW s)).drop (mmM s * mmM s)) (((bitsOf out.reverse).reverse ++ List.replicate (mmM s) 2).take (mmM s))
      ((bitsOf out.reverse).reverse.drop (mmM s)) ↔ checkMM out s = true := by
    rw [rowsOf_bridge s (Nat.le_of_lt hn)]
    have e1 : (bitsOf (mmW s)).drop (mmM s * mmM s) = ((mmW s).drop (mmM s ^ 2)).map sy := by
      have : bitsOf (mmW s) = (mmW s).map sy := rfl
      rw [this, List.map_drop, Nat.pow_two]
    have e2 : (bitsOf out.reverse).reverse = out.map sy := by
      have : bitsOf out.reverse = out.reverse.map sy := rfl
      rw [this, List.map_reverse, List.reverse_reverse]
    rw [e1, e2]
    exact rowsOK_checkMM out s hm
  exact ⟨fun h => hmain.1 (hbr.mpr h), fun h => hmain.2 (fun hh => h (hbr.mp hh))⟩


theorem decomp' (s : List Bool) : (∃ m, s = List.replicate m true) ∨ (∃ m w, s = List.replicate m true ++ false :: w) := by
  obtain ⟨m, rest, h, hr⟩ := decomp s
  rcases hr with rfl | ⟨w, rfl⟩
  · exact Or.inl ⟨m, by simpa using h⟩
  · exact Or.inr ⟨m, w, h⟩

set_option maxHeartbeats 2000000 in
theorem mmPhase (out s : List Bool) (J Y2 : List Nat) (hJ : Bits J) (hY2 : Sym4 Y2) :
    ∃ q, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ checkMM out s = true) ∧
      zmmLogic.Reach (hdR QMM.mK1 [1] (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 1 :: 1 :: Y2))))
        (hdR q (1 :: (J ++ 1 :: (bitsOf s ++ [1]))) (1 :: Y2)) := by
  have h1u : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have hOs : Bits (bitsOf out.reverse) := Bits.ofB _
  have hS : Bits (bitsOf s) := Bits.ofB _
  have hA := toX3a (bitsOf out.reverse) J (bitsOf s) (1 :: Y2) hOs hJ hS (Sym4.cons h1u hY2)
  have hT : Sym4 (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 0 :: 1 :: Y2))) := by
    simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hOs.sym4, hJ.sym4, hS.sym4, hY2]
  have fin31 : checkMM out s = true →
      zmmLogic.Reach (hd QMM.X3a (bitsOf s).reverse (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP31 (1 :: (J ++ 1 :: (bitsOf s ++ [1]))) (1 :: Y2)) →
      ∃ q, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ checkMM out s = true) ∧
      zmmLogic.Reach (hdR QMM.mK1 [1] (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 1 :: 1 :: Y2))))
        (hdR q (1 :: (J ++ 1 :: (bitsOf s ++ [1]))) (1 :: Y2)) :=
    fun hc h => ⟨Q.DP31, Or.inl rfl, ⟨fun _ => hc, fun _ => rfl⟩, hA.trans h⟩
  have fin30 : checkMM out s ≠ true →
      zmmLogic.Reach (hd QMM.X3a (bitsOf s).reverse (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 0 :: 1 :: Y2)))))
        (hdR Q.DP30 (1 :: (J ++ 1 :: (bitsOf s ++ [1]))) (1 :: Y2)) →
      ∃ q, (q = Q.DP31 ∨ q = Q.DP30) ∧ (q = Q.DP31 ↔ checkMM out s = true) ∧
      zmmLogic.Reach (hdR QMM.mK1 [1] (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (bitsOf s ++ 1 :: 1 :: Y2))))
        (hdR q (1 :: (J ++ 1 :: (bitsOf s ++ [1]))) (1 :: Y2)) :=
    fun hc h => ⟨Q.DP30, Or.inr rfl, ⟨fun h' => absurd h' (by decide), fun h' => absurd h' hc⟩, hA.trans h⟩
  rcases decomp' s with ⟨m, rfl⟩ | ⟨m, w, rfl⟩
  · have hMW := mmMW_ones m
    cases m with
    | zero =>
      have hc : checkMM out (List.replicate 0 true) = true := checkMM_of_rows0 _ _ (mmRows_zero _ hMW.1)
      refine fin31 hc ?_
      have := endEmpty (bitsOf out.reverse) [] J (bitsOf (List.replicate 0 true)) Y2 hOs (by simp) hJ hS hY2
      exact this.of_eq (by simp [bitsOf, hd_nil_hdR]) rfl
    | succ m' =>
      have hc : checkMM out (List.replicate (m' + 1) true) = true :=
        checkMM_of_rows0 _ _ (mmRows_short _ (by rw [hMW.1]; omega) (by rw [hMW.2]; simp))
      refine fin31 hc ?_
      rw [bitsOf_ones]
      have h3u : (3 : Nat) ∈ ALL := by simp [ALL]
      have hrep : ∀ k, Sym4 (List.replicate k 3) := fun k a ha => by rw [List.eq_of_mem_replicate ha]; exact h3u
      have hT1 : Sym4 (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (List.replicate (m' + 1) 3 ++ 0 :: 1 :: Y2)))) := by
        simp [sym4_app_iff, sym4_cons_iff, h0, h1u, hOs.sym4, hJ.sym4, hrep, hY2]
      have st1 := x3a3 (List.replicate m' 3) (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (List.replicate (m' + 1) 3 ++ 0 :: 1 :: Y2))))
        (hrep _) hT1
      have st2 := fLoop QMM.X3 (fun c => c = 3) (fun c hc => by rw [hc]; exact h3u)
        (fun L R c hL hR hc => by subst hc; exact x3Step L R hL hR) (List.replicate m' 3)
        (fun a ha => List.eq_of_mem_replicate ha) [] (3 :: 1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: (List.replicate (m' + 1) 3 ++ 0 :: 1 :: Y2))))
        Sym4.nil (Sym4.cons h3u hT1)
      have st3 := endOnes (List.replicate (m' + 1) 3) (bitsOf out.reverse) [] J (List.replicate (m' + 1) 3) Y2
        (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [T3]) hOs (by simp) hJ (fun a ha => by
          rw [List.eq_of_mem_replicate ha]; simp [bits]) hY2
      have e1 : List.replicate (m' + 1) 3 = List.replicate m' 3 ++ [3] := by simp [List.replicate_succ']
      have e2 : (List.replicate (m' + 1) 3).reverse = List.replicate m' 3 ++ [3] := by
        rw [List.reverse_replicate, List.replicate_succ']
      refine (st1.of_eq (by rw [e2]) rfl).trans ?_
      refine (st2.of_eq (by simp) rfl).trans ?_
      exact (st3.of_eq (by simp [hd_nil_hdR, e1]) rfl)
  · have hMW := mmMW_rep w m
    have h3u : (3 : Nat) ∈ ALL := by simp [ALL]
    have h2u : (2 : Nat) ∈ ALL := by simp [ALL]
    have hrep : ∀ k, Sym4 (List.replicate k 3) := fun k a ha => by rw [List.eq_of_mem_replicate ha]; exact h3u
    have hwB : Bits (bitsOf w) := Bits.ofB _
    have hS' : Bits (List.replicate m 3 ++ 2 :: bitsOf w) := by rw [← bitsOf_rep]; exact hS
    have bnil : bitsOf ([] : List Bool) = [] := rfl
    cases m with
    | zero =>
      have hc : checkMM out (List.replicate 0 true ++ false :: w) = true :=
        checkMM_of_rows0 _ _ (mmRows_zero _ hMW.1)
      refine fin31 hc ?_
      rw [bitsOf_rep]
      have := endZero (bitsOf w).reverse (bitsOf out.reverse) [] J (List.replicate 0 3 ++ 2 :: bitsOf w) Y2
        hwB.rev hOs (by simp) hJ hS' hY2
      exact this.of_eq (by simp [hd_snoc]) rfl
    | succ m' =>
      by_cases hw0 : w = []
      · subst hw0
        have hc : checkMM out (List.replicate (m' + 1) true ++ false :: []) = true :=
          checkMM_of_rows0 _ _ (mmRows_short _ (by rw [hMW.1]; omega) (by rw [hMW.2]; simp))
        refine fin31 hc ?_
        rw [bitsOf_rep]
        have hT1 : Sym4 (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf []) ++ 0 :: 1 :: Y2)))) := by
          simp only [sym4_app_iff, sym4_cons_iff, bnil, List.cons_append, List.append_assoc, List.nil_append, h0, h1u, h2u, h3u, hOs.sym4, hJ.sym4, hrep, hY2, and_self, true_and, and_true]
        have st1 := x3a3 (2 :: List.replicate m' 3) (1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf []) ++ 0 :: 1 :: Y2))))
          (by simp [sym4_cons_iff, h2u, hrep]) hT1
        have st2 := fLoop QMM.X3 (fun c => c = 3) (fun c hc => by rw [hc]; exact h3u)
          (fun L R c hL hR hc => by subst hc; exact x3Step L R hL hR) (List.replicate m' 3)
          (fun a ha => List.eq_of_mem_replicate ha) [2] (3 :: 1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf []) ++ 0 :: 1 :: Y2))))
          (by simp [sym4_cons_iff, h2u]) (Sym4.cons h3u hT1)
        have st3 := x3Hole [] (List.replicate m' 3 ++ 3 :: 1 :: (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf []) ++ 0 :: 1 :: Y2))))
          Sym4.nil (by simp [sym4_app_iff, sym4_cons_iff, h0, h1u, h3u, hrep, hOs.sym4, hJ.sym4, h2u, hY2, bnil])
        have st4 := endNoW (List.replicate (m' + 1) 3) (bitsOf out.reverse) [] J (List.replicate (m' + 1) 3 ++ 2 :: bitsOf []) Y2
          (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [T3]) hOs (by simp) hJ
          hS' hY2
        have e1 : List.replicate (m' + 1) 3 = List.replicate m' 3 ++ [3] := by simp [List.replicate_succ']
        have e2 : (List.replicate (m' + 1) 3 ++ 2 :: bitsOf []).reverse = (2 :: List.replicate m' 3) ++ [3] := by
          rw [bnil, List.reverse_append, List.reverse_replicate, e1]; simp
        refine (st1.of_eq (by rw [e2]) rfl).trans ?_
        refine (st2.of_eq (by simp) rfl).trans ?_
        refine (st3.of_eq (by simp) rfl).trans ?_
        exact st4.of_eq (by simp [hd_nil_hdR, e1]) rfl
      · have hbw : bitsOf w ≠ [] := fun h => hw0 (by cases w with
          | nil => rfl
          | cons a t => simp [bitsOf] at h)
        have hTs : Sym4 (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf w) ++ 0 :: 1 :: Y2))) := by
          simp only [sym4_app_iff, sym4_cons_iff, List.cons_append, List.append_assoc, h0, h1u, h2u, h3u, hOs.sym4, hJ.sym4, hrep, hwB.sym4, hY2, and_self, true_and, and_true]
        have hsetup := setupFA (m' + 1) (bitsOf w) (bitsOf out.reverse ++ 1 :: (J ++ 1 :: ((List.replicate (m' + 1) 3 ++ 2 :: bitsOf w) ++ 0 :: 1 :: Y2)))
          (by omega) hwB hbw hTs
        have e : (List.replicate (m' + 1) 3 ++ 2 :: bitsOf w).reverse = (bitsOf w).reverse ++ 2 :: List.replicate (m' + 1) 3 := by
          simp [List.reverse_append, List.reverse_replicate]
        have hlen : (bitsOf w).length = w.length := by simp [bitsOf]
        by_cases hsh : w.length ≤ (m' + 1) * (m' + 1)
        · have hc : checkMM out (List.replicate (m' + 1) true ++ false :: w) = true :=
            checkMM_of_rows0 _ _ (mmRows_short _ (by rw [hMW.1]; omega) (by rw [hMW.1, hMW.2, Nat.pow_two]; exact hsh))
          refine fin31 hc ?_
          rw [bitsOf_rep]
          have hr := dryShort (m' + 1) (by omega) (bitsOf w) hwB (by rw [hlen]; exact hsh) (bitsOf out.reverse) J
            (List.replicate (m' + 1) 3 ++ 2 :: bitsOf w) Y2 hOs hJ hS' hY2
          exact (hsetup.of_eq (by rw [e]) rfl).trans hr
        · have hL := longPhase out (List.replicate (m' + 1) true ++ false :: w) (by rw [hMW.1]; omega)
            (by rw [hMW.1, hMW.2, Nat.pow_two]; omega) J (bitsOf (List.replicate (m' + 1) true ++ false :: w)) Y2 hJ hS hY2
          rw [hMW.1, hMW.2, bitsOf_rep] at hL
          by_cases hc : checkMM out (List.replicate (m' + 1) true ++ false :: w) = true
          · refine fin31 hc ?_
            rw [bitsOf_rep]
            exact (hsetup.of_eq (by rw [e]) rfl).trans (hL.1 hc)
          · refine fin30 hc ?_
            rw [bitsOf_rep]
            exact (hsetup.of_eq (by rw [e]) rfl).trans (hL.2 hc)

end ZP.Mul.MM
