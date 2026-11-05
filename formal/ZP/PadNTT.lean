module

public import ZP.DefsNTT

@[expose] public section

/-! # Padding: inserting `n` records `(none, 0)` after the first `n` records keeps `evalC` -/

namespace ZP

theorem valsAux_append (t p : Nat) : ∀ (as bs : List Rec) (j : Nat) (vs : List Nat),
    valsAux t p j (as ++ bs) vs = valsAux t p (j + as.length) bs (valsAux t p j as vs)
  | [], bs, j, vs => by simp [valsAux]
  | a :: as, bs, j, vs => by
    obtain ⟨u, b⟩ := a
    simp only [List.cons_append, valsAux, List.length_cons]
    rw [valsAux_append t p as bs (j + 1)]
    congr 1
    omega

theorem getD_append_left (A B : List Nat) (i : Nat) (h : i < A.length) : (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (A B : List Nat) (i : Nat) (h : A.length ≤ i) :
    (A ++ B).getD i 0 = B.getD (i - A.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_rep (n L i : Nat) (h : i < n) : (List.replicate n L).getD i 0 = L := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getLastD_append (X Y : List Nat) (d : Nat) :
    (X ++ Y).getLastD d = if Y = [] then X.getLastD d else Y.getLastD d := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_append]
  cases hY : Y.getLast? with
  | none => have : Y = [] := List.getLast?_eq_none_iff.1 hY
            simp [this]
  | some y => have : Y ≠ [] := fun h => by simp [h] at hY
              simp [this]

/-- Inserted records `(none, 0)` repeat the last value. -/
theorem valsAux_none (t p : Nat) (L : Nat) (hL : L < p) :
    ∀ (k j : Nat) (vs : List Nat), t < j → vs.getLastD 0 = L →
    valsAux t p j (List.replicate k ((none : Option Nat), 0)) vs = vs ++ List.replicate k L
  | 0, j, vs, _, _ => by simp [valsAux]
  | k + 1, j, vs, ht, hl => by
    simp only [List.replicate_succ, valsAux]
    have hj : j ≠ t := by omega
    have hv : ((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal none j 0 vs) % p = L := by
      have e : (if j = t then 1 else 0) = 0 := by simp [hj]
      rw [e, hl]; simp [ptrVal, Nat.mod_eq_of_lt hL]
    simp only [hv]
    rw [valsAux_none t p L hL k (j + 1) _ (by omega)]
    · simp [List.replicate_succ', List.append_assoc]
    · simp [getLastD_append]

/-- The pointer shift. -/
def shiftRec (n : Nat) (r : Rec) : Rec := (r.1.map fun u => if u < n then u else u + n, r.2)

/-- Insert `n` copies of `L` after position `n`. -/
def insN (n L : Nat) (X : List Nat) : List Nat := X.take n ++ List.replicate n L ++ X.drop n

theorem valsAux_len (t p : Nat) : ∀ (rs : List Rec) (j : Nat) (vs : List Nat),
    (valsAux t p j rs vs).length = vs.length + rs.length
  | [], j, vs => by simp [valsAux]
  | (u, b) :: rs, j, vs => by
    simp only [valsAux]
    rw [valsAux_len t p rs (j + 1)]
    simp; omega

theorem insN_snoc (n L : Nat) (X : List Nat) (v : Nat) (h : n ≤ X.length) :
    insN n L (X ++ [v]) = insN n L X ++ [v] := by
  simp [insN, List.take_append_of_le_length h, List.drop_append_of_le_length h, List.append_assoc]

theorem insN_last (n L : Nat) (X : List Nat) (h : n ≤ X.length) (hL : (X.take n).getLastD 0 = L) :
    (insN n L X).getLastD 0 = X.getLastD 0 := by
  unfold insN
  rw [getLastD_append]
  by_cases hd : X.drop n = []
  · have hlen : X.length = n := by
      have := List.length_drop (l := X) (i := n)
      rw [hd] at this; simp at this; omega
    have htk : X.take n = X := List.take_of_length_le (by omega)
    rw [htk] at hL
    simp only [hd, if_true]
    rw [getLastD_append]
    cases n with
    | zero =>
      have : X = [] := List.length_eq_zero_iff.1 hlen
      subst this; simp
    | succ n => simp [List.replicate_succ', List.getLastD_eq_getLast?, ← hL, htk]
  · simp only [hd, if_false]
    rw [show X = X.take n ++ X.drop n from (List.take_append_drop n X).symm, getLastD_append]
    simp [hd]

theorem insN_getD_lt (n L : Nat) (X : List Nat) (u : Nat) (hu : u < n) (h : n ≤ X.length) :
    (insN n L X).getD u 0 = X.getD u 0 := by
  unfold insN
  rw [List.append_assoc, getD_append_left _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hu]

theorem insN_getD_ge (n L : Nat) (X : List Nat) (u : Nat) (hu : n ≤ u) (h : n ≤ X.length) :
    (insN n L X).getD (u + n) 0 = X.getD u 0 := by
  unfold insN
  rw [List.append_assoc, getD_append_right _ _ _ (by simp; omega)]
  have : u + n - (X.take n).length = n + (u - n) := by simp; omega
  rw [this, show (List.replicate n L ++ X.drop n).getD (n + (u - n)) 0 = (X.drop n).getD (u - n) 0 by
    rw [getD_append_right _ _ _ (by simp)]; simp]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, show n + (u - n) = u by omega]

theorem valsAux_shift (t p n L : Nat) (ht : t < n) :
    ∀ (rs : List Rec) (j : Nat) (X : List Nat), n ≤ j → X.length = j → (X.take n).getLastD 0 = L →
    valsAux t p (j + n) (rs.map (shiftRec n)) (insN n L X) = insN n L (valsAux t p j rs X)
  | [], j, X, _, _, _ => by simp [valsAux]
  | (u, b) :: rs, j, X, hj, hX, hL => by
    simp only [List.map_cons, valsAux, shiftRec]
    have e1 : (if j + n = t then 1 else 0) = 0 := by simp; omega
    have e2 : (if j = t then 1 else 0) = 0 := by simp; omega
    have hlast := insN_last n L X (by omega) hL
    have hptr : ptrVal (u.map (fun u => if u < n then u else u + n)) (j + n) b (insN n L X)
        = ptrVal u j b X := by
      cases u with
      | none => rfl
      | some u =>
        simp only [Option.map_some, ptrVal]
        by_cases hu : u < n
        · simp only [hu, if_true, show u < j by omega, show u < j + n by omega]
          rw [insN_getD_lt n L X u hu (by omega)]
        · simp only [hu, if_false]
          by_cases huj : u < j
          · simp only [huj, if_true, show u + n < j + n by omega]
            rw [insN_getD_ge n L X u (by omega) (by omega)]
          · simp [huj, show ¬ (u + n < j + n) by omega]
    simp only [e1, e2, hlast, hptr]
    rw [← insN_snoc n L X _ (by omega)]
    rw [show j + n + 1 = (j + 1) + n by omega]
    exact valsAux_shift t p n L ht rs (j + 1) (X ++ [_]) (by omega) (by simp [hX]) (by
      rw [List.take_append_of_le_length (by omega)]; exact hL)

end ZP
