module

public import ZP.MMRowsAll

@[expose] public section

/-! The GF(2) meaning of the accumulator: column `j` of `accFold As Rws C` is `C[j] xor sum_k A[k] B[k][j]`. -/

namespace ZP.Mul.MM

open ZP

/-- Symbol of a bit (`2` = bit `0`, `3` = bit `1`). -/
def sy (b : Bool) : Nat := if b then 3 else 2

/-- Bit of a symbol. -/
def bt (x : Nat) : Bool := decide (x = 3)

def prodCol : List Nat → List (List Nat) → Nat → Bool
  | s :: As, V :: Rws, j => xor (bt s && bt (V.getD j 2)) (prodCol As Rws j)
  | _, _, _ => false

theorem bt_jc (s v x : Nat) (hs : s = 2 ∨ s = 3) (hx : x = 2 ∨ x = 3) :
    bt (jc (aOf s) v x) = xor (bt x) (bt s && bt v) := by
  rcases hs with rfl | rfl <;> rcases hx with rfl | rfl <;> by_cases hv : v = 3 <;> simp [jc, aOf, bt, hv]

theorem accFold_col : ∀ (As : List Nat) (Rws : List (List Nat)) (C : List Nat), (∀ s ∈ As, s = 2 ∨ s = 3) →
    Bits C → (∀ r ∈ Rws, Bits r ∧ r.length = C.length) → ∀ j, j < C.length →
    bt ((accFold As Rws C).getD j 2) = xor (bt (C.getD j 2)) (prodCol As Rws j)
  | [], Rws, C, _, _, _, j, _ => by simp [accFold, prodCol]
  | s :: As, [], C, _, _, _, j, _ => by simp [accFold, prodCol]
  | s :: As, V :: Rws, C, hA, hC, hR, j, hj => by
    obtain ⟨hVb, hVl⟩ := hR V (by simp)
    have h1 := bits_zipWith (aOf s) V C hVb hC
    have h2 := len_zipWith (aOf s) V C hVl
    have ih := accFold_col As Rws (List.zipWith (jc (aOf s)) V C) (fun t ht => hA t (by simp [ht])) h1
      (fun r hr => ⟨(hR r (by simp [hr])).1, by rw [h2]; exact (hR r (by simp [hr])).2⟩) j (by rw [h2]; exact hj)
    simp only [accFold, prodCol]
    rw [ih]
    have hjV : j < V.length := by omega
    have e : (List.zipWith (jc (aOf s)) V C).getD j 2 = jc (aOf s) (V.getD j 2) (C.getD j 2) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, hjV, hj]
    rw [e, bt_jc s _ _ (hA s (by simp))]
    · cases bt (C.getD j 2) <;> cases bt s <;> cases bt (V.getD j 2) <;> cases prodCol As Rws j <;> rfl
    · have : C.getD j 2 ∈ C := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rcases mem_bits (hC _ this) with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem accFoldE_id : ∀ (Rws : List (List Nat)) (C : List Nat), (∀ r ∈ Rws, r.length = C.length) →
    (∀ x ∈ C, x = 2 ∨ x = 3) → accFoldE Rws C = C
  | [], C, _, _ => rfl
  | V :: Rws, C, hR, hC => by
    have hz : List.zipWith (jc 1) V C = C := by
      have hl := hR V (by simp)
      clear hR
      induction V generalizing C with
      | nil => cases C with
        | nil => rfl
        | cons _ _ => simp at hl
      | cons v V ih =>
        cases C with
        | nil => simp at hl
        | cons x C =>
          simp only [List.zipWith_cons_cons, List.cons.injEq]
          refine ⟨by simp [jc], ih C (fun y hy => hC y (by simp [hy])) (by simpa using hl)⟩
    simp only [accFoldE]
    rw [hz]
    exact accFoldE_id Rws C (fun r hr => hR r (by simp [hr])) hC

theorem accRow_col (Rws : List (List Nat)) (As C : List Nat) (hA : ∀ s ∈ As, s = 2 ∨ s = 3) (hC : Bits C)
    (hR : ∀ r ∈ Rws, Bits r ∧ r.length = C.length) (j : Nat) (hj : j < C.length) :
    bt ((accRow Rws As C).getD j 2) = xor (bt (C.getD j 2)) (prodCol As (Rws.take As.length) j) := by
  have hR1 : ∀ r ∈ Rws.take As.length, Bits r ∧ r.length = C.length := fun r hr => hR r (List.mem_of_mem_take hr)
  have hI := accFold_inv As (Rws.take As.length) C hC hR1
  have hE := accFoldE_id (Rws.drop As.length) (accFold As (Rws.take As.length) C)
    (fun r hr => by rw [hI.2]; exact (hR r (List.mem_of_mem_drop hr)).2)
    (fun x hx => by rcases mem_bits (hI.1 x hx) with h | h; exact Or.inl h; exact Or.inr h)
  have : accRow Rws As C = accFold As (Rws.take As.length) C := hE
  rw [this]
  exact accFold_col As _ C hA hC hR1 j hj

/-- The inner loop of `mmC`. -/
def gx (n : Nat) (f : Nat → Bool) : Bool := (List.range n).foldl (fun acc k => xor acc (f k)) false

theorem foldl_shift (f : Nat → Bool) : ∀ (l : List Nat) (b : Bool),
    l.foldl (fun acc k => xor acc (f k)) b = xor b (l.foldl (fun acc k => xor acc (f k)) false)
  | [], b => by simp
  | k :: l, b => by
    simp only [List.foldl_cons]
    rw [foldl_shift f l (xor b (f k)), foldl_shift f l (xor false (f k))]
    cases b <;> cases f k <;> cases l.foldl (fun acc k => xor acc (f k)) false <;> rfl

theorem gx_succ (n : Nat) (f : Nat → Bool) : gx (n + 1) f = xor (f 0) (gx n (fun k => f (k + 1))) := by
  unfold gx
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, foldl_shift]
  simp

theorem prodCol_eq (j : Nat) : ∀ (As : List Nat) (Rws : List (List Nat)), As.length ≤ Rws.length →
    prodCol As Rws j = gx As.length (fun k => bt (As.getD k 2) && bt ((Rws.getD k []).getD j 2))
  | [], Rws, _ => by simp [prodCol, gx]
  | s :: As, [], h => by simp at h
  | s :: As, V :: Rws, h => by
    rw [List.length_cons, gx_succ]
    simp only [prodCol]
    rw [prodCol_eq j As Rws (by simpa using h)]
    simp

theorem bt_sy (b : Bool) : bt (sy b) = b := by cases b <;> simp [bt, sy]

theorem bt_getD_map (l : List Bool) (i : Nat) : bt ((l.map sy).getD i 2) = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : l[i]? with
  | none => simp [bt]
  | some b => simp [bt_sy]

theorem getD_take_drop (l : List Nat) (a m k d : Nat) :
    ((l.drop a).take m).getD k d = if k < m then l.getD (a + k) d else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  by_cases h : k < m <;> simp [h]

theorem gx_ext (f : Nat → Bool) (l m : Nat) (h : l ≤ m) (hf : ∀ k, l ≤ k → f k = false) : gx m f = gx l f := by
  induction m with
  | zero => have : l = 0 := by omega
            subst this; rfl
  | succ m ih =>
    by_cases hl : l = m + 1
    · subst hl; rfl
    · have h1 : l ≤ m := by omega
      unfold gx
      rw [List.range_succ, List.foldl_append]
      have := ih h1
      unfold gx at this
      simp [this, hf m h1]

theorem gx_congr (F G : Nat → Bool) : ∀ n, (∀ k, k < n → F k = G k) → gx n F = gx n G := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    unfold gx
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    have := ih (fun k hk => h k (by omega))
    unfold gx at this
    simp [this, h n (by omega)]

theorem getD_take_append_rep (x : List Nat) (m j : Nat) (hj : j < m) :
    ((x ++ List.replicate m 2).take m).getD j 2 = x.getD j 2 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj, if_true, List.getElem?_append]
  by_cases h : j < x.length
  · simp [h]
  · simp only [h, if_false, List.getElem?_replicate]
    have : x[j]? = none := by simp; omega
    simp [this]
    split <;> simp

theorem eq_rep2 (l : List Nat) (m : Nat) (hb : Bits l) (hl : l.length = m) :
    l = List.replicate m 2 ↔ ∀ j, j < m → bt (l.getD j 2) = false := by
  constructor
  · intro h j hj
    subst h
    simp [bt, List.getD_eq_getElem?_getD, hj]
  · intro h
    apply List.ext_getElem (by simp [hl])
    intro j hj1 hj2
    have hjm : j < m := by omega
    have := h j hjm
    have hm : l[j] ∈ l := List.getElem_mem hj1
    rcases mem_bits (hb _ hm) with h2 | h2
    · simp [h2]
    · exfalso
      simp [List.getD_eq_getElem?_getD, hj1, h2, bt] at this

theorem rowEq (m : Nat) (B : Nat → Nat → Bool) (a out : List Bool) (i : Nat) (hm : m ≠ 0) :
    let Rws := (List.range m).map (fun k => (List.range m).map (fun j => sy (B k j)))
    let Atot := ((a.map sy).drop (i * m))
    let C := (((out.map sy).drop (i * m)) ++ List.replicate m 2).take m
    accRow Rws (Atot.take m) C = List.replicate m 2 ↔
      ∀ j, j < m → out.getD (i * m + j) false = gx m (fun k => a.getD (i * m + k) false && B k j) := by
  intro Rws Atot C
  have hRlen : Rws.length = m := by simp [Rws]
  have hAs : ∀ s ∈ Atot.take m, s = 2 ∨ s = 3 := fun s hs => by
    have := List.mem_of_mem_take hs
    have := List.mem_of_mem_drop this
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp this
    cases b <;> simp [sy]
  have hClen : C.length = m := by
    simp [C, List.length_take]
  have hC : Bits C := fun x hx => by
    have := List.mem_of_mem_take hx
    rcases List.mem_append.mp this with h | h
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop h)
      cases b <;> simp [sy, bits]
    · rw [List.eq_of_mem_replicate h]; simp [bits]
  have hR : ∀ r ∈ Rws, Bits r ∧ r.length = C.length := fun r hr => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    refine ⟨fun x hx => ?_, by simp [hClen]⟩
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    cases B k j <;> simp [sy, bits]
  have hI := accFold_inv (Atot.take m) (Rws.take (Atot.take m).length) C hC
    (fun r hr => hR r (List.mem_of_mem_take hr))
  have hE : accRow Rws (Atot.take m) C = accFold (Atot.take m) (Rws.take (Atot.take m).length) C :=
    accFoldE_id _ _ (fun r hr => by rw [hI.2]; exact (hR r (List.mem_of_mem_drop hr)).2)
      (fun x hx => by rcases mem_bits (hI.1 x hx) with h | h; exact Or.inl h; exact Or.inr h)
  have hAcc : Bits (accRow Rws (Atot.take m) C) := by rw [hE]; exact hI.1
  have hAl : (accRow Rws (Atot.take m) C).length = m := by rw [hE, hI.2, hClen]
  rw [eq_rep2 _ m hAcc hAl]
  refine forall_congr' (fun j => forall_congr' (fun hj => ?_))
  rw [accRow_col Rws (Atot.take m) C hAs hC hR j (by omega), prodCol_eq j _ _ (by
    rw [List.length_take]; simp [hRlen])]
  have hC1 : bt (C.getD j 2) = out.getD (i * m + j) false := by
    have e1 : C.getD j 2 = ((out.map sy).drop (i * m)).getD j 2 := getD_take_append_rep _ m j hj
    rw [e1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at *
    have := bt_getD_map out (i * m + j)
    simp only [List.getD_eq_getElem?_getD] at this
    rw [show i * m + j = i * m + j from rfl]
    exact this
  have hlm : (List.take m Atot).length ≤ m := by rw [List.length_take]; omega
  have hpt : ∀ k, k < (List.take m Atot).length →
      (bt ((List.take m Atot).getD k 2) && bt (((List.take (List.take m Atot).length Rws).getD k []).getD j 2)) =
      (a.getD (i * m + k) false && B k j) := by
    intro k hk
    have hkm : k < m := by omega
    have e1 : (List.take m Atot).getD k 2 = (a.map sy).getD (i * m + k) 2 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hkm, if_true, Atot]
    have e2 : (List.take (List.take m Atot).length Rws).getD k [] = Rws.getD k [] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hk, if_true]
    have e3 : Rws.getD k [] = (List.range m).map (fun j => sy (B k j)) := by
      simp [Rws, List.getD_eq_getElem?_getD, List.getElem?_map, hkm]
    have e4 : ((List.range m).map (fun j => sy (B k j))).getD j 2 = sy (B k j) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj]
    rw [e1, e2, e3, e4, bt_getD_map, bt_sy]
  have hcongr := gx_congr _ (fun k => a.getD (i * m + k) false && B k j) _ hpt
  have hext : gx m (fun k => a.getD (i * m + k) false && B k j) =
      gx (List.take m Atot).length (fun k => a.getD (i * m + k) false && B k j) := by
    by_cases hl : (List.take m Atot).length = m
    · rw [hl]
    · apply gx_ext _ _ _ hlm
      intro k hk
      have hl2 : (List.take m Atot).length < m := by omega
      have hl3 : Atot.length < m := by rw [List.length_take] at hl2; omega
      have : a.length ≤ i * m + k := by
        simp only [Atot, List.length_drop, List.length_map] at hl3 hk hl2
        rw [List.length_take] at hk
        simp only [Atot, List.length_drop, List.length_map] at hk
        omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  rw [hC1, hcongr, ← hext]
  cases out.getD (i * m + j) false <;> cases gx m (fun k => a.getD (i * m + k) false && B k j) <;> simp

theorem rowsOK_iff (m : Nat) (B : Nat → Nat → Bool) (a out : List Bool) (hm : m ≠ 0) :
    ∀ (n i : Nat), a.length - i * m ≤ n * m →
      (rowsOK m ((List.range m).map (fun k => (List.range m).map (fun j => sy (B k j)))) n
        ((a.map sy).drop (i * m)) ((((out.map sy).drop (i * m)) ++ List.replicate m 2).take m)
        ((out.map sy).drop ((i + 1) * m)) ↔
      ∀ i', i ≤ i' → i' * m < a.length →
        ∀ j, j < m → out.getD (i' * m + j) false = gx m (fun k => a.getD (i' * m + k) false && B k j)) := by
  intro n
  induction n with
  | zero =>
    intro i h
    simp only [rowsOK, true_iff]
    intro i' hi hlt
    have : i * m ≤ i' * m := Nat.mul_le_mul_right m hi
    omega
  | succ n ih =>
    intro i h
    by_cases hz : a.length ≤ i * m
    · have : (a.map sy).drop (i * m) = [] := by simp; omega
      rw [rowsOK, this]
      simp only [true_or, true_iff]
      intro i' hi hlt
      have : i * m ≤ i' * m := Nat.mul_le_mul_right m hi
      omega
    · have hne : (a.map sy).drop (i * m) ≠ [] := by
        intro e; have := congrArg List.length e; simp at this; omega
      rw [rowsOK]
      simp only [hne, false_or]
      have e1 : (a.map sy).drop (i * m) = (a.map sy).drop (i * m) := rfl
      have hrow := rowEq m B a out i hm
      simp only at hrow
      rw [hrow]
      have hmm : (i + 1) * m = i * m + m := by rw [Nat.add_mul, Nat.one_mul]
      have hmm2 : (i + 1 + 1) * m = (i + 1) * m + m := by rw [Nat.add_mul (i + 1) 1 m, Nat.one_mul]
      have eA : ((a.map sy).drop (i * m)).drop m = (a.map sy).drop ((i + 1) * m) := by
        rw [List.drop_drop, hmm]
      have eO : ((out.map sy).drop ((i + 1) * m)).drop m = (out.map sy).drop ((i + 1 + 1) * m) := by
        rw [List.drop_drop, hmm2]
      rw [eA, eO]
      have h2 : a.length - (i + 1) * m ≤ n * m := by
        have : (n + 1) * m = n * m + m := Nat.succ_mul n m
        omega
      rw [ih (i + 1) h2]
      constructor
      · rintro ⟨h1, h3⟩ i' hi hlt
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt2
        · exact h1
        · exact h3 i' hlt2 hlt
      · intro hall
        exact ⟨hall i (Nat.le_refl _) (by omega), fun i' hi hlt => hall i' (by omega) hlt⟩

end ZP.Mul.MM
