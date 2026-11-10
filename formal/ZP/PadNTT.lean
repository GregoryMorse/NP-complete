module

public import ZP.AllDefs

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

theorem valsAux_lt (t p : Nat) (hp : 0 < p) : ∀ (rs : List Rec) (j : Nat) (vs : List Nat),
    (∀ x ∈ vs, x < p) → ∀ x ∈ valsAux t p j rs vs, x < p
  | [], j, vs, h => by simpa [valsAux] using h
  | (u, b) :: rs, j, vs, h => by
    simp only [valsAux]
    refine valsAux_lt t p hp rs (j + 1) _ ?_
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h x hx
    · simp at hx; subst hx; exact Nat.mod_lt _ hp

def padRecs (n : Nat) (recs : List Rec) : List Rec :=
  recs.take n ++ List.replicate n ((none : Option Nat), 0) ++ (recs.drop n).map (shiftRec n)

theorem padVals (t p n : Nat) (hp : 0 < p) (hn : 1 ≤ n) (ht : t < n) (recs : List Rec) (hN : n ≤ recs.length) :
    valsAux t p 0 (padRecs n recs) [] =
      insN n ((valsAux t p 0 (recs.take n) []).getLastD 0) (valsAux t p 0 recs []) := by
  generalize hV0 : valsAux t p 0 (recs.take n) [] = V0
  have hlen0 : V0.length = n := by
    rw [← hV0, valsAux_len]; simp; omega
  have hlt0 : ∀ x ∈ V0, x < p := hV0 ▸ valsAux_lt t p hp _ 0 [] (by simp)
  have hL : V0.getLastD 0 < p := by
    have hne : V0 ≠ [] := by intro h; rw [h] at hlen0; simp at hlen0; omega
    rw [List.getLastD_eq_getLast?]
    obtain ⟨y, hy⟩ : ∃ y, V0.getLast? = some y := by
      cases h : V0.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
      | some y => exact ⟨y, rfl⟩
    rw [hy]; exact hlt0 y (List.mem_of_getLast? hy)
  have h1 : valsAux t p 0 (padRecs n recs) [] =
      valsAux t p (n + n) ((recs.drop n).map (shiftRec n)) (V0 ++ List.replicate n (V0.getLastD 0)) := by
    unfold padRecs
    rw [valsAux_append, valsAux_append]
    simp only [List.length_append, List.length_take, List.length_replicate]
    have e : min n recs.length = n := by omega
    simp only [e, Nat.zero_add, hV0]
    rw [valsAux_none t p _ hL n n V0 (by omega) rfl]
  have h2 : valsAux t p 0 recs [] = valsAux t p n (recs.drop n) V0 := by
    rw [show valsAux t p 0 recs [] = valsAux t p 0 (recs.take n ++ recs.drop n) [] by rw [List.take_append_drop]]
    rw [valsAux_append]
    simp only [List.length_take, Nat.zero_add]
    rw [show min n recs.length = n by omega, hV0]
  have hins : V0 ++ List.replicate n (V0.getLastD 0) = insN n (V0.getLastD 0) V0 := by
    unfold insN
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
    simp
  rw [h1, hins, h2]
  exact valsAux_shift t p n _ ht (recs.drop n) n V0 (Nat.le_refl _) hlen0 (by
    rw [List.take_of_length_le (by omega)])

theorem padRecs_length (n : Nat) (recs : List Rec) (h : n ≤ recs.length) :
    (padRecs n recs).length = recs.length + n := by
  simp [padRecs]; omega

theorem padRecs_zs (n : Nat) (recs : List Rec) (h : 2 * n ≤ recs.length) :
    ((padRecs n recs).drop ((padRecs n recs).length - n)).map Prod.snd =
      (recs.drop (recs.length - n)).map Prod.snd := by
  rw [padRecs_length n recs (by omega)]
  have e : recs.length + n - n = (recs.take n ++ List.replicate n ((none : Option Nat), 0)).length +
      (recs.length - 2 * n) := by simp; omega
  unfold padRecs
  rw [e, List.drop_append]
  have hm : min n recs.length = n := by omega
  simp only [List.length_append, List.length_take, List.length_replicate, hm]
  rw [List.drop_of_length_le (by simp [hm])]
  rw [show n + n + (recs.length - 2 * n) - (n + n) = recs.length - 2 * n by omega]
  rw [List.nil_append, ← List.map_drop, List.map_map, List.drop_drop]
  have e2 : n + (recs.length - 2 * n) = recs.length - n := by omega
  rw [e2]
  have : (Prod.snd ∘ shiftRec n) = (Prod.snd : Rec → Nat) := by funext r; rfl
  rw [this]

theorem evalPass_pad (n p : Nat) (hp : 0 < p) (hn : 1 ≤ n) (recs : List Rec) (h : 2 * n ≤ recs.length)
    (t : Nat) (ht : t < n) (E : List Nat) :
    evalPass n p (padRecs n recs) t E = evalPass n p recs t E := by
  have hv := padVals t p n hp hn ht recs (by omega)
  have hlen : (valsAux t p 0 recs []).length = recs.length := by rw [valsAux_len]; simp
  have hzs := padRecs_zs n recs h
  have hpl := padRecs_length n recs (by omega)
  unfold evalPass
  simp only [hzs]
  simp only [hv, hpl, show recs.length + n - n = recs.length by omega]
  have hk : ∀ k, k < n → (insN n ((valsAux t p 0 (recs.take n) []).getLastD 0) (valsAux t p 0 recs [])).getD
      (recs.length + k) 0 = (valsAux t p 0 recs []).getD (recs.length - n + k) 0 := by
    intro k hk
    rw [show recs.length + k = (recs.length - n + k) + n by omega]
    exact insN_getD_ge n _ _ _ (by omega) (by omega)
  have hall : ((List.range n).all fun k => (insN n ((valsAux t p 0 (recs.take n) []).getLastD 0)
        (valsAux t p 0 recs [])).getD (recs.length + k) 0 == E.getD k 0)
      = (List.range n).all fun k => (valsAux t p 0 recs []).getD (recs.length - n + k) 0 == E.getD k 0 := by
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    constructor
    · intro hh k hk'; rw [← hk k hk']; exact hh k hk'
    · intro hh k hk'; rw [hk k hk']; exact hh k hk'
  rw [hall]

theorem evalC_pad (n p : Nat) (hp : 0 < p) (hn : 1 ≤ n) (recs : List Rec) (h : 2 * n ≤ recs.length) :
    evalC n p (padRecs n recs) = evalC n p recs := by
  unfold evalC
  have : ∀ (l : List Nat), (∀ t ∈ l, t < n) → ∀ st : Option (List Nat),
      l.foldl (fun st t => st.bind fun E => evalPass n p (padRecs n recs) t E) st
        = l.foldl (fun st t => st.bind fun E => evalPass n p recs t E) st := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons t l ih =>
      intro hl st
      simp only [List.foldl_cons]
      have ht : t < n := hl t (List.mem_cons_self ..)
      have : (st.bind fun E => evalPass n p (padRecs n recs) t E) = st.bind fun E => evalPass n p recs t E := by
        cases st with
        | none => rfl
        | some E => exact evalPass_pad n p hp hn recs h t ht E
      rw [this]
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
  rw [this (List.range n) (fun t ht => List.mem_range.1 ht)]

/-- Well-formed records: pointers go backwards, coefficients are below `p`. -/
def wfAux (p : Nat) : Nat → List Rec → Prop
  | _, [] => True
  | j, (u, b) :: rs => (∀ x, u = some x → x < j) ∧ b < p ∧ wfAux p (j + 1) rs

theorem wfAux_append (p : Nat) : ∀ (as bs : List Rec) (j : Nat),
    wfAux p j (as ++ bs) ↔ wfAux p j as ∧ wfAux p (j + as.length) bs
  | [], bs, j => by simp [wfAux]
  | (u, b) :: as, bs, j => by
    simp only [List.cons_append, wfAux, List.length_cons]
    rw [wfAux_append p as bs (j + 1)]
    rw [show j + (as.length + 1) = j + 1 + as.length by omega]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

theorem wfAux_none (p : Nat) (hp : 0 < p) : ∀ (k j : Nat), wfAux p j (List.replicate k ((none : Option Nat), 0))
  | 0, j => by simp [wfAux]
  | k + 1, j => by
    simp only [List.replicate_succ, wfAux]
    exact ⟨fun x hx => (by cases hx), hp, wfAux_none p hp k (j + 1)⟩

theorem wfAux_shift (p n : Nat) : ∀ (rs : List Rec) (j : Nat), wfAux p j rs → n ≤ j →
    wfAux p (j + n) (rs.map (shiftRec n))
  | [], j, _, _ => by simp [wfAux]
  | (u, b) :: rs, j, h, hj => by
    obtain ⟨h1, h2, h3⟩ := h
    simp only [List.map_cons, wfAux, shiftRec]
    refine ⟨fun x hx => ?_, h2, ?_⟩
    · cases u with
      | none => simp at hx
      | some u =>
        simp only [Option.map_some, Option.some.injEq] at hx
        have := h1 u rfl
        by_cases hu : u < n
        · simp only [hu, if_true] at hx; omega
        · simp only [hu, if_false] at hx; omega
    · rw [show j + n + 1 = (j + 1) + n by omega]
      exact wfAux_shift p n rs (j + 1) h3 (by omega)

theorem wf_pad (p n : Nat) (hp : 0 < p) (recs : List Rec) (hN : n ≤ recs.length)
    (h : wfAux p 0 recs) : wfAux p 0 (padRecs n recs) := by
  have h' : wfAux p 0 (recs.take n ++ recs.drop n) := by rw [List.take_append_drop]; exact h
  rw [wfAux_append] at h'
  obtain ⟨h1, h2⟩ := h'
  have hl : (recs.take n).length = n := by simp; omega
  rw [hl, Nat.zero_add] at h2
  unfold padRecs
  rw [wfAux_append, wfAux_append]
  simp only [List.length_append, List.length_replicate, hl, Nat.zero_add]
  exact ⟨⟨h1, wfAux_none p hp n n⟩, wfAux_shift p n _ n h2 (Nat.le_refl _)⟩

theorem mem_allRecs (p : Nat) : ∀ (k j : Nat) (recs : List Rec),
    recs ∈ allRecs p k j ↔ recs.length = k ∧ wfAux p j recs
  | 0, j, recs => by
    cases recs with
    | nil => simp [allRecs, wfAux]
    | cons r rs => simp [allRecs]
  | k + 1, j, recs => by
    cases recs with
    | nil => simp [allRecs]
    | cons r rs =>
      obtain ⟨u, b⟩ := r
      simp only [allRecs, List.mem_flatMap, List.mem_map, List.length_cons, wfAux, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨r', hr', rs', hrs', heq⟩
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨hl, hw⟩ := (mem_allRecs p k (j + 1) rs').1 hrs'
        refine ⟨hl, ?_, ?_, hw⟩
        · intro x hx
          unfold recChoices at hr'
          simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hr'
          rcases hr' with ⟨b', hb', e⟩ | ⟨u', hu', b', hb', e⟩
          · simp at e; rw [← e.1] at hx; cases hx
          · simp at e; rw [← e.1] at hx; simp at hx; omega
        · unfold recChoices at hr'
          simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at hr'
          rcases hr' with ⟨b', hb', e⟩ | ⟨u', hu', b', hb', e⟩
          · simp at e; omega
          · simp at e; omega
      · rintro ⟨hl, h1, h2, hw⟩
        refine ⟨(u, b), ?_, rs, (mem_allRecs p k (j + 1) rs).2 ⟨hl, hw⟩, rfl⟩
        unfold recChoices
        simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range]
        cases u with
        | none => exact Or.inl ⟨b, h2, rfl⟩
        | some x => exact Or.inr ⟨x, h1 x rfl, b, h2, rfl⟩

theorem hasCircuit_iff (pr : Nat → Nat) (c n : Nat) :
    hasCircuit pr c n = true ↔ ∃ recs : List Rec, recs.length = c * n ∧ wfAux (pr n) 0 recs ∧
      evalC n (pr n) recs = true := by
  unfold hasCircuit
  rw [List.any_eq_true]
  constructor
  · rintro ⟨recs, hm, he⟩
    obtain ⟨hl, hw⟩ := (mem_allRecs _ _ _ _).1 hm
    exact ⟨recs, hl, hw, he⟩
  · rintro ⟨recs, hl, hw, he⟩
    exact ⟨recs, (mem_allRecs _ _ _ _).2 ⟨hl, hw⟩, he⟩

/-- Padding: one more round of records preserves the existence of a circuit. -/
theorem hasCircuit_pad (pr : Nat → Nat) (c n : Nat) (hc : 2 ≤ c) (hn : 1 ≤ n) (hp : 0 < pr n)
    (h : hasCircuit pr c n = true) : hasCircuit pr (c + 1) n = true := by
  obtain ⟨recs, hl, hw, he⟩ := (hasCircuit_iff pr c n).1 h
  have h2n : 2 * n ≤ recs.length := by rw [hl]; exact Nat.mul_le_mul_right n hc
  refine (hasCircuit_iff pr (c + 1) n).2 ⟨padRecs n recs, ?_, wf_pad _ n hp recs (by omega) hw, ?_⟩
  · rw [padRecs_length n recs (by omega), hl]; rw [Nat.add_mul]; simp
  · rw [evalC_pad n _ hp hn recs h2n]; exact he

end ZP
