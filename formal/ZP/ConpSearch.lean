module

public import ZP.AllDefs

@[expose] public section

namespace ZP

theorem aux_pre : ∀ (T : Nat) (R : List Bool) (tape : Nat → Option Bool) (h top : Nat) (D used : List Bool),
    ∃ s, (runChoiceAux T R tape h top D used).2 = used ++ s ∧ s.length ≤ T := by
  intro T
  induction T with
  | zero => intros; exact ⟨[], by simp [runChoiceAux]⟩
  | succ T ih =>
    intro R tape h top D used
    simp only [runChoiceAux]
    split
    · split
      · split
        · obtain ⟨s, hs, hl⟩ := ih _ _ _ _ D (used ++ [D.getD used.length true])
          exact ⟨D.getD used.length true :: s, by rw [hs]; simp, by simp; omega⟩
        · obtain ⟨s, hs, hl⟩ := ih _ _ _ _ D used
          exact ⟨s, hs, by omega⟩
      · obtain ⟨s, hs, hl⟩ := ih _ _ _ _ D used
        exact ⟨s, hs, by omega⟩
    · exact ⟨[], by simp⟩

theorem aux_agree : ∀ (T : Nat) (R : List Bool) (tape : Nat → Option Bool) (h top : Nat) (D used : List Bool),
    (∀ i < used.length, used[i]? = some (D.getD i true)) →
    ∀ i < (runChoiceAux T R tape h top D used).2.length,
      (runChoiceAux T R tape h top D used).2[i]? = some (D.getD i true) := by
  intro T
  induction T with
  | zero => intro R tape h top D used hu i hi; simpa [runChoiceAux] using hu i (by simpa [runChoiceAux] using hi)
  | succ T ih =>
    intro R tape h top D used hu
    simp only [runChoiceAux]
    split
    · split
      · split
        · apply ih
          intro i hi
          rw [List.getElem?_append]
          split
          · exact hu i ‹_›
          · have : i = used.length := by simp at hi; omega
            subst this; simp
        · exact ih _ _ _ _ D used hu
      · exact ih _ _ _ _ D used hu
    · simpa using hu

theorem aux_congr (k : Nat) (D1 D2 : List Bool) (hk : ∀ i < k, D1.getD i true = D2.getD i true) :
    ∀ (T : Nat) (R : List Bool) (tape : Nat → Option Bool) (h top : Nat) (used : List Bool),
    (runChoiceAux T R tape h top D1 used).2.length ≤ k →
    runChoiceAux T R tape h top D2 used = runChoiceAux T R tape h top D1 used := by
  intro T
  induction T with
  | zero => intros; rfl
  | succ T ih =>
    intro R tape h top used hl
    simp only [runChoiceAux] at hl ⊢
    by_cases h2 : (rotN (iota (tape h)) R).getD 2 false = true
    · simp only [h2, ↓reduceIte] at hl ⊢
      by_cases h1 : (rotN (iota (tape h)) R).getD 1 false = true
      · simp only [h1, ↓reduceIte] at hl ⊢
        by_cases h3 : top < h + 1
        · simp only [h3, ↓reduceIte] at hl ⊢
          obtain ⟨s, hs, _⟩ := aux_pre T _ _ _ _ D1 (used ++ [D1.getD used.length true])
          have hlt : used.length < k := by rw [hs] at hl; simp at hl; omega
          rw [← hk _ hlt]
          exact ih _ _ _ _ _ hl
        · simp only [h3, ↓reduceIte] at hl ⊢
          exact ih _ _ _ _ _ hl
      · simp only [h1, ↓reduceIte] at hl ⊢
        exact ih _ _ _ _ _ hl
    · simp only [h2, ↓reduceIte] at hl ⊢
      rfl

theorem used_len (P x : List Bool) (T : Nat) (D : List Bool) :
    (runChoice P x T D).2.length ≤ T := by
  obtain ⟨s, hs, hl⟩ := aux_pre T (rot (P.reverse ++ [false])) (fun i => x[i]?) 0 (x.length - 1) D []
  unfold runChoice; rw [hs]; simpa using hl

theorem used_agree (P x : List Bool) (T : Nat) (D : List Bool) :
    ∀ i < (runChoice P x T D).2.length, (runChoice P x T D).2[i]? = some (D.getD i true) :=
  aux_agree T _ _ _ _ D [] (by simp)

theorem run_congr (P x : List Bool) (T : Nat) (D1 D2 : List Bool) (k : Nat)
    (hk : ∀ i < k, D1.getD i true = D2.getD i true)
    (hl : (runChoice P x T D1).2.length ≤ k) :
    runChoice P x T D2 = runChoice P x T D1 :=
  aux_congr k D1 D2 hk T _ _ _ _ [] hl

theorem used_up (P x : List Bool) (T : Nat) (D1 D2 : List Bool) (k : Nat)
    (hk : ∀ i < k, D1.getD i true = D2.getD i true)
    (hl : k + 1 ≤ (runChoice P x T D1).2.length) :
    k + 1 ≤ (runChoice P x T D2).2.length := by
  refine Classical.byContradiction fun hc => ?_
  have := run_congr P x T D2 D1 k (fun i hi => (hk i hi).symm) (by omega)
  rw [this] at hl; omega

/-! ### binary values -/

def val : List Bool → Nat
  | [] => 0
  | b :: l => b.toNat * 2 ^ l.length + val l

theorem val_append (l r : List Bool) : val (l ++ r) = val l * 2 ^ r.length + val r := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    simp only [List.cons_append, val, List.length_append, Nat.pow_add, ih]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    simp only [val, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem val_inj : ∀ (p q : List Bool), p.length = q.length → val p = val q → p = q
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: p, c :: q, h, hv => by
    have hl : p.length = q.length := by simpa using h
    have h1 := val_lt p
    have h2 := val_lt q
    simp only [val, hl] at hv h1
    have hb : b = c := by
      cases b <;> cases c <;> simp at hv ⊢ <;> omega
    subst hb
    have : val p = val q := by cases b <;> simp at hv <;> omega
    rw [val_inj p q hl this]

theorem val_rep_true (m : Nat) : val (List.replicate m true) + 1 = 2 ^ m := by
  induction m with
  | zero => simp [val]
  | succ m ih => simp [List.replicate_succ, val, Nat.pow_succ]; omega

theorem val_rep_false (m : Nat) : val (List.replicate m false) = 0 := by
  induction m with
  | zero => simp [val]
  | succ m ih => simp [List.replicate_succ, val, ih]

def padv (L : Nat) (D : List Bool) : Nat := val ((D ++ List.replicate L true).take L)

def nxt (U : List Bool) : Option (List Bool) :=
  match U.reverse.dropWhile (· == false) with | [] => none | _ :: r => some (r.reverse ++ [false])

def acc (P x : List Bool) (T : Nat) (Dl : List Bool) : Prop :=
  ∃ D, padv (T+1) D ≤ padv (T+1) Dl ∧ (runChoice P x T D).1 = true

theorem pad_len (D : List Bool) (n : Nat) : ((D ++ List.replicate n true).take n).length = n := by
  simp

theorem pad_eq (D : List Bool) (n : Nat) (h : D.length ≤ n) :
    (D ++ List.replicate n true).take n = D ++ List.replicate (n - D.length) true := by
  rw [List.take_append, List.take_of_length_le h]
  simp [List.take_replicate]

theorem pad_get (D : List Bool) (n i : Nat) (hi : i < n) :
    ((D ++ List.replicate n true).take n)[i]? = some (D.getD i true) := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_append]
  split
  · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rename_i h
    have : D[i]? = none := by simp; omega
    simp [List.getD_eq_getElem?_getD, this, List.getElem?_replicate]
    omega

theorem blk (x v s q : Nat) (hs : s < q) (h1 : v * q ≤ x * q + s) (h2 : x * q + s < v * q + q) : x = v := by
  rcases Nat.lt_trichotomy x v with h | h | h
  · have := Nat.mul_le_mul_right q (show x + 1 ≤ v by omega)
    rw [Nat.succ_mul] at this; omega
  · exact h
  · have := Nat.mul_le_mul_right q (show v + 1 ≤ x by omega)
    rw [Nat.succ_mul] at this; omega

theorem prefix_of_range (U D : List Bool) (n : Nat) (hn : U.length ≤ n)
    (h1 : val U * 2 ^ (n - U.length) ≤ padv n D)
    (h2 : padv n D < val U * 2 ^ (n - U.length) + 2 ^ (n - U.length)) :
    ∀ i < U.length, U[i]? = some (D.getD i true) := by
  intro i hi
  have hWl := pad_len D n
  have hgt := pad_get D n i
  have hpv : padv n D = val ((D ++ List.replicate n true).take n) := rfl
  generalize (D ++ List.replicate n true).take n = W at hWl hgt hpv
  have hsd : (W.drop U.length).length = n - U.length := by simp [hWl]
  have hv : val W = val (W.take U.length) * 2 ^ (n - U.length) + val (W.drop U.length) := by
    have := val_append (W.take U.length) (W.drop U.length)
    rw [List.take_append_drop] at this
    rw [this, hsd]
  have hlt := val_lt (W.drop U.length)
  rw [hsd] at hlt
  have hP : val (W.take U.length) = val U := by
    apply blk _ _ _ _ hlt
    · omega
    · omega
  have hPU : W.take U.length = U := by
    apply val_inj _ _ _ hP
    simp [hWl]; omega
  rw [← hgt (by omega), ← hPU, List.getElem?_take_of_lt hi]

theorem dropWhile_decomp : ∀ (R : List Bool) (x : Bool) (r : List Bool),
    R.dropWhile (· == false) = x :: r → ∃ j, R = List.replicate j false ++ x :: r ∧ x = true
  | [], x, r, h => by simp at h
  | b :: R, x, r, h => by
    cases b
    · simp [List.dropWhile_cons] at h
      obtain ⟨j, hj, hx⟩ := dropWhile_decomp R x r (by simpa using h)
      exact ⟨j + 1, by simp [List.replicate_succ, hj], hx⟩
    · simp [List.dropWhile_cons] at h
      obtain ⟨h1, h2⟩ := h
      exact ⟨0, by simp [h1, h2], h1⟩

theorem dropWhile_nil : ∀ (R : List Bool), R.dropWhile (· == false) = [] → ∀ b ∈ R, b = false
  | [], _, b, hb => by simp at hb
  | c :: R, h, b, hb => by
    cases c
    · simp [List.dropWhile_cons] at h
      rcases List.mem_cons.mp hb with h' | h'
      · exact h'
      · exact dropWhile_nil R h b h'
    · simp [List.dropWhile_cons] at h

theorem used_pad (P x : List Bool) (T : Nat) (Dl : List Bool)
    (hup : Dl.length ≤ (runChoice P x T Dl).2.length) :
    (Dl ++ List.replicate (T+1) true).take (T+1) =
      (runChoice P x T Dl).2 ++ List.replicate (T + 1 - (runChoice P x T Dl).2.length) true := by
  have hag := used_agree P x T Dl
  have hlen := used_len P x T Dl
  generalize (runChoice P x T Dl).2 = U at hup hag hlen ⊢
  have hU : U = Dl ++ List.replicate (U.length - Dl.length) true := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < U.length
    · rw [hag i hi, List.getElem?_append]
      split
      · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      · rename_i h
        have hn : Dl[i]? = none := List.getElem?_eq_none (by omega)
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hn]
        omega
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  rw [pad_eq _ _ (by omega)]
  have : List.replicate (T + 1 - Dl.length) true =
      List.replicate (U.length - Dl.length) true ++ List.replicate (T + 1 - U.length) true := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [this, ← List.append_assoc, ← hU]

theorem padv_used (P x : List Bool) (T : Nat) (Dl : List Bool)
    (hup : Dl.length ≤ (runChoice P x T Dl).2.length) :
    padv (T+1) Dl + 1 =
      (val (runChoice P x T Dl).2 + 1) * 2 ^ (T + 1 - (runChoice P x T Dl).2.length) := by
  have h := used_pad P x T Dl hup
  unfold padv; rw [h, val_append]
  have := val_rep_true (T + 1 - (runChoice P x T Dl).2.length)
  rw [List.length_replicate]
  rw [Nat.add_mul]; omega

theorem run_of_prefix (P x : List Bool) (T : Nat) (Dl D : List Bool)
    (hag : ∀ i < (runChoice P x T Dl).2.length, (runChoice P x T Dl).2[i]? = some (D.getD i true)) :
    runChoice P x T D = runChoice P x T Dl := by
  apply run_congr P x T Dl D (runChoice P x T Dl).2.length _ (Nat.le_refl _)
  intro i hi
  have h1 := used_agree P x T Dl i hi
  have h2 := hag i hi
  rw [h1] at h2
  exact Option.some.inj h2

theorem dfs_true (P x : List Bool) (T : Nat) (Dl : List Bool)
    (h : (runChoice P x T Dl).1 = true) : acc P x T Dl := ⟨Dl, Nat.le_refl _, h⟩

theorem dfs_none (P x : List Bool) (T : Nat) (Dl : List Bool)
    (hup : Dl.length ≤ (runChoice P x T Dl).2.length)
    (hf : (runChoice P x T Dl).1 = false) (hn : nxt (runChoice P x T Dl).2 = none) :
    ¬ acc P x T Dl := by
  rintro ⟨D, hD, hr⟩
  have hpv := padv_used P x T Dl hup
  have hlen := used_len P x T Dl
  have hrun := run_of_prefix P x T Dl D
  generalize (runChoice P x T Dl).2 = U at hpv hlen hrun hn hup
  have hv : val U = 0 := by
    unfold nxt at hn
    split at hn
    · rename_i hd
      have h0 := dropWhile_nil _ hd
      have : U = List.replicate U.length false := by
        apply List.eq_replicate_iff.mpr
        refine ⟨rfl, ?_⟩
        intro b hb
        have := h0 b (List.mem_reverse.mpr hb)
        simpa using this
      rw [this, val_rep_false]
    · simp at hn
  rw [hv, Nat.zero_add, Nat.one_mul] at hpv
  have hpre := prefix_of_range U D (T+1) (by omega) (by rw [hv, Nat.zero_mul]; exact Nat.zero_le _) (by
    rw [hv, Nat.zero_mul, Nat.zero_add]; omega)
  have := hrun hpre
  rw [this] at hr
  rw [hf] at hr
  exact Bool.false_ne_true hr

theorem dfs_some (P x : List Bool) (T : Nat) (Dl Dl' : List Bool)
    (hup : Dl.length ≤ (runChoice P x T Dl).2.length)
    (hf : (runChoice P x T Dl).1 = false) (hn : nxt (runChoice P x T Dl).2 = some Dl') :
    (acc P x T Dl ↔ acc P x T Dl') ∧ padv (T+1) Dl' < padv (T+1) Dl ∧
      Dl'.length ≤ (runChoice P x T Dl').2.length := by
  have hpv := padv_used P x T Dl hup
  have hlen := used_len P x T Dl
  have hrun := run_of_prefix P x T Dl
  have hag := used_agree P x T Dl
  have hupd := used_up P x T Dl
  generalize (runChoice P x T Dl).2 = U at hpv hlen hrun hn hup hag hupd
  -- structure of U
  obtain ⟨A, j, hUA, hDl'⟩ : ∃ A j, U = A ++ true :: List.replicate j false ∧ Dl' = A ++ [false] := by
    unfold nxt at hn
    split at hn
    · simp at hn
    · rename_i y r hd
      obtain ⟨j, hj, hy⟩ := dropWhile_decomp _ _ _ hd
      refine ⟨r.reverse, j, ?_, ?_⟩
      · have := congrArg List.reverse hj
        simp [hy] at this
        simp [this]
      · simpa using hn.symm
  subst hDl'
  have hlU : U.length = A.length + 1 + j := by rw [hUA]; simp; omega
  have hvU : val U = val A * (2 ^ j * 2) + 2 ^ j := by
    rw [hUA, val_append]
    simp [val, val_rep_false, Nat.pow_succ]
  have hpad' : padv (T+1) (A ++ [false]) + 1 =
      (val A * 2) * (2 ^ j * 2 ^ (T + 1 - U.length)) + 2 ^ j * 2 ^ (T + 1 - U.length) := by
    unfold padv
    rw [pad_eq _ _ (by simp; omega), val_append]
    have hr := val_rep_true (T + 1 - (A ++ [false]).length)
    have e : T + 1 - (A ++ [false]).length = j + (T + 1 - U.length) := by simp; omega
    rw [e, Nat.pow_add] at hr
    rw [List.length_replicate, e, Nat.pow_add]
    have : val (A ++ [false]) = val A * 2 := by simp [val_append, val]
    rw [this]
    omega
  have hkey : padv (T+1) (A ++ [false]) + 1 = val U * 2 ^ (T + 1 - U.length) := by
    rw [hpad', hvU]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hq : 0 < 2 ^ (T + 1 - U.length) := Nat.two_pow_pos _
  rw [Nat.add_mul, Nat.one_mul] at hpv
  have hdlt : padv (T+1) (A ++ [false]) < padv (T+1) Dl := by omega
  refine ⟨⟨?_, fun ⟨D, hD, hr⟩ => ⟨D, Nat.le_trans hD (Nat.le_of_lt hdlt), hr⟩⟩, hdlt, ?_⟩
  · rintro ⟨D, hD, hr⟩
    by_cases hc : padv (T+1) D ≤ padv (T+1) (A ++ [false])
    · exact ⟨D, hc, hr⟩
    · exfalso
      have hpre := prefix_of_range U D (T+1) (by omega) (by omega) (by omega)
      rw [hrun D hpre, hf] at hr
      exact Bool.false_ne_true hr
  · have hk : ∀ i < A.length, Dl.getD i true = (A ++ [false]).getD i true := by
      intro i hi
      have h1 := hag i (by omega)
      rw [hUA, List.getElem?_append_left hi] at h1
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, h1]
    have := hupd (A ++ [false]) A.length hk (by omega)
    simpa using this

theorem top_iff (P x : List Bool) (T : Nat) : runND P x T ↔ acc (core P) x T [] := by
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, ?_, hD⟩
    have h1 := val_lt ((D ++ List.replicate (T+1) true).take (T+1))
    rw [pad_len] at h1
    have h2 := val_rep_true (T+1)
    unfold padv
    rw [List.nil_append, List.take_replicate]
    simp only [Nat.min_self]
    omega
  · rintro ⟨D, _, hD⟩
    exact ⟨D, hD⟩

end ZP
