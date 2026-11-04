module

public import ZP.UG
public import ZP.PNP

@[expose] public section

/-!
# `L ∈ NP`

The verifier `vm 10 UG` reads the pair tape of `s` and `c`, which is the layout of the
two stacks `[s, c]`. It appends eleven empty stacks, returns to cell 0, runs the
compiled interpreter `UG` (`frag_ok`, `ug_ok`) and answers whether stack 0 is
nonempty. Its running time on certificates of length `|s| + 1` is below
`(|s| + 2)^200` (`total_lt`).
-/

namespace ZP.Cx

/-! ## Appending empty stacks -/

/-- Write `m + 1` separators `0 1` on blank cells, then step back onto the last one. -/
def sepRows (s e : Nat) : Nat → List (Act × Act × Act)
  | 0 => [anyA false true (s + 1), anyA true false e]
  | m + 1 => [anyA false true (s + 1), anyA true true (s + 2)] ++ sepRows (s + 2) e m

theorem length_sepRows (s e : Nat) : ∀ m, (sepRows s e m).length = 2 * m + 2
  | 0 => rfl
  | m + 1 => by
    show ([anyA false true (s + 1), anyA true true (s + 2)] ++ sepRows (s + 2) e m).length = _
    rw [List.length_append, length_sepRows (s + 2) e m]
    simp only [List.length_cons, List.length_nil]
    omega

/-- The cells left of the head after writing `m` full separators (reversed). -/
def sepL : Nat → List Bool
  | 0 => []
  | m + 1 => sepL m ++ [true, false]

theorem length_sepL : ∀ m, (sepL m).length = 2 * m
  | 0 => rfl
  | m + 1 => by simp [sepL, length_sepL m] <;> omega

theorem sep_ok {M : Mach} {e : Nat} : ∀ (m s : Nat) (L : List Bool), Sub M s (sepRows s e m) →
    Lead M s L [] e (sepL m ++ L) [false, true] (2 * m + 2)
  | 0, s, L, hs => by
    have hs : Sub M s [anyA false true (s + 1), anyA true false e] := hs
    have h : Lead M s L [] e L [false, true] 2 := by
      zz; zz; exact Lead.refl
    exact h
  | m + 1, s, L, hs => by
    have hs' : Sub M s ([anyA false true (s + 1), anyA true true (s + 2)] ++ sepRows (s + 2) e m) :=
      hs
    have h1 : Lead M s L [] (s + 2) (true :: false :: L) [] 2 := by
      have hs : Sub M s [anyA false true (s + 1), anyA true true (s + 2)] := hs'.left
      zz; zz; exact Lead.refl
    have h2 := sep_ok m (s + 2) (true :: false :: L) (hs'.at rfl)
    exact (h1.trans h2).re rfl (by simp [sepL]) rfl (by omega)

theorem lay_rep : ∀ m, lay (List.replicate (m + 1) []) = (sepL m).reverse ++ [false, true]
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, lay_cons, lay_rep m]
    simp [sepL]

/-! ## The verifier -/

def vrows (m : Nat) (p : Cmd) : List (Act × Act × Act) :=
  gotoRows 0 6 2 ++ sepRows 6 (2 * m + 8) m ++ retRows (2 * m + 8) (2 * m + 28) ++
    frag (m + 3) p (2 * m + 28) (2 * m + 28 + flen (m + 3) p) ++ [(H, .halt false, .halt true)]

def vm (m : Nat) (p : Cmd) : Mach := ⟨vrows m p⟩

theorem vm_sub (m : Nat) (p : Cmd) : Sub (vm m p) 0 (vrows m p) := fun j r h => by
  rw [Nat.zero_add]; exact h

theorem lay_x (x y : List Bool) (m : Nat) :
    lay (x :: y :: List.replicate (m + 1) []) = lay [x, y] ++ ((sepL m).reverse ++ [false, true]) := by
  rw [show x :: y :: List.replicate (m + 1) [] = [x, y] ++ List.replicate (m + 1) [] from rfl,
    lay_append, lay_rep]

theorem vm_ok (m : Nat) {p : Cmd} (hok : Ok (m + 3) p) {x y : List Bool}
    {S' : List (List Bool)} {t : Nat} (h : Exec p (x :: y :: List.replicate (m + 1) []) S' t)
    (F : Nat) (hF : 8 * (lay [x, y]).length + 16 * (m + 3) +
      40 * t * ((lay [x, y]).length + 2 * (m + 3) + 2 * t + 2) < F) :
    exec (vm m p) F 0 (inTape (lay [x, y])) 0 = some (decide (S'.getD 0 [] ≠ [])) := by
  have hs := vm_sub m p
  have h1s : Sub (vm m p) 0 (gotoRows 0 6 2) := hs.left.left.left.left
  have h2s : Sub (vm m p) 6 (sepRows 6 (2 * m + 8) m) :=
    hs.left.left.left.at (by rw [length_gotoRows])
  have h3s : Sub (vm m p) (2 * m + 8) (retRows (2 * m + 8) (2 * m + 28)) :=
    hs.left.left.at (by rw [List.length_append, length_gotoRows, length_sepRows] <;> omega)
  have h4s : Sub (vm m p) (2 * m + 28) (frag (m + 3) p (2 * m + 28) (2 * m + 28 + flen (m + 3) p)) :=
    hs.left.at (by
      rw [List.length_append, List.length_append, length_gotoRows, length_sepRows,
        length_retRows] <;> omega)
  have h5s : Sub (vm m p) (2 * m + 28 + flen (m + 3) p) [(H, .halt false, .halt true)] :=
    hs.at (by
      rw [List.length_append, List.length_append, List.length_append, length_gotoRows,
        length_sepRows, length_retRows, length_frag] <;> omega)
  have g1 := goto 2 0 (by omega) h1s [x, y] [] [] rfl
  have g2 := sep_ok m 6 ((lay [x, y]).reverse ++ []) h2s
  have g3 := ret h3s (sepL m ++ ((lay [x, y]).reverse ++ [])) false true []
  have hlay : (sepL m ++ ((lay [x, y]).reverse ++ [])).reverse ++ [false, true] =
      lay (x :: y :: List.replicate (m + 1) []) ++ [] := by
    rw [lay_x]; simp
  have hlen : (lay (x :: y :: List.replicate (m + 1) [])).length =
      (lay [x, y]).length + 2 * m + 2 := by
    rw [lay_x]; simp [length_sepL] <;> omega
  obtain ⟨X', T4, hT4, g4⟩ := frag_ok (by omega) h (by simp) hok (vm m p) (2 * m + 28)
    (2 * m + 28 + flen (m + 3) p) h4s
    ((lay [x, y]).length + 2 * (m + 3) + 2 * t + 2) [] (by omega)
  have chain := ((((g1.trans g2).trans g3).re rfl rfl hlay rfl).trans g4).ri rfl
    (List.append_nil _)
  have hS'len : S'.length = (m + 2) + 1 := by
    rw [h.len]; simp only [List.length_cons, List.length_replicate] <;> omega
  have hact : (vm m p).act (2 * m + 28 + flen (m + 3) p) (lay S' ++ X').head? =
      .halt (decide (S'.getD 0 [] ≠ [])) := by
    refine (h5s.act (j := 0) (r := (H, .halt false, .halt true)) rfl _).trans ?_
    obtain ⟨st, S'', rfl⟩ := exists_cons hS'len
    cases st with
    | nil => simp [pick]
    | cons b st => simp [pick]
  rw [inTape_z]
  refine (exec_z (vm m p) F 0 [] (lay [x, y])).trans (chain.halts hact F ?_)
  have hL : (sepL m ++ ((lay [x, y]).reverse ++ [])).length = 2 * m + (lay [x, y]).length := by
    simp [length_sepL]
  rw [hL]
  omega

/-! ## Membership in `L` -/

theorem mem_strings : ∀ (n : Nat) (c : List Bool), c ∈ strings n ↔ c.length = n
  | 0, c => by cases c <;> simp [strings]
  | n + 1, c => by
    cases c with
    | nil => simp [strings]
    | cons b c => cases b <;> simp [strings, mem_strings n]

theorem inL_iff (s : List Bool) :
    inL s = true ↔ ∃ c, c.length = s.length + 1 ∧ run s c (s.length + 1) = true := by
  unfold inL
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, hr⟩; exact ⟨c, (mem_strings _ c).mp hc, hr⟩
  · rintro ⟨c, hc, hr⟩; exact ⟨c, (mem_strings _ c).mpr hc, hr⟩

/-- `Ok` as a boolean test. -/
def okb (k : Nat) : Cmd → Bool
  | .push i _ => decide (i < k)
  | .pop i => decide (i < k)
  | .cs i a b c => decide (i < k) && okb k a && okb k b && okb k c
  | .seq p q => okb k p && okb k q
  | .wh i _ _ _ p => decide (i < k) && okb k p
  | .skip => true

theorem okb_ok (k : Nat) : ∀ c, okb k c = true → Ok k c
  | .push i _, h => by simp only [okb, decide_eq_true_eq] at h; exact h
  | .pop i, h => by simp only [okb, decide_eq_true_eq] at h; exact h
  | .cs i a b c, h => by
    simp only [okb, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, okb_ok k a h.1.1.2, okb_ok k b h.1.2, okb_ok k c h.2⟩
  | .seq p q, h => by
    simp only [okb, Bool.and_eq_true] at h
    exact ⟨okb_ok k p h.1, okb_ok k q h.2⟩
  | .wh i _ _ _ p, h => by
    simp only [okb, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, okb_ok k p h.2⟩
  | .skip, _ => trivial

theorem ok_UG : Ok 13 UG := okb_ok 13 UG (by decide)

/-! ## The time bound -/

section bounds
variable {Q : Nat}

theorem qmul {a b p q : Nat} (ha : a ≤ Q ^ p) (hb : b ≤ Q ^ q) : a * b ≤ Q ^ (p + q) := by
  rw [Nat.pow_add]; exact Nat.mul_le_mul ha hb

theorem qadd {a b p : Nat} (hQ : 2 ≤ Q) (ha : a ≤ Q ^ p) (hb : b ≤ Q ^ p) :
    a + b ≤ Q ^ (p + 1) := by
  have h1 : Q ^ (p + 1) = Q ^ p * Q := by rw [Nat.pow_succ]
  have h2 := Nat.mul_le_mul_left (Q ^ p) hQ
  omega

theorem qup {a p q : Nat} (hQ : 1 ≤ Q) (ha : a ≤ Q ^ p) (h : p ≤ q) : a ≤ Q ^ q :=
  Nat.le_trans ha (Nat.pow_le_pow_right hQ h)

theorem q1 {a : Nat} (ha : a ≤ Q) : a ≤ Q ^ 1 := by rw [Nat.pow_one]; exact ha

end bounds

theorem total_Q (n t Q : Nat) (lin : 128 * (n + 2) ≤ Q) (ht : t ≤ ugB n (n + 1)) :
    8 * (4 * n + 6) + 16 * (10 + 3) + 40 * t * (4 * n + 6 + 2 * (10 + 3) + 2 * t + 2) ≤ Q ^ 23 := by
  have hQ2 : 2 ≤ Q := by omega
  have hQ1 : 1 ≤ Q := by omega
  have hR : rB (n + 1) ≤ Q ^ 3 := by
    unfold rB
    have a : (n + 1 + 3) * (8 * (n + 1) + 8) ≤ Q ^ 2 :=
      qmul (q1 (show n + 1 + 3 ≤ Q by omega)) (q1 (show 8 * (n + 1) + 8 ≤ Q by omega))
    have b : 2 * (n + 1) + 3 ≤ Q ^ 2 := qup hQ1 (q1 (by omega)) (by omega)
    have c : _ ≤ Q ^ 3 := qadd hQ2 a b
    omega
  have hS : stepB (n + 1) (n + 1) + 2 ≤ Q ^ 7 := by
    unfold stepB
    have a : rB (n + 1) + 2 ≤ Q ^ 4 := qadd hQ2 hR (qup hQ1 (q1 (show 2 ≤ Q by omega)) (by omega))
    have b : (n + 1 + 4) * (rB (n + 1) + 2) ≤ Q ^ 5 := qmul (q1 (show n + 1 + 4 ≤ Q by omega)) a
    have c : 2 * (n + 1) + 42 ≤ Q ^ 5 := qup hQ1 (q1 (by omega)) (by omega)
    have d : _ ≤ Q ^ 6 := qadd hQ2 b c
    have e : Q ^ 6 ≤ Q ^ 7 := Nat.pow_le_pow_right hQ1 (by omega)
    omega
  have hU : ugB n (n + 1) ≤ Q ^ 10 := by
    unfold ugB
    have p : (n + 1) * (stepB (n + 1) (n + 1) + 2) ≤ Q ^ 8 :=
      qmul (q1 (show n + 1 ≤ Q by omega)) hS
    have r : rB (n + 1) ≤ Q ^ 8 := qup hQ1 hR (by omega)
    have l : 64 * n + 64 ≤ Q ^ 9 := qup hQ1 (q1 (by omega)) (by omega)
    have s1 : _ ≤ Q ^ 9 := qadd hQ2 r p
    have s2 : _ ≤ Q ^ 10 := qadd hQ2 s1 l
    omega
  have ht' : t ≤ Q ^ 10 := Nat.le_trans ht hU
  have w : 4 * n + 6 + 2 * (10 + 3) + 2 * t + 2 ≤ Q ^ 11 := by
    have h1 : 4 * n + 34 ≤ Q ^ 10 := qup hQ1 (q1 (by omega)) (by omega)
    have h2 : Q ^ 11 = Q ^ 10 * Q := Nat.pow_succ
    have h3 := Nat.mul_le_mul_left (Q ^ 10) (show 3 ≤ Q by omega)
    omega
  have v : 40 * t ≤ Q ^ 11 := qmul (q1 (show 40 ≤ Q by omega)) ht'
  have pr : 40 * t * (4 * n + 6 + 2 * (10 + 3) + 2 * t + 2) ≤ Q ^ 22 := qmul v w
  have li : 8 * (4 * n + 6) + 16 * (10 + 3) ≤ Q ^ 22 := qup hQ1 (q1 (by omega)) (by omega)
  exact qadd hQ2 li pr


theorem lin8 (n : Nat) : 128 * (n + 2) ≤ (n + 2) ^ 8 := by
  have h7 : 128 ≤ (n + 2) ^ 7 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 7
    simpa using this
  have hm := Nat.mul_le_mul_right (n + 2) h7
  rw [← Nat.pow_succ] at hm
  exact hm

theorem total_lt (n t a : Nat) (ha : a = 4 * n + 6) (ht : t ≤ ugB n (n + 1)) :
    8 * a + 16 * (10 + 3) + 40 * t * (a + 2 * (10 + 3) + 2 * t + 2) < (n + 2) ^ 200 := by
  subst ha
  have h := total_Q n t _ (lin8 n) ht
  rw [← Nat.pow_mul] at h
  exact Nat.lt_of_le_of_lt h
    (Nat.pow_lt_pow_right (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 n)) (by decide))

/-! ## `L ∈ NP` -/

theorem pairTape_lay (x c : List Bool) : pairTape x c = inTape (lay [x, c]) := rfl

theorem length_lay2 (x c : List Bool) :
    (lay [x, c]).length = 2 * x.length + 2 * c.length + 4 := by
  simp [length_encR] <;> omega

theorem Lp_InNP : InNP Lp := by
  refine ⟨vm 10 UG, 200, 1, fun x => ?_⟩
  unfold Lp
  rw [inL_iff]
  constructor
  · rintro ⟨c, hc, hr⟩
    obtain ⟨S', ⟨t, ht, hE⟩, -, hiff⟩ := ug_ok x c
    have hE' : Exec UG (x :: c :: List.replicate (10 + 1) []) S' t := hE
    refine ⟨c, ?_, ?_⟩
    · have : x.length + 2 ≤ (x.length + 2) ^ 200 := by
        have := Nat.pow_le_pow_right (show 0 < x.length + 2 by omega) (show 1 ≤ 200 by decide)
        rwa [Nat.pow_one] at this
      rw [Nat.one_mul, hc]
      exact Nat.le_trans (Nat.le_succ _) this
    · rw [pairTape_lay, vm_ok 10 ok_UG hE' _ (total_lt x.length t _
        (by rw [length_lay2, hc]; omega) (by rw [hc] at ht; exact ht))]
      exact congrArg some (decide_eq_true (hiff.mpr ⟨hc, hr⟩))
  · rintro ⟨c, -, he⟩
    obtain ⟨S', ⟨t, -, hE⟩, -, hiff⟩ := ug_ok x c
    have hE' : Exec UG (x :: c :: List.replicate (10 + 1) []) S' t := hE
    let B := 8 * (lay [x, c]).length + 16 * (10 + 3) +
      40 * t * ((lay [x, c]).length + 2 * (10 + 3) + 2 * t + 2)
    have h1 := exec_mono _ _ _ _ _ _ he (max ((x.length + 2) ^ 200) (B + 1)) (Nat.le_max_left _ _)
    rw [pairTape_lay, vm_ok 10 ok_UG hE' (max ((x.length + 2) ^ 200) (B + 1))
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))] at h1
    have h2 : S'.getD 0 [] ≠ [] := of_decide_eq_true (Option.some.inj h1)
    obtain ⟨hc, hr⟩ := hiff.mp h2
    exact ⟨c, hc, hr⟩

end ZP.Cx
