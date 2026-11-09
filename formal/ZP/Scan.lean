module

public import ZP.Gad

@[expose] public section

/-!
# Checking a tape

The guest program built for an input `x` (`ZP/Dx.lean`) runs on an arbitrary
certificate tape. These gadgets either read the tape as expected or reach a
rejecting row (`Rej`), from which the machine can only answer `false`.

* `xrows x`: the tape starts with `encR x` and a separator.
* `vgotoRows i`: the tape starts with the layout of `i` stacks; the head stops on the
  first cell of the last separator.
-/

namespace ZP.Cx

/-- From this configuration the machine reaches a row that rejects. -/
def Rej (M : Mach) (q : Nat) (L R : List Bool) : Prop :=
  ∃ q' L' R' T, Lead M q L R q' L' R' T ∧ M.act q' R'.head? = .halt false

theorem Rej.of_lead {M : Mach} {q q1 : Nat} {L R L1 R1 : List Bool} {T : Nat}
    (h : Lead M q L R q1 L1 R1 T) (r : Rej M q1 L1 R1) : Rej M q L R := by
  obtain ⟨q', L', R', T', h', ha⟩ := r
  exact ⟨q', L', R', T + T', h.trans h', ha⟩

theorem rej_at {M : Mach} {base j : Nat} {rows : List (Act × Act × Act)} {L R : List Bool}
    (hs : Sub M base rows) (h : (rows[j]?).map (fun r => pick r R.head?) = some (.halt false)) :
    Rej M (base + j) L R :=
  ⟨_, _, _, 0, Lead.refl, hs.act' h⟩

theorem zexec_mono (M : Mach) (F q : Nat) (L R : List Bool) (b : Bool)
    (h : zexec M F q L R = some b) (F' : Nat) (hF : F ≤ F') : zexec M F' q L R = some b := by
  rw [← exec_z] at h ⊢
  exact exec_mono M F q _ _ b h F' hF

theorem Rej.never {M : Mach} {q : Nat} {L R : List Bool} (r : Rej M q L R) (F : Nat) :
    zexec M F q L R ≠ some true := by
  intro h
  obtain ⟨q', L', R', T, hl, ha⟩ := r
  have h1 := zexec_mono M F q L R true h (max F (T + 1)) (Nat.le_max_left _ _)
  have h2 := hl.halts ha (max F (T + 1)) (Nat.lt_of_lt_of_le (Nat.lt_succ_self T) (Nat.le_max_right _ _))
  rw [h1] at h2
  cases h2

/-! ## The input check -/

def bitRow : Bool → Nat → Act × Act × Act
  | false, q => (H, .go false true q, H)
  | true, q => (H, H, .go true true q)

def xrows (f e : Nat) : List Bool → List (Act × Act × Act)
  | [] => [(H, .go false true (f + 1), H), (H, H, .go true false e)]
  | b :: x => [(H, H, .go true true (f + 1)), bitRow b (f + 2)] ++ xrows (f + 2) e x

theorem length_xrows (e : Nat) : ∀ (x : List Bool) (f : Nat), (xrows f e x).length = 2 * x.length + 2
  | [], _ => rfl
  | b :: x, f => by
    show ([(H, H, .go true true (f + 1)), bitRow b (f + 2)] ++ xrows (f + 2) e x).length = _
    rw [List.length_append, length_xrows e x (f + 2)]
    simp only [List.length_cons, List.length_nil]
    omega

theorem xchk_ok {M : Mach} {e : Nat} : ∀ (x : List Bool) (f : Nat) (L R : List Bool),
    Sub M f (xrows f e x) →
    (∃ rest, R = encR x ++ false :: true :: rest ∧
      Lead M f L R e ((encR x).reverse ++ L) (false :: true :: rest) (2 * x.length + 2)) ∨
    Rej M f L R
  | [], f, L, R, hs => by
    have hs : Sub M f [(H, .go false true (f + 1), H), (H, H, .go true false e)] := hs
    match R with
    | [] => exact Or.inr (rej_at (j := 0) hs rfl)
    | true :: _ => exact Or.inr (rej_at (j := 0) hs rfl)
    | false :: [] =>
      refine Or.inr (Rej.of_lead (q1 := f + 1) (L1 := false :: L) (R1 := []) (T := 1) ?_
        (rej_at hs rfl))
      zz; exact Lead.refl
    | false :: false :: R2 =>
      refine Or.inr (Rej.of_lead (q1 := f + 1) (L1 := false :: L) (R1 := false :: R2) (T := 1) ?_
        (rej_at hs rfl))
      zz; exact Lead.refl
    | false :: true :: rest =>
      refine Or.inl ⟨rest, rfl, ?_⟩
      have h : Lead M f L (false :: true :: rest) e L (false :: true :: rest) 2 := by
        zz; zz; exact Lead.refl
      exact h
  | b :: x, f, L, R, hs => by
    have hs1 : Sub M f [(H, H, .go true true (f + 1)), bitRow b (f + 2)] := hs.left
    have hs2 : Sub M (f + 2) (xrows (f + 2) e x) := hs.at rfl
    have cont : ∀ R2, Lead M f L (true :: b :: R2) (f + 2) (b :: true :: L) R2 2 →
        (∃ rest, true :: b :: R2 = encR (b :: x) ++ false :: true :: rest ∧
          Lead M f L (true :: b :: R2) e ((encR (b :: x)).reverse ++ L) (false :: true :: rest)
            (2 * (b :: x).length + 2)) ∨ Rej M f L (true :: b :: R2) := by
      intro R2 h2
      rcases xchk_ok x (f + 2) (b :: true :: L) R2 hs2 with ⟨rest, hR, h3⟩ | r
      · refine Or.inl ⟨rest, by rw [hR]; simp, (h2.trans h3).re rfl (by simp) rfl ?_⟩
        simp only [List.length_cons]
        omega
      · exact Or.inr (Rej.of_lead h2 r)
    match R with
    | [] => exact Or.inr (rej_at (j := 0) hs1 rfl)
    | false :: _ => exact Or.inr (rej_at (j := 0) hs1 rfl)
    | true :: [] =>
      refine Or.inr (Rej.of_lead (q1 := f + 1) (L1 := true :: L) (R1 := []) (T := 1) ?_ ?_)
      · zz; exact Lead.refl
      · cases b <;> exact rej_at hs1 rfl
    | true :: c :: R2 =>
      cases b <;> cases c
      · exact cont R2 (by zz; zz; exact Lead.refl)
      · refine Or.inr (Rej.of_lead (q1 := f + 1) (L1 := true :: L) (R1 := true :: R2) (T := 1) ?_
          (rej_at hs1 rfl))
        zz; exact Lead.refl
      · refine Or.inr (Rej.of_lead (q1 := f + 1) (L1 := true :: L) (R1 := false :: R2) (T := 1) ?_
          (rej_at hs1 rfl))
        zz; exact Lead.refl
      · exact cont R2 (by zz; zz; exact Lead.refl)

/-! ## The layout check -/

def vskipRows (s n : Nat) (last : Bool) : List (Act × Act × Act) :=
  [(H, .go false true (s + 2), .go true true (s + 1)), same true s, (H, H, .go true (!last) n)]

section vs
variable {M : Mach} {s n : Nat} {last : Bool}

theorem vdata (hs : Sub M s (vskipRows s n last)) : ∀ (R L : List Bool),
    (∃ st X, R = encR st ++ false :: true :: X ∧
      Lead M s L R (s + 2) (false :: ((encR st).reverse ++ L)) (true :: X) (2 * st.length + 1)) ∨
    Rej M s L R
  | [], L => Or.inr (rej_at (j := 0) hs rfl)
  | [true], L => by
    refine Or.inr (Rej.of_lead (q1 := s + 1) (L1 := true :: L) (R1 := []) (T := 1) ?_
      (rej_at hs rfl))
    zz; exact Lead.refl
  | [false], L => by
    refine Or.inr (Rej.of_lead (q1 := s + 2) (L1 := false :: L) (R1 := []) (T := 1) ?_
      (rej_at hs rfl))
    zz; exact Lead.refl
  | true :: b :: R', L => by
    have h2 : Lead M s L (true :: b :: R') s (b :: true :: L) R' 2 := by
      cases b <;> (zz; zz; exact Lead.refl)
    rcases vdata hs R' (b :: true :: L) with ⟨st, X, hR, h3⟩ | r
    · refine Or.inl ⟨b :: st, X, by rw [hR]; simp, (h2.trans h3).re rfl (by simp) rfl ?_⟩
      simp only [List.length_cons]
      omega
    · exact Or.inr (Rej.of_lead h2 r)
  | false :: false :: R', L => by
    refine Or.inr (Rej.of_lead (q1 := s + 2) (L1 := false :: L) (R1 := false :: R') (T := 1) ?_
      (rej_at hs rfl))
    zz; exact Lead.refl
  | false :: true :: R', L => by
    refine Or.inl ⟨[], R', rfl, ?_⟩
    have h : Lead M s L (false :: true :: R') (s + 2) (false :: L) (true :: R') 1 := by
      zz; exact Lead.refl
    exact h

end vs

theorem vskip_ok {M : Mach} {s n : Nat} (hs : Sub M s (vskipRows s n false)) (R L : List Bool) :
    (∃ st X, R = encR st ++ false :: true :: X ∧
      Lead M s L R n ((encR st ++ [false, true]).reverse ++ L) X (2 * st.length + 2)) ∨
    Rej M s L R := by
  rcases vdata hs R L with ⟨st, X, hR, h1⟩ | r
  · refine Or.inl ⟨st, X, hR, ?_⟩
    have h2 : Lead M (s + 2) (false :: ((encR st).reverse ++ L)) (true :: X) n
        (true :: false :: ((encR st).reverse ++ L)) X 1 := by
      zz; exact Lead.refl
    exact (h1.trans h2).re rfl (by simp) rfl (by omega)
  · exact Or.inr r

theorem vskipL_ok {M : Mach} {s n : Nat} (hs : Sub M s (vskipRows s n true)) (R L : List Bool) :
    (∃ st X, R = encR st ++ false :: true :: X ∧
      Lead M s L R n ((encR st).reverse ++ L) (false :: true :: X) (2 * st.length + 2)) ∨
    Rej M s L R := by
  rcases vdata hs R L with ⟨st, X, hR, h1⟩ | r
  · refine Or.inl ⟨st, X, hR, ?_⟩
    have h2 : Lead M (s + 2) (false :: ((encR st).reverse ++ L)) (true :: X) n
        ((encR st).reverse ++ L) (false :: true :: X) 1 := by
      zz; exact Lead.refl
    exact (h1.trans h2).re rfl rfl rfl (by omega)
  · exact Or.inr r

def vgotoRows (s e : Nat) : Nat → List (Act × Act × Act)
  | 0 => []
  | 1 => vskipRows s e true
  | i + 2 => vskipRows s (s + 3) false ++ vgotoRows (s + 3) e (i + 1)

theorem length_vgotoRows (s e : Nat) : ∀ i, (vgotoRows s e i).length = 3 * i
  | 0 => rfl
  | 1 => rfl
  | i + 2 => by
    show (vskipRows s (s + 3) false ++ vgotoRows (s + 3) e (i + 1)).length = _
    rw [List.length_append, length_vgotoRows (s + 3) e (i + 1)]
    simp only [vskipRows, List.length_cons, List.length_nil]
    omega

theorem vgoto_ok {M : Mach} {e : Nat} : ∀ (i s : Nat), Sub M s (vgotoRows s e (i + 1)) →
    ∀ (R L : List Bool),
      (∃ P X, P.length = i + 1 ∧ R = lay P ++ X ∧
        Lead M s L R e ((layI P).reverse ++ L) (false :: true :: X) (lay P).length) ∨
      Rej M s L R
  | 0, s, hs, R, L => by
    rcases vskipL_ok (n := e) hs R L with ⟨st, X, hR, h⟩ | r
    · refine Or.inl ⟨[st], X, rfl, by rw [hR]; simp, h.re rfl (by simp [layI]) rfl ?_⟩
      simp [length_encR] <;> omega
    · exact Or.inr r
  | i + 1, s, hs, R, L => by
    have hs' : Sub M s (vskipRows s (s + 3) false ++ vgotoRows (s + 3) e (i + 1)) := hs
    rcases vskip_ok hs'.left R L with ⟨st, X1, hR, h1⟩ | r
    · rcases vgoto_ok i (s + 3) (hs'.at rfl) X1 ((encR st ++ [false, true]).reverse ++ L) with
        ⟨P, X, hP, hX, h2⟩ | r
      · have hne : P ≠ [] := by
          intro h0; rw [h0] at hP; simp at hP
        obtain ⟨st', P', rfl⟩ : ∃ st' P', P = st' :: P' := by
          cases P with
          | nil => exact absurd rfl hne
          | cons a b => exact ⟨a, b, rfl⟩
        refine Or.inl ⟨st :: st' :: P', X, by simp at hP ⊢; omega, by rw [hR, hX]; simp, ?_⟩
        refine (h1.trans h2).re rfl ?_ rfl ?_
        · simp [layI]
        · simp [length_encR] <;> omega
      · exact Or.inr (Rej.of_lead h1 r)
    · exact Or.inr r

/-! ## Separators fix the regions -/

theorem encR_sep_inj : ∀ (a b r r' : List Bool),
    encR a ++ false :: true :: r = encR b ++ false :: true :: r' → a = b ∧ r = r'
  | [], [], r, r', h => by simpa using h
  | [], c :: b, r, r', h => by simp at h
  | c :: a, [], r, r', h => by simp at h
  | c :: a, d :: b, r, r', h => by
    simp only [encR_cons, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hc, h⟩ := h
    obtain ⟨h1, h2⟩ := encR_sep_inj a b r r' h
    exact ⟨by rw [hc, h1], h2⟩

end ZP.Cx
