module

public import ZP.Zx

@[expose] public section

/-!
# Gadgets on the pair layout

A list of stacks `S` is laid out from cell 0 as `lay S`: for each stack its bits
top first, each bit `b` as the two cells `1 b`, then the separator `0 1`. Cells
after the last separator are junk. Every gadget starts and ends at cell 0.

* `tramp`: two dummy steps, so every fragment has its entry at its base row.
* `gotoRows`: walk to the start of region `i`.
* `testRows`: read the top of the region and return, to one of three exits.
* `pushRows`: shift the rest of the layout right by two cells, inserting `1 b`.
-/

namespace ZP.Cx

def anyA (w r : Bool) (q : Nat) : Act × Act × Act := (.go w r q, .go w r q, .go w r q)

theorem pick_same (r : Bool) (q : Nat) (v : Bool) : pick (same r q) (some v) = .go v r q := by
  cases v <;> rfl

theorem pick_any (w r : Bool) (q : Nat) (s : Option Bool) : pick (anyA w r q) s = .go w r q := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

section steps
variable {M : Mach} {base j : Nat} {rows : List (Act × Act × Act)} {q' q2 T : Nat}
  {L R L2 R2 : List Bool}

theorem Lead.sR (hs : Sub M base rows) {v : Bool} (h : rows[j]? = some (same true q'))
    (rest : Lead M q' (v :: L) R q2 L2 R2 T) : Lead M (base + j) L (v :: R) q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) (v :: R).head? = .go v true q' := by
      rw [hs.act h]; exact pick_same true q' v
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goR hA]
    exact rest F

theorem Lead.sL (hs : Sub M base rows) {v b : Bool} {l : List Bool}
    (h : rows[j]? = some (same false q')) (rest : Lead M q' l (b :: v :: R) q2 L2 R2 T) :
    Lead M (base + j) (b :: l) (v :: R) q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) (v :: R).head? = .go v false q' := by
      rw [hs.act h]; exact pick_same false q' v
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL hA]
    exact rest F

theorem Lead.sL0 (hs : Sub M base rows) {v : Bool} (h : rows[j]? = some (same false q'))
    (rest : Lead M q' [] (v :: R) q2 L2 R2 T) : Lead M (base + j) [] (v :: R) q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) (v :: R).head? = .go v false q' := by
      rw [hs.act h]; exact pick_same false q' v
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL0 hA]
    exact rest F

theorem Lead.aR (hs : Sub M base rows) {w : Bool} (h : rows[j]? = some (anyA w true q'))
    (rest : Lead M q' (w :: L) R.tail q2 L2 R2 T) : Lead M (base + j) L R q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) R.head? = .go w true q' := by
      rw [hs.act h]; exact pick_any w true q' _
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goR hA]
    exact rest F

theorem Lead.aL (hs : Sub M base rows) {w b : Bool} {l : List Bool}
    (h : rows[j]? = some (anyA w false q')) (rest : Lead M q' l (b :: w :: R.tail) q2 L2 R2 T) :
    Lead M (base + j) (b :: l) R q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) R.head? = .go w false q' := by
      rw [hs.act h]; exact pick_any w false q' _
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL hA]
    exact rest F

theorem Lead.aL0 (hs : Sub M base rows) {w : Bool} (h : rows[j]? = some (anyA w false q'))
    (rest : Lead M q' [] (w :: R.tail) q2 L2 R2 T) : Lead M (base + j) [] R q2 L2 R2 (T + 1) :=
  fun F => by
    have hA : M.act (base + j) R.head? = .go w false q' := by
      rw [hs.act h]; exact pick_any w false q' _
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL0 hA]
    exact rest F

end steps

theorem Lead.re {M : Mach} {q q' q2 : Nat} {L R L' R' L2 R2 : List Bool} {T T2 : Nat}
    (h : Lead M q L R q' L' R' T) (e1 : q' = q2) (e2 : L' = L2) (e3 : R' = R2) (e4 : T = T2) :
    Lead M q L R q2 L2 R2 T2 := by
  subst e1 e2 e3 e4; exact h

theorem Lead.ri {M : Mach} {q q' : Nat} {L R L1 R1 L' R' : List Bool} {T : Nat}
    (h : Lead M q L R q' L' R' T) (e1 : L = L1) (e2 : R = R1) : Lead M q L1 R1 q' L' R' T := by
  subst e1 e2; exact h

theorem Sub.at {M : Mach} {base b' : Nat} {A B : List (Act × Act × Act)}
    (hs : Sub M base (A ++ B)) (h : base + A.length = b') : Sub M b' B := h ▸ hs.right

set_option hygiene false in
/-- One step of a gadget whose rows are `Sub M base _` under the name `hs`. -/
macro "zz" : tactic => `(tactic| first
  | (apply Lead.pR hs; rfl) | (apply Lead.pL hs; rfl) | (apply Lead.pL0 hs; rfl)
  | (apply Lead.sR hs; rfl) | (apply Lead.sL hs; rfl) | (apply Lead.sL0 hs; rfl)
  | (apply Lead.aR hs; rfl) | (apply Lead.aL hs; rfl) | (apply Lead.aL0 hs; rfl)
  | (apply Lead.pR (j := 0) hs; rfl) | (apply Lead.pL (j := 0) hs; rfl)
  | (apply Lead.pL0 (j := 0) hs; rfl)
  | (apply Lead.sR (j := 0) hs; rfl) | (apply Lead.sL (j := 0) hs; rfl)
  | (apply Lead.sL0 (j := 0) hs; rfl)
  | (apply Lead.aR (j := 0) hs; rfl) | (apply Lead.aL (j := 0) hs; rfl)
  | (apply Lead.aL0 (j := 0) hs; rfl))

theorem exists_cons {α : Type} {l : List α} {n : Nat} (h : l.length = n + 1) :
    ∃ a t, l = a :: t := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl⟩

/-! ## The layout -/

def encR (st : List Bool) : List Bool := st.flatMap fun b => [true, b]

def lay : List (List Bool) → List Bool
  | [] => []
  | st :: S => encR st ++ false :: true :: lay S

@[simp] theorem encR_nil : encR [] = [] := rfl

@[simp] theorem encR_cons (b : Bool) (st : List Bool) : encR (b :: st) = true :: b :: encR st := by
  simp [encR]

@[simp] theorem lay_nil : lay [] = [] := rfl

@[simp] theorem lay_cons (st : List Bool) (S : List (List Bool)) :
    lay (st :: S) = encR st ++ false :: true :: lay S := rfl

theorem lay_append : ∀ S T : List (List Bool), lay (S ++ T) = lay S ++ lay T
  | [], _ => rfl
  | st :: S, T => by simp [lay_append S T]

theorem length_encR : ∀ st : List Bool, (encR st).length = 2 * st.length
  | [] => rfl
  | b :: st => by simp [length_encR st]; omega

theorem length_lay : ∀ S : List (List Bool), (lay S).length = 2 * (S.map List.length).sum + 2 * S.length
  | [] => rfl
  | st :: S => by simp [length_encR, length_lay S]; omega

theorem lay_two (S : List (List Bool)) (hS : S ≠ []) (X : List Bool) :
    ∃ v1 v2 R, lay S ++ X = v1 :: v2 :: R := by
  obtain ⟨st, S', rfl⟩ : ∃ st S', S = st :: S' := by
    cases S with
    | nil => exact absurd rfl hS
    | cons st S' => exact ⟨st, S', rfl⟩
  cases st with
  | nil => exact ⟨false, true, lay S' ++ X, by simp⟩
  | cons b st => exact ⟨true, b, encR st ++ false :: true :: lay S' ++ X, by simp⟩

/-- The layout without its last separator. -/
def layI : List (List Bool) → List Bool
  | [] => []
  | [st] => encR st
  | st :: st' :: S => encR st ++ false :: true :: layI (st' :: S)

theorem lay_layI : ∀ S : List (List Bool), S ≠ [] → lay S = layI S ++ [false, true]
  | [], h => absurd rfl h
  | [st], _ => by simp [layI]
  | st :: st' :: S, _ => by
    rw [lay_cons, lay_layI (st' :: S) (by simp)]
    simp [layI]

/-! ## Trampoline -/

def tramp (s n : Nat) : List (Act × Act × Act) := [same true (s + 1), same false n]

theorem tramp_ok {M : Mach} {s n : Nat} (hs : Sub M s (tramp s n)) (v1 v2 : Bool) (R : List Bool) :
    Lead M s [] (v1 :: v2 :: R) n [] (v1 :: v2 :: R) 2 := by
  zz; zz; exact Lead.refl

/-! ## Walking to a region -/

def skipRows (s n : Nat) : List (Act × Act × Act) :=
  [(H, .go false true (s + 2), .go true true (s + 1)), same true s, same true n]

theorem skip_data {M : Mach} {s n : Nat} (hs : Sub M s (skipRows s n)) :
    ∀ (st L X : List Bool), Lead M s L (encR st ++ X) s ((encR st).reverse ++ L) X (2 * st.length)
  | [], L, X => Lead.refl
  | b :: st, L, X => by
    have h1 : Lead M s L (true :: b :: (encR st ++ X)) s (b :: true :: L) (encR st ++ X) 2 := by
      cases b <;> (zz; zz; exact Lead.refl)
    exact ((h1.trans (skip_data hs st (b :: true :: L) X)).ri rfl (by simp)).re rfl
      (by simp) rfl (by first | omega | (simp <;> omega))

theorem skip_sep {M : Mach} {s n : Nat} (hs : Sub M s (skipRows s n)) (L X : List Bool) :
    Lead M s L (false :: true :: X) n (true :: false :: L) X 2 := by
  zz; zz; exact Lead.refl

theorem skip_region {M : Mach} {s n : Nat} (hs : Sub M s (skipRows s n)) (st L X : List Bool) :
    Lead M s L (encR st ++ false :: true :: X) n ((encR st ++ [false, true]).reverse ++ L) X
      (2 * st.length + 2) :=
  ((skip_data hs st L _).trans (skip_sep hs _ X)).re rfl (by simp) rfl rfl

def gotoRows (s e : Nat) : Nat → List (Act × Act × Act)
  | 0 => []
  | i + 1 => skipRows s (if i = 0 then e else s + 3) ++ gotoRows (s + 3) e i

theorem length_gotoRows (s e : Nat) : ∀ i, (gotoRows s e i).length = 3 * i
  | 0 => rfl
  | i + 1 => by simp [gotoRows, skipRows, length_gotoRows (s + 3) e i]; omega

theorem goto {M : Mach} {e : Nat} : ∀ (i s : Nat), 0 < i → Sub M s (gotoRows s e i) →
    ∀ (P : List (List Bool)) (L X : List Bool), P.length = i →
      Lead M s L (lay P ++ X) e ((lay P).reverse ++ L) X (lay P).length
  | 0, _, h, _, _, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | i + 1, s, _, hs, P, L, X, hP => by
    obtain ⟨st, P', rfl⟩ := exists_cons hP
    have hs1 : Sub M s (skipRows s (if i = 0 then e else s + 3)) := hs.left
    have hs2 : Sub M (s + 3) (gotoRows (s + 3) e i) := hs.at rfl
    have h1 := skip_region hs1 st L (lay P' ++ X)
    by_cases hi : i = 0
    · subst hi
      have hP' : P' = [] := List.eq_nil_of_length_eq_zero (by simp at hP ⊢; omega)
      subst hP'
      rw [if_pos rfl] at h1
      exact (h1.ri rfl (by simp)).re rfl (by simp) (by simp) (by simp [length_encR])
    · rw [if_neg hi] at h1
      have h2 := goto i (s + 3) (by omega) hs2 P' ((encR st ++ [false, true]).reverse ++ L) X
        (by simp at hP ⊢; omega)
      exact ((h1.trans h2).ri rfl (by simp)).re rfl (by simp) rfl (by first | omega | (simp [length_encR] <;> omega))

/-- Trampoline and walk: the prefix of every operation on region `i`, entering the
operation's rows at `ent`. -/
def preRows (s i ent : Nat) : List (Act × Act × Act) :=
  tramp s (if i = 0 then ent else s + 2) ++ gotoRows (s + 2) ent i

theorem length_preRows (s i ent : Nat) : (preRows s i ent).length = 3 * i + 2 := by
  simp [preRows, tramp, length_gotoRows]

theorem pre_ok {M : Mach} {s i ent : Nat} (hs : Sub M s (preRows s i ent))
    (S : List (List Bool)) (hi : i < S.length) (X : List Bool) :
    Lead M s [] (lay S ++ X) ent (lay (S.take i)).reverse (lay (S.drop i) ++ X)
      ((lay (S.take i)).length + 2) := by
  have hS : S ≠ [] := by intro h; subst h; simp at hi
  obtain ⟨v1, v2, R, hR⟩ := lay_two S hS X
  have ht := tramp_ok (hs.left) v1 v2 R
  rw [← hR] at ht
  have hsplit : lay S ++ X = lay (S.take i) ++ (lay (S.drop i) ++ X) := by
    rw [← List.append_assoc, ← lay_append, List.take_append_drop]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl] at ht
    exact (ht.re rfl (by simp) (by simp) (by simp))
  · rw [if_neg h0] at ht
    have hg := goto i (s + 2) (by omega) (hs.at rfl) (S.take i) [] (lay (S.drop i) ++ X)
      (by first | omega | (simp <;> omega))
    rw [← hsplit] at hg
    exact (ht.trans hg).re rfl (by simp) rfl (by omega)

/-! ## Testing a top -/

def testRows (s ee ef et : Nat) : List (Act × Act × Act) :=
  [(H, .go false true (s + 2), .go true true (s + 1)),
   (H, .go false false (s + 3), .go true false (s + 23)),
   same false (s + 43)] ++ retRows (s + 3) ef ++ retRows (s + 23) et ++ retRows (s + 43) ee

/-- The exit of `testRows` for a stack. -/
def tsel (ee ef et : Nat) : List Bool → Nat
  | [] => ee
  | false :: _ => ef
  | true :: _ => et

theorem test_ok {M : Mach} {s ee ef et : Nat} (hs : Sub M s (testRows s ee ef et))
    (st L X : List Bool) :
    Lead M s L (encR st ++ false :: true :: X) (tsel ee ef et st) []
      (L.reverse ++ encR st ++ false :: true :: X) (7 * L.length + 8) := by
  have hr1 : Sub M (s + 3) (retRows (s + 3) ef) := hs.left.left.at rfl
  have hr2 : Sub M (s + 23) (retRows (s + 23) et) := hs.left.at rfl
  have hr3 : Sub M (s + 43) (retRows (s + 43) ee) := hs.at rfl
  have hs : Sub M s [(H, .go false true (s + 2), .go true true (s + 1)),
      (H, .go false false (s + 3), .go true false (s + 23)), same false (s + 43)] :=
    hs.left.left.left
  cases st with
  | nil =>
    have h1 : Lead M s L (false :: true :: X) (s + 43) L (false :: true :: X) 2 := by
      zz; zz; exact Lead.refl
    exact ((h1.trans (ret hr3 L false true X)).ri rfl (by simp)).re rfl rfl (by simp) (by omega)
  | cons b st =>
    cases b with
    | false =>
      have h1 : Lead M s L (true :: false :: (encR st ++ false :: true :: X)) (s + 3) L
          (true :: false :: (encR st ++ false :: true :: X)) 2 := by
        zz; zz; exact Lead.refl
      exact ((h1.trans (ret hr1 L true false _)).ri rfl (by simp)).re rfl rfl (by simp)
        (by omega)
    | true =>
      have h1 : Lead M s L (true :: true :: (encR st ++ false :: true :: X)) (s + 23) L
          (true :: true :: (encR st ++ false :: true :: X)) 2 := by
        zz; zz; exact Lead.refl
      exact ((h1.trans (ret hr2 L true true _)).ri rfl (by simp)).re rfl rfl (by simp)
        (by omega)

/-! ## Pushing -/

/-- One region of the right shift. States `0..3`: at a pair, carrying `u1 u2`;
`4, 5`: second cell of a bit pair; `6, 7`: second cell of a separator. -/
def blockRows (s n : Nat) : List (Act × Act × Act) :=
  [ (H, .go false true (s + 6), .go false true (s + 4)),
    (H, .go false true (s + 7), .go false true (s + 5)),
    (H, .go true true (s + 6), .go true true (s + 4)),
    (H, .go true true (s + 7), .go true true (s + 5)),
    (H, .go false true (s + 2), .go false true (s + 3)),
    (H, .go true true (s + 2), .go true true (s + 3)),
    (H, .go false true n, .go false true (n + 1)),
    (H, .go true true n, .go true true (n + 1)) ]

/-- Write the carried separator past the end, then return. -/
def finRows (f e : Nat) : List (Act × Act × Act) :=
  [anyA false true (f + 2), anyA false true (f + 3), anyA false false (f + 4),
   anyA true false (f + 4)] ++ retRows (f + 4) e

def pushRows (s e : Nat) : Nat → List (Act × Act × Act)
  | 0 => finRows s e
  | c + 1 => blockRows s (s + 8) ++ pushRows (s + 8) e c

def p0 (s : Nat) (u1 u2 : Bool) : Nat := s + (2 * bn u1 + bn u2)

theorem push_dat {M : Mach} {s n : Nat} (hs : Sub M s (blockRows s n)) (u1 u2 v : Bool)
    (L X : List Bool) :
    Lead M (p0 s u1 u2) L (true :: v :: X) (p0 s true v) (u2 :: u1 :: L) X 2 := by
  cases u1 <;> cases u2 <;> cases v <;> (zz; zz; exact Lead.refl)

theorem push_sep {M : Mach} {s n : Nat} (hs : Sub M s (blockRows s n)) (u1 u2 : Bool)
    (L X : List Bool) :
    Lead M (p0 s u1 u2) L (false :: true :: X) (n + 1) (u2 :: u1 :: L) X 2 := by
  cases u1 <;> cases u2 <;> (zz; zz; exact Lead.refl)

theorem push_region {M : Mach} {s n : Nat} (hs : Sub M s (blockRows s n)) :
    ∀ (st : List Bool) (u1 u2 : Bool) (L X : List Bool),
      Lead M (p0 s u1 u2) L (encR st ++ false :: true :: X) (n + 1)
        ((u1 :: u2 :: encR st).reverse ++ L) X (2 * st.length + 2)
  | [], u1, u2, L, X => (push_sep hs u1 u2 L X).re rfl (by simp) rfl rfl
  | v :: st, u1, u2, L, X =>
    (((push_dat hs u1 u2 v L _).trans (push_region hs st true v (u2 :: u1 :: L) X)).ri rfl
      (by simp)).re rfl (by simp) rfl (by first | omega | (simp <;> omega))

theorem push_blocks {M : Mach} (e : Nat) : ∀ (c s : Nat) (Q : List (List Bool)),
    Q.length = c + 1 → Sub M s (pushRows s e (c + 1)) → ∀ (u1 u2 : Bool) (L X : List Bool),
      Lead M (p0 s u1 u2) L (layI Q ++ false :: true :: X) (s + 8 * (c + 1) + 1)
        ((u1 :: u2 :: layI Q).reverse ++ L) X ((layI Q).length + 2)
  | 0, s, Q, hQ, hs, u1, u2, L, X => by
    obtain ⟨st, Q', rfl⟩ := exists_cons hQ
    have hQ' : Q' = [] := List.eq_nil_of_length_eq_zero (by simpa using hQ)
    subst hQ'
    have hb : Sub M s (blockRows s (s + 8)) := hs.left
    exact (push_region hb st u1 u2 L X).re (by omega) (by simp [layI]) rfl
      (by simp [layI, length_encR])
  | c + 1, s, Q, hQ, hs, u1, u2, L, X => by
    obtain ⟨st, Q', rfl⟩ := exists_cons hQ
    obtain ⟨st', Q'', rfl⟩ := exists_cons (n := c) (by simpa using hQ)
    have hb : Sub M s (blockRows s (s + 8)) := hs.left
    have hr : Sub M (s + 8) (pushRows (s + 8) e (c + 1)) := hs.at rfl
    have h1 := push_region hb st u1 u2 L (layI (st' :: Q'') ++ false :: true :: X)
    have h2 := push_blocks e c (s + 8) (st' :: Q'') (by simp at hQ ⊢; omega) hr false true
      ((u1 :: u2 :: encR st).reverse ++ L) X
    exact ((h1.trans h2).ri rfl (by simp [layI])).re (by omega) (by simp [layI]) rfl
      (by first | omega | (simp [layI, length_encR] <;> omega))

theorem push_fin {M : Mach} {f e : Nat} (hs : Sub M f (finRows f e)) (L X : List Bool) :
    Lead M (f + 1) L X e [] (L.reverse ++ false :: true :: X.drop 2) (7 * L.length + 8) := by
  have hr : Sub M (f + 4) (retRows (f + 4) e) := hs.at rfl
  have hs : Sub M f [anyA false true (f + 2), anyA false true (f + 3), anyA false false (f + 4),
      anyA true false (f + 4)] := hs.left
  have h1 : Lead M (f + 1) L X (f + 4) L (false :: true :: X.tail.tail) 2 := by
    zz; zz; exact Lead.refl
  have e2 : X.tail.tail = X.drop 2 := by
    cases X with
    | nil => rfl
    | cons a X => cases X <;> rfl
  rw [e2] at h1
  exact (h1.trans (ret hr L false true _)).re rfl rfl rfl (by omega)

end ZP.Cx
