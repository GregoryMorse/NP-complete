module

public import ZP.Gad

@[expose] public section

/-!
# The pop gadget

At the start of a region holding at least one bit, every later pair moves two
cells left (`popBlk`, one region at a time); the two cells after the new last
separator become junk. An empty region is left alone.
-/

namespace ZP.Cx

/-- Copy the pairs of one region two cells left. `0, 1`: step right twice; `2`: read
`v1`; `3, 4`: read `v2`; `5..8`, `9..12`: step back; `13..16`: write `v1`;
`17, 18`: write `v2` and go on; `19, 20`: write `v2` after a separator, to `n`. -/
def popBlk (b n : Nat) : List (Act × Act × Act) :=
  [ same true (b + 1), same true (b + 2),
    (H, .go false true (b + 3), .go true true (b + 4)),
    (H, .go false false (b + 5), .go true false (b + 6)),
    (H, .go false false (b + 7), .go true false (b + 8)),
    same false (b + 9), same false (b + 10), same false (b + 11), same false (b + 12),
    same false (b + 13), same false (b + 14), same false (b + 15), same false (b + 16),
    anyA false true (b + 19), anyA false true (b + 20),
    anyA true true (b + 17), anyA true true (b + 18),
    anyA false true b, anyA true true b,
    anyA false true n, anyA true true n ]

theorem pop_d1 {M : Mach} {b n : Nat} (hs : Sub M b (popBlk b n)) (a0 a1 v : Bool)
    (L Y : List Bool) :
    Lead M (b + 1) (a0 :: L) (a1 :: true :: v :: Y) b (v :: true :: L) (true :: v :: Y) 7 := by
  cases v <;> (zz; zz; zz; zz; zz; zz; zz; exact Lead.refl)

theorem pop_s1 {M : Mach} {b n : Nat} (hs : Sub M b (popBlk b n)) (a0 a1 v : Bool)
    (L Y : List Bool) :
    Lead M (b + 1) (a0 :: L) (a1 :: false :: v :: Y) n (v :: false :: L) (false :: v :: Y) 7 := by
  cases v <;> (zz; zz; zz; zz; zz; zz; zz; exact Lead.refl)

theorem pop_c0 {M : Mach} {b n : Nat} (hs : Sub M b (popBlk b n)) (a0 : Bool) (L R : List Bool)
    {q2 : Nat} {L2 R2 : List Bool} {T : Nat} (h : Lead M (b + 1) (a0 :: L) R q2 L2 R2 T) :
    Lead M b L (a0 :: R) q2 L2 R2 (T + 1) := by
  exact Lead.sR (j := 0) (q' := b + 1) hs rfl h

/-- From the second cell of the pair being overwritten. -/
theorem pop_region1 {M : Mach} {b n : Nat} (hs : Sub M b (popBlk b n)) :
    ∀ (st : List Bool) (a0 a1 : Bool) (L Y : List Bool),
      Lead M (b + 1) (a0 :: L) (a1 :: encR st ++ false :: true :: Y) n
        ((encR st ++ [false, true]).reverse ++ L) (false :: true :: Y) (8 * st.length + 7)
  | [], a0, a1, L, Y => (pop_s1 hs a0 a1 true L Y).re rfl (by simp) rfl rfl
  | v :: st, a0, a1, L, Y => by
    have h1 := pop_d1 hs a0 a1 v L (encR st ++ false :: true :: Y)
    have h2 := pop_c0 hs true (v :: true :: L) _ (pop_region1 hs st true v (v :: true :: L) Y)
    exact ((h1.trans h2).ri rfl (by simp)).re rfl (by simp) rfl
      (by first | omega | (simp <;> omega))

def popBlocks (b e : Nat) : Nat → List (Act × Act × Act)
  | 0 => retRows b e
  | c + 1 => popBlk b (b + 21) ++ popBlocks (b + 21) e c

theorem pop_blocks {M : Mach} (e : Nat) : ∀ (c b : Nat) (Q : List (List Bool)), Q.length = c →
    Sub M b (popBlocks b e c) → ∀ (L Y : List Bool),
      ∃ T, T ≤ 7 * L.length + 6 + 22 * (lay Q).length ∧
        Lead M b L (false :: true :: lay Q ++ Y) e [] (L.reverse ++ lay Q ++ false :: true :: Y) T
  | 0, b, Q, hQ, hs, L, Y => by
    have hQ0 : Q = [] := List.eq_nil_of_length_eq_zero hQ
    subst hQ0
    exact ⟨_, by simp, (ret hs L false true Y).re rfl rfl (by simp) rfl⟩
  | c + 1, b, Q, hQ, hs, L, Y => by
    obtain ⟨st, Q', rfl⟩ := exists_cons hQ
    have hb : Sub M b (popBlk b (b + 21)) := hs.left
    have hr : Sub M (b + 21) (popBlocks (b + 21) e c) := hs.at rfl
    have h1 := pop_c0 hb false L _ (pop_region1 hb st false true L (lay Q' ++ Y))
    obtain ⟨T2, hT2, h2⟩ := pop_blocks e c (b + 21) Q' (by simp at hQ ⊢; omega) hr
      ((encR st ++ [false, true]).reverse ++ L) Y
    refine ⟨_, ?_, ((h1.trans h2).ri rfl (by simp)).re rfl rfl (by simp) rfl⟩
    simp [length_encR, length_lay] at hT2 ⊢
    omega

/-- Pop region `i` of `c + 1` remaining regions; the region starts at the head. -/
def popRows (s e c : Nat) : List (Act × Act × Act) :=
  [(H, .go false true (s + 1), .go true true (s + 23)), same false (s + 2)] ++
    retRows (s + 2) e ++ popBlocks (s + 22) e (c + 1)

theorem pop_empty {M : Mach} {s e c : Nat} (hs : Sub M s (popRows s e c)) (L X : List Bool) :
    Lead M s L (false :: true :: X) e [] (L.reverse ++ false :: true :: X) (7 * L.length + 8) := by
  have hr : Sub M (s + 2) (retRows (s + 2) e) := hs.left.at rfl
  have hs : Sub M s [(H, .go false true (s + 1), .go true true (s + 23)), same false (s + 2)] :=
    hs.left.left
  have h1 : Lead M s L (false :: true :: X) (s + 2) L (false :: true :: X) 2 := by
    zz; zz; exact Lead.refl
  exact (h1.trans (ret hr L false true X)).re rfl rfl rfl (by omega)

theorem pop_full {M : Mach} {s e c : Nat} (hs : Sub M s (popRows s e c)) (b : Bool)
    (st : List Bool) (Q : List (List Bool)) (hQ : Q.length = c) (L X : List Bool) :
    ∃ T, T ≤ 30 * (L.length + (lay (st :: Q)).length + 2) ∧
      Lead M s L (encR (b :: st) ++ false :: true :: lay Q ++ X) e []
        (L.reverse ++ lay (st :: Q) ++ false :: true :: X) T := by
  have hb : Sub M (s + 22) (popBlk (s + 22) (s + 22 + 21)) := (hs.at rfl).left
  have hr : Sub M (s + 22 + 21) (popBlocks (s + 22 + 21) e c) := (hs.at rfl).at rfl
  have hs0 : Sub M s [(H, .go false true (s + 1), .go true true (s + 23)), same false (s + 2)] :=
    hs.left.left
  have h0 : Lead M s L (true :: b :: (encR st ++ false :: true :: lay Q ++ X)) (s + 22 + 1)
      (true :: L) (b :: (encR st ++ false :: true :: lay Q ++ X)) 1 := by
    have hs := hs0
    zz; exact Lead.refl
  have h1 := pop_region1 hb st true b L (lay Q ++ X)
  obtain ⟨T2, hT2, h2⟩ := pop_blocks e c (s + 22 + 21) Q hQ hr
    ((encR st ++ [false, true]).reverse ++ L) X
  refine ⟨_, ?_, ((h0.trans ((h1.ri rfl (by simp)).trans (h2.ri rfl (by simp)))).ri rfl
    (by simp)).re rfl rfl (by simp) rfl⟩
  simp [length_encR, length_lay] at hT2 ⊢
  omega

end ZP.Cx
