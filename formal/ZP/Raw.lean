module

public import ZP.Verif

@[expose] public section

/-!
# Machines on the raw input

`InP` runs a machine on the plain input tape `x`. The machine `rm m p` first turns
that tape into the layout of the stacks `x :: [] :: … :: []` (`m + 1` empty stacks),
returns to cell 0 and runs the compiled program `p` (`frag_ok`). It answers whether
stack 0 ends nonempty (`rm_ok`).

* `rawA`: shift the input two cells right, writing the separator `0 1` in front.
* `rawB`: move the first bit `d` after the separator into the encoded stack:
  `encR y ++ 0 1 ++ d :: z` becomes `encR (y ++ [d]) ++ 0 1 ++ z`. This shifts `z`
  one cell right. When `z` is used up, append `m + 1` separators.
-/

namespace ZP.Cx

/-! ## Shift by two -/

/-- The state carrying the two bits `c1 c2`. -/
def kst : Bool → Bool → Nat
  | false, true => 0
  | false, false => 1
  | true, false => 2
  | true, true => 3

def rawA (a : Nat) : List (Act × Act × Act) :=
  [ (.go false true (a + 5), .go false true (a + 2), .go false true (a + 3)),
    (.go false true (a + 4), .go false true (a + 1), .go false true (a + 0)),
    (.go true true (a + 4), .go true true (a + 1), .go true true (a + 0)),
    (.go true true (a + 5), .go true true (a + 2), .go true true (a + 3)),
    (.go false false (a + 6), H, H),
    (.go true false (a + 6), H, H) ]

theorem shiftA {M : Mach} {a : Nat} (hs : Sub M a (rawA a)) :
    ∀ (z : List Bool) (c1 c2 : Bool) (L : List Bool), ∃ W u v,
      W.reverse ++ [u, v] = c1 :: c2 :: z ∧
      Lead M (a + kst c1 c2) L z (a + 6) (W ++ L) [u, v] (z.length + 2)
  | [], c1, c2, L => by
    refine ⟨[], c1, c2, rfl, ?_⟩
    cases c1 <;> cases c2
    · have h : Lead M (a + 1) L [] (a + 6) L [false, false] 2 := by zz; zz; exact Lead.refl
      exact h
    · have h : Lead M (a + 0) L [] (a + 6) L [false, true] 2 := by zz; zz; exact Lead.refl
      exact h
    · have h : Lead M (a + 2) L [] (a + 6) L [true, false] 2 := by zz; zz; exact Lead.refl
      exact h
    · have h : Lead M (a + 3) L [] (a + 6) L [true, true] 2 := by zz; zz; exact Lead.refl
      exact h
  | d :: z, c1, c2, L => by
    obtain ⟨W, u, v, hW, h⟩ := shiftA hs z c2 d (c1 :: L)
    have h1 : Lead M (a + kst c1 c2) L (d :: z) (a + kst c2 d) (c1 :: L) z 1 := by
      cases c1 <;> cases c2 <;> cases d <;> (zz; exact Lead.refl)
    refine ⟨W ++ [c1], u, v, ?_, (h1.trans h).re rfl (by simp) rfl ?_⟩
    · rw [List.reverse_append, List.append_assoc, hW]; rfl
    · simp only [List.length_cons]; omega

/-! ## Moving one bit into the stack -/

def midA (b : Nat) : List (Act × Act × Act) :=
  [ (.go false false (b + 31), .go false false (b + 4), .go false false (b + 5)),
    anyA false false (b + 6), anyA true false (b + 6), anyA true true (b + 7),
    same true (b + 8), same true (b + 10) ]

def midC (b : Nat) : List (Act × Act × Act) :=
  [ (.go false false (b + 11), .go false true (b + 9), .go false true (b + 10)),
    (.go true false (b + 11), .go true true (b + 9), .go true true (b + 10)) ]

def rawB (b m : Nat) : List (Act × Act × Act) :=
  skipRows b (b + 3) ++ midA b ++ midC b ++ retRows (b + 11) b ++ [same true (b + 32)] ++
    sepRows (b + 32) (b + 2 * m + 34) m ++ retRows (b + 2 * m + 34) (b + 2 * m + 54)

theorem length_rawB (b m : Nat) : (rawB b m).length = 2 * m + 54 := by
  simp [rawB, skipRows, midA, midC, length_sepRows, length_retRows] <;> omega

section raw
variable {M : Mach} {b m : Nat}

theorem carry_ok (hs : Sub M b (rawB b m)) :
    ∀ (z : List Bool) (c l : Bool) (L : List Bool), ∃ W u v,
      W.reverse ++ [u, v] = l :: c :: z ∧
      Lead M (b + (9 + bn c)) (l :: L) z (b + 11) (W ++ L) [u, v] (z.length + 1)
  | [], c, l, L => by
    refine ⟨[], l, c, rfl, ?_⟩
    cases c
    · have h : Lead M (b + 9) (l :: L) [] (b + 11) L [l, false] 1 := by zz; exact Lead.refl
      exact h
    · have h : Lead M (b + 10) (l :: L) [] (b + 11) L [l, true] 1 := by zz; exact Lead.refl
      exact h
  | e :: z, c, l, L => by
    obtain ⟨W, u, v, hW, h⟩ := carry_ok hs z e c (l :: L)
    have h1 : Lead M (b + (9 + bn c)) (l :: L) (e :: z) (b + (9 + bn e)) (c :: l :: L) z 1 := by
      cases c <;> cases e
      · have h : Lead M (b + 9) (l :: L) (false :: z) (b + 9) (false :: l :: L) z 1 := by
          zz; exact Lead.refl
        exact h
      · have h : Lead M (b + 9) (l :: L) (true :: z) (b + 10) (false :: l :: L) z 1 := by
          zz; exact Lead.refl
        exact h
      · have h : Lead M (b + 10) (l :: L) (false :: z) (b + 9) (true :: l :: L) z 1 := by
          zz; exact Lead.refl
        exact h
      · have h : Lead M (b + 10) (l :: L) (true :: z) (b + 10) (true :: l :: L) z 1 := by
          zz; exact Lead.refl
        exact h
    refine ⟨W ++ [l], u, v, ?_, (h1.trans h).re rfl (by simp) rfl ?_⟩
    · rw [List.reverse_append, List.append_assoc, hW]; rfl
    · simp only [List.length_cons]; omega

theorem iter_ok (hs : Sub M b (rawB b m)) (y : List Bool) (d : Bool) (z : List Bool) :
    Lead M b [] (encR y ++ false :: true :: d :: z) b [] (encR (y ++ [d]) ++ false :: true :: z)
      (16 * y.length + 8 * z.length + 28) := by
  have hsk : Sub M b (skipRows b (b + 3)) := hs.left.left.left.left.left.left
  have hr1 : Sub M (b + 11) (retRows (b + 11) b) := hs.left.left.left.at rfl
  have g1 := skip_region hsk y [] (d :: z)
  have e1 : (encR y ++ [false, true]).reverse ++ [] = true :: false :: (encR y).reverse := by
    simp
  have g2 : Lead M (b + 3) (true :: false :: (encR y).reverse) (d :: z) (b + 10)
      (false :: d :: true :: (encR y).reverse) z 5 := by
    cases d
    · zz; zz; zz; zz; zz; exact Lead.refl
    · zz; zz; zz; zz; zz; exact Lead.refl
  obtain ⟨W, u, v, hW, g3⟩ := carry_ok hs z true false (d :: true :: (encR y).reverse)
  have g3' : Lead M (b + 10) (false :: d :: true :: (encR y).reverse) z (b + 11)
      (W ++ d :: true :: (encR y).reverse) [u, v] (z.length + 1) := g3
  have g4 := ret hr1 (W ++ d :: true :: (encR y).reverse) u v []
  have hWl : W.length = z.length := by
    have := congrArg List.length hW
    simp at this
    omega
  have et : (W ++ d :: true :: (encR y).reverse).reverse ++ [u, v] =
      encR (y ++ [d]) ++ false :: true :: z := by
    have : (W ++ d :: true :: (encR y).reverse).reverse ++ [u, v] =
        encR y ++ true :: d :: (W.reverse ++ [u, v]) := by simp
    rw [this, hW]
    simp [encR]
  refine ((g1.re rfl e1 rfl rfl).trans (g2.trans (g3'.trans g4))).re rfl rfl et ?_
  simp only [List.length_append, List.length_cons, List.length_reverse, length_encR]
  omega

theorem sep_okv {e : Nat} : ∀ (m s : Nat) (L : List Bool) (v : Bool), Sub M s (sepRows s e m) →
    Lead M s L [v] e (sepL m ++ L) [false, true] (2 * m + 2)
  | 0, s, L, v, hs => by
    have hs : Sub M s [anyA false true (s + 1), anyA true false e] := hs
    have h : Lead M s L [v] e L [false, true] 2 := by
      zz; zz; exact Lead.refl
    exact h
  | m + 1, s, L, v, hs => by
    have hs' : Sub M s ([anyA false true (s + 1), anyA true true (s + 2)] ++ sepRows (s + 2) e m) :=
      hs
    have h1 : Lead M s L [v] (s + 2) (true :: false :: L) [] 2 := by
      have hs : Sub M s [anyA false true (s + 1), anyA true true (s + 2)] := hs'.left
      zz; zz; exact Lead.refl
    have h2 := sep_ok m (s + 2) (true :: false :: L) (hs'.at rfl)
    exact (h1.trans h2).re rfl (by simp [sepL]) rfl (by omega)

theorem done_ok (hs : Sub M b (rawB b m)) (y : List Bool) :
    Lead M b [] (encR y ++ false :: true :: []) (b + 2 * m + 54) []
      (lay (y :: List.replicate (m + 1) [])) (16 * y.length + 16 * m + 26) := by
  have hsk : Sub M b (skipRows b (b + 3)) := hs.left.left.left.left.left.left
  have hsep : Sub M (b + 32) (sepRows (b + 32) (b + 2 * m + 34) m) := hs.left.at rfl
  have hr2 : Sub M (b + 2 * m + 34) (retRows (b + 2 * m + 34) (b + 2 * m + 54)) :=
    hs.at (by
      rw [List.length_append, length_sepRows]
      show b + (32 + (2 * m + 2)) = b + 2 * m + 34
      omega)
  have g1 := skip_region hsk y [] []
  have e1 : (encR y ++ [false, true]).reverse ++ [] = true :: false :: (encR y).reverse := by
    simp
  have g2 : Lead M (b + 3) (true :: false :: (encR y).reverse) [] (b + 32)
      (true :: false :: (encR y).reverse) [false] 2 := by
    zz; zz; exact Lead.refl
  have g3 := sep_okv m (b + 32) (true :: false :: (encR y).reverse) false hsep
  have g4 := ret hr2 (sepL m ++ true :: false :: (encR y).reverse) false true []
  have et : (sepL m ++ true :: false :: (encR y).reverse).reverse ++ [false, true] =
      lay (y :: List.replicate (m + 1) []) := by
    rw [lay_cons, lay_rep]
    simp
  refine ((g1.re rfl e1 rfl rfl).trans (g2.trans (g3.trans g4))).re rfl rfl et ?_
  simp only [List.length_append, List.length_cons, List.length_reverse, length_encR,
    length_sepL]
  omega

theorem loop_ok (hs : Sub M b (rawB b m)) (n : Nat) :
    ∀ (z y : List Bool), y.length + z.length = n → ∃ T,
      T ≤ z.length * (16 * n + 28) + 16 * n + 16 * m + 26 ∧
      Lead M b [] (encR y ++ false :: true :: z) (b + 2 * m + 54) []
        (lay ((y ++ z) :: List.replicate (m + 1) [])) T
  | [], y, hn => by
    refine ⟨_, ?_, (done_ok hs y).re rfl rfl (by simp) rfl⟩
    simp only [List.length_nil, Nat.add_zero] at hn
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    omega
  | d :: z, y, hn => by
    obtain ⟨T, hT, h⟩ := loop_ok hs n z (y ++ [d]) (by simp at hn ⊢; omega)
    refine ⟨_, ?_, (iter_ok hs y d z).trans (h.re rfl rfl (by simp) rfl)⟩
    simp only [List.length_cons] at hn ⊢
    rw [Nat.add_mul, Nat.one_mul]
    generalize z.length * (16 * n + 28) = P at hT ⊢
    omega

end raw

/-! ## The machine -/

def rrows (m : Nat) (p : Cmd) : List (Act × Act × Act) :=
  rawA 0 ++ retRows 6 26 ++ rawB 26 m ++
    frag (m + 2) p (2 * m + 80) (2 * m + 80 + flen (m + 2) p) ++ [(H, .halt false, .halt true)]

def rm (m : Nat) (p : Cmd) : Mach := ⟨rrows m p⟩

theorem rm_sub (m : Nat) (p : Cmd) : Sub (rm m p) 0 (rrows m p) := fun j r h => by
  rw [Nat.zero_add]; exact h

theorem length_lay_raw (x : List Bool) (m : Nat) :
    (lay (x :: List.replicate (m + 1) [])).length = 2 * x.length + 2 * m + 4 := by
  rw [lay_cons, lay_rep]
  simp [length_encR, length_sepL] <;> omega

theorem rm_ok (m : Nat) {p : Cmd} (hok : Ok (m + 2) p) {x : List Bool}
    {S' : List (List Bool)} {t : Nat} (h : Exec p (x :: List.replicate (m + 1) []) S' t)
    (F : Nat) (hF : 40 * x.length + x.length * (16 * x.length + 28) + 16 * m + 100 +
      40 * t * (2 * x.length + 2 * m + 2 * t + 8) < F) :
    exec (rm m p) F 0 (inTape x) 0 = some (decide (S'.getD 0 [] ≠ [])) := by
  have hs := rm_sub m p
  have hA : Sub (rm m p) 0 (rawA 0) := hs.left.left.left.left
  have hR : Sub (rm m p) 6 (retRows 6 26) := hs.left.left.left.at rfl
  have hB : Sub (rm m p) 26 (rawB 26 m) := hs.left.left.at rfl
  have hFr : Sub (rm m p) (2 * m + 80) (frag (m + 2) p (2 * m + 80) (2 * m + 80 + flen (m + 2) p)) :=
    hs.left.at (by
      rw [List.length_append, length_rawB]
      show 0 + (26 + (2 * m + 54)) = 2 * m + 80
      omega)
  have h5 : Sub (rm m p) (2 * m + 80 + flen (m + 2) p) [(H, .halt false, .halt true)] :=
    hs.at (by
      rw [List.length_append, List.length_append, length_rawB, length_frag]
      show 0 + (26 + (2 * m + 54) + flen (m + 2) p) = 2 * m + 80 + flen (m + 2) p
      omega)
  obtain ⟨W, u, v, hW, g1⟩ := shiftA hA x false true []
  have g2 := ret hR (W ++ []) u v []
  have e2 : (W ++ []).reverse ++ [u, v] = encR [] ++ false :: true :: x := by
    rw [List.append_nil, hW]; rfl
  obtain ⟨T3, hT3, g3⟩ := loop_ok hB x.length x [] (by simp)
  have hk : (x :: List.replicate (m + 1) ([] : List Bool)).length = m + 2 := by simp
  obtain ⟨X', T4, hT4, g4⟩ := frag_ok (by omega) h hk hok (rm m p) (2 * m + 80)
    (2 * m + 80 + flen (m + 2) p) hFr
    ((lay (x :: List.replicate (m + 1) [])).length + 2 * t + 2) [] (Nat.le_refl _)
  have chain := (((g1.trans g2).re rfl rfl e2 rfl).trans g3).re (by omega) rfl
    (by simp) rfl |>.trans g4
  have hS'len : S'.length = (m + 1) + 1 := by
    rw [h.len]; simp only [List.length_cons, List.length_replicate]
  have hact : (rm m p).act (2 * m + 80 + flen (m + 2) p) (lay S' ++ X').head? =
      .halt (decide (S'.getD 0 [] ≠ [])) := by
    refine (h5.act (j := 0) (r := (H, .halt false, .halt true)) rfl _).trans ?_
    obtain ⟨st, S'', rfl⟩ := exists_cons hS'len
    cases st with
    | nil => simp [pick]
    | cons b st => simp [pick]
  rw [inTape_z]
  refine (exec_z (rm m p) F 0 [] x).trans (chain.halts hact F ?_)
  have hWl : (W ++ []).length = x.length := by
    have := congrArg List.length hW
    simp at this
    simp
    omega
  have hmono : 40 * t * ((lay (x :: List.replicate (m + 1) [])).length + 2 * t + 2) ≤
      40 * t * (2 * x.length + 2 * m + 2 * t + 8) :=
    Nat.mul_le_mul_left _ (by rw [length_lay_raw]; omega)
  simp only [List.length_nil, Nat.zero_add] at hT3
  generalize 40 * t * (2 * x.length + 2 * m + 2 * t + 8) = P2 at hF hmono
  generalize 40 * t * ((lay (x :: List.replicate (m + 1) [])).length + 2 * t + 2) = P1 at hT4 hmono
  generalize x.length * (16 * x.length + 28) = P0 at hF hT3
  omega

end ZP.Cx
