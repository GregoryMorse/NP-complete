module

public import ZP.Scan
public import ZP.Body

@[expose] public section

/-!
# The machine of an instance

For a verifier `V` (time `(n+2)^k`, certificates up to `(n+2)^k · m`) and an input
`x`, the machine `DX V k m x` reads a raw tape `c`. It checks that `c` starts with
`encR x`, then the layout of two stacks `[x, c0]`, appends ten empty stacks, and runs
`BODY V k m`. All rows except the input check `xrows` are the same for every `x`.

* `dx_shape`: on any tape it either rejects or the tape is `lay [x, c0] ++ X`;
* `dx_good`: on `lay [x, c0] ++ X` it answers whether `c0` is short enough and `V`
  accepts `lay [x, c0]`, within `dxT` steps.
-/

namespace ZP.Cx

/-! ## Positive runs of the checks -/

theorem vskip_pos {M : Mach} {s n : Nat} (hs : Sub M s (vskipRows s n false)) :
    ∀ (st L X : List Bool), Lead M s L (encR st ++ false :: true :: X) n
      ((encR st ++ [false, true]).reverse ++ L) X (2 * st.length + 2)
  | [], L, X => by
    have h : Lead M s L (false :: true :: X) n (true :: false :: L) X 2 := by
      zz; zz; exact Lead.refl
    exact h.re rfl (by simp) rfl rfl
  | b :: st, L, X => by
    have h1 : Lead M s L (true :: b :: (encR st ++ false :: true :: X)) s (b :: true :: L)
        (encR st ++ false :: true :: X) 2 := by
      cases b <;> (zz; zz; exact Lead.refl)
    exact ((h1.trans (vskip_pos hs st (b :: true :: L) X)).ri rfl (by simp)).re rfl (by simp) rfl
      (by simp only [List.length_cons]; omega)

theorem xchk_pos {M : Mach} {e : Nat} : ∀ (x : List Bool) (f : Nat), Sub M f (xrows f e x) →
    ∀ (L rest : List Bool), Lead M f L (encR x ++ false :: true :: rest) e ((encR x).reverse ++ L)
      (false :: true :: rest) (2 * x.length + 2)
  | [], f, hs, L, rest => by
    have hs : Sub M f [(H, .go false true (f + 1), H), (H, H, .go true false e)] := hs
    have h : Lead M f L (false :: true :: rest) e L (false :: true :: rest) 2 := by
      zz; zz; exact Lead.refl
    exact h
  | b :: x, f, hs, L, rest => by
    have hs1 : Sub M f [(H, H, .go true true (f + 1)), bitRow b (f + 2)] := hs.left
    have hs2 : Sub M (f + 2) (xrows (f + 2) e x) := hs.at rfl
    have h1 : Lead M f L (true :: b :: (encR x ++ false :: true :: rest)) (f + 2) (b :: true :: L)
        (encR x ++ false :: true :: rest) 2 := by
      have hs := hs1
      cases b <;> (zz; zz; exact Lead.refl)
    exact ((h1.trans (xchk_pos x (f + 2) hs2 (b :: true :: L) rest)).ri rfl (by simp)).re rfl
      (by simp) rfl (by simp only [List.length_cons]; omega)

theorem drop_tt (R : List Bool) (n : Nat) : R.tail.tail.drop n = R.drop (n + 2) := by
  rcases R with _ | ⟨a, _ | ⟨b, R⟩⟩ <;> simp

/-- Separators written over anything. -/
theorem sep_okj {M : Mach} {e : Nat} : ∀ (m s : Nat) (L R : List Bool), Sub M s (sepRows s e m) →
    Lead M s L R e (sepL m ++ L) (false :: true :: R.drop (2 * m + 2)) (2 * m + 2)
  | 0, s, L, R, hs => by
    have hs : Sub M s [anyA false true (s + 1), anyA true false e] := hs
    have h : Lead M s L R e L (false :: true :: R.tail.tail) 2 := by
      zz; zz; exact Lead.refl
    exact h.re rfl (by simp [sepL]) (by rw [← drop_tt R 0]; rfl) rfl
  | m + 1, s, L, R, hs => by
    have hs' : Sub M s ([anyA false true (s + 1), anyA true true (s + 2)] ++ sepRows (s + 2) e m) :=
      hs
    have h1 : Lead M s L R (s + 2) (true :: false :: L) R.tail.tail 2 := by
      have hs : Sub M s [anyA false true (s + 1), anyA true true (s + 2)] := hs'.left
      zz; zz; exact Lead.refl
    have h2 := sep_okj m (s + 2) (true :: false :: L) R.tail.tail (hs'.at rfl)
    refine (h1.trans h2).re rfl (by simp [sepL]) ?_ (by omega)
    rw [drop_tt]

/-! ## The machine -/

def F0 (V : Mach) (k m : Nat) : Nat := 68 + flen 12 (BODY V k m)

def fxRows (V : Mach) (k m : Nat) : List (Act × Act × Act) :=
  [same false (F0 V k m)] ++ retRows 1 21 ++ vskipRows 21 24 false ++ vskipRows 24 27 false ++
    sepRows 27 47 9 ++ retRows 47 67 ++ frag 12 (BODY V k m) 67 (67 + flen 12 (BODY V k m)) ++
    [(H, .halt false, .halt true)]

theorem length_fxRows (V : Mach) (k m : Nat) : (fxRows V k m).length = F0 V k m := by
  unfold fxRows F0
  rw [List.length_append, List.length_append, length_frag]
  show 67 + flen 12 (BODY V k m) + 1 = 68 + flen 12 (BODY V k m)
  omega

def DX (V : Mach) (k m : Nat) (x : List Bool) : Mach := ⟨fxRows V k m ++ xrows (F0 V k m) 1 x⟩

theorem dx_sub (V : Mach) (k m : Nat) (x : List Bool) :
    Sub (DX V k m x) 0 (fxRows V k m ++ xrows (F0 V k m) 1 x) := fun j r h => by
  rw [Nat.zero_add]; exact h

section dx
variable (V : Mach) (k m : Nat) (x : List Bool)

theorem dx_subs :
    Sub (DX V k m x) 0 [same false (F0 V k m)] ∧ Sub (DX V k m x) 1 (retRows 1 21) ∧
    Sub (DX V k m x) 21 (vskipRows 21 24 false) ∧ Sub (DX V k m x) 24 (vskipRows 24 27 false) ∧
    Sub (DX V k m x) 27 (sepRows 27 47 9) ∧ Sub (DX V k m x) 47 (retRows 47 67) ∧
    Sub (DX V k m x) 67 (frag 12 (BODY V k m) 67 (67 + flen 12 (BODY V k m))) ∧
    Sub (DX V k m x) (67 + flen 12 (BODY V k m)) [(H, .halt false, .halt true)] ∧
    Sub (DX V k m x) (F0 V k m) (xrows (F0 V k m) 1 x) := by
  have hs := dx_sub V k m x
  have hf : Sub (DX V k m x) 0 ([same false (F0 V k m)] ++ retRows 1 21 ++ vskipRows 21 24 false ++
      vskipRows 24 27 false ++ sepRows 27 47 9 ++ retRows 47 67 ++
      frag 12 (BODY V k m) 67 (67 + flen 12 (BODY V k m)) ++ [(H, .halt false, .halt true)]) :=
    hs.left
  refine ⟨hf.left.left.left.left.left.left.left, hf.left.left.left.left.left.left.at rfl,
    hf.left.left.left.left.left.at rfl, hf.left.left.left.left.at rfl, hf.left.left.left.at rfl,
    hf.left.left.at rfl, hf.left.at rfl, hf.at ?_, hs.at (by rw [length_fxRows]; omega)⟩
  rw [List.length_append, length_frag]
  show 0 + (67 + flen 12 (BODY V k m)) = 67 + flen 12 (BODY V k m)
  omega

/-- Every tape is either rejected or starts with the layout of `[x, c0]`. -/
theorem dx_shape (c : List Bool) :
    Rej (DX V k m x) 0 [] c ∨ ∃ c0 X, c = lay [x, c0] ++ X := by
  obtain ⟨h0, h1, h2, h3, -, -, -, -, h8⟩ := dx_subs V k m x
  match c with
  | [] => exact Or.inl (rej_at (j := 0) h0 rfl)
  | v :: c' =>
    have g0 : Lead (DX V k m x) 0 [] (v :: c') (F0 V k m) [] (v :: c') 1 := by
      have hs := h0
      zz; exact Lead.refl
    rcases xchk_ok x (F0 V k m) [] (v :: c') h8 with ⟨rest, hc, g1⟩ | r
    · have g2 := ret h1 ((encR x).reverse ++ []) false true rest
      have g12 := (g0.trans g1).trans g2
      rcases vskip_ok h2 (v :: c') [] with ⟨st, X1, hc1, g3⟩ | r
      · rcases vskip_ok h3 X1 ((encR st ++ [false, true]).reverse ++ []) with ⟨c0, X, hc2, -⟩ | r
        · have hst := (encR_sep_inj st x X1 rest (hc1.symm.trans hc)).1
          refine Or.inr ⟨c0, X, ?_⟩
          rw [hc1, hc2, hst]
          simp
        · have e : (((encR x).reverse ++ []).reverse ++ false :: true :: rest) = v :: c' := by
            rw [hc]; simp
          exact Or.inl (Rej.of_lead (g12.re rfl rfl e rfl) (Rej.of_lead g3 r))
      · have e : (((encR x).reverse ++ []).reverse ++ false :: true :: rest) = v :: c' := by
          rw [hc]; simp
        exact Or.inl (Rej.of_lead (g12.re rfl rfl e rfl) r)
    · exact Or.inl (Rej.of_lead g0 r)

def dxT (n c t : Nat) : Nat := 40 * n + 20 * c + 300 + 40 * t * (2 * n + 2 * c + 2 * t + 26)

theorem dx_good (c0 X : List Bool) : ∃ t, t ≤ bodyB V k m x.length c0.length ∧ ∃ b : Bool,
    (b = true ↔ c0.length ≤ (x.length + 2) ^ k * m ∧
      (zexec V ((x.length + 2) ^ k) 0 [] (lay [x, c0])).getD false = true) ∧
    ∀ F, dxT x.length c0.length t < F → zexec (DX V k m x) F 0 [] (lay [x, c0] ++ X) = some b := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := dx_subs V k m x
  obtain ⟨S', ⟨t, ht, hE⟩, hiff⟩ := body_ok V k m x c0
  refine ⟨t, ht, decide (S'.getD 0 [] ≠ []), decide_eq_true_iff.trans hiff, ?_⟩
  obtain ⟨v1, v2, R0, hc⟩ := lay_two [x, c0] (by simp) X
  have hR : lay [x, c0] ++ X = encR x ++ false :: true :: (encR c0 ++ false :: true :: X) := by simp
  have g0 : Lead (DX V k m x) 0 [] (v1 :: v2 :: R0) (F0 V k m) [] (v1 :: v2 :: R0) 1 := by
    have hs := h0
    zz; exact Lead.refl
  have gx := xchk_pos x (F0 V k m) h8 [] (encR c0 ++ false :: true :: X)
  have gr1 := ret h1 ((encR x).reverse ++ []) false true (encR c0 ++ false :: true :: X)
  have gv1 := vskip_pos h2 x [] (encR c0 ++ false :: true :: X)
  have gv2 := vskip_pos h3 c0 ((encR x ++ [false, true]).reverse ++ []) X
  have gs := sep_okj 9 27 ((encR c0 ++ [false, true]).reverse ++ ((encR x ++ [false, true]).reverse ++ []))
    X h4
  have gr2 := ret h5 (sepL 9 ++ ((encR c0 ++ [false, true]).reverse ++
    ((encR x ++ [false, true]).reverse ++ []))) false true (X.drop (2 * 9 + 2))
  have hlay : (sepL 9 ++ ((encR c0 ++ [false, true]).reverse ++
      ((encR x ++ [false, true]).reverse ++ []))).reverse ++ false :: true :: X.drop (2 * 9 + 2) =
      lay (x :: c0 :: List.replicate 10 []) ++ X.drop (2 * 9 + 2) := by
    rw [show x :: c0 :: List.replicate 10 [] = [x, c0] ++ List.replicate (9 + 1) [] from rfl,
      lay_append, lay_rep]
    simp
  have hS : (x :: c0 :: List.replicate 10 ([] : List Bool)).length = 12 := by simp
  obtain ⟨X', T4, hT4, g4⟩ := frag_ok (by omega) hE hS (ok_BODY V k m) (DX V k m x) 67
    (67 + flen 12 (BODY V k m)) h6 ((lay (x :: c0 :: List.replicate 10 [])).length + 2 * t + 2)
    (X.drop (2 * 9 + 2)) (Nat.le_refl _)
  have e1 : ((encR x).reverse ++ []).reverse ++ false :: true :: (encR c0 ++ false :: true :: X) =
      encR x ++ false :: true :: (encR c0 ++ false :: true :: X) := by simp
  have chain := ((((((((g0.re rfl rfl (hc.symm.trans hR) rfl).trans gx).trans
    (gr1.re rfl rfl e1 rfl)).trans gv1).trans gv2).trans gs).trans
    (gr2.re rfl rfl hlay rfl)).trans g4).ri rfl hc.symm
  have hS'len : S'.length = 11 + 1 := by rw [hE.len, hS]
  have hact : (DX V k m x).act (67 + flen 12 (BODY V k m)) (lay S' ++ X').head? =
      .halt (decide (S'.getD 0 [] ≠ [])) := by
    refine (h7.act (j := 0) (r := (H, .halt false, .halt true)) rfl _).trans ?_
    obtain ⟨st, S'', rfl⟩ := exists_cons hS'len
    cases st with
    | nil => simp [pick]
    | cons b st => simp [pick]
  intro F hF
  refine chain.halts hact F (Nat.lt_of_le_of_lt ?_ hF)
  have hW : (lay (x :: c0 :: List.replicate 10 [])).length + 2 * t + 2 =
      2 * x.length + 2 * c0.length + 2 * t + 26 := by
    rw [show x :: c0 :: List.replicate 10 [] = [x, c0] ++ List.replicate (9 + 1) [] from rfl,
      lay_append, lay_rep]
    simp [length_encR, length_sepL]
    omega
  rw [hW] at hT4
  unfold dxT
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil,
    length_encR, length_sepL]
  generalize 40 * t * (2 * x.length + 2 * c0.length + 2 * t + 26) = P at hT4 ⊢
  omega

end dx

end ZP.Cx
