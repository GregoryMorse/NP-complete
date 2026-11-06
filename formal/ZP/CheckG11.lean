import ZP.CheckG10

/-! # The check phase of the GI machine (part 11): the tape `Tc` of an instance -/

namespace ZP.G

open ZP

def flatR (L : List Nat) : List Nat := L.flatMap fun t => 1 :: List.replicate t 3

def tcOfList : List Nat → List Nat
  | [] => []
  | t0 :: tl => List.replicate t0 3 ++ flatR tl

theorem flatR_append_one : ∀ L : List Nat, flatR L ++ [1] = 1 :: Enc L
  | [] => by simp [flatR, Enc]
  | a :: L => by
    have ih := flatR_append_one L
    simp only [flatR, List.flatMap_cons] at ih ⊢
    simp only [Enc, U, List.append_assoc, List.cons_append] at ih ⊢
    rw [ih]
    simp

theorem flatR_snoc (L : List Nat) (c : Nat) : flatR (L ++ [c]) = flatR L ++ 1 :: List.replicate c 3 := by
  simp [flatR, List.flatMap_append]

theorem flatR_append (L L' : List Nat) : flatR (L ++ L') = flatR L ++ flatR L' := by
  simp [flatR, List.flatMap_append]

theorem tcOfList_snoc (L : List Nat) (hL : L ≠ []) (c : Nat) :
    tcOfList (L ++ [c]) = tcOfList L ++ 1 :: List.replicate c 3 := by
  match L, hL with
  | t0 :: tl, _ =>
    simp [tcOfList, flatR_snoc, List.append_assoc]

theorem runsAux_ne : ∀ (s : List Bool) (c : Nat), runsAux s c ≠ []
  | [], c => by simp [runsAux]
  | true :: r, c => by simpa [runsAux] using runsAux_ne r (c + 1)
  | false :: r, c => by simp [runsAux]

/-- The copy of `s` (reversed, `0 ↦ M`, `1 ↦ 1`) is the unary list of the runs. -/
theorem tc_runs : ∀ (s : List Bool) (c : Nat),
    (s.reverse.map fun b => if b then 3 else 1) ++ List.replicate c 3 = tcOfList (runsAux s c).reverse
  | [], c => by simp [runsAux, tcOfList, flatR]
  | true :: r, c => by
    have ih := tc_runs r (c + 1)
    simp only [runsAux]
    rw [← ih]
    simp [List.replicate_succ, List.append_assoc]
  | false :: r, c => by
    have ih := tc_runs r 0
    simp only [runsAux, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    have hne : (runsAux r 0).reverse ≠ [] := by simpa using runsAux_ne r 0
    rw [tcOfList_snoc _ hne, ← ih]
    simp [List.append_assoc]

theorem fz_bitsOf (s : List Bool) :
    fz (bitsOf s).reverse = s.reverse.map fun b => if b then 3 else 1 := by
  simp only [fz, bitsOf, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b <;> simp

theorem rep3_cons_inj : ∀ (a b : Nat) (u v : Nat) (U V : List Nat), (u = 0 ∨ u = 1) → (v = 0 ∨ v = 1) →
    List.replicate a 3 ++ u :: U = List.replicate b 3 ++ v :: V → a = b
  | 0, 0, _, _, _, _, _, _, _ => rfl
  | 0, b + 1, u, v, U, V, hu, _, h => by
    simp [List.replicate_succ] at h
    omega
  | a + 1, 0, u, v, U, V, _, hv, h => by
    simp [List.replicate_succ] at h
    omega
  | a + 1, b + 1, u, v, U, V, hu, hv, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := rep3_cons_inj a b u v U V hu hv h
    omega

theorem gEnv_m (E : GEnv) (m0 : Nat) (rest : List Nat) (hr : rest = [] ∨ ∃ t, rest = 1 :: t)
    (hTc : E.Tc = List.replicate m0 3 ++ rest) : E.m = m0 := by
  have hT := E.hT
  rw [hTc] at hT
  symm
  rcases hr with rfl | ⟨t, rfl⟩
  · exact rep3_cons_inj m0 E.m 0 E.z (E.Z) E.Z' (Or.inl rfl) E.hz (by simpa using hT)
  · exact rep3_cons_inj m0 E.m 1 E.z (t ++ 0 :: E.Z) E.Z' (Or.inr rfl) E.hz (by simpa using hT)

theorem CheckSpec_congr {E : GEnv} {chk1 chk2 : List Nat → Bool} {Acc : ZC → Prop}
    (h : ∀ w, chk1 w = chk2 w) (hc : E.CheckSpec chk1 Acc) : E.CheckSpec chk2 Acc := by
  intro rest hv
  have := hc rest hv
  rw [h rest] at this
  exact this

theorem csForm1 (E : GEnv) (m0 : Nat) (hTc : E.Tc = List.replicate m0 3) :
    E.CheckSpec (fun w => checkG w m0 [] []) (AccS E.Z) :=
  checkSpecS0M E hTc m0

theorem csForm2 (E : GEnv) (m0 : Nat) (R' : List Nat) (y : Nat) (hR' : ∀ e ∈ R', 1 ≤ e) (hy : 1 ≤ y)
    (hTc : E.Tc = List.replicate m0 3 ++ 1 :: (Enc R' ++ List.replicate y 3)) :
    E.CheckSpec (fun w => checkG w m0 (R' ++ [y]) []) (AccS E.Z) := by
  have hm : E.m = m0 := gEnv_m E m0 _ (Or.inr ⟨_, rfl⟩) hTc
  have hchk : ∀ w, checkG w m0 (R' ++ [y]) [] = false := by
    intro w; rw [checkG_nil]; simp
  have hQy : ∀ a ∈ List.replicate y 3, a ∈ O13 := fun a ha => by
    rw [List.eq_of_mem_replicate ha]; simp [O13]
  cases m0 with
  | zero =>
    cases R' with
    | nil =>
      exact checkSpecM0U E hm _ (hchk []) y hy (by simpa [Enc] using hTc)
    | cons x X'' =>
      exact checkSpecM0X E hm _ (hchk []) x X'' (List.replicate y 3) hQy (hR' x (by simp))
        (fun e he => hR' e (by simp [he])) (by simpa using hTc)
  | succ p =>
    cases R' with
    | nil =>
      exact checkSpecS3 E p [] y (by simp) (by simp) hy (by simpa [Enc] using hTc)
    | cons x R1 =>
      cases R1 with
      | nil =>
        exact checkSpecS3 E p [x] y (by simp) (by simpa using hR' x (by simp)) hy hTc
      | cons x2 R2 =>
        refine CheckSpec_congr (fun w => by rw [hchk w, checkG_nil]; simp) (checkSpecE E p (x :: x2 :: R2)
          (List.replicate y 3) (Or.inr (Or.inr (Or.inr ⟨List.replicate y 3, bits_rep3 y, by
            intro h; have := congrArg List.length h; simp at this; omega, rfl⟩))) hQy hR' (by simp) hTc)

theorem csForm3 (E : GEnv) (m0 : Nat) (X H0 : List Nat) (hX : ∀ e ∈ X, 1 ≤ e)
    (hH0 : H0 = [] ∨ H0 = [1] ∨ (∃ J', NoB J' ∧ H0 = 1 :: 1 :: J')) (hH0o : ∀ a ∈ H0, a ∈ O13)
    (hTc : E.Tc = List.replicate m0 3 ++ 1 :: (Enc X ++ H0)) :
    E.CheckSpec (fun w => checkG w m0 X []) (AccS E.Z) := by
  have hm : E.m = m0 := gEnv_m E m0 _ (Or.inr ⟨_, rfl⟩) hTc
  cases m0 with
  | zero =>
    cases X with
    | nil => exact checkSpecM0E E hm H0 hH0 hH0o (by simpa [Enc] using hTc)
    | cons x X' =>
      refine checkSpecM0X E hm _ (by simp [checkG_nil]) x X' H0 hH0o (hX x (by simp))
        (fun e he => hX e (by simp [he])) (by simpa using hTc)
  | succ p =>
    refine checkSpecE E p X H0 (by
      rcases hH0 with h | h | ⟨J', hJ', h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨J', hJ', h⟩))) hH0o hX ?_ hTc
    rintro ⟨t, ht, hne, h⟩
    exfalso
    rcases hH0 with h' | h' | ⟨J', hJ', h'⟩
    · exact hne (h.symm.trans h')
    · have := ht 1 (by rw [← h, h']; simp)
      simp [bits] at this
    · have := ht 1 (by rw [← h, h']; simp)
      simp [bits] at this

theorem csForm4 (E : GEnv) (m0 : Nat) (X H J : List Nat) (hX : ∀ e ∈ X, 1 ≤ e) (hne : H ≠ [])
    (hHv : ∀ e ∈ H, 1 ≤ e) (hJ : JShape J) (hJo : ∀ a ∈ J, a ∈ O13)
    (hTc : E.Tc = List.replicate m0 3 ++ 1 :: (Enc X ++ 1 :: ((Enc H).dropLast ++ J))) :
    E.CheckSpec (fun w => checkG w m0 X H) (AccS E.Z) := by
  have hm : E.m = m0 := gEnv_m E m0 _ (Or.inr ⟨_, rfl⟩) hTc
  have hHP : HP (Hs H []) 0 = (Enc H).dropLast := by rw [Hs_nil, HP_Enc H hne hHv]
  cases m0 with
  | zero =>
    cases X with
    | nil => exact checkSpecM0A E hm H J hne hHv hJ hJo (by rw [hHP]; simpa [Enc] using hTc)
    | cons x X' =>
      refine checkSpecM0X E hm _ (checkG_nil0 0 (x :: X') H hX (by simp)) x X' (1 :: ((Enc H).dropLast ++ J))
        (fun a ha => ?_) (hX x (by simp)) (fun e he => hX e (by simp [he])) (by simpa using hTc)
      rcases List.mem_cons.1 ha with rfl | ha
      · simp [O13]
      · rcases List.mem_append.1 ha with ha | ha
        · exact Enc_o13 H a (List.dropLast_subset _ ha)
        · exact hJo a ha
  | succ p =>
    exact checkSpecA E p hm X H J hne hHv hJ hJo hX (by rw [hHP]; exact hTc)

end ZP.G
