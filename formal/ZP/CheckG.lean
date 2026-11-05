module

public import ZP.SearchG

@[expose] public section

/-! # The check phase of the GI machine: unmarking walk over the stack and `m` -/

namespace ZP.G

open ZP

theorem gglStart (X : List Nat) (a : Nat) (ha : a ∈ NB) (hX : Sym4 X) :
    zgiLogic.Reach (hdR QG.gGL [0] (a :: X)) (hdR QG.gUW2 [0] (a :: X)) := by
  have hV : Valid [ALL] [X] := Valid.cons hX (Valid.nil _)
  simp [NB] at ha
  rcases ha with rfl | rfl | rfl
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 1, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 1, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 2, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 2, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [X]) (E := []) (k := 4) hV trivial
      (ls := [.sym 0]) (rs := [.sym 3, .blk 0 .id]) (ls' := [.sym 0]) (rs' := [.sym 3, .blk 0 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem gglWalk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gGL A R) (hdR QG.gUW2 [0] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem uwStep (q q' : Nat) (P R : List Nat) (b : Nat) (hb : b ∈ bits) (hP : Sym4 P) (hR : Sym4 R)
    (hq : q = QG.gUW ∨ q = QG.gUW2) (hq' : q' = QG.gUW) :
    zgiLogic.Reach (hdR q P (b :: R)) (hdR q' (P ++ [unm1 b]) R) := by
  subst hq'
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gUW) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])

theorem uwEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gUW P (1 :: R)) (hdR QG.gUW2 (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem uwCells (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gUW P (c ++ 1 :: R)) (hdR QG.gUW2 (P ++ unm c ++ [1]) R)
  | [], P, _, hP => (uwEnd P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := uwStep QG.gUW QG.gUW P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4]) (Or.inl rfl) rfl
    have hP' : Sym4 (P ++ [unm1 b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [unm1, ALL, hP]
    have h2 := uwCells R hR c (P ++ [unm1 b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp [unm]))

/-- A stack entry that may carry marks: nonempty, cells `0`/`1`. -/
def ME (c : List Nat) : List Nat := c ++ [1]

def MEs : List (List Nat) → List Nat
  | [] => []
  | c :: cs => ME c ++ MEs cs

theorem MEs_sym4 : ∀ cs : List (List Nat), (∀ c ∈ cs, Bits c) → Sym4 (MEs cs)
  | [], _ => Sym4.nil
  | c :: cs, h => by
    have hc := h c (List.mem_cons_self ..)
    have := MEs_sym4 cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp [MEs, ME, ALL, hc.sym4, this]

theorem uwEntry (c P R : List Nat) (hc : Bits c) (hne : c ≠ []) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gUW2 P (c ++ 1 :: R)) (hdR QG.gUW2 (P ++ unm c ++ [1]) R) := by
  cases c with
  | nil => exact absurd rfl hne
  | cons b c =>
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := uwStep QG.gUW2 QG.gUW P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4]) (Or.inr rfl) rfl
    have hP' : Sym4 (P ++ [unm1 b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [unm1, ALL, hP]
    have h2 := uwCells R hR c (P ++ [unm1 b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp [unm]))

theorem uwWalk (R : List Nat) (hR : Sym4 R) : ∀ (cs : List (List Nat)) (P : List Nat),
    (∀ c ∈ cs, Bits c ∧ c ≠ []) → Sym4 P →
    zgiLogic.Reach (hdR QG.gUW2 P (MEs cs ++ R)) (hdR QG.gUW2 (P ++ unm (MEs cs)) R)
  | [], P, _, _ => by
    simp only [MEs, List.nil_append, unm_nil, List.append_nil]; exact LTM.Reach.refl _ _
  | c :: cs, P, h, hP => by
    obtain ⟨hc, hne⟩ := h c (List.mem_cons_self ..)
    have hcs : ∀ d ∈ cs, Bits d ∧ d ≠ [] := fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hM : Sym4 (MEs cs ++ R) := (MEs_sym4 cs (fun d hd => (hcs d hd).1)).app hR
    have h1 := uwEntry c P (MEs cs ++ R) hc hne hP hM
    have hP' : Sym4 (P ++ unm c ++ [1]) := by
      have := unm_nb (A := c) hc.noB
      simp [ALL, hP, this.sym4]
    have h2 := uwWalk R hR cs _ hcs hP'
    exact (h1.of_eq (by simp [MEs, ME, List.append_assoc]) rfl).trans
      (h2.of_eq rfl (by simp [MEs, ME, unm_append, unm1, List.append_assoc]))

theorem uw2End (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gUW2 P (1 :: R)) (hdR QG.gXm (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `gXm` unmarks the cells of `m` and leaves them. -/
theorem xmStep (P R : List Nat) (b : Nat) (hb : b ∈ bits) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gXm P (b :: R)) (hdR QG.gXm (P ++ [unm1 b]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gXm) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])
  · exact (checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gXm) (A' := P ++ [3]) (R' := R) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)).of_eq rfl (by simp [unm1])

theorem xmEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gXm P (1 :: R)) (hdR QG.gY1e (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem xmCells (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gXm P (c ++ 1 :: R)) (hdR QG.gY1e (P ++ unm c ++ [1]) R)
  | [], P, _, hP => (xmEnd P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := xmStep P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [unm1 b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [unm1, ALL, hP]
    have h2 := xmCells R hR c (P ++ [unm1 b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp [unm]))

theorem MEs_noB : ∀ cs : List (List Nat), (∀ c ∈ cs, Bits c) → NoB (MEs cs)
  | [], _ => NoB.nil
  | c :: cs, h => by
    have hc := h c (List.mem_cons_self ..)
    have := MEs_noB cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp [MEs, ME, NB, hc.noB, this]

/-- The unmarking walk over `w` and `m`: from the left end of the entries to the start of `X`. -/
theorem phaseU (ws : List (List Nat)) (c R P : List Nat) (hws : ∀ e ∈ ws, Bits e ∧ e ≠ [])
    (hc : Bits c) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gUW2 P (MEs ws ++ 1 :: (c ++ 1 :: R)))
      (hdR QG.gY1e (P ++ unm (MEs ws) ++ [1] ++ unm c ++ [1]) R) := by
  have hR1 : Sym4 (1 :: (c ++ 1 :: R)) := by simp [ALL, hc.sym4, hR]
  have h1 := uwWalk (1 :: (c ++ 1 :: R)) hR1 ws P hws hP
  have hn := unm_nb (MEs_noB ws (fun e he => (hws e he).1))
  have hP1 : Sym4 (P ++ unm (MEs ws)) := by simp [hP, hn.sym4]
  have h2 := uw2End (P ++ unm (MEs ws)) (c ++ 1 :: R) hP1 (by simp [ALL, hc.sym4, hR])
  have hP2 : Sym4 (P ++ unm (MEs ws) ++ [1]) := by simp [hP, hn.sym4, ALL]
  have h3 := xmCells R hR c _ hc hP2
  exact (h1.of_eq rfl rfl).trans ((h2.of_eq rfl rfl).trans (h3.of_eq rfl rfl))

/-- A consumed label (all cells marked) is skipped; the parity flips. -/
theorem lblSkipE (P R : List Nat) (e : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1e P (List.replicate (e + 1) 2 ++ 1 :: R))
      (hdR QG.gY1o (P ++ (List.replicate (e + 1) 2 ++ [1])) R) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate e 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk e) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gY1e P (2 :: (List.replicate e 2 ++ 1 :: R)))
      (hdR QG.gY1o (P ++ 2 :: (List.replicate e 2 ++ [1])) R) :=
    checkFF (env := [P, List.replicate e 2, R]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

/-- The next cell of the current label is marked. -/
theorem lblMarkE (P R : List Nat) (j : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1e P (List.replicate j 2 ++ 3 :: R))
      (hdR QG.gLPe (P ++ List.replicate (j + 1) 2) R) := by
  cases j with
  | zero =>
    have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
    have : zgiLogic.Reach (hdR QG.gY1e P (3 :: R)) (hdR QG.gLPe (P ++ [2]) R) :=
      checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    exact this.of_eq (by simp) (by simp)
  | succ j =>
    have hV : Valid [ALL, Mk, ALL] [P, List.replicate j 2, R] :=
      Valid.cons hP (Valid.cons (rep2_mk j) (Valid.cons hR (Valid.nil _)))
    have : zgiLogic.Reach (hdR QG.gY1e P (2 :: (List.replicate j 2 ++ 3 :: R)))
        (hdR QG.gLPe (P ++ 2 :: (List.replicate j 2 ++ [2])) R) :=
      checkFF (env := [P, List.replicate j 2, R]) (E := []) (k := 6) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    exact this.of_eq (by simp [List.replicate_succ]) (by rw [rep_cons_snoc])

/-- A consumed label (all cells marked) is skipped; the parity flips. -/
theorem lblSkipO (P R : List Nat) (e : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1o P (List.replicate (e + 1) 2 ++ 1 :: R))
      (hdR QG.gY1e (P ++ (List.replicate (e + 1) 2 ++ [1])) R) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate e 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk e) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gY1o P (2 :: (List.replicate e 2 ++ 1 :: R)))
      (hdR QG.gY1e (P ++ 2 :: (List.replicate e 2 ++ [1])) R) :=
    checkFF (env := [P, List.replicate e 2, R]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

/-- The next cell of the current label is marked. -/
theorem lblMarkO (P R : List Nat) (j : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gY1o P (List.replicate j 2 ++ 3 :: R))
      (hdR QG.gLPo (P ++ List.replicate (j + 1) 2) R) := by
  cases j with
  | zero =>
    have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
    have : zgiLogic.Reach (hdR QG.gY1o P (3 :: R)) (hdR QG.gLPo (P ++ [2]) R) :=
      checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    exact this.of_eq (by simp) (by simp)
  | succ j =>
    have hV : Valid [ALL, Mk, ALL] [P, List.replicate j 2, R] :=
      Valid.cons hP (Valid.cons (rep2_mk j) (Valid.cons hR (Valid.nil _)))
    have : zgiLogic.Reach (hdR QG.gY1o P (2 :: (List.replicate j 2 ++ 3 :: R)))
        (hdR QG.gLPo (P ++ 2 :: (List.replicate j 2 ++ [2])) R) :=
      checkFF (env := [P, List.replicate j 2, R]) (E := []) (k := 6) hV trivial
        (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 3, .blk 2 .id])
        (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 2]) (rs' := [.blk 2 .id])
        (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
    exact this.of_eq (by simp [List.replicate_succ]) (by rw [rep_cons_snoc])

theorem lpMore (q : Nat) (hq : q = QG.gLPe ∨ q = QG.gLPo) (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR q P (3 :: R)) (hd QG.gLW1 P (3 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases hq with rfl | rfl <;>
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lpEndE (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gLPe P (1 :: R)) (hd QG.gM1 P (1 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lpEndO (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gLPo P (1 :: R)) (hd QG.gIL0 P (1 :: R)) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lw1Walk (A R : List Nat) (hA : NoB A) (hR : Sym4 R) :
    zgiLogic.Reach (hd QG.gLW1 A R) (hdR QG.gLW2b [0] (A ++ R)) := by
  have hV : Valid [NB, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := [.sym 0]) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lw2bSkip (P R : List Nat) (e : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gLW2b P (List.replicate (e + 1) 2 ++ 1 :: R))
      (hdR QG.gLW2b (P ++ (List.replicate (e + 1) 2 ++ [1])) R) := by
  have hV : Valid [ALL, Mk, ALL] [P, List.replicate e 2, R] :=
    Valid.cons hP (Valid.cons (rep2_mk e) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gLW2b P (2 :: (List.replicate e 2 ++ 1 :: R)))
      (hdR QG.gLW2b (P ++ 2 :: (List.replicate e 2 ++ [1])) R) :=
    checkFF (env := [P, List.replicate e 2, R]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 2, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

theorem lw2bFail (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gLW2b P (1 :: R)) (hdR QG.gFG (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The first unmarked entry of `w` is marked completely. -/
theorem lw2bMark (P R : List Nat) (v : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gLW2b P (List.replicate (v + 1) 3 ++ 1 :: R))
      (hdR QG.gCX2 (P ++ (List.replicate (v + 1) 2 ++ [1])) R) := by
  have hV : Valid [ALL, T3, ALL] [P, List.replicate v 3, R] :=
    Valid.cons hP (Valid.cons (rep_t3 v) (Valid.cons hR (Valid.nil _)))
  have : zgiLogic.Reach (hdR QG.gLW2b P (3 :: (List.replicate v 3 ++ 1 :: R)))
      (hdR QG.gCX2 (P ++ 2 :: (List.replicate v 2 ++ [1])) R) :=
    checkFF (env := [P, List.replicate v 3, R]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id, .sym 1, .blk 2 .id])
      (ls' := [.blk 0 .id, .sym 2, .blk 1 (.const 2), .sym 1]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  exact this.of_eq (by simp [List.replicate_succ]) (by simp [List.replicate_succ])

theorem cxStep (q : Nat) (hq : q = QG.gCX ∨ q = QG.gCX2) (P R : List Nat) (b : Nat) (hb : b ∈ bits)
    (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR q P (b :: R)) (hdR QG.gCX (P ++ [b]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  rcases mem_bits hb with rfl | rfl <;> rcases hq with rfl | rfl
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gCX) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gCX) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gCX) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkFF (env := [P, R]) (E := []) (k := 3) (q' := QG.gCX) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cxEnd (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gCX P (1 :: R)) (hdR QG.gCX2 (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cx2End (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gCX2 P (1 :: R)) (hdR QG.gXm (P ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [P, R] := Valid.cons hP (Valid.cons hR (Valid.nil _))
  exact checkFF (env := [P, R]) (E := []) (k := 3) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cxCells (R : List Nat) (hR : Sym4 R) : ∀ (c P : List Nat), Bits c → Sym4 P →
    zgiLogic.Reach (hdR QG.gCX P (c ++ 1 :: R)) (hdR QG.gCX2 (P ++ c ++ [1]) R)
  | [], P, _, hP => (cxEnd P R hP hR).of_eq (by simp) (by simp)
  | b :: c, P, hc, hP => by
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := cxStep QG.gCX (Or.inl rfl) P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := cxCells R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem cxEntry (c P R : List Nat) (hc : Bits c) (hne : c ≠ []) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR QG.gCX2 P (c ++ 1 :: R)) (hdR QG.gCX2 (P ++ c ++ [1]) R) := by
  cases c with
  | nil => exact absurd rfl hne
  | cons b c =>
    have hb := hc b (List.mem_cons_self ..)
    have hc' : Bits c := fun a ha => hc a (List.mem_cons_of_mem _ ha)
    have h1 := cxStep QG.gCX2 (Or.inr rfl) P (c ++ 1 :: R) b hb hP (by simp [ALL, hR, hc'.sym4])
    have hP' : Sym4 (P ++ [b]) := by
      rcases mem_bits hb with rfl | rfl <;> simp [ALL, hP]
    have h2 := cxCells R hR c (P ++ [b]) hc' hP'
    exact (h1.of_eq rfl rfl).trans (h2.of_eq rfl (by simp))

theorem cxWalk (R : List Nat) (hR : Sym4 R) : ∀ (cs : List (List Nat)) (P : List Nat),
    (∀ c ∈ cs, Bits c ∧ c ≠ []) → Sym4 P →
    zgiLogic.Reach (hdR QG.gCX2 P (MEs cs ++ 1 :: R)) (hdR QG.gXm (P ++ MEs cs ++ [1]) R)
  | [], P, _, hP => (cx2End P R hP hR).of_eq (by simp [MEs]) (by simp [MEs])
  | c :: cs, P, h, hP => by
    obtain ⟨hc, hne⟩ := h c (List.mem_cons_self ..)
    have hcs : ∀ d ∈ cs, Bits d ∧ d ≠ [] := fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hM : Sym4 (MEs cs ++ 1 :: R) := by
      have := MEs_sym4 cs (fun d hd => (hcs d hd).1)
      simp [ALL, this, hR]
    have h1 := cxEntry c P (MEs cs ++ 1 :: R) hc hne hP hM
    have hP' : Sym4 (P ++ c ++ [1]) := by simp [ALL, hP, hc.sym4]
    have h2 := cxWalk R hR cs _ hcs hP'
    exact (h1.of_eq (by simp [MEs, ME, List.append_assoc]) rfl).trans
      (h2.of_eq rfl (by simp [MEs, ME, List.append_assoc]))

/-- `gY1e` / `gY1o` by parity. -/
def Y1 (b : Bool) : Nat := if b then QG.gY1o else QG.gY1e
def LP (b : Bool) : Nat := if b then QG.gLPo else QG.gLPe

@[simp] theorem Y1_false : Y1 false = QG.gY1e := rfl

theorem lblSkipB (b : Bool) (P R : List Nat) (e : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (Y1 b) P (List.replicate (e + 1) 2 ++ 1 :: R))
      (hdR (Y1 (!b)) (P ++ (List.replicate (e + 1) 2 ++ [1])) R) := by
  cases b
  · exact lblSkipE P R e hP hR
  · exact lblSkipO P R e hP hR

theorem lblMarkB (b : Bool) (P R : List Nat) (j : Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (Y1 b) P (List.replicate j 2 ++ 3 :: R))
      (hdR (LP b) (P ++ List.replicate (j + 1) 2) R) := by
  cases b
  · exact lblMarkE P R j hP hR
  · exact lblMarkO P R j hP hR

theorem lpMoreB (b : Bool) (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (LP b) P (3 :: R)) (hd QG.gLW1 P (3 :: R)) := by
  cases b
  · exact lpMore QG.gLPe (Or.inl rfl) P R hP hR
  · exact lpMore QG.gLPo (Or.inr rfl) P R hP hR

/-- Consumed labels are skipped; the parity flips for each. -/
theorem lblWalk (R : List Nat) (hR : Sym4 R) : ∀ (d : List Nat) (b : Bool) (P : List Nat),
    (∀ e ∈ d, 1 ≤ e) → Sym4 P →
    zgiLogic.Reach (hdR (Y1 b) P (MEnc d ++ R))
      (hdR (Y1 (xor b (decide (d.length % 2 = 1)))) (P ++ MEnc d) R)
  | [], b, P, _, _ => by
    simp only [MEnc, List.nil_append, List.append_nil, List.length_nil]
    cases b <;> exact (LTM.Reach.refl _ _)
  | e :: d, b, P, h, hP => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by have := h e (List.mem_cons_self ..); omega⟩
    have hd : ∀ x ∈ d, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hM : Sym4 (MEnc d ++ R) := by simp [hR]
    have h1 := lblSkipB b P (MEnc d ++ R) k hP hM
    have hP' : Sym4 (P ++ (List.replicate (k + 1) 2 ++ [1])) := by simp [ALL, hP]
    have h2 := lblWalk R hR d (!b) _ hd hP'
    refine (h1.of_eq (by simp [MEnc]) rfl).trans (h2.of_eq rfl ?_)
    have : xor (!b) (decide (d.length % 2 = 1)) = xor b (decide (((k + 1) :: d).length % 2 = 1)) := by
      simp only [List.length_cons]
      by_cases hn : d.length % 2 = 1
      · have : ¬ ((d.length + 1) % 2 = 1) := by omega
        cases b <;> simp [hn, this]
      · have : (d.length + 1) % 2 = 1 := by omega
        cases b <;> simp [hn, this]
    simp [MEnc, List.append_assoc, this]

theorem hdR_z0 (q : Nat) (A R : List Nat) : hdR q (0 :: A) R = hdR q A R := by
  have := F.hdR_zeros q [0] A R (by simp [F.B0])
  simpa using this

theorem lw2bSkipList (R : List Nat) (hR : Sym4 R) : ∀ (ms : List Nat) (P : List Nat),
    (∀ e ∈ ms, 1 ≤ e) → Sym4 P →
    zgiLogic.Reach (hdR QG.gLW2b P (MEnc ms ++ R)) (hdR QG.gLW2b (P ++ MEnc ms) R)
  | [], P, _, _ => by simp only [MEnc, List.nil_append, List.append_nil]; exact LTM.Reach.refl _ _
  | e :: ms, P, h, hP => by
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by have := h e (List.mem_cons_self ..); omega⟩
    have hm : ∀ x ∈ ms, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hM : Sym4 (MEnc ms ++ R) := by simp [hR]
    have h1 := lw2bSkip P (MEnc ms ++ R) k hP hM
    have hP' : Sym4 (P ++ (List.replicate (k + 1) 2 ++ [1])) := by simp [ALL, hP]
    have h2 := lw2bSkipList R hR ms _ hm hP'
    exact (h1.of_eq (by simp [MEnc]) rfl).trans (h2.of_eq rfl (by simp [MEnc, List.append_assoc]))

theorem Enc_MEs : ∀ l : List Nat, Enc l = MEs (l.map fun e => List.replicate e 3)
  | [] => rfl
  | e :: l => by simp [Enc, MEs, ME, U, Enc_MEs l]

theorem Enc_entries (l : List Nat) (h : ∀ e ∈ l, 1 ≤ e) :
    ∀ c ∈ l.map (fun e => List.replicate e 3), Bits c ∧ c ≠ [] := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  refine ⟨bits_rep3 e, ?_⟩
  have := h e he
  intro hh
  have := congrArg List.length hh
  simp at this; omega

/-- One iteration of the label loop: the label has more cells, so one entry of `w` is skipped. -/
theorem labelIter (b : Bool) (ms ws' : List Nat) (v m : Nat) (d : List Nat) (j r' : Nat) (Xrest : List Nat)
    (hms : ∀ e ∈ ms, 1 ≤ e) (hws : ∀ e ∈ ws', 1 ≤ e) (hX : Sym4 Xrest) :
    zgiLogic.Reach
      (hdR (LP b) (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2)
        (3 :: (List.replicate r' 3 ++ 1 :: Xrest)))
      (hdR QG.gY1e (MEnc (ms ++ [v + 1]) ++ Enc ws' ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate (j + 1) 2 ++ 3 :: (List.replicate r' 3 ++ 1 :: Xrest))) := by
  have hcs := Enc_entries ws' hws
  have hEnc : Enc ws' = MEs (ws'.map fun e => List.replicate e 3) := Enc_MEs ws'
  have hRt : Sym4 (3 :: (List.replicate r' 3 ++ 1 :: Xrest)) := by simp [ALL, hX]
  have hP0 : Sym4 (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [ALL]
  have hP0n : NoB (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++ List.replicate (j + 1) 2) := by
    simp [NB]
  have hA := lpMoreB b _ (List.replicate r' 3 ++ 1 :: Xrest) hP0 (by simp [ALL, hX])
  have hB := lw1Walk _ _ hP0n hRt
  have hRest : Sym4 (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ 1 :: Xrest))) := by
    simp [ALL, hX]
  have hRest2 : Sym4 (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ 1 :: Xrest)))) := by
    simp [ALL, hRest, hX]
  have hT : Sym4 (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ 1 :: Xrest))))) := by
    simp [ALL, hRest2, hX]
  have hC1 := lw2bSkipList (List.replicate (v + 1) 3 ++ 1 :: (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ 1 :: Xrest))))))
    (by simp [ALL, hT, hX]) ms [0] hms (by simp [ALL])
  have hC2 := lw2bMark ([0] ++ MEnc ms) (Enc ws' ++ 1 :: (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++
      (3 :: (List.replicate r' 3 ++ 1 :: Xrest))))) v (by simp [ALL]) hT
  have hD := cxWalk (List.replicate m 3 ++ 1 :: (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ 1 :: Xrest))))
    hRest2 (ws'.map fun e => List.replicate e 3) ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1])) hcs (by simp [ALL])
  have hE := xmCells (MEnc d ++ List.replicate (j + 1) 2 ++ (3 :: (List.replicate r' 3 ++ 1 :: Xrest))) hRest
    (List.replicate m 3) ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1]) ++ MEs (ws'.map fun e => List.replicate e 3) ++ [1])
    (bits_rep3 m) (by rw [← hEnc]; simp [ALL])
  rw [← hEnc] at hD hE
  have hAll := hA.trans (hB.trans ((hC1.of_eq (by simp [Enc, U, MEnc, List.append_assoc]) rfl).trans
    ((hC2.of_eq rfl rfl).trans ((hD.of_eq (by simp [List.append_assoc]) rfl).trans (hE.of_eq (by simp [List.append_assoc]) rfl)))))
  refine hAll.of_eq rfl ?_
  rw [unm_rep3] at *
  rw [show ([0] ++ MEnc ms ++ (List.replicate (v + 1) 2 ++ [1]) ++ Enc ws' ++ [1] ++ List.replicate m 3 ++ [1]) =
    0 :: (MEnc (ms ++ [v + 1]) ++ Enc ws' ++ [1] ++ (List.replicate m 3 ++ [1])) by
      simp [MEnc_append, MEnc, List.append_assoc]]
  rw [hdR_z0]

/-- The state after the label is complete: `a` is found (parity even) or `b` is found (odd). -/
def LDone (b : Bool) : Nat := if b then QG.gIL0 else QG.gM1

theorem lpEndB (b : Bool) (P R : List Nat) (hP : Sym4 P) (hR : Sym4 R) :
    zgiLogic.Reach (hdR (LP b) P (1 :: R)) (hd (LDone b) P (1 :: R)) := by
  cases b
  · exact lpEndE P R hP hR
  · exact lpEndO P R hP hR

theorem labelFind (m : Nat) (d : List Nat) (Xrest : List Nat) (hdd : ∀ e ∈ d, 1 ≤ e) (hX : Sym4 Xrest) :
    ∀ (r : Nat) (ms ws : List Nat) (j : Nat), (∀ e ∈ ms, 1 ≤ e) → (∀ e ∈ ws, 1 ≤ e) → r ≤ ws.length →
    zgiLogic.Reach
      (hdR QG.gY1e (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]))
        (MEnc d ++ List.replicate j 2 ++ List.replicate (r + 1) 3 ++ 1 :: Xrest))
      (hd (LDone (decide (d.length % 2 = 1)))
        (MEnc (ms ++ ws.take r) ++ Enc (ws.drop r) ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++
          List.replicate (j + r + 1) 2) (1 :: Xrest)) := by
  intro r
  induction r with
  | zero =>
    intro ms ws j hms hws hr
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (0 + 1) 3 ++ 1 :: Xrest) (by simp [ALL, hX]) d false
      (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (1 :: Xrest) j (by simp [ALL]) (by simp [ALL, hX])
    have hE := lpEndB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ws ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d ++
      List.replicate (j + 1) 2) Xrest (by simp [ALL]) hX
    simp only [Bool.false_xor] at hL
    refine (hL.of_eq (by simp [List.append_assoc]) rfl).trans ((hM.of_eq (by simp [List.append_assoc]) rfl).trans
      (hE.of_eq rfl ?_))
    simp [List.append_assoc]
  | succ r ih =>
    intro ms ws j hms hws hr
    obtain ⟨w1, ws', hw⟩ : ∃ w1 ws', ws = w1 :: ws' := by
      cases ws with
      | nil => simp at hr
      | cons a l => exact ⟨a, l, rfl⟩
    subst hw
    obtain ⟨v, rfl⟩ : ∃ v, w1 = v + 1 := ⟨w1 - 1, by have := hws w1 (List.mem_cons_self ..); omega⟩
    have hws' : ∀ e ∈ ws', 1 ≤ e := fun e he => hws e (List.mem_cons_of_mem _ he)
    have hL := lblWalk (List.replicate j 2 ++ List.replicate (r + 1 + 1) 3 ++ 1 :: Xrest) (by simp [ALL, hX]) d false
      (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1])) hdd (by simp [ALL])
    have hM := lblMarkB (decide (d.length % 2 = 1)) (MEnc ms ++ Enc ((v + 1) :: ws') ++ [1] ++ (List.replicate m 3 ++ [1]) ++ MEnc d)
      (List.replicate (r + 1) 3 ++ 1 :: Xrest) j (by simp [ALL]) (by simp [ALL, hX])
    have hI := labelIter (decide (d.length % 2 = 1)) ms ws' v m d j r Xrest hms hws' hX
    have hF := ih (ms ++ [v + 1]) ws' (j + 1) (by
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hms e he
        · simp at he; omega) hws' (by simp at hr; omega)
    simp only [Bool.false_xor] at hL
    refine (hL.of_eq (by simp [List.append_assoc]) rfl).trans ((hM.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans
      ((hI.of_eq (by simp [List.replicate_succ, List.append_assoc]) rfl).trans (hF.of_eq (by simp [List.replicate_succ, List.append_assoc]) ?_)))
    simp [List.append_assoc, MEnc_append, Nat.add_assoc, Nat.add_comm 1 r]

end ZP.G
