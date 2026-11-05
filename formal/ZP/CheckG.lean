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

end ZP.G
