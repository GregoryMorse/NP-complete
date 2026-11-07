module

public import ZP.RecordNTT

@[expose] public section

/-! # NTT machine: the evaluation phase (part 1): witness initialisation `WI0` .. `RZ0` -/

namespace ZP.NTT

open ZP ZP.G

/-- `WI0`: scan left to the blank edge. -/
theorem wi0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WI0 L R) (hdR QNTT.WI1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Words that `WI1`/`WI2` restore: fields of marks, separated by single `M`s. -/
inductive Rest : List Nat → List Nat → Prop
  | nil : Rest [] []
  | bit {b : Nat} {u v : List Nat} : b ∈ [2, 3] → Rest u v → Rest (b :: u) (3 :: v)
  | mb {b : Nat} {u v : List Nat} : b ∈ [2, 3] → Rest u v → Rest (1 :: b :: u) (1 :: 3 :: v)

theorem Rest.sym4_src {u v : List Nat} (h : Rest u v) : Sym4 u := by
  induction h with
  | nil => exact Sym4.nil
  | bit hb _ ih => exact Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) ih
  | mb hb _ ih =>
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) ih)

theorem Rest.sym4_dst {u v : List Nat} (h : Rest u v) : Sym4 v := by
  induction h with
  | nil => exact Sym4.nil
  | bit hb _ ih => exact Sym4.cons (by simp [ALL]) ih
  | mb hb _ ih => exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) ih)

theorem wi1Bit (A : List Nat) (b : Nat) (R : List Nat) (hb : b ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WI1 A (b :: R)) (hdR QNTT.WI1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wi1Mb (A : List Nat) (b : Nat) (R : List Nat) (hb : b ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WI1 A (1 :: b :: R)) (hdR QNTT.WI1 (A ++ [1, 3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wi1Walk {u v : List Nat} (h : Rest u v) :
    ∀ (A R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach (hdR QNTT.WI1 A (u ++ R)) (hdR QNTT.WI1 (A ++ v) R) := by
  induction h with
  | nil => intro A R _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u v hb h ih =>
    intro A R hA hR
    have h1 := wi1Bit A b (u ++ R) hb hA (h.sym4_src.app hR)
    have h2 := ih (A ++ [3]) R (hA.app (by intro y hy; simp at hy; subst hy; simp [ALL])) hR
    simpa using h1.trans h2
  | @mb b u v hb h ih =>
    intro A R hA hR
    have h1 := wi1Mb A b (u ++ R) hb hA (h.sym4_src.app hR)
    have h2 := ih (A ++ [1, 3]) R (hA.app (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [ALL])) hR
    simpa using h1.trans h2

/-- The record separator `MM` is reached from `WI1`. -/
theorem wi1MM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WI1 A (1 :: 1 :: R)) (hdR QNTT.WH1 (A ++ [1, 1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ### One record -/

theorem sym4_cell (a : Nat) (h : a ∈ [1, 2, 3]) : Sym4 [a] := by
  intro y hy; simp at hy; subst hy; simp at h; simp [ALL]; omega

theorem whSweep0 (A h R : List Nat) (hA : Sym4 A) (hh : BitsD h) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WH0 A (h ++ 1 :: R)) (hd QNTT.WP0 (A ++ h) (1 :: R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, h, R] := Valid.cons hA (Valid.cons hh (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, h, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem whSweep1 (A h R : List Nat) (hA : Sym4 A) (hh : BitsD h) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WH1 A (h ++ 1 :: R)) (hd QNTT.WP1 (A ++ h) (1 :: R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, h, R] := Valid.cons hA (Valid.cons hh (Valid.cons hR (Valid.nil _)))
  exact checkFT (env := [A, h, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wp0 (A : List Nat) (p : Nat) (R : List Nat) (hp : p ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WP0 (A ++ [p]) R) (hdR QNTT.WE0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hp; rcases hp with rfl | rfl
  · exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wp1 (A : List Nat) (p : Nat) (R : List Nat) (hp : p ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.WP1 (A ++ [p]) R) (hdR QNTT.WE0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hp; rcases hp with rfl | rfl
  · exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem we0 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WE0 A (1 :: R)) (hdR QNTT.WAc (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wac (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WAc A (f ++ 1 :: R)) (hdR QNTT.WE1 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem we1 (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WE1 A (a :: R)) (hdR QNTT.WE2 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem we2 (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WE2 A (a :: R)) (hdR QNTT.WE3 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem we3 (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WE3 A (f ++ 1 :: R)) (hdR QNTT.WS (A ++ List.replicate f.length 2 ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 2), .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsField (A f : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hf : BitsD f)
    (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.WS A (f ++ 1 :: b :: rest)) (hdR QNTT.WS (A ++ f ++ [1, b]) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 2, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 2]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 3, .blk 2 .id])
      (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 3]) (rs' := [.blk 2 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsBlock (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.WS A (f ++ rest)) (hdR QNTT.WS (A ++ f) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFF (env := [A, f, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsMM (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.WS A (f ++ 1 :: 1 :: rest)) (hdR QNTT.WH0 (A ++ f ++ [1, 1]) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  simpa using checkFF (env := [A, f, rest]) (E := []) (k := 6) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsEnd (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.WS A f) (hd QNTT.RZ0 (A ++ f) []) := by
  have hV : Valid [ALL, [2, 3]] [A, f] := Valid.cons hA (Valid.cons hf (Valid.nil _))
  exact checkFT (env := [A, f]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem wsGood {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.WS A (u ++ rest)) (hdR QNTT.WS (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := wsBlock A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have h1 := wsField A [] b (u ++ rest) hA (by intro x hx; simp at hx) hb (hu'.sym4.app hr)
    have h2 := ih (A ++ [] ++ [1, b]) rest (by simpa using hA.app sb) hr
    simpa using h1.trans h2

theorem sym4_M {l : List Nat} (h : Sym4 l) : Sym4 (1 :: l) := Sym4.cons (by simp [ALL]) h

theorem sym4_B {b : Nat} {l : List Nat} (hb : b ∈ [2, 3]) (h : Sym4 l) : Sym4 (b :: l) :=
  Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) h

theorem recMid (A acc : List Nat) (e0 e1 : Nat) (eT : List Nat) (t0 : Nat) (tr Tl : List Nat)
    (hA : Sym4 A) (hacc : BitsD acc) (he0 : e0 ∈ [2, 3]) (he1 : e1 ∈ [2, 3]) (heT : BitsD eT)
    (ht0 : t0 ∈ [2, 3]) (htr : GoodW tr) (hTl : Sym4 Tl) :
    znttLogic.Reach
      (hdR QNTT.WE0 A (1 :: (acc ++ 1 :: (e0 :: e1 :: eT ++ 1 :: (t0 :: tr ++ Tl)))))
      (hdR QNTT.WS (A ++ 1 :: (acc ++ 1 :: (3 :: 3 :: List.replicate eT.length 2 ++ 1 :: t0 :: tr))) Tl) := by
  have sU : Sym4 (tr ++ Tl) := htr.sym4.app hTl
  have sZ : Sym4 (t0 :: tr ++ Tl) := sym4_B ht0 sU
  have sE3 : Sym4 (eT ++ 1 :: (t0 :: tr ++ Tl)) := heT.sym4.app (sym4_M sZ)
  have sE2 : Sym4 (e1 :: eT ++ 1 :: (t0 :: tr ++ Tl)) := sym4_B he1 sE3
  have sE1 : Sym4 (e0 :: e1 :: eT ++ 1 :: (t0 :: tr ++ Tl)) := sym4_B he0 sE2
  have sA1 : Sym4 (acc ++ 1 :: (e0 :: e1 :: eT ++ 1 :: (t0 :: tr ++ Tl))) := hacc.sym4.app (sym4_M sE1)
  have c1 : Sym4 [1] := sym4_cell 1 (by simp)
  have c3 : Sym4 [3] := sym4_cell 3 (by simp)
  have h0 := we0 A _ hA sA1
  have h1 := wac (A ++ [1]) acc _ (hA.app c1) hacc sE1
  have h2 := we1 (A ++ [1] ++ acc ++ [1]) e0 _ he0 ((hA.app c1).app hacc.sym4 |>.app c1) sE2
  have s2 : Sym4 (A ++ [1] ++ acc ++ [1] ++ [3]) := (((hA.app c1).app hacc.sym4).app c1).app c3
  have h3 := we2 _ e1 _ he1 s2 sE3
  have s3 : Sym4 (A ++ [1] ++ acc ++ [1] ++ [3] ++ [3]) := s2.app c3
  have h4 := we3 _ eT _ s3 heT (sym4_B ht0 sU |> fun _ => sym4_B ht0 sU)
  have s4 : Sym4 (A ++ [1] ++ acc ++ [1] ++ [3] ++ [3] ++ List.replicate eT.length 2 ++ [1]) :=
    ((s3.app (BitsD.rep _ _ (by simp)).sym4).app c1)
  have h5 := wsBlock _ [t0] (tr ++ Tl) s4 (by intro x hx; simp at hx; subst hx; exact ht0) sU
  have s5 : Sym4 (A ++ [1] ++ acc ++ [1] ++ [3] ++ [3] ++ List.replicate eT.length 2 ++ [1] ++ [t0]) :=
    s4.app (sym4_B ht0 Sym4.nil)
  have h6 := wsGood htr _ Tl s5 hTl
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 ⊢
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))

/-- A record of the evaluation phase (the cells after `MM`): `F O Pf M acc M E M b M u`
(three `P`-wide fields and the pointer `u`; `b` and `u` are nonempty). -/
structure Rc where
  F : Nat
  O : Nat
  Pf : Nat
  acc : List Nat
  E : List Nat
  b0 : Nat
  br : List Nat
  u0 : Nat
  ur : List Nat

def Rc.tl0 (r : Rc) : Nat := r.b0
def Rc.tlr (r : Rc) : List Nat := r.br ++ 1 :: r.u0 :: r.ur

def Rc.body (r : Rc) : List Nat :=
  [r.F, r.O, r.Pf] ++ 1 :: (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: r.tlr))

/-- After the witness initialisation: input flag `x`, `E := 1`. -/
def Rc.initB (r : Rc) (x : Nat) : List Nat :=
  [r.F, r.O, x] ++ 1 :: (r.acc ++ 1 :: ((3 :: 3 :: List.replicate (r.E.length - 2) 2) ++ 1 :: r.tl0 :: r.tlr))

structure Rc.Ok (r : Rc) : Prop where
  F : r.F ∈ [2, 3]
  O : r.O ∈ [2, 3]
  Pf : r.Pf ∈ [2, 3]
  acc : BitsD r.acc
  E : BitsD r.E
  Elen : 2 ≤ r.E.length
  b0 : r.b0 ∈ [2, 3]
  br : BitsD r.br
  u0 : r.u0 ∈ [2, 3]
  ur : BitsD r.ur

theorem Rc.Ok.tl0 {r : Rc} (h : r.Ok) : r.tl0 ∈ [2, 3] := h.b0

theorem Rc.Ok.tlr {r : Rc} (h : r.Ok) : GoodW r.tlr :=
  GoodW.app (GoodW.bits h.br) (GoodW.mb h.u0 (GoodW.bits h.ur))

theorem Rc.tail_sym4 (r : Rc) (hr : r.Ok) : Sym4 (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: r.tlr)) :=
  hr.acc.sym4.app (sym4_M (hr.E.sym4.app (sym4_M (sym4_B hr.tl0 hr.tlr.sym4))))

/-- Common part of a record: from `WE0` to the end of the record (`Tl` is `[]` or `MM ..`). -/
theorem recWS (A : List Nat) (r : Rc) (hr : r.Ok) (Tl : List Nat) (hA : Sym4 A) (hTl : Sym4 Tl) (x : Nat) (hx : x ∈ [2, 3]) :
    znttLogic.Reach (hdR QNTT.WE0 (A ++ [r.F, r.O, x]) (1 :: (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: (r.tlr ++ Tl)))))
      (hdR QNTT.WS (A ++ r.initB x) Tl) := by
  obtain ⟨e0, e1, eT, hE⟩ : ∃ e0 e1 eT, r.E = e0 :: e1 :: eT := by
    have := hr.Elen
    match h : r.E, this with
    | e0 :: e1 :: eT, _ => exact ⟨e0, e1, eT, rfl⟩
  have hEb := hr.E
  rw [hE] at hEb
  have gen : ∀ (l : List Nat) (a : Nat) , BitsD (a :: l) → a ∈ [2, 3] ∧ BitsD l := fun l a h =>
    ⟨h a (by simp), fun y hy => h y (by simp [hy])⟩
  obtain ⟨he0, hE1⟩ := gen _ _ hEb
  obtain ⟨he1, heT⟩ := gen _ _ hE1
  have sA : Sym4 (A ++ [r.F, r.O, x]) := hA.app (sym4_B hr.F (sym4_B hr.O (sym4_B hx Sym4.nil)))
  have := recMid (A ++ [r.F, r.O, x]) r.acc e0 e1 eT r.tl0 r.tlr Tl sA hr.acc he0 he1 heT hr.tl0 hr.tlr hTl
  rw [hE]
  simp only [Rc.initB, hE, List.append_assoc, List.cons_append, List.nil_append, List.length_cons,
    Nat.add_sub_cancel] at this ⊢
  simpa using this

/-- `WH0`/`WH1` .. `WE0`: the header sweep and the input flag. -/
theorem recHead0 (A : List Nat) (r : Rc) (hr : r.Ok) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WH0 A (r.body ++ R))
      (hdR QNTT.WE0 (A ++ [r.F, r.O, 2]) (1 :: (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: (r.tlr ++ R))))) := by
  have sH : BitsD [r.F, r.O, r.Pf] := by
    intro y hy; simp at hy; rcases hy with rfl | rfl | rfl
    · exact hr.F
    · exact hr.O
    · exact hr.Pf
  have sT : Sym4 (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: (r.tlr ++ R))) :=
    hr.acc.sym4.app (sym4_M (hr.E.sym4.app (sym4_M (sym4_B hr.tl0 (hr.tlr.sym4.app hR)))))
  have h1 := whSweep0 A [r.F, r.O, r.Pf] _ hA sH sT
  have h2 := wp0 (A ++ [r.F, r.O]) r.Pf _ hr.Pf (hA.app (sym4_B hr.F (sym4_B hr.O Sym4.nil))) (sym4_M sT)
  simp only [Rc.body, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact h1.trans h2

theorem recHead1 (A : List Nat) (r : Rc) (hr : r.Ok) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.WH1 A (r.body ++ R))
      (hdR QNTT.WE0 (A ++ [r.F, r.O, 3]) (1 :: (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: (r.tlr ++ R))))) := by
  have sH : BitsD [r.F, r.O, r.Pf] := by
    intro y hy; simp at hy; rcases hy with rfl | rfl | rfl
    · exact hr.F
    · exact hr.O
    · exact hr.Pf
  have sT : Sym4 (r.acc ++ 1 :: (r.E ++ 1 :: r.tl0 :: (r.tlr ++ R))) :=
    hr.acc.sym4.app (sym4_M (hr.E.sym4.app (sym4_M (sym4_B hr.tl0 (hr.tlr.sym4.app hR)))))
  have h1 := whSweep1 A [r.F, r.O, r.Pf] _ hA sH sT
  have h2 := wp1 (A ++ [r.F, r.O]) r.Pf _ hr.Pf (hA.app (sym4_B hr.F (sym4_B hr.O Sym4.nil))) (sym4_M sT)
  simp only [Rc.body, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact h1.trans h2

def tailB : List Rc → List Nat
  | [] => []
  | r :: rs => 1 :: 1 :: (r.body ++ tailB rs)

def tailI : List Rc → List Nat
  | [] => []
  | r :: rs => 1 :: 1 :: (r.initB 2 ++ tailI rs)

theorem Rc.body_sym4 (r : Rc) (hr : r.Ok) : Sym4 r.body :=
  sym4_B hr.F (sym4_B hr.O (sym4_B hr.Pf (sym4_M (r.tail_sym4 hr))))

theorem Rc.initB_sym4 (r : Rc) (hr : r.Ok) (x : Nat) (hx : x ∈ [2, 3]) : Sym4 (r.initB x) := by
  have hE : Sym4 (3 :: 3 :: List.replicate (r.E.length - 2) 2) :=
    sym4_B (by simp) (sym4_B (by simp) (BitsD.rep _ _ (by simp)).sym4)
  have s3 : Sym4 ((3 :: 3 :: List.replicate (r.E.length - 2) 2) ++ 1 :: r.tl0 :: r.tlr) :=
    hE.app (sym4_M (sym4_B hr.tl0 hr.tlr.sym4))
  have s4 := hr.acc.sym4.app (sym4_M s3)
  exact sym4_B hr.F (sym4_B hr.O (sym4_B hx (sym4_M s4)))

theorem tailB_sym4 : ∀ (rs : List Rc), (∀ r ∈ rs, r.Ok) → Sym4 (tailB rs)
  | [], _ => Sym4.nil
  | r :: rs, h => sym4_M (sym4_M ((r.body_sym4 (h r (by simp))).app (tailB_sym4 rs (fun r' hr' => h r' (by simp [hr'])))))

theorem initRest : ∀ (rs : List Rc), (∀ r ∈ rs, r.Ok) → ∀ (r : Rc), r.Ok → ∀ (A : List Nat), Sym4 A →
    znttLogic.Reach (hdR QNTT.WH0 A (r.body ++ tailB rs)) (hd QNTT.RZ0 (A ++ r.initB 2 ++ tailI rs) [])
  | [], _, r, hr, A, hA => by
    have h1 := recHead0 A r hr [] hA Sym4.nil
    have h2 := recWS A r hr [] hA Sym4.nil 2 (by simp)
    have h3 := wsEnd (A ++ r.initB 2) [] (hA.app (r.initB_sym4 hr 2 (by simp))) (fun _ h => by simp at h)
    simp only [tailB, tailI, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact h1.trans (h2.trans h3)
  | r' :: rs, hok, r, hr, A, hA => by
    have hr' : r'.Ok := hok r' (by simp)
    have hrs : ∀ x ∈ rs, x.Ok := fun x hx => hok x (by simp [hx])
    have sT : Sym4 (tailB (r' :: rs)) := tailB_sym4 _ hok
    have h1 := recHead0 A r hr _ hA sT
    have h2 := recWS A r hr _ hA sT 2 (by simp)
    have sA' : Sym4 (A ++ r.initB 2) := hA.app (r.initB_sym4 hr 2 (by simp))
    have sR : Sym4 (r'.body ++ tailB rs) := (r'.body_sym4 hr').app (tailB_sym4 rs hrs)
    have h3 := wsMM (A ++ r.initB 2) [] (r'.body ++ tailB rs) sA' (fun _ h => by simp at h) sR
    have h4 := initRest rs hrs r' hr' (A ++ r.initB 2 ++ [] ++ [1, 1]) (by simpa using sA'.app (sym4_M (sym4_M Sym4.nil)))
    simp only [tailB, tailI, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))

/-- First record after the parameters: input flag `1`, then the others get `0`. -/
theorem initFirst (A : List Nat) (r : Rc) (hr : r.Ok) (rs : List Rc) (hrs : ∀ x ∈ rs, x.Ok) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.WH1 A (r.body ++ tailB rs)) (hd QNTT.RZ0 (A ++ r.initB 3 ++ tailI rs) []) := by
  cases rs with
  | nil =>
    have h1 := recHead1 A r hr [] hA Sym4.nil
    have h2 := recWS A r hr [] hA Sym4.nil 3 (by simp)
    have h3 := wsEnd (A ++ r.initB 3) [] (hA.app (r.initB_sym4 hr 3 (by simp))) (fun _ h => by simp at h)
    simp only [tailB, tailI, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact h1.trans (h2.trans h3)
  | cons r' rs =>
    have hr' : r'.Ok := hrs r' (by simp)
    have hrs' : ∀ x ∈ rs, x.Ok := fun x hx => hrs x (by simp [hx])
    have sT : Sym4 (tailB (r' :: rs)) := tailB_sym4 _ hrs
    have h1 := recHead1 A r hr _ hA sT
    have h2 := recWS A r hr _ hA sT 3 (by simp)
    have sA' : Sym4 (A ++ r.initB 3) := hA.app (r.initB_sym4 hr 3 (by simp))
    have sR : Sym4 (r'.body ++ tailB rs) := (r'.body_sym4 hr').app (tailB_sym4 rs hrs')
    have h3 := wsMM (A ++ r.initB 3) [] (r'.body ++ tailB rs) sA' (fun _ h => by simp at h) sR
    have h4 := initRest rs hrs' r' hr' (A ++ r.initB 3 ++ [] ++ [1, 1]) (by simpa using sA'.app (sym4_M (sym4_M Sym4.nil)))
    simp only [tailB, tailI, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))

/-- The witness initialisation `WI0` .. `RZ0`. -/
theorem witnessInit (L R Pm Pm' : List Nat) (hL : NoB L) (hRest : Rest Pm Pm') (r : Rc) (hr : r.Ok)
    (rs : List Rc) (hrs : ∀ x ∈ rs, x.Ok) (hLR : L ++ R = Pm ++ 1 :: 1 :: (r.body ++ tailB rs)) :
    znttLogic.Reach (hd QNTT.WI0 L R)
      (hd QNTT.RZ0 (Pm' ++ [1, 1] ++ r.initB 3 ++ tailI rs) []) := by
  have sT : Sym4 (r.body ++ tailB rs) := (r.body_sym4 hr).app (tailB_sym4 rs hrs)
  have sR : Sym4 R := by
    have : Sym4 (L ++ R) := by
      rw [hLR]; exact hRest.sym4_src.app (sym4_M (sym4_M sT))
    intro x hx; exact this x (List.mem_append_right _ hx)
  have h1 := wi0Scan L R hL sR
  rw [hLR] at h1
  have h2 := wi1Walk hRest [] (1 :: 1 :: (r.body ++ tailB rs)) Sym4.nil (sym4_M (sym4_M sT))
  have h3 := wi1MM (Pm') (r.body ++ tailB rs) hRest.sym4_dst sT
  have h4 := initFirst (Pm' ++ [1, 1]) r hr rs hrs (hRest.sym4_dst.app (sym4_M (sym4_M Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

/-! ### Pass start: `RZ0` .. `FAL` -/

theorem rz0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RZ0 L R) (hdR QNTT.RZ1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rz1Block (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RZ1 A (f ++ rest)) (hdR QNTT.RZ1 (A ++ f) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFF (env := [A, f, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rz1Field (A : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RZ1 A (1 :: b :: rest)) (hdR QNTT.RZ1 (A ++ [1, b]) rest) := by
  have hV : Valid [ALL, ALL] [A, rest] := Valid.cons hA (Valid.cons hr (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 2, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, rest]) (E := []) (k := 6) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 3, .blk 1 .id])
      (ls' := [.blk 0 .id, .sym 1, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rz1Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.RZ1 A (u ++ rest)) (hdR QNTT.RZ1 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := rz1Block A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have h1 := rz1Field A b (u ++ rest) hA hb (hu'.sym4.app hr)
    have h2 := ih (A ++ [1, b]) rest (hA.app sb) hr
    simpa using h1.trans h2

theorem rz1MM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RZ1 A (1 :: 1 :: R)) (hdR QNTT.RH0 (A ++ [1, 1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem rh0Step (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH0 A (a :: R)) (hdR QNTT.RH1 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rh1Step (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH1 A (a :: R)) (hdR QNTT.RH2 (A ++ [a]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rai (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RAi A (a :: R)) (hdR QNTT.RA0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ra0 (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RA0 A (a :: R)) (hdR QNTT.RA1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem rh2a (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH2 A (2 :: R)) (hdR QNTT.RH3 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rh2b (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH2 A (3 :: R)) (hdR QNTT.RH4 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rh3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH3 A (1 :: R)) (hdR QNTT.RA0 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rh4 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RH4 A (1 :: R)) (hdR QNTT.RAi (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ra1 (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RA1 A (f ++ 1 :: R)) (hdR QNTT.RSE (A ++ List.replicate f.length 2 ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 2), .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rse (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RSE A (f ++ 1 :: R)) (hdR QNTT.RSB (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rsb (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RSB A (f ++ 1 :: R)) (hdR QNTT.RU (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ru (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RU A (List.replicate a 2 ++ 3 :: R))
      (hdR QNTT.RU2 (A ++ List.replicate a 3 ++ [3]) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3), .sym 3]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ru2 (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RU2 A (f ++ 1 :: R)) (hdR QNTT.RN (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ru2End (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.RU2 A f) (hd QNTT.FAL (A ++ f) []) := by
  have hV : Valid [ALL, [2, 3]] [A, f] := Valid.cons hA (Valid.cons hf (Valid.nil _))
  exact checkFT (env := [A, f]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rnStep (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RN A (1 :: R)) (hdR QNTT.RH0 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The accumulator after the pass start: `1` (no input) or `2` (input). -/
def accI (pf L : Nat) : List Nat :=
  if pf = 3 then 3 :: 3 :: List.replicate (L - 2) 2 else 3 :: List.replicate (L - 1) 2

theorem inALL {a : Nat} (h : a ∈ [2, 3]) : a ∈ ALL := by
  simp at h; rcases h with rfl | rfl <;> simp [ALL]

theorem all1 : 1 ∈ ALL := by simp [ALL]
theorem all2 : 2 ∈ ALL := by simp [ALL]
theorem all3 : 3 ∈ ALL := by simp [ALL]

local macro "sy" : tactic => `(tactic| (simp only [Sym4_app_iff, Sym4_cons_iff, Sym4_rep_iff, Sym4_nil_iff,
  all1, all2, all3, or_true, true_and, and_true, and_self, *]; done))

theorem recPass2 (A : List Nat) (r : Rc) (hr : r.Ok) (hPf : r.Pf = 2) (hacc2 : 2 ≤ r.acc.length)
    (a : Nat) (ur' Tl : List Nat) (hu : r.u0 :: r.ur = List.replicate a 2 ++ 3 :: ur')
    (hA : Sym4 A) (hTl : Sym4 Tl) :
    znttLogic.Reach (hdR QNTT.RH0 A (r.body ++ Tl))
      (hdR QNTT.RU2 (A ++ [2, r.O, 2] ++ 1 :: (accI 2 r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 :: (List.replicate a 3 ++ [3])))))
        (ur' ++ Tl)) := by
  obtain ⟨a0, a1, aT, hacc⟩ : ∃ a0 a1 aT, r.acc = a0 :: a1 :: aT := by
    match h : r.acc, hacc2 with
    | a0 :: a1 :: aT, _ => exact ⟨a0, a1, aT, rfl⟩
  have hF := hr.F; have hO := hr.O
  have hAcc := hr.acc; rw [hacc] at hAcc
  have ha0 : a0 ∈ [2, 3] := hAcc a0 (by simp)
  have ha1 : a1 ∈ [2, 3] := hAcc a1 (by simp)
  have haT : BitsD aT := fun x hx => hAcc x (by simp [hx])
  have hur' : BitsD ur' := by
    intro x hx
    have h2 : x ∈ r.u0 :: r.ur := by rw [hu]; simp [hx]
    simp at h2; rcases h2 with h2 | h2
    · rw [h2]; exact hr.u0
    · exact hr.ur x h2
  have fF := inALL hF; have fO := inALL hO; have f0 := inALL ha0; have f1 := inALL ha1
  have sE := hr.E.sym4; have sB := hr.br.sym4; have sT := haT.sym4; have sU := hur'.sym4
  have fb := inALL hr.b0
  have e : r.body ++ Tl = r.F :: r.O :: 2 :: 1 :: a0 :: a1 :: (aT ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
      (List.replicate a 2 ++ 3 :: (ur' ++ Tl))))) := by
    simp [Rc.body, Rc.tlr, Rc.tl0, hPf, hacc, hu]
  rw [e]
  have hA1 : BitsD (a1 :: aT) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact ha1; exact haT x hx
  have hBB : BitsD (r.b0 :: r.br) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact hr.b0; exact hr.br x hx
  refine (rh0Step A r.F _ hF hA ?_).trans ((rh1Step _ r.O _ hO ?_ ?_).trans ((rh2a _ _ ?_ ?_).trans
    ((rh3 _ _ ?_ ?_).trans ((ra0 _ a0 _ ha0 ?_ ?_).trans ((ra1 _ (a1 :: aT) _ ?_ hA1 ?_).trans
    ((rse _ r.E _ ?_ hr.E ?_).trans ((rsb _ (r.b0 :: r.br) _ ?_ hBB ?_).trans
    ((ru _ a _ ?_ ?_).of_eq rfl ?_))))))))
  all_goals first | sy | skip
  simp [accI, hacc]


theorem recPass3 (A : List Nat) (r : Rc) (hr : r.Ok) (hPf : r.Pf = 3) (hacc2 : 2 ≤ r.acc.length)
    (a : Nat) (ur' Tl : List Nat) (hu : r.u0 :: r.ur = List.replicate a 2 ++ 3 :: ur')
    (hA : Sym4 A) (hTl : Sym4 Tl) :
    znttLogic.Reach (hdR QNTT.RH0 A (r.body ++ Tl))
      (hdR QNTT.RU2 (A ++ [2, r.O, 3] ++ 1 :: (accI 3 r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 :: (List.replicate a 3 ++ [3])))))
        (ur' ++ Tl)) := by
  obtain ⟨a0, a1, aT, hacc⟩ : ∃ a0 a1 aT, r.acc = a0 :: a1 :: aT := by
    match h : r.acc, hacc2 with
    | a0 :: a1 :: aT, _ => exact ⟨a0, a1, aT, rfl⟩
  have hF := hr.F; have hO := hr.O
  have hAcc := hr.acc; rw [hacc] at hAcc
  have ha0 : a0 ∈ [2, 3] := hAcc a0 (by simp)
  have ha1 : a1 ∈ [2, 3] := hAcc a1 (by simp)
  have haT : BitsD aT := fun x hx => hAcc x (by simp [hx])
  have hur' : BitsD ur' := by
    intro x hx
    have h2 : x ∈ r.u0 :: r.ur := by rw [hu]; simp [hx]
    simp at h2; rcases h2 with h2 | h2
    · rw [h2]; exact hr.u0
    · exact hr.ur x h2
  have fF := inALL hF; have fO := inALL hO; have f0 := inALL ha0; have f1 := inALL ha1
  have sE := hr.E.sym4; have sB := hr.br.sym4; have sT := haT.sym4; have sU := hur'.sym4
  have fb := inALL hr.b0
  have e : r.body ++ Tl = r.F :: r.O :: 3 :: 1 :: a0 :: a1 :: (aT ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
      (List.replicate a 2 ++ 3 :: (ur' ++ Tl))))) := by
    simp [Rc.body, Rc.tlr, Rc.tl0, hPf, hacc, hu]
  rw [e]
  have hA1 : BitsD (a1 :: aT) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact ha1; exact haT x hx
  have hBB : BitsD (r.b0 :: r.br) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact hr.b0; exact hr.br x hx
  refine (rh0Step A r.F _ hF hA ?_).trans ((rh1Step _ r.O _ hO ?_ ?_).trans ((rh2b _ _ ?_ ?_).trans
    ((rh4 _ _ ?_ ?_).trans ((rai _ a0 _ ha0 ?_ ?_).trans ((ra0 _ a1 _ ha1 ?_ ?_).trans ((ra1 _ aT _ ?_ haT ?_).trans
    ((rse _ r.E _ ?_ hr.E ?_).trans ((rsb _ (r.b0 :: r.br) _ ?_ hBB ?_).trans
    ((ru _ a _ ?_ ?_).of_eq rfl ?_)))))))))
  all_goals first | sy | skip
  simp [accI, hacc]

/-- `RU` restores the leading marks of a pointer. -/
def restoreU : List Nat → List Nat
  | 2 :: l => 3 :: restoreU l
  | l => l

theorem restoreU_rep (a : Nat) (ur : List Nat) :
    restoreU (List.replicate a 2 ++ 3 :: ur) = List.replicate a 3 ++ 3 :: ur := by
  induction a with
  | zero => simp [restoreU]
  | succ a ih => simp [List.replicate_succ, restoreU, ih]

/-- The record after the pass start. -/
def Rc.ps (r : Rc) : Rc :=
  { F := 2, O := r.O, Pf := r.Pf, acc := accI r.Pf r.acc.length, E := r.E, b0 := r.b0, br := r.br,
    u0 := (restoreU (r.u0 :: r.ur)).headD 3, ur := (restoreU (r.u0 :: r.ur)).tail }

/-- The pointer has the form `0^a 1 ...` (so `RU` stops). -/
def Rc.Rest (r : Rc) : Prop := ∃ a ur', r.u0 :: r.ur = List.replicate a 2 ++ 3 :: ur'

theorem Rc.ps_body (r : Rc) (hr : r.Rest) :
    r.ps.body = [2, r.O, r.Pf] ++ 1 :: (accI r.Pf r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
      restoreU (r.u0 :: r.ur)))) := by
  obtain ⟨a, ur', h⟩ := hr
  have hu' : restoreU (r.u0 :: r.ur) = List.replicate a 3 ++ 3 :: ur' := by rw [h, restoreU_rep]
  simp only [Rc.ps, Rc.body, Rc.tlr, Rc.tl0, hu']
  cases a <;> simp [List.replicate_succ]

def tailP : List Rc → List Nat
  | [] => []
  | r :: rs => 1 :: 1 :: (r.ps.body ++ tailP rs)

theorem recPassC (A : List Nat) (r : Rc) (hr : r.Ok) (hacc2 : 2 ≤ r.acc.length)
    (a : Nat) (ur' Tl : List Nat) (hu : r.u0 :: r.ur = List.replicate a 2 ++ 3 :: ur')
    (hA : Sym4 A) (hTl : Sym4 Tl) :
    znttLogic.Reach (hdR QNTT.RH0 A (r.body ++ Tl))
      (hdR QNTT.RU2 (A ++ [2, r.O, r.Pf] ++ 1 :: (accI r.Pf r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
        (List.replicate a 3 ++ [3]))))) (ur' ++ Tl)) := by
  have hP := hr.Pf
  simp at hP; rcases hP with h | h
  · have := recPass2 A r hr h hacc2 a ur' Tl hu hA hTl
    rw [h]; exact this
  · have := recPass3 A r hr h hacc2 a ur' Tl hu hA hTl
    rw [h]; exact this

theorem Rc.ur_bits (r : Rc) (hr : r.Ok) (a : Nat) (ur' : List Nat) (hu : r.u0 :: r.ur = List.replicate a 2 ++ 3 :: ur') :
    BitsD ur' := by
  intro x hx
  have h2 : x ∈ r.u0 :: r.ur := by rw [hu]; simp [hx]
  simp at h2; rcases h2 with h2 | h2
  · rw [h2]; exact hr.u0
  · exact hr.ur x h2

/-- Records ready for a pass start. -/
structure Rc.PS (r : Rc) : Prop where
  ok : r.Ok
  acc2 : 2 ≤ r.acc.length
  rest : r.Rest

theorem Rc.ps_sym4 (r : Rc) (h : r.PS) : Sym4 r.ps.body := by
  obtain ⟨a, ur', hu⟩ := h.rest
  rw [Rc.ps_body r h.rest]
  have hr := h.ok
  have hacc : Sym4 (accI r.Pf r.acc.length) := by
    unfold accI; split
    · exact sym4_B (by simp) (sym4_B (by simp) (BitsD.rep _ _ (by simp)).sym4)
    · exact sym4_B (by simp) (BitsD.rep _ _ (by simp)).sym4
  have hU : Sym4 (restoreU (r.u0 :: r.ur)) := by
    rw [hu, restoreU_rep]
    exact (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4.app (sym4_B (by simp) (r.ur_bits hr a ur' hu).sym4)
  have s1 := hr.br.sym4.app (sym4_M hU)
  exact sym4_B (by simp) (sym4_B hr.O (sym4_B hr.Pf
    (sym4_M (hacc.app (sym4_M (hr.E.sym4.app (sym4_M (sym4_B hr.b0 s1))))))))

theorem passStart : ∀ (rs : List Rc), (∀ r ∈ rs, r.PS) → ∀ (r : Rc), r.PS → ∀ (A : List Nat), Sym4 A →
    znttLogic.Reach (hdR QNTT.RH0 A (r.body ++ tailB rs)) (hd QNTT.FAL (A ++ r.ps.body ++ tailP rs) [])
  | [], _, r, hr, A, hA => by
    obtain ⟨a, ur', hu⟩ := hr.rest
    have h1 := recPassC A r hr.ok hr.acc2 a ur' [] hu hA Sym4.nil
    have bU := r.ur_bits hr.ok a ur' hu
    have eL : (A ++ [2, r.O, r.Pf] ++ 1 :: (accI r.Pf r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
        (List.replicate a 3 ++ [3]))))) ++ ur' = A ++ r.ps.body := by
      rw [Rc.ps_body r hr.rest, hu, restoreU_rep]; simp
    have sL := ((Sym4_app_iff.mp (eL ▸ hA.app (r.ps_sym4 hr))).1)
    have h2 := ru2End _ ur' sL bU
    rw [eL] at h2
    simp only [tailB, tailP, List.append_nil] at h1 ⊢
    exact h1.trans h2
  | r' :: rs, hok, r, hr, A, hA => by
    have hr' : r'.PS := hok r' (by simp)
    have hrs : ∀ x ∈ rs, x.PS := fun x hx => hok x (by simp [hx])
    obtain ⟨a, ur', hu⟩ := hr.rest
    have sT : Sym4 (tailB (r' :: rs)) := tailB_sym4 _ (fun x hx => (hok x hx).ok)
    have h1 := recPassC A r hr.ok hr.acc2 a ur' _ hu hA sT
    have bU := r.ur_bits hr.ok a ur' hu
    have eL : (A ++ [2, r.O, r.Pf] ++ 1 :: (accI r.Pf r.acc.length ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 ::
        (List.replicate a 3 ++ [3]))))) ++ ur' = A ++ r.ps.body := by
      rw [Rc.ps_body r hr.rest, hu, restoreU_rep]; simp
    have sL := ((Sym4_app_iff.mp (eL ▸ hA.app (r.ps_sym4 hr))).1)
    have sR : Sym4 (r'.body ++ tailB rs) :=
      (r'.body_sym4 hr'.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
    have h2 := ru2 _ ur' (1 :: (r'.body ++ tailB rs)) sL bU (sym4_M sR)
    have h3 := rnStep (_ ++ ur' ++ [1]) (r'.body ++ tailB rs) (by
      rw [eL]; exact (hA.app (r.ps_sym4 hr)).app (sym4_M Sym4.nil)) sR
    rw [eL] at h2 h3
    have h4 := passStart rs hrs r' hr' (A ++ r.ps.body ++ [1] ++ [1]) (by
      exact ((hA.app (r.ps_sym4 hr)).app (sym4_M Sym4.nil)).app (sym4_M Sym4.nil))
    simp only [tailB, tailP, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))

/-- The pass start `RZ0` .. `FAL` over the whole tape. -/
theorem passStartAll (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (r : Rc) (hr : r.PS)
    (rs : List Rc) (hrs : ∀ x ∈ rs, x.PS) (hLe : L = Pm ++ 1 :: 1 :: (r.body ++ tailB rs)) :
    znttLogic.Reach (hd QNTT.RZ0 L [])
      (hd QNTT.FAL (Pm ++ [1, 1] ++ r.ps.body ++ tailP rs) []) := by
  have sT : Sym4 (r.body ++ tailB rs) :=
    (r.body_sym4 hr.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
  have h1 := rz0Scan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := rz1Good hP [] (1 :: 1 :: (r.body ++ tailB rs)) Sym4.nil (sym4_M (sym4_M sT))
  have h3 := rz1MM Pm (r.body ++ tailB rs) hP.sym4 sT
  have h4 := passStart rs hrs r hr (Pm ++ [1, 1]) (hP.sym4.app (sym4_M (sym4_M Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.append_nil] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

end ZP.NTT

