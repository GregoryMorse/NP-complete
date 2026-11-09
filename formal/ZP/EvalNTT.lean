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
  rw [hLe]
  exact h1.trans (h2.trans (h3.trans h4))

/-! ### Decrement of the pointers: `DAc` .. `RFL` -/

theorem dacSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DAc A (f ++ 1 :: R)) (hdR QNTT.DE (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem deSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DE A (f ++ 1 :: R)) (hdR QNTT.DB (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dbSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DB A (f ++ 1 :: R)) (hdR QNTT.DU0 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dhSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DH A (f ++ 1 :: R)) (hdR QNTT.DAc (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du0Skip (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DU0 A (List.replicate a 2 ++ R)) (hdR QNTT.DU0 (A ++ List.replicate a 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du0Hit (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DU0 A (3 :: R)) (hdR QNTT.DU1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du1Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DU1 (A ++ [3]) (3 :: R)) (hd QNTT.DU2 (A ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du2Mark (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.DU2 (A ++ [3]) R) (hdR QNTT.DN0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du1Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DU1 A (2 :: R)) (hdR QNTT.DN0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DU1 A (1 :: R)) (hdR QNTT.DN1 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem du1B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.DU1 A []) (hd QNTT.RFL A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dn0Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DN0 A (f ++ R)) (hdR QNTT.DN0 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dn0M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DN0 A (1 :: R)) (hdR QNTT.DN1 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dn0B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.DN0 A []) (hd QNTT.RFL A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem dn1 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.DN1 A (1 :: R)) (hdR QNTT.DH (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- The pointer decrement: the first mark of `1 1` becomes `0`. -/
def decU : List Nat → List Nat
  | 2 :: l => 2 :: decU l
  | 3 :: 3 :: l => 2 :: 3 :: l
  | l => l

theorem decU_rep (a : Nat) (rest : List Nat) :
    decU (List.replicate a 2 ++ 3 :: rest) = List.replicate a 2 ++
      (match rest with | 3 :: l => 2 :: 3 :: l | _ => 3 :: rest) := by
  induction a with
  | zero => cases rest with
    | nil => simp [decU]
    | cons x l => rcases x with _ | _ | _ | _ | x <;> simp [decU]
  | succ a ih => simp [List.replicate_succ, decU, ih]

theorem dn0Fin (A f T : List Nat) (hA : Sym4 A) (hf : BitsD f) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.DN0 A (f ++ 1 :: 1 :: T)) (hdR QNTT.DH (A ++ f ++ [1, 1]) T) := by
  have h1 := dn0Block A f (1 :: 1 :: T) hA hf (sym4_M (sym4_M hT))
  have h2 := dn0M (A ++ f) (1 :: T) (hA.app hf.sym4) (sym4_M hT)
  have h3 := dn1 (A ++ f ++ [1]) T ((hA.app hf.sym4).app (sym4_M Sym4.nil)) hT
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

theorem dn0FinE (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.DN0 A f) (hd QNTT.RFL (A ++ f) []) := by
  have h1 := dn0Block A f [] hA hf Sym4.nil
  have h2 := dn0B (A ++ f) (hA.app hf.sym4)
  simp only [List.append_nil] at h1 ⊢
  exact h1.trans h2

/-- The pointer of one record, followed by `MM`. -/
theorem uDecMM (A : List Nat) (a : Nat) (rest T : List Nat) (hA : Sym4 A) (hr : BitsD rest) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.DU0 A (List.replicate a 2 ++ 3 :: (rest ++ 1 :: 1 :: T)))
      (hdR QNTT.DH (A ++ decU (List.replicate a 2 ++ 3 :: rest) ++ [1, 1]) T) := by
  have sA2 : Sym4 (A ++ List.replicate a 2) := hA.app (BitsD.rep _ _ (by simp)).sym4
  have sA3 : Sym4 (A ++ List.replicate a 2 ++ [3]) := sA2.app (sym4_cell 3 (by simp))
  have sM : Sym4 (1 :: 1 :: T) := sym4_M (sym4_M hT)
  cases rest with
  | nil =>
    have h1 := du0Skip A a (3 :: 1 :: 1 :: T) hA (sym4_B (by simp) sM)
    have h2 := du0Hit (A ++ List.replicate a 2) (1 :: 1 :: T) sA2 sM
    have h3 := du1M (A ++ List.replicate a 2 ++ [3]) (1 :: T) sA3 (sym4_M hT)
    have h4 := dn1 (A ++ List.replicate a 2 ++ [3] ++ [1]) T (sA3.app (sym4_cell 1 (by simp))) hT
    rw [decU_rep]
    simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))
  | cons x l =>
    have hx : x ∈ [2, 3] := hr x (by simp)
    have hl : BitsD l := fun y hy => hr y (by simp [hy])
    have h1 := du0Skip A a (3 :: x :: (l ++ 1 :: 1 :: T)) hA (sym4_B (by simp) (sym4_B hx (hl.sym4.app sM)))
    have h2 := du0Hit (A ++ List.replicate a 2) (x :: (l ++ 1 :: 1 :: T)) sA2 (sym4_B hx (hl.sym4.app sM))
    simp at hx; rcases hx with rfl | rfl
    · have h3 := du1Zero (A ++ List.replicate a 2 ++ [3]) (l ++ 1 :: 1 :: T) sA3 (hl.sym4.app sM)
      have h4 := dn0Fin (A ++ List.replicate a 2 ++ [3] ++ [2]) l T (sA3.app (sym4_cell 2 (by simp))) hl hT
      rw [decU_rep]
      simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 ⊢
      exact h1.trans (h2.trans (h3.trans h4))
    · have h3 := du1Two (A ++ List.replicate a 2) (l ++ 1 :: 1 :: T) sA2 (hl.sym4.app sM)
      have h4 := du2Mark (A ++ List.replicate a 2) (3 :: (l ++ 1 :: 1 :: T)) sA2 (sym4_B (by simp) (hl.sym4.app sM))
      have h5 := dn0Fin (A ++ List.replicate a 2 ++ [2]) (3 :: l) T (sA2.app (sym4_cell 2 (by simp)))
        (fun y hy => by simp at hy; rcases hy with rfl | hy; simp; exact hl y hy) hT
      rw [decU_rep]
      simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 h5 ⊢
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem uDecEnd (A : List Nat) (a : Nat) (rest : List Nat) (hA : Sym4 A) (hr : BitsD rest) :
    znttLogic.Reach (hdR QNTT.DU0 A (List.replicate a 2 ++ 3 :: rest))
      (hd QNTT.RFL (A ++ decU (List.replicate a 2 ++ 3 :: rest)) []) := by
  have sA2 : Sym4 (A ++ List.replicate a 2) := hA.app (BitsD.rep _ _ (by simp)).sym4
  have sA3 : Sym4 (A ++ List.replicate a 2 ++ [3]) := sA2.app (sym4_cell 3 (by simp))
  cases rest with
  | nil =>
    have h1 := du0Skip A a [3] hA (sym4_cell 3 (by simp))
    have h2 := du0Hit (A ++ List.replicate a 2) [] sA2 Sym4.nil
    have h3 := du1B (A ++ List.replicate a 2 ++ [3]) sA3
    rw [decU_rep]
    simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 ⊢
    exact h1.trans (h2.trans h3)
  | cons x l =>
    have hx : x ∈ [2, 3] := hr x (by simp)
    have hl : BitsD l := fun y hy => hr y (by simp [hy])
    have h1 := du0Skip A a (3 :: x :: l) hA (sym4_B (by simp) (sym4_B hx hl.sym4))
    have h2 := du0Hit (A ++ List.replicate a 2) (x :: l) sA2 (sym4_B hx hl.sym4)
    simp at hx; rcases hx with rfl | rfl
    · have h3 := du1Zero (A ++ List.replicate a 2 ++ [3]) l sA3 hl.sym4
      have h4 := dn0FinE (A ++ List.replicate a 2 ++ [3] ++ [2]) l (sA3.app (sym4_cell 2 (by simp))) hl
      rw [decU_rep]
      simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 ⊢
      exact h1.trans (h2.trans (h3.trans h4))
    · have h3 := du1Two (A ++ List.replicate a 2) l sA2 hl.sym4
      have h4 := du2Mark (A ++ List.replicate a 2) (3 :: l) sA2 (sym4_B (by simp) hl.sym4)
      have h5 := dn0FinE (A ++ List.replicate a 2 ++ [2]) (3 :: l) (sA2.app (sym4_cell 2 (by simp)))
        (fun y hy => by simp at hy; rcases hy with rfl | hy; simp; exact hl y hy)
      rw [decU_rep]
      simp only [List.nil_append, List.append_assoc, List.cons_append] at h1 h2 h3 h4 h5 ⊢
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- The part of a record after `Pf M`. -/
def Rc.tl (r : Rc) : List Nat :=
  r.acc ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 :: r.u0 :: r.ur))

theorem Rc.body_eq (r : Rc) : r.body = [r.F, r.O, r.Pf] ++ 1 :: r.tl := by
  simp [Rc.body, Rc.tl, Rc.tlr, Rc.tl0]

/-- The record after the pointer decrement. -/
def Rc.dec (r : Rc) : Rc :=
  { r with u0 := (decU (r.u0 :: r.ur)).headD 3, ur := (decU (r.u0 :: r.ur)).tail }

structure Rc.DE (r : Rc) : Prop where
  ok : r.Ok
  rest : r.Rest

theorem Rc.dec_tl (r : Rc) (h : r.Rest) :
    r.dec.tl = r.acc ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 :: decU (r.u0 :: r.ur))) := by
  obtain ⟨a, ur', hu⟩ := h
  have hd : decU (r.u0 :: r.ur) ≠ [] := by
    rw [hu, decU_rep]; cases ur' with
    | nil => simp
    | cons x l => rcases x with _ | _ | _ | _ | x <;> simp
  simp only [Rc.dec, Rc.tl]
  generalize decU (r.u0 :: r.ur) = d at hd ⊢
  cases d with
  | nil => exact absurd rfl hd
  | cons x l => simp

theorem Rc.dec_body (r : Rc) (h : r.Rest) :
    r.dec.body = [r.F, r.O, r.Pf] ++ 1 :: (r.acc ++ 1 :: (r.E ++ 1 :: r.b0 :: (r.br ++ 1 :: decU (r.u0 :: r.ur)))) := by
  rw [Rc.body_eq, Rc.dec_tl r h]
  rfl

theorem Rc.tl_sym4 (r : Rc) (hr : r.Ok) : Sym4 r.tl := r.tail_sym4 hr

def tailD : List Rc → List Nat
  | [] => []
  | r :: rs => 1 :: 1 :: (r.dec.body ++ tailD rs)

theorem decRecE (A : List Nat) (r : Rc) (hr : r.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.DAc A r.tl) (hd QNTT.RFL (A ++ r.dec.tl) []) := by
  obtain ⟨a, ur', hu⟩ := hr.rest
  have ho := hr.ok
  have hBB : BitsD (r.b0 :: r.br) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact ho.b0; exact ho.br x hx
  have bU := r.ur_bits ho a ur' hu
  have e : r.tl = r.acc ++ 1 :: (r.E ++ 1 :: ((r.b0 :: r.br) ++ 1 :: (List.replicate a 2 ++ 3 :: ur'))) := by
    simp [Rc.tl, hu]
  have sAcc := ho.acc.sym4; have sE := ho.E.sym4; have sBB := hBB.sym4
  rw [e]
  refine (dacSkip A r.acc _ hA ho.acc ?_).trans ((deSkip _ r.E _ ?_ ho.E ?_).trans
    ((dbSkip _ (r.b0 :: r.br) _ ?_ hBB ?_).trans ((uDecEnd _ a ur' ?_ bU).of_eq rfl ?_)))
  all_goals first
    | (simp only [Sym4_app_iff, Sym4_cons_iff, Sym4_rep_iff, Sym4_nil_iff, all1, all2, all3, or_true, true_and,
        and_true, and_self, hA, sAcc, sE, sBB, bU.sym4]; done)
    | skip
  rw [Rc.dec_tl r ⟨a, ur', hu⟩, hu]
  simp

theorem decRecM (A : List Nat) (r : Rc) (hr : r.DE) (T : List Nat) (hA : Sym4 A) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.DAc A (r.tl ++ 1 :: 1 :: T)) (hdR QNTT.DH (A ++ r.dec.tl ++ [1, 1]) T) := by
  obtain ⟨a, ur', hu⟩ := hr.rest
  have ho := hr.ok
  have hBB : BitsD (r.b0 :: r.br) := fun x hx => by
    simp at hx; rcases hx with rfl | hx; exact ho.b0; exact ho.br x hx
  have bU := r.ur_bits ho a ur' hu
  have e : r.tl ++ 1 :: 1 :: T = r.acc ++ 1 :: (r.E ++ 1 :: ((r.b0 :: r.br) ++ 1 ::
      (List.replicate a 2 ++ 3 :: (ur' ++ 1 :: 1 :: T)))) := by
    simp [Rc.tl, hu]
  have sAcc := ho.acc.sym4; have sE := ho.E.sym4; have sBB := hBB.sym4
  rw [e]
  refine (dacSkip A r.acc _ hA ho.acc ?_).trans ((deSkip _ r.E _ ?_ ho.E ?_).trans
    ((dbSkip _ (r.b0 :: r.br) _ ?_ hBB ?_).trans ((uDecMM _ a ur' T ?_ bU hT).of_eq rfl ?_)))
  all_goals first
    | (simp only [Sym4_app_iff, Sym4_cons_iff, Sym4_rep_iff, Sym4_nil_iff, all1, all2, all3, or_true, true_and,
        and_true, and_self, hA, hT, sAcc, sE, sBB, bU.sym4]; done)
    | skip
  rw [Rc.dec_tl r ⟨a, ur', hu⟩, hu]
  simp

theorem Rc.hdr_bits (r : Rc) (hr : r.Ok) : BitsD [r.F, r.O, r.Pf] := by
  intro y hy; simp at hy; rcases hy with rfl | rfl | rfl
  · exact hr.F
  · exact hr.O
  · exact hr.Pf

theorem decU_mem : ∀ (l : List Nat) (x : Nat), x ∈ decU l → x ∈ l ∨ x = 2
  | [], x, h => by simp [decU] at h
  | [a], x, h => by
    rcases a with _ | _ | _ | _ | a <;> simp [decU] at h ⊢ <;> simp [h]
  | 2 :: l, x, h => by
    simp only [decU, List.mem_cons] at h
    rcases h with h | h
    · right; exact h
    · rcases decU_mem l x h with h' | h'
      · left; simp [h']
      · right; exact h'
  | 3 :: 3 :: l, x, h => by
    simp only [decU, List.mem_cons] at h
    rcases h with h | h | h
    · right; exact h
    · left; simp [h]
    · left; simp [h]
  | 3 :: 2 :: l, x, h => by simp [decU] at h; left; simp [h]
  | 3 :: 1 :: l, x, h => by simp [decU] at h; left; simp [h]
  | 3 :: 0 :: l, x, h => by simp [decU] at h; left; simp [h]
  | 3 :: (n + 4) :: l, x, h => by simp [decU] at h; left; simp [h]
  | 1 :: l, x, h => by simp [decU] at h; left; simp [h]
  | 0 :: l, x, h => by simp [decU] at h; left; simp [h]
  | (n + 4) :: l, x, h => by simp [decU] at h; left; simp [h]

theorem decU_sym4 (l : List Nat) (h : Sym4 l) : Sym4 (decU l) := by
  intro x hx
  rcases decU_mem l x hx with h' | h'
  · exact h x h'
  · subst h'; simp [ALL]

theorem Rc.dec_tl_sym4 (r : Rc) (hr : r.DE) : Sym4 r.dec.tl := by
  rw [Rc.dec_tl r hr.rest]
  have ho := hr.ok
  have hU : Sym4 (r.u0 :: r.ur) := sym4_B ho.u0 ho.ur.sym4
  exact ho.acc.sym4.app (sym4_M (ho.E.sym4.app (sym4_M (sym4_B ho.b0 (ho.br.sym4.app (sym4_M (decU_sym4 _ hU)))))))

theorem decAll : ∀ (rs : List Rc), (∀ x ∈ rs, x.DE) → ∀ (r : Rc), r.DE → ∀ (A : List Nat), Sym4 A →
    znttLogic.Reach (hdR QNTT.DAc A (r.tl ++ tailB rs)) (hd QNTT.RFL (A ++ r.dec.tl ++ tailD rs) [])
  | [], _, r, hr, A, hA => by
    have := decRecE A r hr hA
    simpa [tailB, tailD] using this
  | r' :: rs, hok, r, hr, A, hA => by
    have hr' : r'.DE := hok r' (by simp)
    have hrs : ∀ x ∈ rs, x.DE := fun x hx => hok x (by simp [hx])
    have sRest : Sym4 (r'.tl ++ tailB rs) :=
      (r'.tl_sym4 hr'.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
    have sT : Sym4 (r'.body ++ tailB rs) :=
      (r'.body_sym4 hr'.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
    have h1 := decRecM A r hr (r'.body ++ tailB rs) hA sT
    have sA' : Sym4 (A ++ r.dec.tl ++ [1, 1]) := by
      exact (hA.app (r.dec_tl_sym4 hr)).app (sym4_M (sym4_M Sym4.nil))
    have h2 := dhSkip (A ++ r.dec.tl ++ [1, 1]) [r'.F, r'.O, r'.Pf] (r'.tl ++ tailB rs) sA' (r'.hdr_bits hr'.ok) sRest
    have h3 := decAll rs hrs r' hr' (A ++ r.dec.tl ++ [1, 1] ++ [r'.F, r'.O, r'.Pf] ++ [1]) (by
      exact (sA'.app (r'.hdr_bits hr'.ok).sym4).app (sym4_M Sym4.nil))
    rw [Rc.body_eq] at h1
    simp only [tailB, tailD, Rc.body_eq, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact h1.trans (h2.trans h3)

/-! ### Cursor entry: `FAL` .. `DAc` / `CP0` -/

theorem falScan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.FAL L R) (hdR QNTT.FAs [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fasBlock (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.FAs A (f ++ rest)) (hdR QNTT.FAs (A ++ f) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFF (env := [A, f, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fasField (A : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.FAs A (1 :: b :: rest)) (hdR QNTT.FAs (A ++ [1, b]) rest) := by
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

theorem fasGood {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.FAs A (u ++ rest)) (hdR QNTT.FAs (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := fasBlock A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have h1 := fasField A b (u ++ rest) hA hb (hu'.sym4.app hr)
    have h2 := ih (A ++ [1, b]) rest (hA.app sb) hr
    simpa using h1.trans h2

theorem fasMM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FAs A (1 :: 1 :: R)) (hdR QNTT.FA0 (A ++ [1, 1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fa0Mark (A : List Nat) (a : Nat) (R : List Nat) (ha : a ∈ [2, 3]) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FA0 A (a :: R)) (hdR QNTT.FA1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at ha; rcases ha with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fa1n (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FA1 A (2 :: R)) (hdR QNTT.FAn (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fa1o (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FA1 A (3 :: R)) (hdR QNTT.FAo (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fanSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FAn A (f ++ 1 :: R)) (hdR QNTT.DAc (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem faoSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FAo A (f ++ 1 :: R)) (hdR QNTT.CP0 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Cursor on the first record, a non-output node: decrement all pointers (`FAL` .. `RFL`). -/
theorem faN (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (r : Rc) (hr : r.DE) (hO : r.O = 2)
    (rs : List Rc) (hrs : ∀ x ∈ rs, x.DE) (hLe : L = Pm ++ 1 :: 1 :: (r.body ++ tailB rs)) :
    znttLogic.Reach (hd QNTT.FAL L [])
      (hd QNTT.RFL (Pm ++ [1, 1] ++ [3, r.O, r.Pf] ++ 1 :: r.dec.tl ++ tailD rs) []) := by
  have ho := hr.ok
  have sTl : Sym4 (r.tl ++ tailB rs) := (r.tl_sym4 ho).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
  have sT : Sym4 (r.body ++ tailB rs) := (r.body_sym4 ho).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
  have sPm := hP.sym4
  have sMM : Sym4 (Pm ++ [1, 1]) := sPm.app (sym4_M (sym4_M Sym4.nil))
  have h1 := falScan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := fasGood hP [] (1 :: 1 :: (r.body ++ tailB rs)) Sym4.nil (sym4_M (sym4_M sT))
  have h3 := fasMM Pm (r.body ++ tailB rs) sPm sT
  rw [Rc.body_eq] at h3
  have h4 := fa0Mark (Pm ++ [1, 1]) r.F (r.O :: r.Pf :: 1 :: (r.tl ++ tailB rs)) ho.F sMM
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1n (Pm ++ [1, 1] ++ [3]) (r.Pf :: 1 :: (r.tl ++ tailB rs)) (sMM.app (sym4_cell 3 (by simp)))
    (sym4_B ho.Pf (sym4_M sTl))
  have h6 := fanSkip (Pm ++ [1, 1] ++ [3] ++ [2]) [r.Pf] (r.tl ++ tailB rs)
    ((sMM.app (sym4_cell 3 (by simp))).app (sym4_cell 2 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have h7 := decAll rs hrs r hr (Pm ++ [1, 1] ++ [3] ++ [2] ++ [r.Pf] ++ [1]) (by
    have := (((sMM.app (sym4_cell 3 (by simp))).app (sym4_cell 2 (by simp))).app
      (sym4_B ho.Pf Sym4.nil)).app (sym4_M Sym4.nil)
    exact this)
  simp only [hO, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, Rc.body_eq] at h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [hLe]
  simp only [hO, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, Rc.body_eq]
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-! ### Finding the cursor: `RFL` .. `BU0` -/

theorem rflScan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.RFL L R) (hdR QNTT.RF0 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf0Block (A f rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RF0 A (f ++ rest)) (hdR QNTT.RF0 (A ++ f) rest) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, rest] :=
    Valid.cons hA (Valid.cons hf (Valid.cons hr (Valid.nil _)))
  exact checkFF (env := [A, f, rest]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf0Field (A : List Nat) (b : Nat) (rest : List Nat) (hA : Sym4 A) (hb : b ∈ [2, 3]) (hr : Sym4 rest) :
    znttLogic.Reach (hdR QNTT.RF0 A (1 :: b :: rest)) (hdR QNTT.RF0 (A ++ [1, b]) rest) := by
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

theorem rf0Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.RF0 A (u ++ rest)) (hdR QNTT.RF0 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := rf0Block A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have h1 := rf0Field A b (u ++ rest) hA hb (hu'.sym4.app hr)
    have h2 := ih (A ++ [1, b]) rest (hA.app sb) hr
    simpa using h1.trans h2

theorem rf0MM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RF0 A (1 :: 1 :: R)) (hdR QNTT.RF2 (A ++ [1, 1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf2Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RF2 A (2 :: R)) (hdR QNTT.RF0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf2One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RF2 A (3 :: R)) (hdR QNTT.RF3 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf3o (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RF3 A (3 :: R)) (hdR QNTT.RFo (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rf3n (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RF3 A (2 :: R)) (hdR QNTT.RFn (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rfnSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RFn A (f ++ 1 :: R)) (hdR QNTT.BU0n (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem rfoSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.RFo A (f ++ 1 :: R)) (hdR QNTT.BU0o (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem Rc.tl_good (r : Rc) (hr : r.Ok) (hacc : r.acc ≠ []) : GoodW (1 :: r.tl) := by
  obtain ⟨a0, ar, ha⟩ := List.exists_cons_of_ne_nil hacc
  obtain ⟨e0, er, he⟩ := List.exists_cons_of_ne_nil (show r.E ≠ [] by
    intro h; have := hr.Elen; rw [h] at this; simp at this)
  have hA := hr.acc; rw [ha] at hA
  have hE := hr.E; rw [he] at hE
  have g : ∀ (l : List Nat) (a : Nat), BitsD (a :: l) → a ∈ [2, 3] ∧ BitsD l := fun l a h =>
    ⟨h a (by simp), fun y hy => h y (by simp [hy])⟩
  obtain ⟨ha0, har⟩ := g _ _ hA
  obtain ⟨he0, her⟩ := g _ _ hE
  simp only [Rc.tl, ha, he]
  exact GoodW.mb ha0 (GoodW.app (GoodW.bits har) (GoodW.mb he0 (GoodW.app (GoodW.bits her)
    (GoodW.mb hr.b0 (GoodW.app (GoodW.bits hr.br) (GoodW.mb hr.u0 (GoodW.bits hr.ur)))))))

theorem Rc.rest_good (r : Rc) (hr : r.Ok) (hacc : r.acc ≠ []) : GoodW (r.O :: r.Pf :: 1 :: r.tl) :=
  GoodW.bit hr.O (GoodW.bit hr.Pf (r.tl_good hr hacc))

/-- Walk over records before the cursor (`F = 0`). -/
theorem rfPre : ∀ (pre : List Rc), (∀ x ∈ pre, x.Ok ∧ x.acc ≠[] ∧ x.F = 2) → ∀ (A R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach (hdR QNTT.RF0 A (tailB pre ++ 1 :: 1 :: R)) (hdR QNTT.RF2 (A ++ tailB pre ++ [1, 1]) R)
  | [], _, A, R, hA, hR => by
    simpa [tailB] using rf0MM A R hA hR
  | r :: pre, hok, A, R, hA, hR => by
    obtain ⟨ho, hac, hF⟩ := hok r (by simp)
    have hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2 := fun x hx => hok x (by simp [hx])
    have sP : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
    have sRest : Sym4 (r.O :: r.Pf :: 1 :: r.tl) := (r.rest_good ho hac).sym4
    have sM2 : Sym4 (tailB pre ++ 1 :: 1 :: R) := sP.app (sym4_M (sym4_M hR))
    have eb : r.body = 2 :: (r.O :: r.Pf :: 1 :: r.tl) := by simp [Rc.body_eq, hF]
    have h1 := rf0MM A (r.body ++ (tailB pre ++ 1 :: 1 :: R)) hA (by
      rw [eb]; exact sym4_B (by simp) (sRest.app sM2))
    have h2 := rf2Zero (A ++ [1, 1]) ((r.O :: r.Pf :: 1 :: r.tl) ++ (tailB pre ++ 1 :: 1 :: R))
      (hA.app (sym4_M (sym4_M Sym4.nil))) (sRest.app sM2)
    have h3 := rf0Good (r.rest_good ho hac) (A ++ [1, 1] ++ [2]) (tailB pre ++ 1 :: 1 :: R)
      ((hA.app (sym4_M (sym4_M Sym4.nil))).app (sym4_cell 2 (by simp))) sM2
    have h4 := rfPre pre hpre (A ++ [1, 1] ++ [2] ++ (r.O :: r.Pf :: 1 :: r.tl)) R
      (((hA.app (sym4_M (sym4_M Sym4.nil))).app (sym4_cell 2 (by simp))).app sRest) hR
    rw [eb] at h1
    simp only [tailB, eb, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    exact h1.trans (h2.trans (h3.trans h4))

theorem tailB_append (a b : List Rc) : tailB (a ++ b) = tailB a ++ tailB b := by
  induction a with
  | nil => simp [tailB]
  | cons r a ih => simp [tailB, ih]

/-- Cursor search: records before the cursor have `F = 0`, the cursor has `F = 1`. -/
theorem rfFind (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r : Rc) (hr : r.Ok) (hF : r.F = 3)
    (post : List Rc) (hpost : ∀ x ∈ post, x.Ok)
    (hLe : L = Pm ++ tailB (pre ++ r :: post)) :
    (r.O = 2 → znttLogic.Reach (hd QNTT.RFL L [])
      (hdR QNTT.BU0n (Pm ++ tailB pre ++ [1, 1, 3, 2, r.Pf, 1]) (r.tl ++ tailB post))) ∧
    (r.O = 3 → znttLogic.Reach (hd QNTT.RFL L [])
      (hdR QNTT.BU0o (Pm ++ tailB pre ++ [1, 1, 3, 3, r.Pf, 1]) (r.tl ++ tailB post))) := by
  have sP : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have sPost : Sym4 (tailB post) := tailB_sym4 post hpost
  have sTl : Sym4 (r.tl ++ tailB post) := (r.tl_sym4 hr).app sPost
  have sPm := hP.sym4
  have e : L = Pm ++ (tailB pre ++ 1 :: 1 :: (r.body ++ tailB post)) := by
    rw [hLe, tailB_append]; simp [tailB]
  have sBody : Sym4 (r.body ++ tailB post) := (r.body_sym4 hr).app sPost
  have h1 := rflScan L [] hL Sym4.nil
  have h2 := rf0Good hP [] (tailB pre ++ 1 :: 1 :: (r.body ++ tailB post)) Sym4.nil
    (sP.app (sym4_M (sym4_M sBody)))
  have h3 := rfPre pre hpre Pm (r.body ++ tailB post) sPm sBody
  have eb : r.body = 3 :: (r.O :: r.Pf :: 1 :: r.tl) := by simp [Rc.body_eq, hF]
  have sA : Sym4 (Pm ++ tailB pre ++ [1, 1]) := (sPm.app sP).app (sym4_M (sym4_M Sym4.nil))
  have sRest : Sym4 (r.O :: r.Pf :: 1 :: (r.tl ++ tailB post)) := sym4_B hr.O (sym4_B hr.Pf (sym4_M sTl))
  rw [eb] at h3
  have h4 := rf2One (Pm ++ tailB pre ++ [1, 1]) (r.O :: r.Pf :: 1 :: (r.tl ++ tailB post)) sA
    sRest
  have sA3 : Sym4 (Pm ++ tailB pre ++ [1, 1] ++ [3]) := sA.app (sym4_cell 3 (by simp))
  have sPf : BitsD [r.Pf] := fun y hy => by simp at hy; subst hy; exact hr.Pf
  have hsrc : Sym4 (r.Pf :: 1 :: (r.tl ++ tailB post)) := sym4_B hr.Pf (sym4_M sTl)
  constructor
  · intro hO
    have h5 := rf3n (Pm ++ tailB pre ++ [1, 1] ++ [3]) (r.Pf :: 1 :: (r.tl ++ tailB post)) sA3 hsrc
    have h6 := rfnSkip (Pm ++ tailB pre ++ [1, 1] ++ [3] ++ [2]) [r.Pf] (r.tl ++ tailB post)
      (sA3.app (sym4_cell 2 (by simp))) sPf sTl
    simp only [hO, e, eb, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 ⊢
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  · intro hO
    have h5 := rf3o (Pm ++ tailB pre ++ [1, 1] ++ [3]) (r.Pf :: 1 :: (r.tl ++ tailB post)) sA3 hsrc
    have h6 := rfoSkip (Pm ++ tailB pre ++ [1, 1] ++ [3] ++ [3]) [r.Pf] (r.tl ++ tailB post)
      (sA3.app (sym4_cell 3 (by simp))) sPf sTl
    simp only [hO, e, eb, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 ⊢
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem rfFind0 (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r : Rc) (hr : r.Ok) (hF : r.F = 3)
    (post : List Rc) (hpost : ∀ x ∈ post, x.Ok)
    (hLe : L = Pm ++ tailB (pre ++ r :: post)) :
    (r.O = 2 → znttLogic.Reach (hdR QNTT.RF0 [] L)
      (hdR QNTT.BU0n (Pm ++ tailB pre ++ [1, 1, 3, 2, r.Pf, 1]) (r.tl ++ tailB post))) ∧
    (r.O = 3 → znttLogic.Reach (hdR QNTT.RF0 [] L)
      (hdR QNTT.BU0o (Pm ++ tailB pre ++ [1, 1, 3, 3, r.Pf, 1]) (r.tl ++ tailB post))) := by
  have sP : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have sPost : Sym4 (tailB post) := tailB_sym4 post hpost
  have sTl : Sym4 (r.tl ++ tailB post) := (r.tl_sym4 hr).app sPost
  have sPm := hP.sym4
  have e : L = Pm ++ (tailB pre ++ 1 :: 1 :: (r.body ++ tailB post)) := by
    rw [hLe, tailB_append]; simp [tailB]
  have sBody : Sym4 (r.body ++ tailB post) := (r.body_sym4 hr).app sPost
  have h2 := rf0Good hP [] (tailB pre ++ 1 :: 1 :: (r.body ++ tailB post)) Sym4.nil
    (sP.app (sym4_M (sym4_M sBody)))
  have h3 := rfPre pre hpre Pm (r.body ++ tailB post) sPm sBody
  have eb : r.body = 3 :: (r.O :: r.Pf :: 1 :: r.tl) := by simp [Rc.body_eq, hF]
  have sA : Sym4 (Pm ++ tailB pre ++ [1, 1]) := (sPm.app sP).app (sym4_M (sym4_M Sym4.nil))
  have sRest : Sym4 (r.O :: r.Pf :: 1 :: (r.tl ++ tailB post)) := sym4_B hr.O (sym4_B hr.Pf (sym4_M sTl))
  rw [eb] at h3
  have h4 := rf2One (Pm ++ tailB pre ++ [1, 1]) (r.O :: r.Pf :: 1 :: (r.tl ++ tailB post)) sA
    sRest
  have sA3 : Sym4 (Pm ++ tailB pre ++ [1, 1] ++ [3]) := sA.app (sym4_cell 3 (by simp))
  have sPf : BitsD [r.Pf] := fun y hy => by simp at hy; subst hy; exact hr.Pf
  have hsrc : Sym4 (r.Pf :: 1 :: (r.tl ++ tailB post)) := sym4_B hr.Pf (sym4_M sTl)
  constructor
  · intro hO
    have h5 := rf3n (Pm ++ tailB pre ++ [1, 1] ++ [3]) (r.Pf :: 1 :: (r.tl ++ tailB post)) sA3 hsrc
    have h6 := rfnSkip (Pm ++ tailB pre ++ [1, 1] ++ [3] ++ [2]) [r.Pf] (r.tl ++ tailB post)
      (sA3.app (sym4_cell 2 (by simp))) sPf sTl
    simp only [hO, e, eb, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h2 h3 h4 h5 h6 ⊢
    exact h2.trans (h3.trans (h4.trans (h5.trans h6)))
  · intro hO
    have h5 := rf3o (Pm ++ tailB pre ++ [1, 1] ++ [3]) (r.Pf :: 1 :: (r.tl ++ tailB post)) sA3 hsrc
    have h6 := rfoSkip (Pm ++ tailB pre ++ [1, 1] ++ [3] ++ [3]) [r.Pf] (r.tl ++ tailB post)
      (sA3.app (sym4_cell 3 (by simp))) sPf sTl
    simp only [hO, e, eb, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h2 h3 h4 h5 h6 ⊢
    exact h2.trans (h3.trans (h4.trans (h5.trans h6)))

/-! ### Counters: `1^k 0^(w-k)` and the increments `IA*`, `IR*` -/

/-- A counter field of width `w` holding `k` marks (value `k - 1`). -/
def fld (w k : Nat) : List Nat := List.replicate k 3 ++ List.replicate (w - k) 2

/-- The successor of `k` modulo the width. -/
def incK (w k : Nat) : Nat := if k = w then 1 else k + 1

theorem ia0Skip (A : List Nat) (k : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IA0 A (List.replicate k 3 ++ R)) (hdR QNTT.IA0 (A ++ List.replicate k 3) R) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate k 3, R] :=
    Valid.cons hA (Valid.cons (repSet k 3) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate k 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ia0Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IA0 A (2 :: R)) (hdR QNTT.LA (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ia0M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IA0 (A ++ [3]) (1 :: R)) (hd QNTT.IAW (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem iawSweep (A : List Nat) (w : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IAW (A ++ [1] ++ List.replicate w 3) R)
      (hdR QNTT.IAW2 (A ++ [1]) (List.replicate w 2 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate w 3, R] :=
    Valid.cons hA (Valid.cons (repSet w 3) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A, List.replicate w 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 (.const 2), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem iaw2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IAW2 A (2 :: R)) (hdR QNTT.LA (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `IA0` .. `LA`: the counter of the next record is incremented (modulo its width). -/
theorem iaInc (A0 R : List Nat) (w k : Nat) (hk : 1 ≤ k) (hkw : k ≤ w) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IA0 (A0 ++ [1]) (fld w k ++ 1 :: R))
      (hdR QNTT.LA (A0 ++ [1] ++ List.replicate (incK w k) 3) (List.replicate (w - incK w k) 2 ++ 1 :: R)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sR1 : Sym4 (1 :: R) := sym4_M hR
  by_cases hkw' : k = w
  · subst hkw'
    obtain ⟨w', rfl⟩ : ∃ w', k = w' + 1 := ⟨k - 1, by omega⟩
    have h1 := ia0Skip (A0 ++ [1]) (w' + 1) (1 :: R) sA1 sR1
    have sK : Sym4 (A0 ++ [1] ++ List.replicate w' 3) := sA1.app (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4
    have h1' : znttLogic.Reach (hdR QNTT.IA0 (A0 ++ [1]) (fld (w' + 1) (w' + 1) ++ 1 :: R))
        (hdR QNTT.IA0 ((A0 ++ [1] ++ List.replicate w' 3) ++ [3]) (1 :: R)) :=
      h1.of_eq (by simp [fld]) (by simp [List.replicate_succ'])
    have h2 := ia0M (A0 ++ [1] ++ List.replicate w' 3) R sK hR
    have h3 := iawSweep A0 (w' + 1) (1 :: R) hA sR1
    have h4 := iaw2 (A0 ++ [1]) (List.replicate w' 2 ++ 1 :: R) sA1 (by
      exact (BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4.app sR1)
    simp only [incK, if_true] at *
    have e3 : A0 ++ [1] ++ List.replicate (w' + 1) 3 = A0 ++ [1] ++ List.replicate w' 3 ++ [3] := by
      simp [List.replicate_succ']
    rw [e3] at h3
    refine h1'.trans (h2.trans (h3.trans ?_))
    simpa [List.replicate_succ] using h4
  · obtain ⟨j, hj⟩ : ∃ j, w - k = j + 1 := ⟨w - k - 1, by omega⟩
    have h1 := ia0Skip (A0 ++ [1]) k (2 :: (List.replicate j 2 ++ 1 :: R)) sA1
      (sym4_B (by simp) ((BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4.app sR1))
    have h2 := ia0Zero (A0 ++ [1] ++ List.replicate k 3) (List.replicate j 2 ++ 1 :: R)
      (sA1.app (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4)
      ((BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4.app sR1)
    have hi : incK w k = k + 1 := by simp [incK, hkw']
    rw [hi, show w - (k + 1) = j by omega]
    have h1' : znttLogic.Reach (hdR QNTT.IA0 (A0 ++ [1]) (fld w k ++ 1 :: R))
        (hdR QNTT.IA0 (A0 ++ [1] ++ List.replicate k 3) (2 :: (List.replicate j 2 ++ 1 :: R))) :=
      h1.of_eq (by simp [fld, hj, List.replicate_succ]) rfl
    refine h1'.trans (h2.of_eq rfl ?_)
    simp [List.replicate_succ']

/-! ### Visiting a record: `LA` .. `CU*` .. `LN*` / `AB*` -/

theorem laSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LA A (f ++ 1 :: R)) (hdR QNTT.LE (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem leSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LE A (f ++ 1 :: R)) (hdR QNTT.LB (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lbSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LB A (f ++ 1 :: R)) (hdR QNTT.CU0 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem lhSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LH A (f ++ 1 :: R)) (hdR QNTT.LA (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem abe8Skip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB8 A (f ++ 1 :: R)) (hdR QNTT.AB9 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab9Skip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB9 A (f ++ 1 :: R)) (hdR QNTT.AB2 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab3Skip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ABR3 A (f ++ 1 :: R)) (hdR QNTT.LN0 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu0Skip (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU0 A (List.replicate a 2 ++ R)) (hdR QNTT.CU0 (A ++ List.replicate a 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu0Hit (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU0 A (3 :: R)) (hdR QNTT.CU1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu1Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU1 A (3 :: R)) (hdR QNTT.CU2 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu1Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU1 A (2 :: R)) (hdR QNTT.LN0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU1 A (1 :: R)) (hdR QNTT.LN1 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu1B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.CU1 A []) (hd QNTT.RFL A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu2Three (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU2 A (3 :: R)) (hdR QNTT.LN0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ln0Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LN0 A (f ++ R)) (hdR QNTT.LN0 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ln0M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LN0 A (1 :: R)) (hdR QNTT.LN1 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ln0B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.LN0 A []) (hd QNTT.RFL A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ln1 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.LN1 A (1 :: R)) (hdR QNTT.LH (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ### Captured record: add `b` to the accumulator (`AB*`, `IR*`) -/

theorem cu2Cap0 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU2 (A ++ [3]) (2 :: R)) (hd QNTT.AB0 (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu2CapM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CU2 (A ++ [3]) (1 :: R)) (hd QNTT.AB0 (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cu2CapB (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.CU2 (A ++ [3]) []) (hd QNTT.AB0 (A ++ [3]) []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := []) (ls' := [.blk 0 .id, .sym 3]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab0Sweep (X b u R : List Nat) (hX : Sym4 X) (hb : BitsD b) (hu : BitsD u) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.AB0 (X ++ b ++ [1] ++ u) R) (hd QNTT.AB1 (X ++ b) (1 :: u ++ R)) := by
  have hV : Valid [ALL, [2, 3], [2, 3], ALL] [X, b, u, R] :=
    Valid.cons hX (Valid.cons hb (Valid.cons hu (Valid.cons hR (Valid.nil _))))
  simpa using checkTT (env := [X, b, u, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id, .sym 1, .blk 2 .id]) (rs := [.blk 3 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.sym 1, .blk 2 .id, .blk 3 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab1Sweep (X b R : List Nat) (hX : Sym4 X) (hb : BitsD b) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.AB1 (X ++ [1] ++ b) R) (hdR QNTT.AB2 (X ++ [1]) (b ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, b, R] := Valid.cons hX (Valid.cons hb (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [X, b, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab2Sweep (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB2 A (List.replicate j 2 ++ 3 :: R))
      (hdR QNTT.AB3 (A ++ List.replicate j 2 ++ [3]) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] :=
    Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 3]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab3One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB3 (A ++ [3]) (3 :: R)) (hd QNTT.AB4 (A ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab3Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB3 (A ++ [3]) (2 :: R)) (hd QNTT.ABR (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab3M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB3 (A ++ [3]) (1 :: R)) (hd QNTT.ABR (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab4 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.AB4 (A ++ [3]) R) (hd QNTT.AB5 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ab5Sweep (X : List Nat) (j : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.AB5 (X ++ [1] ++ List.replicate j 2) R)
      (hd QNTT.AB6 X (1 :: List.replicate j 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [X, List.replicate j 2, R] :=
    Valid.cons hX (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ir0One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IR0 (A ++ [3]) R) (hd QNTT.IRW A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ir0Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IR0 (A ++ [2]) R) (hd QNTT.IR1 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ir1Sweep (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IR1 (A ++ [3] ++ List.replicate j 2) R)
      (hdR QNTT.IR2 (A ++ [3]) (List.replicate j 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] :=
    Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ir2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IR2 A (2 :: R)) (hdR QNTT.AB8 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem irwSweep (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IRW (A ++ [1] ++ List.replicate j 3) R)
      (hdR QNTT.IRW2 (A ++ [1]) (List.replicate j 2 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate j 3, R] :=
    Valid.cons hA (Valid.cons (repSet j 3) (Valid.cons hR (Valid.nil _)))
  exact checkTF (env := [A, List.replicate j 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 (.const 2), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem irw2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IRW2 A (2 :: R)) (hdR QNTT.AB8 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem rep_cons_app (j c : Nat) (R : List Nat) :
    List.replicate j c ++ c :: R = c :: (List.replicate j c ++ R) := by
  induction j with
  | zero => simp
  | succ j ih => simp [List.replicate_succ, ih]

theorem ab6Sweep (Z E R : List Nat) (hZ : Sym4 Z) (hE : BitsD E) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.AB6 (Z ++ [1] ++ E) R) (hd QNTT.IR0 Z (1 :: E ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [Z, E, R] := Valid.cons hZ (Valid.cons hE (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [Z, E, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `IR0` .. `AB8`: the accumulator is incremented (modulo its width). -/
theorem irInc (A0 R : List Nat) (w k : Nat) (hk : 1 ≤ k) (hkw : k ≤ w) (hA : Sym4 A0) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IR0 (A0 ++ [1] ++ fld w k) R)
      (hdR QNTT.AB8 (A0 ++ [1] ++ List.replicate (incK w k) 3) (List.replicate (w - incK w k) 2 ++ R)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  by_cases hkw' : k = w
  · subst hkw'
    obtain ⟨w', rfl⟩ : ∃ w', k = w' + 1 := ⟨k - 1, by omega⟩
    have sK : Sym4 (A0 ++ [1] ++ List.replicate w' 3) := sA1.app (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4
    have h1 := ir0One (A0 ++ [1] ++ List.replicate w' 3) R sK hR
    have h1' : znttLogic.Reach (hd QNTT.IR0 (A0 ++ [1] ++ fld (w' + 1) (w' + 1)) R)
        (hd QNTT.IRW (A0 ++ [1] ++ List.replicate w' 3) (2 :: R)) :=
      h1.of_eq (by simp [fld, List.replicate_succ']) rfl
    have h2 := irwSweep A0 w' (2 :: R) hA (sym4_B (by simp) hR)
    have h3 := irw2 (A0 ++ [1]) (List.replicate w' 2 ++ R) sA1
      ((BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4.app hR)
    simp only [incK, if_true] at *
    refine h1'.trans (h2.trans (h3.of_eq ?_ ?_))
    · simp [rep_cons_app]
    · simp [List.replicate_succ']
  · obtain ⟨j, hj⟩ : ∃ j, w - k = j + 1 := ⟨w - k - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have s3 : Sym4 (A0 ++ [1] ++ List.replicate k' 3) := sA1.app (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4
    have h1 := ir0Zero (A0 ++ [1] ++ List.replicate (k' + 1) 3 ++ List.replicate j 2) R
      ((sA1.app (BitsD.rep (k' + 1) 3 (by simp)).sym4).app (BitsD.rep j 2 (by simp)).sym4) hR
    have h1' : znttLogic.Reach (hd QNTT.IR0 (A0 ++ [1] ++ fld w (k' + 1)) R)
        (hd QNTT.IR1 (A0 ++ [1] ++ List.replicate k' 3 ++ [3] ++ List.replicate j 2) (2 :: R)) :=
      h1.of_eq (by simp [fld, hj, List.replicate_succ']) (by simp [List.replicate_succ'])
    have h2 := ir1Sweep (A0 ++ [1] ++ List.replicate k' 3) j (2 :: R) s3 (sym4_B (by simp) hR)
    have h3 := ir2 (A0 ++ [1] ++ List.replicate k' 3 ++ [3]) (List.replicate j 2 ++ R)
      (s3.app (sym4_cell 3 (by simp))) ((BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4.app hR)
    have hi : incK w (k' + 1) = k' + 2 := by simp [incK, hkw']
    rw [hi, show w - (k' + 2) = j by omega]
    refine h1'.trans (h2.trans (h3.of_eq ?_ ?_))
    · simp [rep_cons_app]
    · simp [List.replicate_succ']


/-- One unit of a captured record: `acc += 1`, the leading mark of `b` is consumed. -/
theorem abUnit (A0 E : List Nat) (w k m r s : Nat) (T : List Nat) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hA : Sym4 A0) (hE : BitsD E) (hT : Sym4 T) :
    znttLogic.Reach
      (hdR QNTT.AB2 (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1])
        (List.replicate m 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ T))
      (hdR QNTT.AB2 (A0 ++ [1] ++ fld w (incK w k) ++ [1] ++ E ++ [1])
        (List.replicate (m + 1) 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++ T)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sF : Sym4 (fld w k) := by
    unfold fld
    exact (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4.app (BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4
  have sF' : Sym4 (fld w (incK w k)) := by
    unfold fld
    exact (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4.app (BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have sY : Sym4 (A0 ++ [1] ++ fld w k ++ [1] ++ E) :=
    ((sA1.app sF).app (sym4_cell 1 (by simp))).app hE.sym4
  have sR' : Sym4 (List.replicate r 3 ++ List.replicate s 2 ++ T) := ((s3 r).app (s2 s)).app hT
  have h1 := ab2Sweep (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1]) m
    (List.replicate (r + 1) 3 ++ List.replicate s 2 ++ T) (sY.app (sym4_cell 1 (by simp)))
    (((s3 _).app (s2 s)).app hT)
  have h2 := ab3One (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1] ++ List.replicate m 2)
    (List.replicate r 3 ++ List.replicate s 2 ++ T) ((sY.app (sym4_cell 1 (by simp))).app (s2 m)) sR'
  have h3 := ab4 (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1] ++ List.replicate m 2)
    (3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)) ((sY.app (sym4_cell 1 (by simp))).app (s2 m))
    (sym4_B (by simp) sR')
  have h4 := ab5Sweep (A0 ++ [1] ++ fld w k ++ [1] ++ E) m
    (2 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)) sY
    (sym4_B (by simp) (sym4_B (by simp) sR'))
  have h5 := ab6Sweep (A0 ++ [1] ++ fld w k) E
    (1 :: (List.replicate m 2 ++ 2 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)))
    (sA1.app sF) hE (sym4_M ((s2 m).app (sym4_B (by simp) (sym4_B (by simp) sR'))))
  have h6 := irInc A0 (1 :: E ++ 1 :: (List.replicate m 2 ++ 2 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)))
    w k hk hkw hA (sym4_M (hE.sym4.app (sym4_M ((s2 m).app (sym4_B (by simp) (sym4_B (by simp) sR'))))))
  have h7 := abe8Skip (A0 ++ [1] ++ List.replicate (incK w k) 3) (List.replicate (w - incK w k) 2)
    (E ++ 1 :: (List.replicate m 2 ++ 2 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)))
    (sA1.app (s3 _)) (BitsD.rep _ _ (by simp)) (hE.sym4.app (sym4_M ((s2 m).app (sym4_B (by simp) (sym4_B (by simp) sR')))))
  have h8 := ab9Skip (A0 ++ [1] ++ List.replicate (incK w k) 3 ++ List.replicate (w - incK w k) 2 ++ [1]) E
    (List.replicate m 2 ++ 2 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T))
    (((sA1.app (s3 _)).app (s2 _)).app (sym4_cell 1 (by simp))) hE ((s2 m).app (sym4_B (by simp) (sym4_B (by simp) sR')))
  simp only [fld, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  refine h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.of_eq rfl ?_)))))))
  simp [List.replicate_succ, rep_cons_app]

theorem abrSweep (X b R : List Nat) (hX : Sym4 X) (hb : BitsD b) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.ABR (X ++ [1] ++ b) R) (hdR QNTT.ABR2 (X ++ [1]) (b ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, b, R] := Valid.cons hX (Valid.cons hb (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [X, b, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem abr2Sweep (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ABR2 A (List.replicate m 2 ++ 3 :: R))
      (hdR QNTT.ABR3 (A ++ List.replicate m 3 ++ [3]) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] :=
    Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 (.const 3), .sym 3]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `incK` iterated. -/
def incKn (w : Nat) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => incKn w n (incK w k)

theorem incK_bounds (w k : Nat) (hk : 1 ≤ k) (hkw : k ≤ w) : 1 ≤ incK w k ∧ incK w k ≤ w := by
  unfold incK; split <;> omega

theorem incKn_bounds (w : Nat) : ∀ (n k : Nat), 1 ≤ k → k ≤ w → 1 ≤ incKn w n k ∧ incKn w n k ≤ w
  | 0, k, hk, hkw => ⟨hk, hkw⟩
  | n + 1, k, hk, hkw => by
    have h := incK_bounds w k hk hkw
    exact incKn_bounds w n _ h.1 h.2

/-- The unit loop of a captured record: `n` units are consumed. -/
theorem abLoop (A0 E : List Nat) (w s : Nat) (T : List Nat) (hA : Sym4 A0) (hE : BitsD E) (hT : Sym4 T) :
    ∀ (n m k : Nat), 1 ≤ k → k ≤ w →
    znttLogic.Reach
      (hdR QNTT.AB2 (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1])
        (List.replicate m 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++ T))
      (hdR QNTT.AB2 (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1])
        (List.replicate (m + n) 2 ++ List.replicate 1 3 ++ List.replicate s 2 ++ T))
  | 0, m, k, _, _ => by simpa [incKn] using LTM.Reach.refl znttLogic _
  | n + 1, m, k, hk, hkw => by
    have h1 := abUnit A0 E w k m n s T hk hkw hA hE hT
    have hb := incK_bounds w k hk hkw
    have h2 := abLoop A0 E w s T hA hE hT n (m + 1) (incK w k) hb.1 hb.2
    refine h1.trans (h2.of_eq ?_ ?_)
    · simp [List.replicate_succ]
    · simp [incKn, Nat.add_assoc, Nat.add_comm 1 n]

theorem bd_app {a b : List Nat} (ha : BitsD a) (hb : BitsD b) : BitsD (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem ab3End (A : List Nat) (s : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.AB3 (A ++ [3]) (List.replicate s 2 ++ 1 :: R))
      (hd QNTT.ABR (A ++ [3]) (List.replicate s 2 ++ 1 :: R)) := by
  cases s with
  | zero => simpa using ab3M A R hA hR
  | succ s =>
    have := ab3Zero A (List.replicate s 2 ++ 1 :: R) hA
      ((BitsD.rep s 2 (by simp)).sym4.app (sym4_M hR))
    simpa [List.replicate_succ] using this

/-- A captured record: `acc += (number of marks of b) - 1`, `b` restored, back in `LN0` after `u`. -/
theorem capVisit (A0 E u R : List Nat) (w k m n s : Nat) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hA : Sym4 A0) (hE : BitsD E) (hu : BitsD u) (hR : Sym4 R) :
    znttLogic.Reach
      (hd QNTT.AB0 (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1] ++
        (List.replicate m 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2) ++ [1] ++ u) R)
      (hdR QNTT.LN0 (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1] ++
        (List.replicate (m + n + 1) 3 ++ List.replicate s 2) ++ [1]) (u ++ R)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have hF : ∀ k', Sym4 (fld w k') := fun k' => by
    unfold fld
    exact (BitsD.rep _ _ (by simp : 3 ∈ [2, 3])).sym4.app (BitsD.rep _ _ (by simp : 2 ∈ [2, 3])).sym4
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have hb : BitsD (List.replicate m 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2) :=
    bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))
  have sT : Sym4 (1 :: (u ++ R)) := sym4_M (hu.sym4.app hR)
  have sX : ∀ k', Sym4 (A0 ++ [1] ++ fld w k' ++ [1] ++ E) := fun k' =>
    ((sA1.app (hF k')).app sM).app hE.sym4
  have g0 := ab0Sweep (A0 ++ [1] ++ fld w k ++ [1] ++ E ++ [1])
    (List.replicate m 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2) u R ((sX k).app sM) hb hu hR
  have g1 := ab1Sweep (A0 ++ [1] ++ fld w k ++ [1] ++ E)
    (List.replicate m 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2) (1 :: u ++ R) (sX k) hb sT
  have g2 := abLoop A0 E w s (1 :: (u ++ R)) hA hE sT n m k hk hkw
  have hb' := incKn_bounds w n k hk hkw
  have g3 := ab2Sweep (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1]) (m + n)
    (List.replicate s 2 ++ 1 :: (u ++ R)) ((sX _).app sM) ((s2 s).app sT)
  have g4 := ab3End (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1] ++ List.replicate (m + n) 2) s (u ++ R)
    (((sX _).app sM).app (s2 _)) (hu.sym4.app hR)
  have g5 := abrSweep (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E) (List.replicate (m + n) 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (u ++ R)) (sX _) (bd_app (BitsD.rep _ _ (by simp)) (by intro x hx; simp at hx; simp [hx])) ((s2 s).app sT)
  have g6 := abr2Sweep (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1]) (m + n)
    (List.replicate s 2 ++ 1 :: (u ++ R)) ((sX _).app sM) ((s2 s).app sT)
  have g7 := ab3Skip (A0 ++ [1] ++ fld w (incKn w n k) ++ [1] ++ E ++ [1] ++ List.replicate (m + n) 3 ++ [3])
    (List.replicate s 2) (u ++ R) (((((sX _).app sM).app (s3 _)).app (sym4_cell 3 (by simp)))) (BitsD.rep _ _ (by simp))
    (hu.sym4.app hR)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g0 g1 g2 g3 g4 g5 g6 g7 ⊢
  refine g0.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.of_eq rfl ?_)))))))
  simp [← Nat.add_assoc, List.replicate_succ']

/-! ### The visit of the records after the cursor (`LA`, `CU*`, `LN*`, `AB*`) -/

/-- Numeric state of a record during the broadcast: accumulator `fld w k`, `E`,
`b = 0^m 1^(n+1) 0^s` and the pointer `u = 0^a 1^(c+1) 0^t`. -/
structure VR where
  F : Nat
  O : Nat
  P : Nat
  w : Nat
  k : Nat
  E : List Nat
  m : Nat
  n : Nat
  s : Nat
  a : Nat
  c : Nat
  t : Nat

def VR.b (v : VR) : List Nat := List.replicate v.m 2 ++ List.replicate (v.n + 1) 3 ++ List.replicate v.s 2
def VR.u (v : VR) : List Nat := List.replicate v.a 2 ++ List.replicate (v.c + 1) 3 ++ List.replicate v.t 2
def VR.tl (v : VR) : List Nat := fld v.w v.k ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.u))
def VR.recd (v : VR) : List Nat := [1, 1, v.F, v.O, v.P, 1] ++ v.tl

/-- The effect of a visit: a captured record (`c = 1`) adds `n` to its accumulator and restores `b`. -/
def VR.vis (v : VR) : VR :=
  if v.c = 1 then { v with k := incKn v.w v.n v.k, m := 0, n := v.m + v.n } else v

structure VR.Ok (v : VR) : Prop where
  F : v.F ∈ [2, 3]
  O : v.O ∈ [2, 3]
  P : v.P ∈ [2, 3]
  k1 : 1 ≤ v.k
  kw : v.k ≤ v.w
  E : BitsD v.E
  Elen : 2 ≤ v.E.length

def tailVR (vs : List VR) : List Nat := (vs.map VR.recd).flatten

theorem VR.Ok.b {v : VR} (_ : v.Ok) : BitsD v.b :=
  bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))

theorem VR.Ok.u {v : VR} (_ : v.Ok) : BitsD v.u :=
  bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))

theorem fld_bits (w k : Nat) : BitsD (fld w k) :=
  bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))

theorem VR.Ok.tl_sym4 {v : VR} (h : v.Ok) : Sym4 v.tl :=
  (fld_bits _ _).sym4.app (sym4_M (h.E.sym4.app (sym4_M (h.b.sym4.app (sym4_M h.u.sym4)))))

/-- `LA` .. `CU0`: step over the accumulator, `E` and `b`. -/
theorem visitPre (v : VR) (hv : v.Ok) (A Next : List Nat) (hA : Sym4 A) (hN : Sym4 Next) :
    znttLogic.Reach (hdR QNTT.LA A (v.tl ++ Next))
      (hdR QNTT.CU0 (A ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) (v.u ++ Next)) := by
  have sU := hv.u.sym4
  have sB := hv.b.sym4
  have sE := hv.E.sym4
  have h1 := laSkip A (fld v.w v.k) (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ Next))) hA (fld_bits _ _)
    (sE.app (sym4_M (sB.app (sym4_M (sU.app hN)))))
  have h2 := leSkip (A ++ fld v.w v.k ++ [1]) v.E (v.b ++ 1 :: (v.u ++ Next))
    ((hA.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))) hv.E (sB.app (sym4_M (sU.app hN)))
  have h3 := lbSkip (A ++ fld v.w v.k ++ [1] ++ v.E ++ [1]) v.b (v.u ++ Next)
    ((((hA.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app sE).app (sym4_cell 1 (by simp))) hv.b (sU.app hN)
  simp only [VR.tl, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)


/-- The configuration `CU0` at the pointer of a record. -/
def cu0Cfg (v : VR) (A0 Next : List Nat) : ZC :=
  hdR QNTT.CU0 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) (v.u ++ Next)

/-- `LN0` over a block of bits and then the end of the tape. -/
theorem lnEnd (A f : List Nat) (hA : Sym4 A) (hf : BitsD f) :
    znttLogic.Reach (hdR QNTT.LN0 A f) (hd QNTT.RFL (A ++ f) []) := by
  have h1 := ln0Block A f [] hA hf Sym4.nil
  have h2 := ln0B (A ++ f) (hA.app hf.sym4)
  simp only [List.append_nil] at h1
  exact h1.trans h2

/-- `LN0` over a block of bits to the next record header. -/
theorem lnNext (A f Rest : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 Rest) :
    znttLogic.Reach (hdR QNTT.LN0 A (f ++ 1 :: 1 :: Rest)) (hdR QNTT.LH (A ++ f ++ [1, 1]) Rest) := by
  have h1 := ln0Block A f (1 :: 1 :: Rest) hA hf (sym4_M (sym4_M hR))
  have h2 := ln0M (A ++ f) (1 :: Rest) (hA.app hf.sym4) (sym4_M hR)
  have h3 := ln1 (A ++ f ++ [1]) Rest ((hA.app hf.sym4).app (sym4_cell 1 (by simp))) hR
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3)

theorem cu2Any (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R)
    (hh : R = [] ∨ ∃ R', R = 1 :: R' ∨ R = 2 :: R') :
    znttLogic.Reach (hdR QNTT.CU2 (A ++ [3]) R) (hd QNTT.AB0 (A ++ [3]) R) := by
  rcases hh with rfl | ⟨R', rfl | rfl⟩
  · exact cu2CapB A hA
  · exact cu2CapM A R' hA (fun y hy => hR y (by simp [hy]))
  · exact cu2Cap0 A R' hA (fun y hy => hR y (by simp [hy]))

theorem rep_ne_three (t : Nat) (Next : List Nat) (hNn : Next = [] ∨ ∃ R', Next = 1 :: R') :
    List.replicate t 2 ++ Next = [] ∨ ∃ R', List.replicate t 2 ++ Next = 1 :: R' ∨ List.replicate t 2 ++ Next = 2 :: R' := by
  cases t with
  | zero =>
    rcases hNn with rfl | ⟨R', rfl⟩
    · simp
    · exact Or.inr ⟨R', Or.inl (by simp)⟩
  | succ t => exact Or.inr ⟨List.replicate t 2 ++ Next, Or.inr (by simp [List.replicate_succ])⟩

/-- A captured record, from `LA` to `LN0` behind its pointer. -/
theorem visitCap (v : VR) (hv : v.Ok) (hc : v.c = 1) (A0 Next : List Nat) (hA : Sym4 A0) (hN : Sym4 Next)
    (hNn : Next = [] ∨ ∃ R', Next = 1 :: R') (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 Next)) :
    znttLogic.Reach S
      (hdR QNTT.LN0 (A0 ++ [1] ++ fld v.vis.w v.vis.k ++ [1] ++ v.vis.E ++ [1] ++ v.vis.b ++ [1])
        (v.vis.u ++ Next)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hu : v.u = List.replicate v.a 2 ++ [3, 3] ++ List.replicate v.t 2 := by
    simp [VR.u, hc, List.replicate_succ]
  have hL : Sym4 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) :=
    (((((sA1.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app hv.E.sym4).app (sym4_cell 1 (by simp))).app
      hv.b.sym4).app (sym4_cell 1 (by simp))
  have h0 := hS
  unfold cu0Cfg at h0
  have h1 := cu0Skip (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) v.a
    (3 :: 3 :: (List.replicate v.t 2 ++ Next)) hL (sym4_B (by simp) (sym4_B (by simp) ((s2 _).app hN)))
  have h2 := cu0Hit (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2)
    (3 :: (List.replicate v.t 2 ++ Next)) (hL.app (s2 _)) (sym4_B (by simp) ((s2 _).app hN))
  have h3 := cu1Two (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
    (List.replicate v.t 2 ++ Next) ((hL.app (s2 _)).app (sym4_cell 3 (by simp))) ((s2 _).app hN)
  have h4 := cu2Any (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
    (List.replicate v.t 2 ++ Next) ((hL.app (s2 _)).app (sym4_cell 3 (by simp))) ((s2 _).app hN)
    (rep_ne_three v.t Next hNn)
  have h5 := capVisit A0 v.E (List.replicate v.a 2 ++ [3, 3]) (List.replicate v.t 2 ++ Next) v.w v.k v.m v.n v.s
    hv.k1 hv.kw hA hv.E (bd_app (BitsD.rep _ _ (by simp)) (by intro x hx; simp at hx; simp [hx]))
    ((s2 _).app hN)
  rw [hu] at h0
  simp only [VR.vis, hc, if_true, VR.b, VR.u, VR.tl, List.append_assoc, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 ⊢
  refine h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.of_eq ?_ ?_)))))
  · simp [List.replicate_succ]
  · simp [List.replicate_succ, hc]

/-- A record that is not captured (and not the special last-one case): `LA` to `LN0` inside `u`. -/
theorem visitNoLn (v : VR) (hv : v.Ok) (hc : v.c ≠ 1) (hne : ¬(v.c = 0 ∧ v.t = 0)) (A0 Next : List Nat)
    (hA : Sym4 A0) (hN : Sym4 Next) (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 Next)) :
    ∃ f1 f2, v.u = f1 ++ f2 ∧ BitsD f2 ∧
      znttLogic.Reach S
        (hdR QNTT.LN0 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ f1) (f2 ++ Next)) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have hL : Sym4 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) :=
    (((((sA1.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app hv.E.sym4).app (sym4_cell 1 (by simp))).app
      hv.b.sym4).app (sym4_cell 1 (by simp))
  have h0 := hS
  unfold cu0Cfg at h0
  obtain ⟨c', hc'⟩ : ∃ c', v.c = c' := ⟨_, rfl⟩
  rcases c' with _ | _ | c''
  · -- c = 0, t = t' + 1
    obtain ⟨t', ht⟩ : ∃ t', v.t = t' + 1 := ⟨v.t - 1, by omega⟩
    have hu : v.u = List.replicate v.a 2 ++ [3] ++ [2] ++ List.replicate t' 2 := by
      simp [VR.u, hc', ht, List.replicate_succ]
    refine ⟨List.replicate v.a 2 ++ [3] ++ [2], List.replicate t' 2, hu, BitsD.rep _ _ (by simp), ?_⟩
    have h1 := cu0Skip (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) v.a
      (3 :: 2 :: (List.replicate t' 2 ++ Next)) hL (sym4_B (by simp) (sym4_B (by simp) ((s2 _).app hN)))
    have h2 := cu0Hit (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2)
      (2 :: (List.replicate t' 2 ++ Next)) (hL.app (s2 _)) (sym4_B (by simp) ((s2 _).app hN))
    have h3 := cu1Zero (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
      (List.replicate t' 2 ++ Next) ((hL.app (s2 _)).app (sym4_cell 3 (by simp))) ((s2 _).app hN)
    rw [hu] at h0
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h0 h1 h2 h3 ⊢
    exact h0.trans (h1.trans (h2.trans h3))
  · exact absurd hc' hc
  · have hu : v.u = List.replicate v.a 2 ++ [3, 3, 3] ++ (List.replicate c'' 3 ++ List.replicate v.t 2) := by
      simp [VR.u, hc', List.replicate_succ]
    refine ⟨List.replicate v.a 2 ++ [3, 3, 3], List.replicate c'' 3 ++ List.replicate v.t 2, hu,
      bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)), ?_⟩
    have sR : Sym4 (List.replicate c'' 3 ++ List.replicate v.t 2 ++ Next) := ((s3 _).app (s2 _)).app hN
    have h1 := cu0Skip (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) v.a
      (3 :: 3 :: 3 :: (List.replicate c'' 3 ++ List.replicate v.t 2 ++ Next)) hL
      (sym4_B (by simp) (sym4_B (by simp) (sym4_B (by simp) sR)))
    have h2 := cu0Hit (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2)
      (3 :: 3 :: (List.replicate c'' 3 ++ List.replicate v.t 2 ++ Next)) (hL.app (s2 _))
      (sym4_B (by simp) (sym4_B (by simp) sR))
    have h3 := cu1Two (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
      (3 :: (List.replicate c'' 3 ++ List.replicate v.t 2 ++ Next)) ((hL.app (s2 _)).app (sym4_cell 3 (by simp)))
      (sym4_B (by simp) sR)
    have h4 := cu2Three (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3] ++ [3])
      (List.replicate c'' 3 ++ List.replicate v.t 2 ++ Next)
      (((hL.app (s2 _)).app (sym4_cell 3 (by simp))).app (sym4_cell 3 (by simp))) sR
    rw [hu] at h0
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 ⊢
    exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem vis_tl_eq (v : VR) (hc : v.c ≠ 1) : v.vis = v := by simp [VR.vis, hc]

/-- The last-record special case `u = 0^a 1`: `CU1` meets the end. -/
theorem visitSpecialEnd (v : VR) (hv : v.Ok) (hc : v.c = 0) (ht : v.t = 0) (A0 : List Nat) (hA : Sym4 A0) (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 [])) :
    znttLogic.Reach S (hd QNTT.RFL (A0 ++ [1] ++ v.tl) []) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hL : Sym4 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) :=
    (((((sA1.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app hv.E.sym4).app (sym4_cell 1 (by simp))).app
      hv.b.sym4).app (sym4_cell 1 (by simp))
  have h0 := hS
  unfold cu0Cfg at h0
  have hu : v.u = List.replicate v.a 2 ++ [3] := by simp [VR.u, hc, ht]
  have h1 := cu0Skip (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) v.a [3] hL
    (sym4_cell 3 (by simp))
  have h2 := cu0Hit (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2) []
    (hL.app (s2 _)) Sym4.nil
  have h3 := cu1B (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
    ((hL.app (s2 _)).app (sym4_cell 3 (by simp)))
  rw [hu] at h0
  simp only [VR.tl, hu, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h1 h2 h3 ⊢
  exact h0.trans (h1.trans (h2.trans h3))

theorem visitSpecialNext (v : VR) (hv : v.Ok) (hc : v.c = 0) (ht : v.t = 0) (A0 Rest : List Nat) (hA : Sym4 A0)
    (hR : Sym4 Rest) (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 (1 :: 1 :: Rest))) :
    znttLogic.Reach S
      (hdR QNTT.LH (A0 ++ [1] ++ v.tl ++ [1, 1]) Rest) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hL : Sym4 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) :=
    (((((sA1.app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app hv.E.sym4).app (sym4_cell 1 (by simp))).app
      hv.b.sym4).app (sym4_cell 1 (by simp))
  have sN : Sym4 (1 :: 1 :: Rest) := sym4_M (sym4_M hR)
  have h0 := hS
  unfold cu0Cfg at h0
  have hu : v.u = List.replicate v.a 2 ++ [3] := by simp [VR.u, hc, ht]
  have h1 := cu0Skip (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1]) v.a (3 :: 1 :: 1 :: Rest) hL
    (sym4_B (by simp) sN)
  have h2 := cu0Hit (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2) (1 :: 1 :: Rest)
    (hL.app (s2 _)) sN
  have h3 := cu1M (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3])
    (1 :: Rest) ((hL.app (s2 _)).app (sym4_cell 3 (by simp))) (sym4_M hR)
  have h4 := ln1 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ List.replicate v.a 2 ++ [3] ++ [1])
    Rest (((hL.app (s2 _)).app (sym4_cell 3 (by simp))).app (sym4_cell 1 (by simp))) hR
  rw [hu] at h0
  simp only [VR.tl, hu, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h0 h1 h2 h3 h4 ⊢
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem vis_Ok (v : VR) (hv : v.Ok) : v.vis.Ok := by
  unfold VR.vis
  split
  · exact { F := hv.F, O := hv.O, P := hv.P, k1 := (incKn_bounds v.w v.n v.k hv.k1 hv.kw).1,
            kw := (incKn_bounds v.w v.n v.k hv.k1 hv.kw).2, E := hv.E, Elen := hv.Elen }
  · exact hv

theorem VR.Ok.left {v : VR} (hv : v.Ok) (A0 : List Nat) (hA : Sym4 A0) (f : List Nat) (hf : Sym4 f) :
    Sym4 (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ f) :=
  (((((((hA.app (sym4_cell 1 (by simp))).app (fld_bits _ _).sym4).app (sym4_cell 1 (by simp))).app
    hv.E.sym4).app (sym4_cell 1 (by simp))).app hv.b.sym4).app (sym4_cell 1 (by simp))).app hf

/-- The last record of the tape. -/
theorem visitEnd (v : VR) (hv : v.Ok) (A0 : List Nat) (hA : Sym4 A0) (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 [])) :
    znttLogic.Reach S (hd QNTT.RFL (A0 ++ [1] ++ v.vis.tl) []) := by
  by_cases hc : v.c = 1
  · have h := visitCap v hv hc A0 [] hA Sym4.nil (Or.inl rfl) S hS
    have hv' := vis_Ok v hv
    have hl := lnEnd (A0 ++ [1] ++ fld v.vis.w v.vis.k ++ [1] ++ v.vis.E ++ [1] ++ v.vis.b ++ [1]) v.vis.u
      (by simpa using hv'.left A0 hA [] Sym4.nil) hv'.u
    simp only [VR.tl, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h hl ⊢
    exact h.trans hl
  · rw [vis_tl_eq v hc]
    by_cases hs : v.c = 0 ∧ v.t = 0
    · exact visitSpecialEnd v hv hs.1 hs.2 A0 hA S hS
    · obtain ⟨f1, f2, hu, hf2, h⟩ := visitNoLn v hv hc hs A0 [] hA Sym4.nil S hS
      have hf1 : BitsD f1 := fun x hx => hv.u x (by rw [hu]; exact List.mem_append.2 (Or.inl hx))
      have hl := lnEnd (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ f1) f2
        (hv.left A0 hA f1 hf1.sym4) hf2
      simp only [List.append_nil] at h
      simp only [VR.tl, hu, List.append_assoc, List.cons_append, List.nil_append] at h hl ⊢
      exact h.trans hl

theorem VR.Ok.hdr {v : VR} (hv : v.Ok) (A0 : List Nat) (hA : Sym4 A0) :
    Sym4 (A0 ++ [1] ++ v.tl ++ [1, 1]) :=
  ((hA.app (sym4_cell 1 (by simp))).app hv.tl_sym4).app (sym4_M (sym4_M Sym4.nil))

/-- A record followed by another header `MM f M`. -/
theorem visitNext (v : VR) (hv : v.Ok) (A0 f Rest : List Nat) (hA : Sym4 A0) (hf : BitsD f) (hR : Sym4 Rest) (S : ZC) (hS : znttLogic.Reach S (cu0Cfg v A0 (1 :: 1 :: (f ++ 1 :: Rest)))) :
    znttLogic.Reach S
      (hdR QNTT.LA (A0 ++ [1] ++ v.vis.tl ++ [1, 1] ++ f ++ [1]) Rest) := by
  have sN : Sym4 (f ++ 1 :: Rest) := hf.sym4.app (sym4_M hR)
  by_cases hc : v.c = 1
  · have h := visitCap v hv hc A0 (1 :: 1 :: (f ++ 1 :: Rest)) hA (sym4_M (sym4_M sN)) (Or.inr ⟨_, rfl⟩) S hS
    have hv' := vis_Ok v hv
    have hl := lnNext (A0 ++ [1] ++ fld v.vis.w v.vis.k ++ [1] ++ v.vis.E ++ [1] ++ v.vis.b ++ [1]) v.vis.u
      (f ++ 1 :: Rest) (by simpa using hv'.left A0 hA [] Sym4.nil) hv'.u sN
    have hs := lhSkip (A0 ++ [1] ++ v.vis.tl ++ [1, 1]) f Rest (hv'.hdr A0 hA) hf hR
    simp only [VR.tl, List.append_assoc, List.cons_append, List.nil_append] at h hl hs ⊢
    exact h.trans (hl.trans hs)
  · rw [vis_tl_eq v hc]
    have hs := lhSkip (A0 ++ [1] ++ v.tl ++ [1, 1]) f Rest (hv.hdr A0 hA) hf hR
    by_cases hz : v.c = 0 ∧ v.t = 0
    · have h := visitSpecialNext v hv hz.1 hz.2 A0 (f ++ 1 :: Rest) hA sN S hS
      exact h.trans hs
    · obtain ⟨f1, f2, hu, hf2, h⟩ := visitNoLn v hv hc hz A0 (1 :: 1 :: (f ++ 1 :: Rest)) hA (sym4_M (sym4_M sN)) S hS
      have hf1 : BitsD f1 := fun x hx => hv.u x (by rw [hu]; exact List.mem_append.2 (Or.inl hx))
      have hl := lnNext (A0 ++ [1] ++ fld v.w v.k ++ [1] ++ v.E ++ [1] ++ v.b ++ [1] ++ f1) f2
        (f ++ 1 :: Rest) (hv.left A0 hA f1 hf1.sym4) hf2 sN
      simp only [VR.tl, hu, List.append_assoc, List.cons_append, List.nil_append] at h hl hs ⊢
      exact h.trans (hl.trans hs)

theorem vis_hdr (v : VR) : v.vis.F = v.F ∧ v.vis.O = v.O ∧ v.vis.P = v.P := by
  unfold VR.vis; split <;> simp

theorem VR.Ok.hdr3 {v : VR} (hv : v.Ok) : BitsD [v.F, v.O, v.P] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h
  · rw [h]; exact hv.F
  · rw [h]; exact hv.O
  · rw [h]; exact hv.P

theorem VR.Ok.recd_sym4 {v : VR} (hv : v.Ok) : Sym4 v.recd := by
  simp only [VR.recd, List.cons_append, List.nil_append]
  exact sym4_M (sym4_M (sym4_B hv.F (sym4_B hv.O (sym4_B hv.P (sym4_M hv.tl_sym4)))))

theorem tailVR_sym4 : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → Sym4 (tailVR vs)
  | [], _ => Sym4.nil
  | v :: vs, h => by
    simp only [tailVR, List.map_cons, List.flatten_cons]
    exact (h v (by simp)).recd_sym4.app (tailVR_sym4 vs (fun w hw => h w (by simp [hw])))

/-- The whole broadcast sweep after the cursor record has been marked: every later record is visited. -/
theorem visitAllS : ∀ (vs : List VR) (v : VR), v.Ok → (∀ w ∈ vs, w.Ok) → ∀ (A0 : List Nat), Sym4 A0 →
    ∀ (S : ZC), znttLogic.Reach S (cu0Cfg v A0 (tailVR vs)) →
    znttLogic.Reach S (hd QNTT.RFL (A0 ++ [1] ++ v.vis.tl ++ tailVR (vs.map VR.vis)) [])
  | [], v, hv, _, A0, hA, S, hS => by
    have := visitEnd v hv A0 hA S (by simpa [tailVR] using hS)
    simpa [tailVR] using this
  | w :: vs, v, hv, hvs, A0, hA, S, hS => by
    have hw : w.Ok := hvs w (by simp)
    have hvs' : ∀ x ∈ vs, x.Ok := fun x hx => hvs x (by simp [hx])
    have hf : BitsD [w.F, w.O, w.P] := hw.hdr3
    have h1 := visitNext v hv A0 [w.F, w.O, w.P] (w.tl ++ tailVR vs) hA hf
      (hw.tl_sym4.app (tailVR_sym4 vs hvs')) S (by simpa [tailVR, VR.recd] using hS)
    have h2 := visitAllS vs w hw hvs' (A0 ++ [1] ++ v.vis.tl ++ [1, 1] ++ [w.F, w.O, w.P])
      ((((hA.app (sym4_cell 1 (by simp))).app (vis_Ok v hv).tl_sym4).app (sym4_M (sym4_M Sym4.nil))).app hf.sym4) _
      (visitPre w hw (A0 ++ [1] ++ v.vis.tl ++ [1, 1] ++ [w.F, w.O, w.P] ++ [1]) (tailVR vs)
        (((((hA.app (sym4_cell 1 (by simp))).app (vis_Ok v hv).tl_sym4).app (sym4_M (sym4_M Sym4.nil))).app hf.sym4).app
          (sym4_cell 1 (by simp))) (tailVR_sym4 vs hvs'))
    obtain ⟨e1, e2, e3⟩ := vis_hdr w
    simp only [tailVR, VR.recd, List.map_cons, List.flatten_cons, e1, e2, e3, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

theorem visitAll (vs : List VR) (v : VR) (hv : v.Ok) (hvs : ∀ w ∈ vs, w.Ok) (A0 : List Nat) (hA : Sym4 A0) :
    znttLogic.Reach (hdR QNTT.LA (A0 ++ [1]) (v.tl ++ tailVR vs))
      (hd QNTT.RFL (A0 ++ [1] ++ v.vis.tl ++ tailVR (vs.map VR.vis)) []) :=
  visitAllS vs v hv hvs A0 hA _ (visitPre v hv (A0 ++ [1]) (tailVR vs) (hA.app (sym4_cell 1 (by simp)))
    (tailVR_sym4 vs hvs))

/-! ### Cursor record: marking one unit of `acc` (`BU*`, `BS*`) -/

theorem bu0Skip (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU0n A (List.replicate a 2 ++ R)) (hdR QNTT.BU0n (A ++ List.replicate a 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] :=
    Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu0Hit (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU0n A (3 :: R)) (hdR QNTT.BU1n (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu1Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1n (A ++ [3]) (3 :: R)) (hd QNTT.BU2n (A ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu2Mark (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BU2n (A ++ [3]) R) (hdR QNTT.BS0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs0Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS0 A (f ++ R)) (hdR QNTT.BS0 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs0M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS0 A (1 :: R)) (hdR QNTT.BS1 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs0B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.BS0 A []) (hd QNTT.RFL A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs1Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS1 A (2 :: R)) (hdR QNTT.BS0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs1Three (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS1 A (3 :: R)) (hdR QNTT.BS0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bs1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS1 A (1 :: R)) (hdR QNTT.BSh (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bshSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BSh A (f ++ 1 :: R)) (hdR QNTT.IA0 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- `BS1` then bits: continue as `BS0` over a nonempty bit block. -/
theorem bs1Block (A : List Nat) (c : Nat) (f R : List Nat) (hA : Sym4 A) (hc : c ∈ [2, 3]) (hf : BitsD f)
    (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BS1 A (c :: f ++ R)) (hdR QNTT.BS0 (A ++ c :: f) R) := by
  have hfR : Sym4 (f ++ R) := hf.sym4.app hR
  have h2 := bs0Block (A ++ [c]) f R (hA.app (sym4_cell c (by simp at hc ⊢; omega))) hf hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have h1 := bs1Two A (f ++ R) hA hfR
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2
  · have h1 := bs1Three A (f ++ R) hA hfR
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

theorem bits_head (l : List Nat) (hne : l ≠ []) (hl : BitsD l) : ∃ c f, l = c :: f ∧ c ∈ [2, 3] ∧ BitsD f := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c f => exact ⟨c, f, rfl, hl c (by simp), fun x hx => hl x (by simp [hx])⟩

theorem VR.Ok.Ene {v : VR} (hv : v.Ok) : v.E ≠ [] := by
  intro h; have := hv.Elen; rw [h] at this; simp at this

theorem VR.Ok.bne {v : VR} (_ : v.Ok) : v.b ≠ [] := by
  simp [VR.b, List.replicate_succ]

theorem VR.Ok.une {v : VR} (_ : v.Ok) : v.u ≠ [] := by
  simp [VR.u, List.replicate_succ]

/-- `BS0` along the rest of the cursor record: to the end of the tape. -/
theorem bsTailEnd (v : VR) (hv : v.Ok) (X ac2 : List Nat) (hX : Sym4 X) (hac : BitsD ac2) :
    znttLogic.Reach (hdR QNTT.BS0 X (ac2 ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.u))))
      (hd QNTT.RFL (X ++ ac2 ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.u))) []) := by
  obtain ⟨e, fe, hE, he, hfe⟩ := bits_head v.E hv.Ene hv.E
  obtain ⟨b0, fb, hB, hb0, hfb⟩ := bits_head v.b hv.bne hv.b
  obtain ⟨u0, fu, hU, hu0, hfu⟩ := bits_head v.u hv.une hv.u
  have sE := hv.E.sym4
  have sB := hv.b.sym4
  have sU := hv.u.sym4
  rw [hE] at sE ⊢
  rw [hB] at sB ⊢
  rw [hU] at sU ⊢
  have sac := hac.sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have s1 := bs0Block X ac2 (1 :: (e :: fe ++ 1 :: (b0 :: fb ++ 1 :: (u0 :: fu)))) hX hac
    (sym4_M (sE.app (sym4_M (sB.app (sym4_M sU)))))
  have s2 := bs0M (X ++ ac2) (e :: fe ++ 1 :: (b0 :: fb ++ 1 :: (u0 :: fu))) (hX.app sac)
    (sE.app (sym4_M (sB.app (sym4_M sU))))
  have s3 := bs1Block (X ++ ac2 ++ [1]) e fe (1 :: (b0 :: fb ++ 1 :: (u0 :: fu))) ((hX.app sac).app sM) he hfe
    (sym4_M (sB.app (sym4_M sU)))
  have s4 := bs0M (X ++ ac2 ++ [1] ++ e :: fe) (b0 :: fb ++ 1 :: (u0 :: fu))
    (((hX.app sac).app sM).app sE) (sB.app (sym4_M sU))
  have s5 := bs1Block (X ++ ac2 ++ [1] ++ e :: fe ++ [1]) b0 fb (1 :: (u0 :: fu))
    ((((hX.app sac).app sM).app sE).app sM) hb0 hfb (sym4_M sU)
  have s6 := bs0M (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb) (u0 :: fu)
    ((((((hX.app sac).app sM).app sE).app sM).app sB)) sU
  have s7 := bs1Block (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb ++ [1]) u0 fu []
    (((((((hX.app sac).app sM).app sE).app sM).app sB)).app sM) hu0 hfu Sym4.nil
  have s8 := bs0B (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb ++ [1] ++ u0 :: fu)
    (((((((hX.app sac).app sM).app sE).app sM).app sB).app sM).app sU)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at s1 s2 s3 s4 s5 s6 s7 s8 ⊢
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8))))))

/-- `BS0` along the rest of the cursor record: to the next record. -/
theorem bsTailNext (v : VR) (hv : v.Ok) (X ac2 Rest : List Nat) (hX : Sym4 X) (hac : BitsD ac2) (hR : Sym4 Rest) :
    znttLogic.Reach (hdR QNTT.BS0 X (ac2 ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ 1 :: 1 :: Rest)))))
      (hdR QNTT.BSh (X ++ ac2 ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ [1, 1])))) Rest) := by
  obtain ⟨e, fe, hE, he, hfe⟩ := bits_head v.E hv.Ene hv.E
  obtain ⟨b0, fb, hB, hb0, hfb⟩ := bits_head v.b hv.bne hv.b
  obtain ⟨u0, fu, hU, hu0, hfu⟩ := bits_head v.u hv.une hv.u
  have sE := hv.E.sym4
  have sB := hv.b.sym4
  have sU := hv.u.sym4
  rw [hE] at sE ⊢
  rw [hB] at sB ⊢
  rw [hU] at sU ⊢
  have sac := hac.sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have sN : Sym4 (1 :: 1 :: Rest) := sym4_M (sym4_M hR)
  have s1 := bs0Block X ac2 (1 :: (e :: fe ++ 1 :: (b0 :: fb ++ 1 :: (u0 :: fu ++ 1 :: 1 :: Rest)))) hX hac
    (sym4_M (sE.app (sym4_M (sB.app (sym4_M (sU.app sN))))))
  have s2 := bs0M (X ++ ac2) (e :: fe ++ 1 :: (b0 :: fb ++ 1 :: (u0 :: fu ++ 1 :: 1 :: Rest))) (hX.app sac)
    (sE.app (sym4_M (sB.app (sym4_M (sU.app sN)))))
  have s3 := bs1Block (X ++ ac2 ++ [1]) e fe (1 :: (b0 :: fb ++ 1 :: (u0 :: fu ++ 1 :: 1 :: Rest)))
    ((hX.app sac).app sM) he hfe (sym4_M (sB.app (sym4_M (sU.app sN))))
  have s4 := bs0M (X ++ ac2 ++ [1] ++ e :: fe) (b0 :: fb ++ 1 :: (u0 :: fu ++ 1 :: 1 :: Rest))
    (((hX.app sac).app sM).app sE) (sB.app (sym4_M (sU.app sN)))
  have s5 := bs1Block (X ++ ac2 ++ [1] ++ e :: fe ++ [1]) b0 fb (1 :: (u0 :: fu ++ 1 :: 1 :: Rest))
    ((((hX.app sac).app sM).app sE).app sM) hb0 hfb (sym4_M (sU.app sN))
  have s6 := bs0M (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb) (u0 :: fu ++ 1 :: 1 :: Rest)
    (((((hX.app sac).app sM).app sE).app sM).app sB) (sU.app sN)
  have s7 := bs1Block (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb ++ [1]) u0 fu (1 :: 1 :: Rest)
    ((((((hX.app sac).app sM).app sE).app sM).app sB).app sM) hu0 hfu sN
  have s8 := bs0M (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb ++ [1] ++ u0 :: fu) (1 :: Rest)
    (((((((hX.app sac).app sM).app sE).app sM).app sB).app sM).app sU) (sym4_M hR)
  have s9 := bs1M (X ++ ac2 ++ [1] ++ e :: fe ++ [1] ++ b0 :: fb ++ [1] ++ u0 :: fu ++ [1]) Rest
    ((((((((hX.app sac).app sM).app sE).app sM).app sB).app sM).app sU).app sM) hR
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at s1 s2 s3 s4 s5 s6 s7 s8 s9 ⊢
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans s9)))))))

/-- The record after the cursor gets `+1` (`IA0`), then is visited as usual. -/
def VR.inc (v : VR) : VR := { v with k := incK v.w v.k }

theorem VR.Ok.inc {v : VR} (hv : v.Ok) : v.inc.Ok :=
  { F := hv.F, O := hv.O, P := hv.P, k1 := (incK_bounds v.w v.k hv.k1 hv.kw).1,
    kw := (incK_bounds v.w v.k hv.k1 hv.kw).2, E := hv.E, Elen := hv.Elen }

theorem incPre (v : VR) (hv : v.Ok) (A0 Next : List Nat) (hA : Sym4 A0) (hN : Sym4 Next) :
    znttLogic.Reach (hdR QNTT.IA0 (A0 ++ [1]) (v.tl ++ Next)) (cu0Cfg v.inc A0 Next) := by
  have sA1 : Sym4 (A0 ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sU := hv.u.sym4
  have sB := hv.b.sym4
  have sE := hv.E.sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have sR : Sym4 (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ Next))) := sE.app (sym4_M (sB.app (sym4_M (sU.app hN))))
  have s1 := iaInc A0 (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ Next))) v.w v.k hv.k1 hv.kw hA sR
  have hb2 : BitsD (List.replicate (v.w - incK v.w v.k) 2) := BitsD.rep _ _ (by simp)
  have hb3 : BitsD (List.replicate (incK v.w v.k) 3) := BitsD.rep _ _ (by simp)
  have s2 := laSkip (A0 ++ [1] ++ List.replicate (incK v.w v.k) 3) (List.replicate (v.w - incK v.w v.k) 2)
    (v.E ++ 1 :: (v.b ++ 1 :: (v.u ++ Next)))
    (sA1.app hb3.sym4) hb2 sR
  have s3 := leSkip (A0 ++ [1] ++ List.replicate (incK v.w v.k) 3 ++ List.replicate (v.w - incK v.w v.k) 2 ++ [1])
    v.E (v.b ++ 1 :: (v.u ++ Next))
    (((sA1.app hb3.sym4).app hb2.sym4).app sM) hv.E (sB.app (sym4_M (sU.app hN)))
  have s4 := lbSkip (A0 ++ [1] ++ List.replicate (incK v.w v.k) 3 ++ List.replicate (v.w - incK v.w v.k) 2 ++ [1]
      ++ v.E ++ [1]) v.b (v.u ++ Next)
    ((((sA1.app hb3.sym4).app hb2.sym4).app sM).app sE |>.app sM) hv.b (sU.app hN)
  simp only [cu0Cfg, VR.inc, VR.tl, fld, List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 s4 ⊢
  exact s1.trans (s2.trans (s3.trans s4))

theorem incVisitAll (vs : List VR) (v : VR) (hv : v.Ok) (hvs : ∀ w ∈ vs, w.Ok) (A0 : List Nat) (hA : Sym4 A0) :
    znttLogic.Reach (hdR QNTT.IA0 (A0 ++ [1]) (v.tl ++ tailVR vs))
      (hd QNTT.RFL (A0 ++ [1] ++ v.inc.vis.tl ++ tailVR (vs.map VR.vis)) []) :=
  visitAllS vs v.inc hv.inc hvs A0 hA _ (incPre v hv A0 (tailVR vs) hA (tailVR_sym4 vs hvs))

/-- The effect of one cursor unit on the later records. -/
def stepList : List VR → List VR
  | [] => []
  | w :: ws => w.inc.vis :: ws.map VR.vis

/-- Marking one unit of the cursor record's accumulator (`BU0n` .. `BS0`), up to the cursor record's end. -/
theorem cursorMark (X : List Nat) (a r s : Nat) (T : List Nat) (hX : Sym4 X) (hT : Sym4 T) :
    znttLogic.Reach
      (hdR QNTT.BU0n X (List.replicate a 2 ++ 3 :: 3 :: List.replicate r 3 ++ List.replicate s 2 ++ T))
      (hdR QNTT.BS0 (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2 ++ T)) := by
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have sR : Sym4 (List.replicate r 3 ++ List.replicate s 2 ++ T) := ((s3 r).app (s2 s)).app hT
  have h1 := bu0Skip X a (3 :: 3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)) hX
    (sym4_B (by simp) (sym4_B (by simp) sR))
  have h2 := bu0Hit (X ++ List.replicate a 2) (3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)) (hX.app (s2 a))
    (sym4_B (by simp) sR)
  have h3 := bu1Two (X ++ List.replicate a 2) (List.replicate r 3 ++ List.replicate s 2 ++ T) (hX.app (s2 a)) sR
  have h4 := bu2Mark (X ++ List.replicate a 2) (3 :: (List.replicate r 3 ++ List.replicate s 2 ++ T)) (hX.app (s2 a))
    (sym4_B (by simp) sR)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h1 h2 h3 h4 ⊢
  exact h1.trans (h2.trans (h3.trans h4))

/-- One unit of the cursor record, with the whole sweep over the later records, back to `RFL`. -/
theorem cursorUnit (c : VR) (hc : c.Ok) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) (X : List Nat) (a r s : Nat)
    (hX : Sym4 X) :
    znttLogic.Reach
      (hdR QNTT.BU0n X (List.replicate a 2 ++ 3 :: 3 :: List.replicate r 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hd QNTT.RFL (X ++ List.replicate (a + 1) 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (stepList vs))))) []) := by
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have hac2 : BitsD (List.replicate (r + 1) 3 ++ List.replicate s 2) :=
    bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))
  have sX2 : Sym4 (X ++ List.replicate a 2 ++ [2]) := (hX.app (s2 a)).app (sym4_cell 2 (by simp))
  have sEBU : ∀ N, Sym4 N → Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ N))) := fun N hN =>
    hc.E.sym4.app (sym4_M (hc.b.sym4.app (sym4_M (hc.u.sym4.app hN))))
  cases vs with
  | nil =>
    have hm := cursorMark X a r s (1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [])))) hX (sym4_M (sEBU [] Sym4.nil))
    have he := bsTailEnd c hc (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2) sX2 hac2
    simp only [tailVR, stepList, List.map_nil, List.flatten_nil, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append, List.replicate_succ'] at hm he ⊢
    exact hm.trans he
  | cons w ws =>
    have hw : w.Ok := hvs w (by simp)
    have hws : ∀ x ∈ ws, x.Ok := fun x hx => hvs x (by simp [hx])
    have hf : BitsD [w.F, w.O, w.P] := hw.hdr3
    have sRest : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
      hf.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
    have hm := cursorMark X a r s (1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))
      hX (sym4_M (sEBU _ (by simpa [tailVR, VR.recd] using sym4_M (sym4_M sRest))))
    have hn := bsTailNext c hc (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2)
      ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sX2 hac2 sRest
    have sA : Sym4 (X ++ List.replicate a 2 ++ [2] ++ (List.replicate (r + 1) 3 ++ List.replicate s 2) ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) :=
      (sX2.app hac2.sym4).app (sym4_M (sEBU [1, 1] (sym4_M (sym4_M Sym4.nil))))
    have hs := bshSkip _ [w.F, w.O, w.P] (w.tl ++ tailVR ws) sA hf (hw.tl_sym4.app (tailVR_sym4 ws hws))
    have hv := incVisitAll ws w hw hws (X ++ List.replicate a 2 ++ [2] ++ (List.replicate (r + 1) 3 ++ List.replicate s 2) ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1]))) ++ [w.F, w.O, w.P]) (sA.app hf.sym4)
    have e1 : w.inc.vis.F = w.F := by simpa [VR.inc] using (vis_hdr w.inc).1
    have e2 : w.inc.vis.O = w.O := by simpa [VR.inc] using (vis_hdr w.inc).2.1
    have e3 : w.inc.vis.P = w.P := by simpa [VR.inc] using (vis_hdr w.inc).2.2
    simp only [tailVR, stepList, VR.recd, List.map_cons, List.flatten_cons, e1, e2, e3, List.append_assoc,
      List.cons_append, List.nil_append, List.replicate_succ'] at hm hn hs hv ⊢
    exact hm.trans (hn.trans (hs.trans hv))

/-- The tail of one unit: the broadcast sweep from `BS0` over the later records, back to `RFL`. -/
theorem cursorTail (c : VR) (hc : c.Ok) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) (X : List Nat) (a r s : Nat)
    (hX : Sym4 X) :
    znttLogic.Reach
      (hdR QNTT.BS0 (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hd QNTT.RFL (X ++ List.replicate (a + 1) 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (stepList vs))))) []) := by
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have hac2 : BitsD (List.replicate (r + 1) 3 ++ List.replicate s 2) :=
    bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))
  have sX2 : Sym4 (X ++ List.replicate a 2 ++ [2]) := (hX.app (s2 a)).app (sym4_cell 2 (by simp))
  have sEBU : ∀ N, Sym4 N → Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ N))) := fun N hN =>
    hc.E.sym4.app (sym4_M (hc.b.sym4.app (sym4_M (hc.u.sym4.app hN))))
  cases vs with
  | nil =>
    have he := bsTailEnd c hc (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2) sX2 hac2
    simp only [tailVR, stepList, List.map_nil, List.flatten_nil, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append, List.replicate_succ'] at he ⊢
    exact he
  | cons w ws =>
    have hw : w.Ok := hvs w (by simp)
    have hws : ∀ x ∈ ws, x.Ok := fun x hx => hvs x (by simp [hx])
    have hf : BitsD [w.F, w.O, w.P] := hw.hdr3
    have sRest : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
      hf.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
    have hn := bsTailNext c hc (X ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2)
      ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sX2 hac2 sRest
    have sA : Sym4 (X ++ List.replicate a 2 ++ [2] ++ (List.replicate (r + 1) 3 ++ List.replicate s 2) ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) :=
      (sX2.app hac2.sym4).app (sym4_M (sEBU [1, 1] (sym4_M (sym4_M Sym4.nil))))
    have hs := bshSkip _ [w.F, w.O, w.P] (w.tl ++ tailVR ws) sA hf (hw.tl_sym4.app (tailVR_sym4 ws hws))
    have hv := incVisitAll ws w hw hws (X ++ List.replicate a 2 ++ [2] ++ (List.replicate (r + 1) 3 ++ List.replicate s 2) ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1]))) ++ [w.F, w.O, w.P]) (sA.app hf.sym4)
    have e1 : w.inc.vis.F = w.F := by simpa [VR.inc] using (vis_hdr w.inc).1
    have e2 : w.inc.vis.O = w.O := by simpa [VR.inc] using (vis_hdr w.inc).2.1
    have e3 : w.inc.vis.P = w.P := by simpa [VR.inc] using (vis_hdr w.inc).2.2
    simp only [tailVR, stepList, VR.recd, List.map_cons, List.flatten_cons, e1, e2, e3, List.append_assoc,
      List.cons_append, List.nil_append, List.replicate_succ'] at hn hs hv ⊢
    exact hn.trans (hs.trans hv)

/-! ### Bridge `VR` ↔ `Rc` -/

/-- A record as an `Rc`, with an explicit accumulator. -/
def VR.toRcA (v : VR) (ac : List Nat) : Rc :=
  { F := v.F, O := v.O, Pf := v.P, acc := ac, E := v.E, b0 := v.b.headD 2, br := v.b.tail,
    u0 := v.u.headD 2, ur := v.u.tail }

def VR.toRc (v : VR) : Rc := v.toRcA (fld v.w v.k)

theorem VR.toRcA_tl (v : VR) (hv : v.Ok) (ac : List Nat) :
    (v.toRcA ac).tl = ac ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.u)) := by
  obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hv.bne
  obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hv.une
  simp [Rc.tl, VR.toRcA, hB, hU]

theorem VR.toRc_tl (v : VR) (hv : v.Ok) : v.toRc.tl = v.tl := by
  simpa [VR.toRc, VR.tl] using v.toRcA_tl hv (fld v.w v.k)

theorem VR.toRcA_body (v : VR) (hv : v.Ok) (ac : List Nat) :
    (v.toRcA ac).body = [v.F, v.O, v.P] ++ 1 :: (ac ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.u))) := by
  rw [Rc.body_eq, v.toRcA_tl hv]; rfl

theorem VR.toRcA_ok (v : VR) (hv : v.Ok) (ac : List Nat) (hac : BitsD ac) : (v.toRcA ac).Ok := by
  obtain ⟨b0, br, hB, hb0, hbr⟩ := bits_head v.b hv.bne hv.b
  obtain ⟨u0, ur, hU, hu0, hur⟩ := bits_head v.u hv.une hv.u
  exact { F := hv.F, O := hv.O, Pf := hv.P, acc := hac, E := hv.E, Elen := hv.Elen,
          b0 := by simpa [VR.toRcA, hB] using hb0, br := by simpa [VR.toRcA, hB] using hbr,
          u0 := by simpa [VR.toRcA, hU] using hu0, ur := by simpa [VR.toRcA, hU] using hur }

theorem VR.toRcA_rest (v : VR) (ac : List Nat) : (v.toRcA ac).Rest := by
  refine ⟨v.a, List.replicate v.c 3 ++ List.replicate v.t 2, ?_⟩
  have : v.u = List.replicate v.a 2 ++ 3 :: (List.replicate v.c 3 ++ List.replicate v.t 2) := by
    simp [VR.u, List.replicate_succ]
  have hne : v.u ≠ [] := by rw [this]; cases v.a <;> simp [List.replicate_succ]
  obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hne
  simp only [VR.toRcA, hU, List.headD_cons, List.tail_cons]
  rw [← hU]; exact this

theorem tailB_toRc : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → tailB (vs.map VR.toRc) = tailVR vs
  | [], _ => rfl
  | v :: vs, h => by
    have hv : v.Ok := h v (by simp)
    have := tailB_toRc vs (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, tailB, tailVR, VR.recd, List.flatten_cons, List.map_cons] at this ⊢
    rw [Rc.body_eq, VR.toRc_tl v hv, this]
    simp [VR.tl, VR.toRc, VR.toRcA]

/-- The pointer decrement on the `VR` model (`decU`). -/
def VR.dec (v : VR) : VR := if v.c = 0 then v else { v with a := v.a + 1, c := v.c - 1 }

theorem VR.decU_u (v : VR) : decU v.u = v.dec.u := by
  have hu : v.u = List.replicate v.a 2 ++ 3 :: (List.replicate v.c 3 ++ List.replicate v.t 2) := by
    simp [VR.u, List.replicate_succ]
  rw [hu, decU_rep]
  rcases hc : v.c with _ | c'
  · have : v.dec = v := by simp [VR.dec, hc]
    rw [this, VR.u, hc]
    rcases ht : v.t with _ | t' <;> simp [List.replicate_succ]
  · have : v.dec.a = v.a + 1 ∧ v.dec.c = c' ∧ v.dec.t = v.t := by simp [VR.dec, hc]
    simp only [VR.u, this.1, this.2.1, this.2.2, List.replicate_succ]
    simp [rep_cons_app]

theorem VR.dec_toRcA_tl (v : VR) (hv : v.Ok) (ac : List Nat) :
    (v.toRcA ac).dec.tl = ac ++ 1 :: (v.E ++ 1 :: (v.b ++ 1 :: v.dec.u)) := by
  obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hv.bne
  obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hv.une
  rw [Rc.dec_tl _ (v.toRcA_rest ac), ← VR.decU_u]
  simp [VR.toRcA, hB, hU]

/-! ### Column advance (`CA*`) -/

theorem bu1Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1n (A ++ [3]) (2 :: R)) (hd QNTT.CA0 (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1n (A ++ [3]) (1 :: R)) (hd QNTT.CA0 (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca0Sweep (X ac R : List Nat) (hX : Sym4 X) (hac : BitsD ac) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CA0 (X ++ [1] ++ ac) R) (hd QNTT.CA1 X (1 :: ac ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, ac, R] := Valid.cons hX (Valid.cons hac (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, ac, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca1Sweep (Y f R : List Nat) (hY : Sym4 Y) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CA1 (Y ++ [1] ++ f) R) (hdR QNTT.CA2 (Y ++ [1]) (f ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [Y, f, R] := Valid.cons hY (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [Y, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca2Three (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA2 A (3 :: R)) (hdR QNTT.CA4 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca4Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA4 A (f ++ R)) (hdR QNTT.CA4 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca4M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA4 A (1 :: R)) (hdR QNTT.CA5 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca4B (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.CA4 A []) (hd QNTT.PE0 A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca5M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA5 A (1 :: R)) (hdR QNTT.FA0 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca5Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA5 A (2 :: R)) (hdR QNTT.CA4 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca5Three (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA5 A (3 :: R)) (hdR QNTT.CA4 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ca5Block (A : List Nat) (c : Nat) (f R : List Nat) (hA : Sym4 A) (hc : c ∈ [2, 3]) (hf : BitsD f)
    (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CA5 A (c :: f ++ R)) (hdR QNTT.CA4 (A ++ c :: f) R) := by
  have hfR : Sym4 (f ++ R) := hf.sym4.app hR
  have h2 := ca4Block (A ++ [c]) f R (hA.app (sym4_cell c (by simp at hc ⊢; omega))) hf hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have h1 := ca5Two A (f ++ R) hA hfR
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2
  · have h1 := ca5Three A (f ++ R) hA hfR
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

/-- From `CA1` (just left of the cursor header): `F := 0`, walk to the header of the next record. -/
theorem caNext (c : VR) (hc : c.Ok) (Y ac Rest : List Nat) (hY : Sym4 Y) (hac : BitsD ac) (hne : ac ≠ [])
    (hRest : Sym4 Rest) :
    znttLogic.Reach
      (hd QNTT.CA1 (Y ++ [1, 1, 3, c.O, c.P]) (1 :: (ac ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ 1 :: 1 :: Rest)))))
      )
      (hdR QNTT.FA0 (Y ++ [1, 1, 2, c.O, c.P, 1] ++ ac ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) Rest) := by
  obtain ⟨a0, af, hacc, ha0, haf⟩ := bits_head ac hne hac
  obtain ⟨e, fe, hE, he, hfe⟩ := bits_head c.E hc.Ene hc.E
  obtain ⟨b0, fb, hB, hb0, hfb⟩ := bits_head c.b hc.bne hc.b
  obtain ⟨u0, fu, hU, hu0, hfu⟩ := bits_head c.u hc.une hc.u
  rw [hE, hB, hU]
  subst hacc
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have sA := hac.sym4
  have sE : Sym4 (e :: fe) := hE ▸ hc.E.sym4
  have sB : Sym4 (b0 :: fb) := hB ▸ hc.b.sym4
  have sU : Sym4 (u0 :: fu) := hU ▸ hc.u.sym4
  have sN : Sym4 (1 :: 1 :: Rest) := sym4_M (sym4_M hRest)
  have sO : BitsD [c.O, c.P] := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h
    · rw [h]; exact hc.O
    · rw [h]; exact hc.P
  have sF : BitsD [3, c.O, c.P] := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h
    · rw [h]; simp
    · rw [h]; exact hc.O
    · rw [h]; exact hc.P
  have sTl : Sym4 ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest))) :=
    sE.app (sym4_M (sB.app (sym4_M (sU.app sN))))
  have sH : Sym4 (Y ++ [1]) := hY.app sM
  -- the header
  have t2 := ca1Sweep (Y ++ [1]) [3, c.O, c.P] (1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)))))
    sH sF (sym4_M (sA.app (sym4_M sTl)))
  have t3 := ca2Three (Y ++ [1] ++ [1]) ([c.O, c.P] ++ 1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)))))
    (sH.app sM) (sO.sym4.app (sym4_M (sA.app (sym4_M sTl))))
  have t4 := ca4Block (Y ++ [1] ++ [1] ++ [2]) [c.O, c.P] (1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)))))
    ((sH.app sM).app (sym4_cell 2 (by simp))) sO (sym4_M (sA.app (sym4_M sTl)))
  have t5 := ca4M (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P]) ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest))))
    (((sH.app sM).app (sym4_cell 2 (by simp))).app sO.sym4) (sA.app (sym4_M sTl))
  have sP : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1]) :=
    ((((sH.app sM).app (sym4_cell 2 (by simp))).app sO.sym4)).app sM
  have t6 := ca5Block (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1]) a0 af
    (1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)))) sP ha0 haf (sym4_M sTl)
  have sP2 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af) := sP.app sA
  have t7 := ca4M _ ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest))) sP2 sTl
  have sP3 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af ++ [1]) := sP2.app sM
  have t8 := ca5Block _ e fe (1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest))) sP3 he hfe
    (sym4_M (sB.app (sym4_M (sU.app sN))))
  have sP4 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af ++ [1] ++ e :: fe) := sP3.app sE
  have t9 := ca4M _ ((b0 :: fb) ++ 1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)) sP4 (sB.app (sym4_M (sU.app sN)))
  have sP5 := sP4.app sM
  have t10 := ca5Block _ b0 fb (1 :: ((u0 :: fu) ++ 1 :: 1 :: Rest)) sP5 hb0 hfb (sym4_M (sU.app sN))
  have sP6 := sP5.app sB
  have t11 := ca4M _ ((u0 :: fu) ++ 1 :: 1 :: Rest) sP6 (sU.app sN)
  have sP7 := sP6.app sM
  have t12 := ca5Block _ u0 fu (1 :: 1 :: Rest) sP7 hu0 hfu sN
  have sP8 := sP7.app sU
  have t13 := ca4M _ (1 :: Rest) sP8 (sym4_M hRest)
  have t14 := ca5M _ Rest (sP8.app sM) hRest
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ⊢
  exact t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans (t10.trans (t11.trans
    (t12.trans (t13.trans t14)))))))))))

/-- The last record: from `CA1` to the pass end `PE0`. -/
theorem caLast (c : VR) (hc : c.Ok) (Y ac : List Nat) (hY : Sym4 Y) (hac : BitsD ac) (hne : ac ≠ [])
      :
    znttLogic.Reach
      (hd QNTT.CA1 (Y ++ [1, 1, 3, c.O, c.P]) (1 :: (ac ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))))
      )
      (hd QNTT.PE0 (Y ++ [1, 1, 2, c.O, c.P, 1] ++ ac ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) []) := by
  obtain ⟨a0, af, hacc, ha0, haf⟩ := bits_head ac hne hac
  obtain ⟨e, fe, hE, he, hfe⟩ := bits_head c.E hc.Ene hc.E
  obtain ⟨b0, fb, hB, hb0, hfb⟩ := bits_head c.b hc.bne hc.b
  obtain ⟨u0, fu, hU, hu0, hfu⟩ := bits_head c.u hc.une hc.u
  rw [hE, hB, hU]
  subst hacc
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have sA := hac.sym4
  have sE : Sym4 (e :: fe) := hE ▸ hc.E.sym4
  have sB : Sym4 (b0 :: fb) := hB ▸ hc.b.sym4
  have sU : Sym4 (u0 :: fu) := hU ▸ hc.u.sym4
  have sN : Sym4 ([] : List Nat) := Sym4.nil
  have sO : BitsD [c.O, c.P] := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h
    · rw [h]; exact hc.O
    · rw [h]; exact hc.P
  have sF : BitsD [3, c.O, c.P] := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h
    · rw [h]; simp
    · rw [h]; exact hc.O
    · rw [h]; exact hc.P
  have sTl : Sym4 ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu)))) :=
    sE.app (sym4_M (sB.app (sym4_M sU)))
  have sH : Sym4 (Y ++ [1]) := hY.app sM
  -- the header
  have t2 := ca1Sweep (Y ++ [1]) [3, c.O, c.P] (1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu))))))
    sH sF (sym4_M (sA.app (sym4_M sTl)))
  have t3 := ca2Three (Y ++ [1] ++ [1]) ([c.O, c.P] ++ 1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu))))))
    (sH.app sM) (sO.sym4.app (sym4_M (sA.app (sym4_M sTl))))
  have t4 := ca4Block (Y ++ [1] ++ [1] ++ [2]) [c.O, c.P] (1 :: ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu))))))
    ((sH.app sM).app (sym4_cell 2 (by simp))) sO (sym4_M (sA.app (sym4_M sTl)))
  have t5 := ca4M (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P]) ((a0 :: af) ++ 1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu)))))
    (((sH.app sM).app (sym4_cell 2 (by simp))).app sO.sym4) (sA.app (sym4_M sTl))
  have sP : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1]) :=
    ((((sH.app sM).app (sym4_cell 2 (by simp))).app sO.sym4)).app sM
  have t6 := ca5Block (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1]) a0 af
    (1 :: ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu))))) sP ha0 haf (sym4_M sTl)
  have sP2 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af) := sP.app sA
  have t7 := ca4M _ ((e :: fe) ++ 1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu)))) sP2 sTl
  have sP3 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af ++ [1]) := sP2.app sM
  have t8 := ca5Block _ e fe (1 :: ((b0 :: fb) ++ 1 :: ((u0 :: fu)))) sP3 he hfe
    (sym4_M (sB.app (sym4_M sU)))
  have sP4 : Sym4 (Y ++ [1] ++ [1] ++ [2] ++ [c.O, c.P] ++ [1] ++ a0 :: af ++ [1] ++ e :: fe) := sP3.app sE
  have t9 := ca4M _ ((b0 :: fb) ++ 1 :: ((u0 :: fu))) sP4 (sB.app (sym4_M sU))
  have sP5 := sP4.app sM
  have t10 := ca5Block _ b0 fb (1 :: ((u0 :: fu))) sP5 hb0 hfb (sym4_M sU)
  have sP6 := sP5.app sB
  have t11 := ca4M _ ((u0 :: fu)) sP6 sU
  have sP7 := sP6.app sM
  have t12 := ca5Block _ u0 fu [] sP7 hu0 hfu sN
  have sP8 := sP7.app sU
  have t13 := ca4B _ sP8
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ⊢
  exact t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans (t9.trans (t10.trans (t11.trans
    (t12.trans t13))))))))))


/-! ### No blanks -/

theorem noB_M : NoB [1] := by intro a ha; simp [NB] at ha ⊢; omega

theorem noB_rep (k c : Nat) (hc : c ∈ [2, 3]) : NoB (List.replicate k c) := (BitsD.rep k c hc).noB

theorem noB_cell {c : Nat} (hc : c ∈ [1, 2, 3]) : NoB [c] := by
  intro a ha; simp at ha; subst ha; simpa [NB] using hc

theorem GoodW.noB {u : List Nat} (h : GoodW u) : NoB u := by
  induction h with
  | nil => intro a ha; simp at ha
  | bit hb _ ih => exact (NoB_cons_iff).2 ⟨by simp [NB]; simp at hb; omega, ih⟩
  | mb hb _ ih => exact (NoB_cons_iff).2 ⟨by simp [NB], (NoB_cons_iff).2 ⟨by simp [NB]; simp at hb; omega, ih⟩⟩

theorem Rc.body_noB (r : Rc) (hr : r.Ok) : NoB r.body := by
  have hF : r.F ∈ NB := by have := hr.F; simp at this; simp [NB]; omega
  have hO : r.O ∈ NB := by have := hr.O; simp at this; simp [NB]; omega
  have hP : r.Pf ∈ NB := by have := hr.Pf; simp at this; simp [NB]; omega
  have hb0 : r.b0 ∈ NB := by have := hr.b0; simp at this; simp [NB]; omega
  have hu0 : r.u0 ∈ NB := by have := hr.u0; simp at this; simp [NB]; omega
  simp only [Rc.body, Rc.tlr, Rc.tl0, NoB_app_iff, NoB_cons_iff, List.cons_append, List.nil_append]
  exact ⟨hF, hO, hP, by simp [NB], hr.acc.noB, by simp [NB], hr.E.noB, by simp [NB], hb0, hr.br.noB, by simp [NB],
    hu0, hr.ur.noB⟩

theorem tailB_noB : ∀ (rs : List Rc), (∀ r ∈ rs, r.Ok) → NoB (tailB rs)
  | [], _ => by intro a ha; simp [tailB] at ha
  | r :: rs, h => by
    simp only [tailB, NoB_cons_iff, NoB_app_iff]
    exact ⟨by simp [NB], by simp [NB], Rc.body_noB r (h r (by simp)),
      tailB_noB rs (fun x hx => h x (by simp [hx]))⟩

theorem VR.Ok.tl_noB {v : VR} (hv : v.Ok) : NoB v.tl := by
  simp only [VR.tl, NoB_app_iff, NoB_cons_iff]
  exact ⟨(fld_bits _ _).noB, by simp [NB], hv.E.noB, by simp [NB], hv.b.noB, by simp [NB], hv.u.noB⟩

theorem VR.Ok.recd_noB {v : VR} (hv : v.Ok) : NoB v.recd := by
  have hF : v.F ∈ NB := by have := hv.F; simp at this; simp [NB]; omega
  have hO : v.O ∈ NB := by have := hv.O; simp at this; simp [NB]; omega
  have hP : v.P ∈ NB := by have := hv.P; simp at this; simp [NB]; omega
  simp only [VR.recd, List.cons_append, List.nil_append, NoB_cons_iff]
  exact ⟨by simp [NB], by simp [NB], hF, hO, hP, by simp [NB], hv.tl_noB⟩

theorem tailVR_noB : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → NoB (tailVR vs)
  | [], _ => by intro a ha; simp [tailVR] at ha
  | v :: vs, h => by
    simp only [tailVR, List.map_cons, List.flatten_cons, NoB_app_iff]
    exact ⟨(h v (by simp)).recd_noB, tailVR_noB vs (fun x hx => h x (by simp [hx]))⟩

/-! ### The cursor loop -/

theorem stepList_ok : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → ∀ w ∈ stepList vs, w.Ok
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    intro w hw
    simp only [stepList, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨x, hx, rfl⟩
    · exact vis_Ok _ (h v (by simp)).inc
    · exact vis_Ok _ (h x (by simp [hx]))

def stepN : Nat → List VR → List VR
  | 0, vs => vs
  | n + 1, vs => stepN n (stepList vs)

theorem stepN_ok (r : Nat) : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → ∀ w ∈ stepN r vs, w.Ok := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_ok vs h)

/-- The tape while the cursor record (a non-output node) still has `r + 1` marks to broadcast. -/
def curTape (Pm : List Nat) (pre : List Rc) (c : VR) (a r s : Nat) (vs : List VR) : List Nat :=
  Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
    1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))

theorem curTape_noB (c : VR) (hc : c.Ok) (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) :
    NoB (curTape Pm pre c a r s vs) := by
  have hPc : c.P ∈ NB := by have := hc.P; simp at this; simp [NB]; omega
  simp only [curTape, NoB_app_iff, NoB_cons_iff, List.cons_append, List.nil_append]
  exact ⟨⟨⟨⟨⟨⟨hP.noB, tailB_noB pre (fun x hx => (hpre x hx).1)⟩, by simp [NB], by simp [NB], by simp [NB],
    by simp [NB], hPc, by simp [NB]⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩,
    by simp [NB], hc.E.noB, by simp [NB], hc.b.noB, by simp [NB], hc.u.noB, tailVR_noB vs hvs⟩

theorem cursorLoop (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s : Nat) :
    ∀ (r a : Nat) (vs : List VR), (∀ w ∈ vs, w.Ok) →
    znttLogic.Reach (hd QNTT.RFL (curTape Pm pre c a r s vs) [])
      (hd QNTT.RFL (curTape Pm pre c (a + r) 0 s (stepN r vs)) [])
  | 0, a, vs, hvs => by simpa [stepN] using LTM.Reach.refl znttLogic (hd QNTT.RFL (curTape Pm pre c a 0 s vs) [])
  | r + 1, a, vs, hvs => by
    have sPm := hP.sym4
    have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
    have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
    have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
    have sM : Sym4 [1] := sym4_cell 1 (by simp)
    have hcur : (c.toRcA (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2)).Ok :=
      c.toRcA_ok hc _ (bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp)))
    have hvs' : ∀ w ∈ vs.map VR.toRc, w.Ok := by
      intro w hw; simp only [List.mem_map] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact v.toRcA_ok (hvs v hv) _ (fld_bits _ _)
    have hLe : curTape Pm pre c a (r + 1) s vs = Pm ++ tailB (pre ++ (c.toRcA (List.replicate a 2 ++
        List.replicate (r + 2) 3 ++ List.replicate s 2)) :: vs.map VR.toRc) := by
      rw [tailB_append]
      simp only [tailB]
      rw [tailB_toRc vs hvs]
      simp [curTape, VR.toRcA_body c hc, hF, hO, List.append_assoc]
    have hA := (rfFind (curTape Pm pre c a (r + 1) s vs) Pm (curTape_noB c hc Pm hP pre hpre a (r + 1) s vs hvs) hP pre hpre _ hcur hF (vs.map VR.toRc) hvs' hLe).1
      hO
    have hX : Sym4 (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) :=
      (sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B (by simp) (sym4_B hc.P (sym4_M Sym4.nil))))))
    have hU := cursorUnit c hc vs hvs (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) a r s hX
    have hIH := cursorLoop c hc hF hO Pm hP pre hpre s r (a + 1) (stepList vs) (stepList_ok vs hvs)
    rw [VR.toRcA_tl c hc, tailB_toRc vs hvs] at hA
    simp only [curTape, stepN, VR.toRcA, List.append_assoc, List.cons_append, List.nil_append,
      List.replicate_succ] at hA hU hIH ⊢
    have e : a + 1 + r = a + (r + 1) := by omega
    rw [e] at hIH
    exact hA.trans (hU.trans hIH)

theorem bu1Any (A : List Nat) (s : Nat) (T : List Nat) (hA : Sym4 A) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.BU1n (A ++ [3]) (List.replicate s 2 ++ 1 :: T))
      (hd QNTT.CA0 (A ++ [3]) (List.replicate s 2 ++ 1 :: T)) := by
  cases s with
  | zero => simpa using bu1M A T hA hT
  | succ s =>
    have := bu1Zero A (List.replicate s 2 ++ 1 :: T) hA ((BitsD.rep s 2 (by simp)).sym4.app (sym4_M hT))
    simpa [List.replicate_succ] using this

/-- `FA0` on the next record, a non-output node: mark it as the cursor, decrement all later pointers. -/
theorem fa0N (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 2) (ws : List Rc) (hws : ∀ x ∈ ws, x.DE)
    (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.RFL (A ++ [3, w.O, w.Pf] ++ 1 :: w.dec.tl ++ tailD ws) []) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1n (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) (hA.app (sym4_cell 3 (by simp)))
    (sym4_B ho.Pf (sym4_M sTl))
  have h6 := fanSkip (A ++ [3] ++ [2]) [w.Pf] (w.tl ++ tailB ws)
    ((hA.app (sym4_cell 3 (by simp))).app (sym4_cell 2 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have h7 := decAll ws hws w hw (A ++ [3] ++ [2] ++ [w.Pf] ++ [1]) (by
    exact (((hA.app (sym4_cell 3 (by simp))).app (sym4_cell 2 (by simp))).app
      (sym4_B ho.Pf Sym4.nil)).app (sym4_M Sym4.nil))
  simp only [hO, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 ⊢
  exact h4.trans (h5.trans (h6.trans h7))

theorem VR.dec_fields (v : VR) : v.dec.w = v.w ∧ v.dec.k = v.k ∧ v.dec.E = v.E ∧ v.dec.b = v.b ∧
    v.dec.F = v.F ∧ v.dec.O = v.O ∧ v.dec.P = v.P := by
  unfold VR.dec; split <;> simp [VR.b]

theorem VR.dec_ok (v : VR) (hv : v.Ok) : v.dec.Ok := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := v.dec_fields
  exact { F := by rw [e5]; exact hv.F, O := by rw [e6]; exact hv.O, P := by rw [e7]; exact hv.P,
          k1 := by rw [e2]; exact hv.k1, kw := by rw [e2, e1]; exact hv.kw,
          E := by rw [e3]; exact hv.E, Elen := by rw [e3]; exact hv.Elen }

theorem VR.dec_toRc_tl (v : VR) (hv : v.Ok) : v.toRc.dec.tl = v.dec.tl := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := v.dec_fields
  rw [VR.toRc, VR.dec_toRcA_tl v hv]
  simp [VR.tl, e1, e2, e3, e4]

theorem tailD_toRc : ∀ (vs : List VR), (∀ v ∈ vs, v.Ok) → tailD (vs.map VR.toRc) = tailVR (vs.map VR.dec)
  | [], _ => rfl
  | v :: vs, h => by
    have hv : v.Ok := h v (by simp)
    have := tailD_toRc vs (fun x hx => h x (by simp [hx]))
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := v.dec_fields
    simp only [List.map_cons, tailD, tailVR, VR.recd, List.flatten_cons, List.map_cons] at this ⊢
    rw [Rc.body_eq, this, VR.dec_toRc_tl v hv, e5, e6, e7]
    simp [VR.toRc, VR.toRcA, Rc.dec]

/-- The finished cursor record as an `Rc` (flag `F = 0`). -/
def VR.done (c : VR) (a s : Nat) : Rc :=
  { c.toRcA (List.replicate a 2 ++ 3 :: List.replicate s 2) with F := 2 }

theorem VR.done_ok (c : VR) (hc : c.Ok) (a s : Nat) : (c.done a s).Ok := by
  have := c.toRcA_ok hc (List.replicate a 2 ++ 3 :: List.replicate s 2)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
  exact { this with F := by simp [VR.done] }

/-- The next cursor record. -/
def VR.cur (w : VR) : VR := { w.dec with F := 3 }

theorem VR.cur_ok (w : VR) (hw : w.Ok) : w.cur.Ok :=
  { (w.dec_ok hw) with F := by simp [VR.cur] }

theorem colAdvance (c w : VR) (ws : List VR) (hc : c.Ok) (hw : w.Ok) (hws : ∀ x ∈ ws, x.Ok) (hF : c.F = 3)
    (hO : c.O = 2) (hOw : w.O = 2) (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a s : Nat) :
    znttLogic.Reach (hd QNTT.RFL (curTape Pm pre c a 0 s (w :: ws)) [])
      (hd QNTT.RFL (curTape Pm (pre ++ [c.done a s]) w.cur 0 (w.k - 1) (w.w - w.k) (ws.map VR.dec)) []) := by
  have hvs : ∀ x ∈ w :: ws, x.Ok := fun x hx => by
    simp at hx; rcases hx with rfl | hx
    · exact hw
    · exact hws x hx
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have sM : Sym4 [1] := sym4_cell 1 (by simp)
  have hacc : BitsD (List.replicate a 2 ++ List.replicate (0 + 1) 3 ++ List.replicate s 2) :=
    bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))
  have hcur : (c.toRcA (List.replicate a 2 ++ List.replicate (0 + 1) 3 ++ List.replicate s 2)).Ok :=
    c.toRcA_ok hc _ hacc
  have hvs' : ∀ x ∈ (w :: ws).map VR.toRc, x.Ok := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact v.toRcA_ok (hvs v hv) _ (fld_bits _ _)
  have hLe : curTape Pm pre c a 0 s (w :: ws) = Pm ++ tailB (pre ++ (c.toRcA (List.replicate a 2 ++
      List.replicate (0 + 1) 3 ++ List.replicate s 2)) :: (w :: ws).map VR.toRc) := by
    rw [tailB_append]
    simp only [tailB]
    rw [tailB_toRc (w :: ws) hvs]
    simp [curTape, VR.toRcA_body c hc, hF, hO, List.append_assoc]
  have hA := (rfFind (curTape Pm pre c a 0 s (w :: ws)) Pm (curTape_noB c hc Pm hP pre hpre a 0 s (w :: ws) hvs) hP
    pre hpre _ hcur hF ((w :: ws).map VR.toRc) hvs' hLe).1 hO
  rw [VR.toRcA_tl c hc, tailB_toRc (w :: ws) hvs] at hA
  have hX : Sym4 (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) :=
    (sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B (by simp) (sym4_B hc.P (sym4_M Sym4.nil))))))
  have sU := hc.u.sym4
  have sB := hc.b.sym4
  have sE := hc.E.sym4
  have sW : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))) := by
    refine sE.app (sym4_M (sB.app (sym4_M (sU.app ?_))))
    exact tailVR_sym4 (w :: ws) hvs
  have b1 := bu0Skip (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) a
    (3 :: (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))) hX
    (sym4_B (by simp) ((s2 s).app (sym4_M sT)))
  have b2 := bu0Hit (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1] ++ List.replicate a 2)
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws))))) (hX.app (s2 a))
    ((s2 s).app (sym4_M sT))
  have b3 := bu1Any (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1] ++ List.replicate a 2) s
    (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))) (hX.app (s2 a)) sT
  have b4 := ca0Sweep (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P]) (List.replicate a 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))
    ((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B (by simp) (sym4_B hc.P Sym4.nil))))))
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) ((s2 s).app (sym4_M sT))
  have b5 := caNext c hc (Pm ++ tailB pre) (List.replicate a 2 ++ 3 :: List.replicate s 2)
    ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) (sPm.app sPre)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
    (by cases a <;> simp [List.replicate_succ]) sW
  have hwd : w.toRc.DE := ⟨w.toRcA_ok hw _ (fld_bits _ _), w.toRcA_rest _⟩
  have hws' : ∀ x ∈ ws.map VR.toRc, x.DE := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v.toRcA_ok (hws v hv) _ (fld_bits _ _), v.toRcA_rest _⟩
  have b6 := fa0N (Pm ++ tailB pre ++ [1, 1, 2, c.O, c.P, 1] ++ (List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) w.toRc hwd (by simpa [VR.toRc, VR.toRcA] using hOw)
    (ws.map VR.toRc) hws'
    (((((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P (sym4_M Sym4.nil))))))).app
      (BitsD.sym4 (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)))).app
      (sym4_M (sE.app (sym4_M (sB.app (sym4_M (sU.app (sym4_M (sym4_M Sym4.nil))))))))))
  rw [VR.toRc_tl w hw, tailB_toRc ws hws, VR.dec_toRc_tl w hw, tailD_toRc ws hws] at b6
  simp only [VR.toRc, VR.toRcA] at b6
  have hdone : (c.done a s).body = [2, c.O, c.P] ++ 1 :: ((List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) := by
    have e : (c.done a s).tl = (c.toRcA (List.replicate a 2 ++ 3 :: List.replicate s 2)).tl := rfl
    rw [Rc.body_eq, e, VR.toRcA_tl c hc]
    rfl
  simp only [tailB_append, tailB, hdone, List.append_nil, curTape, VR.cur, hO, hF, List.append_assoc, List.cons_append,
    List.nil_append, List.replicate_succ] at hA b1 b2 b3 b4 b5 b6 ⊢
  refine hA.trans (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.of_eq rfl ?_))))))
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := w.dec_fields
  obtain ⟨k', hk'⟩ : ∃ k', w.k = k' + 1 := ⟨w.k - 1, by have := hw.k1; omega⟩
  simp [VR.tl, fld, VR.b, VR.u, e1, e2, e3, e6, e7, hOw, hk', List.replicate_succ] at e4 ⊢


/-! ### Output node: compare `acc = E` (`CP*`, `CPE*`) -/
theorem cp0Hit (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP0 A (3 :: R)) (hdR QNTT.CP1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp1Two (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP1 (A ++ [3]) (3 :: R)) (hd QNTT.CP2 (A ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp1Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP1 A (2 :: R)) (hdR QNTT.CPE (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP1 A (1 :: R)) (hdR QNTT.CPE2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp2Mark (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CP2 (A ++ [3]) R) (hdR QNTT.CP3 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp4One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP4 A (3 :: R)) (hdR QNTT.CP5 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp5One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP5 A (3 :: R)) (hdR QNTT.CP6 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp6Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP6 (A ++ [3]) (2 :: R)) (hd QNTT.CP7 (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp6M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP6 (A ++ [3]) (1 :: R)) (hd QNTT.CP7 (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cp7Mark (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CP7 (A ++ [3]) R) (hd QNTT.CP8 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cpeM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE A (1 :: R)) (hdR QNTT.CPE2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cpe2One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE2 A (3 :: R)) (hdR QNTT.CPE3 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem cpe3Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE3 (A ++ [3]) (2 :: R)) (hd QNTT.CPE4 (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp0Skip (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP0 A (List.replicate j 2 ++ R)) (hdR QNTT.CP0 (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] :=
    Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp3Skip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP3 A (f ++ 1 :: R)) (hdR QNTT.CP4 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp6Skip (A : List Nat) (t : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP6 A (List.replicate t 3 ++ R)) (hdR QNTT.CP6 (A ++ List.replicate t 3) R) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate t 3, R] :=
    Valid.cons hA (Valid.cons (repSet t 3) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate t 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp8Sweep (X : List Nat) (t : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CP8 (X ++ [1] ++ List.replicate t 3) R)
      (hd QNTT.CP9 X (1 :: List.replicate t 3 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [X, List.replicate t 3, R] :=
    Valid.cons hX (Valid.cons (repSet t 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate t 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp9Sweep (X ac R : List Nat) (hX : Sym4 X) (hac : BitsD ac) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CP9 (X ++ [1] ++ ac) R) (hdR QNTT.CP0 (X ++ [1]) (ac ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, ac, R] := Valid.cons hX (Valid.cons hac (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [X, ac, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpeSkip (A : List Nat) (t : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE A (List.replicate t 2 ++ R)) (hdR QNTT.CPE (A ++ List.replicate t 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate t 2, R] :=
    Valid.cons hA (Valid.cons (repSet t 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate t 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpe4Sweep (X R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CPE4 (X ++ [1] ++ [3]) R) (hd QNTT.CPE5 X (1 :: 3 :: R)) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .sym 3]) (rs := [.blk 1 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpe5Sweep (Y ac R : List Nat) (hY : Sym4 Y) (hac : BitsD ac) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CPE5 (Y ++ [1] ++ ac) R) (hdR QNTT.CPE6 (Y ++ [1]) (ac ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [Y, ac, R] := Valid.cons hY (Valid.cons hac (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [Y, ac, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpe6 (Y : List Nat) (j : Nat) (R : List Nat) (hY : Sym4 Y) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE6 (Y ++ [1]) (List.replicate j 2 ++ 3 :: R))
      (hd QNTT.CPE7 (Y ++ [1] ++ List.replicate j 3) (3 :: R)) := by
  have hV : Valid [ALL, [2], ALL] [Y, List.replicate j 2, R] :=
    Valid.cons hY (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFT (env := [Y, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id, .sym 3, .blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1, .blk 1 (.const 3)]) (rs' := [.sym 3, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpe7 (X : List Nat) (j : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.CPE7 (X ++ [1] ++ List.replicate j 3) R)
      (hdR QNTT.DAc (X ++ [1]) (List.replicate j 3 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [X, List.replicate j 3, R] :=
    Valid.cons hX (Valid.cons (repSet j 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [X, List.replicate j 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id])
    (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ### Output compare: `acc = E` -/

theorem rep_comm (e c : Nat) : [c] ++ List.replicate e c = List.replicate e c ++ [c] := by
  show c :: List.replicate e c = _
  rw [← List.replicate_succ, List.replicate_succ']

theorem cpe3M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE3 (A ++ [3]) (1 :: R)) (hd QNTT.CPE4 (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp67 (A : List Nat) (z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP6 (A ++ [3]) (List.replicate z 2 ++ 1 :: R))
      (hd QNTT.CP8 A (List.replicate (z + 1) 2 ++ 1 :: R)) := by
  cases z with
  | zero =>
    have h1 := cp6M A R hA hR
    have h2 := cp7Mark A (1 :: R) hA (by simp [ALL, hR])
    simpa using h1.trans h2
  | succ k =>
    have h1 := cp6Zero A (List.replicate k 2 ++ 1 :: R) hA (by simp [ALL, hR])
    have h2 := cp7Mark A (2 :: (List.replicate k 2 ++ 1 :: R)) hA (by simp [ALL, hR])
    simpa [List.replicate_succ] using h1.trans h2

theorem cpRound (A : List Nat) (a e z : Nat) (f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: 3 :: f ++ 1 :: (3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2) ++ 1 :: R)))
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate (a + 1) 2 ++ 3 :: f ++ 1 :: (List.replicate (e + 1) 3 ++ List.replicate (z + 1) 2 ++ 1 :: R))) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sQ : Sym4 (A ++ [1] ++ List.replicate a 2) := sP.app (BitsD.rep a 2 (by simp)).sym4
  have hf3 : BitsD (3 :: f) := BitsD.cons (by simp) hf
  have sE : Sym4 (List.replicate e 3) := (BitsD.rep e 3 (by simp)).sym4
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sf : Sym4 f := hf.sym4
  have SS : ∀ l, Sym4 l → Sym4 l := fun _ h => h
  have h1 := cp0Skip (A ++ [1]) a (3 :: 3 :: (f ++ 1 :: ((3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2)) ++ 1 :: R))) sP
    (by simp [ALL, sf, hR, sE, sZ])
  have h2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2)) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sE, sZ])
  have h3 := cp1Two (A ++ [1] ++ List.replicate a 2) (f ++ 1 :: ((3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2)) ++ 1 :: R)) sQ
    (by simp [ALL, sf, hR, sE, sZ])
  have h4 := cp2Mark (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2)) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sE, sZ])
  have h5 := cp3Skip (A ++ [1] ++ List.replicate a 2 ++ [2]) (3 :: f) ((3 :: 3 :: (List.replicate e 3 ++ List.replicate z 2)) ++ 1 :: R)
    (by simp [ALL, hA, sQ]) hf3 (by simp [ALL, hR, sE, sZ])
  have h6 := cp4One (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1]) (3 :: (List.replicate e 3 ++ List.replicate z 2) ++ 1 :: R)
    (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sE, sZ])
  have h7 := cp5One (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) ((List.replicate e 3 ++ List.replicate z 2) ++ 1 :: R)
    (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sE, sZ])
  have h8 := cp6Skip (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3] ++ [3]) e (List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
  have hq : A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3] ++ [3] ++ List.replicate e 3
      = (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ ([3] ++ List.replicate e 3)) ++ [3] := by
    have key : ([3] : List Nat) ++ ([3] ++ List.replicate e 3) = [3] ++ (List.replicate e 3 ++ [3]) := by
      show 3 :: 3 :: List.replicate e 3 = 3 :: (List.replicate e 3 ++ [3])
      rw [← List.replicate_succ', List.replicate_succ]
    simp only [List.append_assoc, key]
  have h9 := cp67 (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ ([3] ++ List.replicate e 3)) z R
    (by simp [ALL, hA, sQ, sf, sE]) hR
  have hr : [3] ++ List.replicate e 3 = List.replicate (e + 1) 3 := by simp [List.replicate_succ]
  rw [hr] at h9 hq
  rw [hq] at h8
  have h10 := cp8Sweep (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f)) (e + 1)
    (List.replicate (z + 1) 2 ++ 1 :: R) (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
  have h11 := cp9Sweep A (List.replicate a 2 ++ [2] ++ (3 :: f)) (1 :: (List.replicate (e + 1) 3 ++ (List.replicate (z + 1) 2 ++ 1 :: R)))
    hA (bd_app (bd_app (BitsD.rep a 2 (by simp)) (BitsD.cons (by simp) (BitsD.rep 0 2 (by simp)))) hf3)
    (by simp [ALL, hR, sE, sZ])
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⊢
  refine h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11.of_eq rfl ?_))))))))))
  simp [List.replicate_succ']

theorem cpe1 (B : List Nat) (s : Nat) (Rr : List Nat) (hB : Sym4 B) (hR : Sym4 Rr) :
    znttLogic.Reach (hdR QNTT.CP1 B (List.replicate s 2 ++ 1 :: Rr))
      (hdR QNTT.CPE2 (B ++ List.replicate s 2 ++ [1]) Rr) := by
  cases s with
  | zero => simpa using cp1M B Rr hB hR
  | succ k =>
    have h1 := cp1Zero B (List.replicate k 2 ++ 1 :: Rr) hB (by simp [ALL, hR])
    have h2 := cpeSkip (B ++ [2]) k (1 :: Rr) (by simp [ALL, hB]) (by simp [ALL, hR])
    have h3 := cpeM (B ++ [2] ++ List.replicate k 2) Rr (by simp [ALL, hB]) hR
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3
    refine h1.trans (h2.trans (h3.of_eq rfl ?_))
    simp [List.replicate_succ]

theorem cpe34 (A : List Nat) (z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE3 (A ++ [3]) (List.replicate z 2 ++ 1 :: R))
      (hd QNTT.CPE4 (A ++ [3]) (List.replicate z 2 ++ 1 :: R)) := by
  cases z with
  | zero => simpa using cpe3M A R hA hR
  | succ k =>
    simpa [List.replicate_succ] using cpe3Zero A (List.replicate k 2 ++ 1 :: R) hA (by simp [ALL, hR])

theorem cpTerm (A : List Nat) (a s z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: (List.replicate s 2 ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R))))
      (hdR QNTT.DAc (A ++ [1]) (List.replicate a 3 ++ 3 :: (List.replicate s 2 ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R)))) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sS : Sym4 (List.replicate s 2) := (BitsD.rep s 2 (by simp)).sym4
  have sA2 : Sym4 (List.replicate a 2) := (BitsD.rep a 2 (by simp)).sym4
  have g1 := cp0Skip (A ++ [1]) a (3 :: (List.replicate s 2 ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R))) sP
    (by simp [ALL, sS, sZ, hR])
  have g2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (List.replicate s 2 ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R))
    (by simp [ALL, hA, sA2]) (by simp [ALL, sS, sZ, hR])
  have g3 := cpe1 (A ++ [1] ++ List.replicate a 2 ++ [3]) s (3 :: List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2]) (by simp [ALL, sZ, hR])
  have g4 := cpe2One (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1]) (List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, hR])
  have g5 := cpe34 (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1]) z R
    (by simp [ALL, hA, sA2, sS]) hR
  have g6 := cpe4Sweep (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2) (List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, hR])
  have g7 := cpe5Sweep A (List.replicate a 2 ++ [3] ++ List.replicate s 2) (1 :: 3 :: (List.replicate z 2 ++ 1 :: R)) hA
    (bd_app (bd_app (BitsD.rep a 2 (by simp)) (BitsD.rep 1 3 (by simp))) (BitsD.rep s 2 (by simp)))
    (by simp [ALL, sZ, hR])
  have g8 := cpe6 A a (List.replicate s 2 ++ 1 :: 3 :: (List.replicate z 2 ++ 1 :: R)) hA (by simp [ALL, sS, sZ, hR])
  have g9 := cpe7 A a (3 :: (List.replicate s 2 ++ 1 :: 3 :: (List.replicate z 2 ++ 1 :: R))) hA
    (by simp [ALL, sS, sZ, hR])
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 g6 g7 g8 g9 ⊢
  refine g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans g9)))))))

theorem cmpAcc (A : List Nat) (n : Nat) : ∀ (a s z : Nat) (R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (n + 1) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hdR QNTT.DAc (A ++ [1]) (List.replicate (a + n + 1) 3 ++ List.replicate s 2 ++
        1 :: (3 :: List.replicate (z + n) 2) ++ 1 :: R)) := by
  induction n with
  | zero =>
    intro a s z R hA hR
    have := cpTerm A a s z R hA hR
    simpa [List.replicate_succ'] using this
  | succ n ih =>
    intro a s z R hA hR
    have h := cpRound A a n z (List.replicate n 3 ++ List.replicate s 2) R hA
      (bd_app (BitsD.rep n 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
    have ih' := ih (a + 1) s (z + 1) R hA hR
    rw [show a + 1 + n + 1 = a + (n + 1) + 1 by omega, show z + 1 + n = z + (n + 1) by omega] at ih'
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h ih' ⊢
    exact h.trans ih'

/-- `FA0` on the next record, an output node whose `E` matches the accumulator: compare, then decrement. -/
theorem fa0O (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 3) (n s z : Nat)
    (hacc : w.acc = List.replicate (n + 1) 3 ++ List.replicate s 2)
    (hE : w.E = List.replicate (n + 1) 3 ++ List.replicate z 2)
    (ws : List Rc) (hws : ∀ x ∈ ws, x.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.RFL (A ++ [3, w.O, w.Pf] ++ 1 :: ({ w with E := 3 :: List.replicate (z + n) 2 } : Rc).dec.tl ++ tailD ws) []) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have sA3 : Sym4 (A ++ [3]) := hA.app (sym4_cell 3 (by simp))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1o (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) sA3 (sym4_B ho.Pf (sym4_M sTl))
  have h6 := faoSkip (A ++ [3] ++ [3]) [w.Pf] (w.tl ++ tailB ws) (sA3.app (sym4_cell 3 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have sR' : Sym4 (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    have := sTl
    simp only [Rc.tl] at this
    simp [hacc, hE] at this
    simpa using this.2.2.2.2.2.2
  have hwt : w.tl ++ tailB ws = List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
      1 :: (List.replicate (n + 1) 3 ++ List.replicate z 2) ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    simp [Rc.tl, hacc, hE]
  rw [hwt] at h4 h5 h6 ⊢
  have h7 := cmpAcc (A ++ [3] ++ [3] ++ [w.Pf]) n 0 s z (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)
    ((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil)) sR'
  have hw' : ({ w with E := 3 :: List.replicate (z + n) 2 } : Rc).DE := by
    refine ⟨{ ho with E := ?_, Elen := ?_ }, hw.rest⟩
    · exact BitsD.cons (by simp) (BitsD.rep _ _ (by simp))
    · have := ho.Elen
      simp [hE] at this
      show 2 ≤ (3 :: List.replicate (z + n) 2).length
      simp only [List.length_cons, List.length_replicate]
      omega
  have sA5 : Sym4 (A ++ [3] ++ [3] ++ [w.Pf] ++ [1]) :=
    (((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil))).app (sym4_cell 1 (by simp))
  have h8 := decAll ws hws { w with E := 3 :: List.replicate (z + n) 2 } hw' (A ++ [3] ++ [3] ++ [w.Pf] ++ [1]) sA5
  simp only [hO, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 h8 ⊢
  refine h4.trans (h5.trans (h6.trans (h7.trans (h8.of_eq ?_ rfl))))
  simp [Rc.tl, hacc, List.replicate_succ, Nat.add_comm, Nat.add_left_comm]

/-! ### Output cursor unit: single-step and sweep primitives (`BU*o`, `BZ*`, `IE*`, `TS*`, `BZR*`) -/

theorem bu0oSkip (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU0o A (List.replicate j 2 ++ R)) (hdR QNTT.BU0o (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] := Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu0oHit (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU0o A (3 :: R)) (hdR QNTT.BU1o (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu1oOne (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1o A (3 :: R)) (hdR QNTT.BZ0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz0Skip (A : List Nat) (f : List Nat) (R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ0 A (f ++ 1 :: R)) (hdR QNTT.BZ1 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz1Skip (A : List Nat) (f : List Nat) (R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ1 A (f ++ 1 :: R)) (hdR QNTT.BZ2 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz2Skip (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ2 A (List.replicate j 2 ++ R)) (hdR QNTT.BZ2 (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] := Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz2Hit (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ2 A (3 :: R)) (hdR QNTT.BZ3 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz3One (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ3 (A ++ [3]) (3 :: R)) (hd QNTT.BZ4 (A ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz3Zero (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ3 (A ++ [3]) (2 :: R)) (hd QNTT.BZR (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz3M (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZ3 (A ++ [3]) (1 :: R)) (hd QNTT.BZR (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz4Mark (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZ4 (A ++ [3]) R) (hd QNTT.BZ5 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz5Sweep (X : List Nat) (m : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZ5 (X ++ List.replicate m 2) R) (hd QNTT.BZ5 X (List.replicate m 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [X, List.replicate m 2, R] := Valid.cons hX (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bz5M (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZ5 (X ++ [1]) R) (hd QNTT.IE0 X (1 :: R)) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ie0One (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IE0 (A ++ [3]) R) (hd QNTT.IEW A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ie0Zero (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IE0 (A ++ [2]) R) (hd QNTT.IE1 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem iewSweep (A : List Nat) (t : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IEW (A ++ List.replicate t 3) R) (hd QNTT.IEW A (List.replicate t 2 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate t 3, R] := Valid.cons hA (Valid.cons (repSet t 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, List.replicate t 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 2), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem iewM (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IEW (A ++ [1]) R) (hdR QNTT.IEW2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem iew2Mark (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IEW2 (A ++ [1]) (2 :: R)) (hd QNTT.TS0 (A ++ [1]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ie1Sweep (X : List Nat) (t : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IE1 (X ++ List.replicate t 2) R) (hd QNTT.IE1 X (List.replicate t 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [X, List.replicate t 2, R] := Valid.cons hX (Valid.cons (repSet t 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate t 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ie1One (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.IE1 (X ++ [3]) R) (hdR QNTT.IE2 (X ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTF (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ie2Mark (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.IE2 (X ++ [3]) (2 :: R)) (hd QNTT.TS0 (X ++ [3]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts0Left (L : List Nat) (R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.TS0 L R) (hdR QNTT.TS1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  simpa using checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts1Skip (A : List Nat) (f : List Nat) (R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.TS1 A (f ++ 1 :: R)) (hdR QNTT.TS2 (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts2Skip (A : List Nat) (j : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.TS2 A (List.replicate j 2 ++ R)) (hdR QNTT.TS2 (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] := Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts2Mark (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.TS2 A (3 :: R)) (hdR QNTT.TS3 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts3One (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.TS3 (A ++ [2]) (3 :: R)) (hd QNTT.RFL (A ++ [2]) (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem ts3M (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.TS3 (A ++ [2]) (1 :: R)) (hd QNTT.TSW (A ++ [2]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem tswSweep (X : List Nat) (t : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.TSW (X ++ List.replicate t 2) R) (hd QNTT.TSW X (List.replicate t 3 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [X, List.replicate t 2, R] := Valid.cons hX (Valid.cons (repSet t 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate t 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 (.const 3), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem tswM (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.TSW (X ++ [1]) R) (hd QNTT.RFL X (1 :: R)) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzrSweep (X : List Nat) (f : List Nat) (R : List Nat) (hX : Sym4 X) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR (X ++ f) R) (hd QNTT.BZR X (f ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, f, R] := Valid.cons hX (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzrM (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR (X ++ [1]) R) (hdR QNTT.BZR2 (X ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTF (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr2Skip (A : List Nat) (m : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZR2 A (List.replicate m 2 ++ R)) (hdR QNTT.BZR2 (A ++ List.replicate m 3) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate m 2, R] := Valid.cons hA (Valid.cons (repSet m 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate m 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 (.const 3)]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr2One (X : List Nat) (m : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZR2 (X ++ [1] ++ List.replicate m 3) (3 :: R)) (hd QNTT.BZR3 (X ++ [1] ++ List.replicate m 3) (3 :: R)) := by
  have hV : Valid [ALL, [3], ALL] [X, List.replicate m 3, R] := Valid.cons hX (Valid.cons (repSet m 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkFT (env := [X, List.replicate m 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.sym 3, .blk 2 .id]) (ls' := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs' := [.sym 3, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr3Sweep (X : List Nat) (m : Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR3 (X ++ [1] ++ List.replicate m 3) R) (hd QNTT.BZR4 X (1 :: List.replicate m 3 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [X, List.replicate m 3, R] := Valid.cons hX (Valid.cons (repSet m 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, List.replicate m 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr4Sweep (X : List Nat) (f : List Nat) (R : List Nat) (hX : Sym4 X) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR4 (X ++ f) R) (hd QNTT.BZR4 X (f ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, f, R] := Valid.cons hX (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [X, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr4M (X : List Nat) (R : List Nat) (hX : Sym4 X) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR4 (X ++ [1]) R) (hd QNTT.BZR5 X (1 :: R)) := by
  have hV : Valid [ALL, ALL] [X, R] := Valid.cons hX (Valid.cons hR (Valid.nil _))
  simpa using checkTT (env := [X, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr5Sweep (X : List Nat) (ac : List Nat) (R : List Nat) (hX : Sym4 X) (hac : BitsD ac) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BZR5 (X ++ [1] ++ ac) R) (hdR QNTT.BZR6 (X ++ [1]) (ac ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [X, ac, R] := Valid.cons hX (Valid.cons hac (Valid.cons hR (Valid.nil _)))
  simpa using checkTF (env := [X, ac, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr6Skip (A : List Nat) (a : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZR6 A (List.replicate a 2 ++ R)) (hdR QNTT.BZR6 (A ++ List.replicate a 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate a 2, R] := Valid.cons hA (Valid.cons (repSet a 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, List.replicate a 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id]) (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bzr6Mark (A : List Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BZR6 A (3 :: R)) (hdR QNTT.BS0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ### `E += 1` and `S += 1` -/

theorem rep_app_cons (n c : Nat) (x : List Nat) :
    List.replicate n c ++ c :: x = c :: (List.replicate n c ++ x) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem ieStep (Y : List Nat) (wE e : Nat) (T : List Nat) (hY : Sym4 Y) (hYn : NoB Y) (hT : Sym4 T)
    (he : 1 ≤ e) (hew : e ≤ wE) :
    znttLogic.Reach (hd QNTT.IE0 (Y ++ [1] ++ fld wE e) (1 :: T))
      (hdR QNTT.TS1 [] (Y ++ [1] ++ fld wE (incK wE e) ++ 1 :: T)) := by
  have sY1 : Sym4 (Y ++ [1]) := hY.app (sym4_cell 1 (by simp))
  have nY1 : NoB (Y ++ [1]) := by simp [NoB_app_iff, hYn, NB]
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have n3 : ∀ j, NoB (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).noB
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  by_cases h : e' + 1 = wE
  · subst h
    have h1 := ie0One (Y ++ [1] ++ List.replicate e' 3) (1 :: T) ((sY1.app (s3 _))) (sym4_M hT)
    have h2 := iewSweep (Y ++ [1]) e' (2 :: 1 :: T) sY1 (sym4_B (by simp) (sym4_M hT))
    have h3 := iewM Y (2 :: (List.replicate e' 2 ++ 1 :: T)) hY (sym4_B (by simp) ((s2 _).app (sym4_M hT)))
    have h4 := iew2Mark Y (List.replicate e' 2 ++ 1 :: T) hY ((s2 _).app (sym4_M hT))
    have h5 := ts0Left (Y ++ [1]) (3 :: (List.replicate e' 2 ++ 1 :: T)) nY1
      (sym4_B (by simp) ((s2 _).app (sym4_M hT)))
    simp only [fld, incK, ite_true, Nat.sub_self, List.replicate_zero, List.append_nil, Nat.add_sub_cancel,
      List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 ⊢
    rw [rep_app_cons] at h2
    refine (h1.trans (h2.trans (h3.trans (h4.trans h5)))).of_eq (by simp [List.replicate_succ']) ?_
    simp [List.replicate_succ]
  · have hlt : e' + 1 < wE := by omega
    obtain ⟨z', rfl⟩ : ∃ z', wE = e' + 1 + z' + 1 := ⟨wE - e' - 2, by omega⟩
    have hinc : incK (e' + 1 + z' + 1) (e' + 1) = e' + 2 := by simp [incK]; omega
    have h1 := ie0Zero (Y ++ [1] ++ List.replicate e' 3 ++ [3] ++ List.replicate z' 2) (1 :: T)
      (((sY1.app (s3 _)).app (sym4_cell 3 (by simp))).app (s2 _)) (sym4_M hT)
    have h2 := ie1Sweep (Y ++ [1] ++ List.replicate e' 3 ++ [3]) z' (2 :: 1 :: T)
      ((sY1.app (s3 _)).app (sym4_cell 3 (by simp))) (sym4_B (by simp) (sym4_M hT))
    rw [rep_app_cons] at h2
    have h3 := ie1One (Y ++ [1] ++ List.replicate e' 3) (2 :: (List.replicate z' 2 ++ 1 :: T)) (sY1.app (s3 _))
      (sym4_B (by simp) ((s2 _).app (sym4_M hT)))
    have h4 := ie2Mark (Y ++ [1] ++ List.replicate e' 3) (List.replicate z' 2 ++ 1 :: T) (sY1.app (s3 _))
      ((s2 _).app (sym4_M hT))
    have h5 := ts0Left (Y ++ [1] ++ List.replicate e' 3 ++ [3]) (3 :: (List.replicate z' 2 ++ 1 :: T))
      (by simp [NoB_app_iff, hYn, NB, n3]) (sym4_B (by simp) ((s2 _).app (sym4_M hT)))
    rw [hinc]
    have hs : e' + 1 + z' + 1 - (e' + 1) = z' + 1 := by omega
    have hs2 : e' + 1 + z' + 1 - (e' + 2) = z' := by omega
    refine (h1.trans (h2.trans (h3.trans (h4.trans h5)))).of_eq ?_ ?_
    · simp [fld, hs, List.replicate_succ']
    · simp [fld, hs2, List.replicate_succ, rep_app_cons]

/-- The register `S` (thermometer `0^j 1^q`, value = number of marks mod `p`) after `S += 1`. -/
def sInc (j q : Nat) : List Nat :=
  if q ≤ 1 then List.replicate (j + 1) 3 else List.replicate (j + 1) 2 ++ List.replicate (q - 1) 3

theorem tsStep (Wf : List Nat) (hW : BitsD Wf) (j q : Nat) (hq : 1 ≤ q) (P2 : List Nat) (hP : Sym4 P2) :
    znttLogic.Reach
      (hdR QNTT.TS1 [] (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2)))
      (hdR QNTT.RF0 [] (Wf ++ 1 :: (sInc j q ++ 1 :: P2))) := by
  have sW := hW.sym4
  have sW1 : Sym4 (Wf ++ [1]) := sW.app (sym4_cell 1 (by simp))
  have nW := hW.noB
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
  have hW1 : NoB (Wf ++ [1]) := by simp [NoB_app_iff, nW, NB]
  have hWj : NoB (Wf ++ [1] ++ List.replicate j 2) := by
    simp [NoB_app_iff, nW, NB, noB_rep]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have g1 := ts1Skip [] Wf (List.replicate j 2 ++ List.replicate (q' + 1) 3 ++ 1 :: P2) Sym4.nil hW
    (by simp [ALL, s2, s3, hP])
  have g2 := ts2Skip (Wf ++ [1]) j (List.replicate (q' + 1) 3 ++ 1 :: P2) sW1 (by simp [ALL, s3, hP])
  have g3 := ts2Mark (Wf ++ [1] ++ List.replicate j 2) (List.replicate q' 3 ++ 1 :: P2) (sW1.app (s2 _))
    (by simp [ALL, s3, hP])
  cases q' with
  | succ q'' =>
    have g4 := ts3One (Wf ++ [1] ++ List.replicate j 2) (List.replicate q'' 3 ++ 1 :: P2) (sW1.app (s2 _))
      (by simp [ALL, s3, hP])
    have g5 := rflScan (Wf ++ [1] ++ List.replicate j 2 ++ [2]) (3 :: (List.replicate q'' 3 ++ 1 :: P2))
      (by simp [NoB_app_iff, nW, NB, noB_rep]) (by simp [ALL, s3, hP])
    simp only [List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 ⊢
    refine (g1.trans (g2.trans (g3.trans (g4.trans g5)))).of_eq rfl ?_
    simp [sInc, List.replicate_succ, rep_app_cons]
  | zero =>
    have g4 := ts3M (Wf ++ [1] ++ List.replicate j 2) P2 (sW1.app (s2 _)) hP
    have g5 := tswSweep (Wf ++ [1]) (j + 1) (1 :: P2) sW1 (sym4_M hP)
    have g6 := tswM Wf (List.replicate (j + 1) 3 ++ 1 :: P2) sW ((s3 _).app (sym4_M hP))
    have g7 := rflScan Wf (1 :: (List.replicate (j + 1) 3 ++ 1 :: P2)) nW (sym4_M ((s3 _).app (sym4_M hP)))
    have e : Wf ++ [1] ++ List.replicate j 2 ++ [2] = Wf ++ [1] ++ List.replicate (j + 1) 2 := by
      rw [List.append_assoc _ (List.replicate j 2), ← List.replicate_succ']
    rw [e] at g3 g4
    simp only [List.replicate_zero, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append] at g1 g2 g3 g4 g5 g6 g7 ⊢
    refine (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans g7)))))).of_eq rfl ?_
    simp [sInc, List.replicate_succ, rep_app_cons]

/-! ### Output cursor: one broadcast step -/

/-- The cursor record is an output node: `RF0` finds it and dispatches to `BU0o`. -/
theorem rfO (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) :
    znttLogic.Reach
      (hdR QNTT.RF0 [] (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++
        List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hdR QNTT.BU0o (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) (List.replicate a 2 ++ List.replicate (r + 1) 3 ++
        List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))))) := by
  have hacc : BitsD (List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2) :=
    bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))
  have hcur : (c.toRcA (List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2)).Ok :=
    c.toRcA_ok hc _ hacc
  have hvs' : ∀ x ∈ vs.map VR.toRc, x.Ok := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact v.toRcA_ok (hvs v hv) _ (fld_bits _ _)
  have hLe : Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++
        List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))) =
      Pm ++ tailB (pre ++ (c.toRcA (List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2)) :: vs.map VR.toRc) := by
    rw [tailB_append]
    simp only [tailB]
    rw [tailB_toRc vs hvs]
    simp [VR.toRcA_body c hc, hF, hO, List.append_assoc]
  have hnb : NoB (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++
        List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))) := by
    have hPc : c.P ∈ NB := by have := hc.P; simp at this; simp [NB]; omega
    simp only [NoB_app_iff, NoB_cons_iff, List.cons_append, List.nil_append]
    exact ⟨⟨⟨⟨⟨⟨hP.noB, tailB_noB pre (fun x hx => (hpre x hx).1)⟩, by simp [NB], by simp [NB], by simp [NB],
      by simp [NB], hPc, by simp [NB]⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩,
      by simp [NB], hc.E.noB, by simp [NB], hc.b.noB, by simp [NB], hc.u.noB, tailVR_noB vs hvs⟩
  have hA := (rfFind0 _ Pm hnb hP pre hpre _ hcur hF (vs.map VR.toRc) hvs' hLe).2 hO
  rw [VR.toRcA_tl c hc, tailB_toRc vs hvs] at hA
  simpa [VR.toRcA, List.append_assoc] using hA

theorem goodW_reg (Wf S P2 : List Nat) (hW : BitsD Wf) (hS : BitsD S) (hne : S ≠ []) (hP2 : GoodW (1 :: P2)) :
    GoodW (Wf ++ 1 :: (S ++ 1 :: P2)) := by
  cases S with
  | nil => exact absurd rfl hne
  | cons b S0 =>
    exact GoodW.app (GoodW.bits hW) (GoodW.mb (hS b (by simp))
      (GoodW.app (GoodW.bits (fun x hx => hS x (by simp [hx]))) hP2))

theorem sInc_bits (j q : Nat) : BitsD (sInc j q) := by
  unfold sInc; split
  · exact BitsD.rep _ _ (by simp)
  · exact bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))

theorem sInc_ne (j q : Nat) : sInc j q ≠ [] := by
  unfold sInc; split <;> simp

theorem fld_len (w k : Nat) (h : k ≤ w) : (fld w k).length = w := by simp [fld]; omega

/-- One broadcast step of the output cursor with at least two ones left in `b`: `E += 1`, `S += 1`, one more
`b`-mark, back to `BU0o` via `RFL`. -/
theorem oStep (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (Wf : List Nat) (hW : BitsD Wf) (j q : Nat)
    (hq : 1 ≤ q) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok)
    (wE e : Nat) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e) (n' : Nat) (hn : c.n = n' + 1) :
    znttLogic.Reach
      (hdR QNTT.BU0o (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hdR QNTT.BU0o (Wf ++ 1 :: (sInc j q ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 ::
          (fld wE (incK wE e) ++ 1 :: (({ c with m := c.m + 1, n := n' } : VR).b ++ 1 :: (c.u ++ tailVR vs))))) := by
  have hS0 : BitsD (List.replicate j 2 ++ List.replicate q 3) :=
    bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))
  have hG0 := goodW_reg Wf _ P2 hW hS0 (by obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩; simp [List.replicate_succ]) hP2
  have hG1 := goodW_reg Wf _ P2 hW (sInc_bits j q) (sInc_ne j q) hP2
  have hElen := hc.Elen
  rw [hE, fld_len _ _ hew] at hElen
  have hinc : incK wE e ≤ wE := by unfold incK; split <;> omega
  have hc1 : ({ c with m := c.m + 1, n := n', E := fld wE (incK wE e) } : VR).Ok :=
    { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
      Elen := by show 2 ≤ (fld wE (incK wE e)).length; rw [fld_len _ _ hinc]; exact hElen }
  have hNext := rfO { c with m := c.m + 1, n := n', E := fld wE (incK wE e) } hc1 hF hO _ hG1 pre hpre a (r + 1) s vs hvs
  have hb : c.b = (List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) := by simp [VR.b, hn, List.replicate_succ]
  have sW := hW.sym4
  have sP2 : Sym4 P2 := by
    have := hP2.sym4; simp at this; exact this.2
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have sE : Sym4 (fld wE e) := (fld_bits _ _).sym4
  have sU := hc.u.sym4
  have sV := tailVR_sym4 vs hvs
  have hP23 : c.P = 2 ∨ c.P = 3 := by have := hc.P; simpa using this
  have hPA : c.P ∈ ALL := by simp [ALL]; omega
  have nPm := hG0.noB
  have nX : NoB (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) := by
    exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨nPm, tailB_noB pre (fun x hx => (hpre x hx).1)⟩, by simp [NB]; omega⟩
  rw [hb, hE]
  have bRacc : BitsD (List.replicate r 3 ++ List.replicate s 2) := bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))
  have g1 := bu0oSkip (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) a (3 :: 3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: ((fld wE e) ++ 1 :: ((List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) ++ 1 :: (c.u ++ tailVR vs))))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g2 := bu0oHit ((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2) (3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: ((fld wE e) ++ 1 :: ((List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) ++ 1 :: (c.u ++ tailVR vs))))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g3 := bu1oOne ((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3]) ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: ((fld wE e) ++ 1 :: ((List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) ++ 1 :: (c.u ++ tailVR vs)))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g4 := bz0Skip ((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3]) (List.replicate r 3 ++ List.replicate s 2) ((fld wE e) ++ 1 :: ((List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) bRacc (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g5 := bz1Skip (((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1]) (fld wE e) ((List.replicate c.m 2 ++ 3 :: 3 :: (List.replicate n' 3 ++ List.replicate c.s 2)) ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (fld_bits _ _) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g6 := bz2Skip (((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e) ++ [1]) c.m (3 :: 3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g7 := bz2Hit ((((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e) ++ [1]) ++ List.replicate c.m 2) (3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g8 := bz3One ((((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e) ++ [1]) ++ List.replicate c.m 2) ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g9 := bz4Mark ((((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e) ++ [1]) ++ List.replicate c.m 2) (3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g10 := bz5Sweep (((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e) ++ [1]) c.m (2 :: 3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g11 := bz5M (((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ (fld wE e)) (List.replicate c.m 2 ++ 2 :: 3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
  have g12 := ieStep ((Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) wE e (List.replicate c.m 2 ++ 2 :: 3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega)
    (NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨nX, noB_rep _ _ (by simp)⟩, by simp [NB]⟩, by simp [NB]⟩, bRacc.noB⟩) (by simp [ALL, sW, sP2, sPre, sE, sU, sV] <;> omega) he hew
  have sEi : Sym4 (fld wE (incK wE e)) := (fld_bits _ _).sym4
  have g13 := tsStep Wf hW j q hq (P2 ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2) ++ [1] ++ fld wE (incK wE e) ++ 1 :: (List.replicate c.m 2 ++ 2 :: 3 :: ((List.replicate n' 3 ++ List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs)))) (by simp [ALL, sP2, sPre, sU, sV, sEi] <;> omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 hNext ⊢
  refine (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans (g9.trans (g10.trans (g11.trans (g12.trans ((g13.of_eq rfl ?_).trans hNext))))))))))))).of_eq ?_ ?_
  · simp [VR.b, VR.u, List.replicate_succ, rep_app_cons, List.append_assoc]
  · simp [VR.b, VR.u, List.replicate_succ, rep_app_cons, List.append_assoc]
  · simp [VR.b, VR.u, List.replicate_succ, rep_app_cons, List.append_assoc]

/-! ### Output cursor: all `b`-steps, the last step, and one whole unit -/

/-- `S := S + 1` on the thermometer `0^j 1^q` (pair `(j, q)`). -/
def sNext (p : Nat × Nat) : Nat × Nat := if p.2 ≤ 1 then (0, p.1 + 1) else (p.1 + 1, p.2 - 1)

def sAdv : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p => sAdv n (sNext p)

def eAdv (wE : Nat) : Nat → Nat → Nat
  | 0, e => e
  | n + 1, e => eAdv wE n (incK wE e)

theorem sInc_eq (j q : Nat) :
    sInc j q = List.replicate (sNext (j, q)).1 2 ++ List.replicate (sNext (j, q)).2 3 := by
  unfold sInc sNext
  by_cases h : q ≤ 1 <;> simp [h]

theorem sNext_pos (p : Nat × Nat) (h : 1 ≤ p.2) : 1 ≤ (sNext p).2 := by
  unfold sNext; split <;> simp <;> omega

theorem sAdv_pos : ∀ (n : Nat) (p : Nat × Nat), 1 ≤ p.2 → 1 ≤ (sAdv n p).2
  | 0, p, h => h
  | n + 1, p, h => sAdv_pos n _ (sNext_pos p h)

theorem eAdv_bounds (wE : Nat) : ∀ (n e : Nat), 1 ≤ e → e ≤ wE → 1 ≤ eAdv wE n e ∧ eAdv wE n e ≤ wE
  | 0, e, h1, h2 => ⟨h1, h2⟩
  | n + 1, e, h1, h2 => eAdv_bounds wE n _ (incK_bounds wE e h1 h2).1 (incK_bounds wE e h1 h2).2

theorem vrE_ok (c : VR) (hc : c.Ok) (E' : List Nat) (hE' : BitsD E') (hlen : 2 ≤ E'.length) (m n : Nat) :
    ({ c with m := m, n := n, E := E' } : VR).Ok :=
  { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := hE', Elen := hlen }

theorem oLoop (n : Nat) : ∀ (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (Wf : List Nat) (hW : BitsD Wf)
    (j q : Nat) (hq : 1 ≤ q) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok)
    (wE e : Nat) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e) (hn : c.n = n),
    znttLogic.Reach
      (hdR QNTT.BU0o (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hdR QNTT.BU0o (Wf ++ 1 :: (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3 ++ 1 :: P2) ++
          tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 ::
          (fld wE (eAdv wE n e) ++ 1 :: (({ c with m := c.m + n, n := 0 } : VR).b ++ 1 :: (c.u ++ tailVR vs)))))
  := by
  induction n with
  | zero =>
    intro c hc hF hO Wf hW j q hq P2 hP2 pre hpre a r s vs hvs wE e he hew hE hn
    refine (LTM.Reach.refl znttLogic _).of_eq rfl ?_
    simp [sAdv, eAdv, hE, VR.b, hn]
  | succ n ih =>
    intro c hc hF hO Wf hW j q hq P2 hP2 pre hpre a r s vs hvs wE e he hew hE hn
    have h1 := oStep c hc hF hO Wf hW j q hq P2 hP2 pre hpre a r s vs hvs wE e he hew hE n hn
    have hElen := hc.Elen
    rw [hE, fld_len _ _ hew] at hElen
    have hb := incK_bounds wE e he hew
    have hc1 := vrE_ok c hc (fld wE (incK wE e)) (fld_bits _ _) (by rw [fld_len _ _ hb.2]; exact hElen) (c.m + 1) n
    have h2 := ih { c with m := c.m + 1, n := n, E := fld wE (incK wE e) } hc1 hF hO Wf hW (sNext (j, q)).1 (sNext (j, q)).2
      (sNext_pos (j, q) hq) P2 hP2 pre hpre a r s vs hvs wE (incK wE e) hb.1 hb.2 rfl rfl
    rw [← sInc_eq] at h2
    refine (h1.trans h2).of_eq rfl ?_
    have e1 : c.m + 1 + n = c.m + (n + 1) := by omega
    simp [sAdv, eAdv, e1, VR.b, VR.u]

theorem bz3Any (A : List Nat) (s : Nat) (T : List Nat) (hA : Sym4 A) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.BZ3 (A ++ [3]) (List.replicate s 2 ++ 1 :: T))
      (hd QNTT.BZR (A ++ [3]) (List.replicate s 2 ++ 1 :: T)) := by
  cases s with
  | zero => simpa using bz3M A T hA hT
  | succ k =>
    simpa [List.replicate_succ] using
      bz3Zero A (List.replicate k 2 ++ 1 :: T) hA ((BitsD.rep k 2 (by simp)).sym4.app (sym4_M hT))

/-- The last `b`-unit of the output cursor: `b` is restored, the accumulator unit is marked, on to `BS0`. -/
theorem oLast (c : VR) (hc : c.Ok) (hn : c.n = 0) (X' : List Nat) (hX : Sym4 X') (a r s : Nat) (vs : List VR)
    (hvs : ∀ w ∈ vs, w.Ok) :
    znttLogic.Reach
      (hdR QNTT.BU0o ((X' ++ [1]) ) (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hdR QNTT.BS0 ((X' ++ [1]) ++ List.replicate a 2 ++ [2]) (List.replicate (r + 1) 3 ++ List.replicate s 2 ++
        1 :: (c.E ++ 1 :: (({ c with m := 0, n := c.m } : VR).b ++ 1 :: (c.u ++ tailVR vs))))) := by
  have hb : c.b = (List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) := by simp [VR.b, hn]
  have sX : Sym4 (X' ++ [1]) := hX.app (sym4_cell 1 (by simp))
  have sE := hc.E.sym4
  have sU := hc.u.sym4
  have sV := tailVR_sym4 vs hvs
  have bd3 : BitsD [3] := BitsD.rep 1 3 (by simp)
  have bRacc : BitsD (List.replicate r 3 ++ List.replicate s 2) := bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))
  have g1 := bu0oSkip (X' ++ [1]) a (3 :: 3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: (c.E ++ 1 :: ((List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g2 := bu0oHit ((X' ++ [1]) ++ List.replicate a 2) (3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: (c.E ++ 1 :: ((List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g3 := bu1oOne ((X' ++ [1]) ++ List.replicate a 2 ++ [3]) ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: (c.E ++ 1 :: ((List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs)))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g4 := bz0Skip ((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3]) (List.replicate r 3 ++ List.replicate s 2) (c.E ++ 1 :: ((List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) bRacc (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g5 := bz1Skip (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1]) c.E ((List.replicate c.m 2 ++ 3 :: List.replicate c.s 2) ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sX, sE, sU, sV] <;> omega) hc.E (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g6 := bz2Skip (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E ++ [1]) c.m (3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g7 := bz2Hit ((((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E ++ [1]) ++ List.replicate c.m 2) (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g8 := bz3Any ((((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E ++ [1]) ++ List.replicate c.m 2) c.s (c.u ++ tailVR vs) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g9 := bzrSweep (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E ++ [1]) (List.replicate c.m 2 ++ [3]) (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sX, sE, sU, sV] <;> omega) (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g10 := bzrM (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E) ((List.replicate c.m 2 ++ [3]) ++ (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g11 := bzr2Skip (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E ++ [1]) c.m (3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g12 := bzr2One (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E) c.m (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs)) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g13 := bzr3Sweep (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1] ++ c.E) c.m (3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g14 := bzr4Sweep (((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) ++ [1]) c.E (1 :: List.replicate c.m 3 ++ 3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) hc.E (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g15 := bzr4M ((X' ++ [1]) ++ List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) (c.E ++ 1 :: List.replicate c.m 3 ++ 3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g16 := bzr5Sweep X' (List.replicate a 2 ++ [3] ++ [3] ++ (List.replicate r 3 ++ List.replicate s 2)) (1 :: (c.E ++ 1 :: (List.replicate c.m 3 ++ 3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs))))) hX
    (bd_app (bd_app (bd_app (BitsD.rep _ _ (by simp)) bd3) bd3) bRacc) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g17 := bzr6Skip ((X' ++ [1])) a (3 :: 3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: (c.E ++ 1 :: (List.replicate c.m 3 ++ 3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs)))))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  have g18 := bzr6Mark ((X' ++ [1]) ++ List.replicate a 2) (3 :: ((List.replicate r 3 ++ List.replicate s 2) ++ 1 :: (c.E ++ 1 :: (List.replicate c.m 3 ++ 3 :: (List.replicate c.s 2 ++ 1 :: (c.u ++ tailVR vs)))))) (by simp [ALL, sX, sE, sU, sV] <;> omega) (by simp [ALL, sX, sE, sU, sV] <;> omega)
  rw [hb]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 ⊢
  refine (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans (g9.trans (g10.trans (g11.trans (g12.trans (g13.trans (g14.trans (g15.trans (g16.trans (g17.trans (g18)))))))))))))))))).of_eq ?_ ?_
  · rfl
  · simp [VR.b, hn, List.replicate_succ, rep_app_cons, List.append_assoc]

/-- The whole mark phase of an output unit: all `b`-steps, then the last one. -/
theorem oMark (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (Wf : List Nat) (hW : BitsD Wf)
    (j q : Nat) (hq : 1 ≤ q) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok)
    (wE e : Nat) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e) (hn : c.n = n) :
    znttLogic.Reach
      (hdR QNTT.BU0o (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hdR QNTT.BS0 (Wf ++ 1 :: (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3 ++ 1 :: P2) ++
          tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ [2])
        (List.replicate (r + 1) 3 ++ List.replicate s 2 ++ 1 :: (fld wE (eAdv wE n e) ++ 1 ::
          (({ c with m := 0, n := c.m + n } : VR).b ++ 1 :: (c.u ++ tailVR vs))))) := by
  have h1 := oLoop n c hc hF hO Wf hW j q hq P2 hP2 pre hpre a r s vs hvs wE e he hew hE hn
  have hb := eAdv_bounds wE n e he hew
  have hElen := hc.Elen
  rw [hE, fld_len _ _ hew] at hElen
  have hc2 := vrE_ok c hc (fld wE (eAdv wE n e)) (fld_bits _ _) (by rw [fld_len _ _ hb.2]; exact hElen) (c.m + n) 0
  have h2 := oLast { c with m := c.m + n, n := 0, E := fld wE (eAdv wE n e) } hc2 rfl
    (Wf ++ 1 :: (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3 ++ 1 :: P2) ++ tailB pre ++
      [1, 1, 3, 3, c.P]) (by
        have hp : c.P = 2 ∨ c.P = 3 := by have := hc.P; simpa using this
        have hG := goodW_reg Wf (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3) P2 hW
          (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
          (by have := sAdv_pos n (j, q) hq; obtain ⟨q', hq'⟩ : ∃ q', (sAdv n (j, q)).2 = q' + 1 := ⟨(sAdv n (j, q)).2 - 1, by omega⟩
              simp [hq', List.replicate_succ]) hP2
        have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
        have sP2 : Sym4 P2 := by have := hP2.sym4; simp at this; exact this.2
        simp [ALL, hW.sym4, sP2, sPre] <;> omega) a r s vs hvs
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  refine (h1.trans h2).of_eq ?_ ?_
  · rfl
  · simp [VR.b, VR.u]

/-- One unit of the output cursor record (`b` of `n + 1` ones): `E += n`, `S += n`, mark one accumulator unit,
broadcast, back to `RFL`. -/
theorem outUnit (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (Wf : List Nat) (hW : BitsD Wf)
    (j q : Nat) (hq : 1 ≤ q) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok)
    (wE e : Nat) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e) (hn : c.n = n) :
    znttLogic.Reach
      (hdR QNTT.BU0o (Wf ++ 1 :: (List.replicate j 2 ++ List.replicate q 3 ++ 1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1])
        (List.replicate a 2 ++ List.replicate (r + 2) 3 ++ List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      (hd QNTT.RFL (Wf ++ 1 :: (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3 ++ 1 :: P2) ++
          tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate (a + 1) 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
          1 :: (fld wE (eAdv wE n e) ++ 1 :: (({ c with m := 0, n := c.m + n } : VR).b ++ 1 ::
            (c.u ++ tailVR (stepList vs))))) []) := by
  have h1 := oMark n c hc hF hO Wf hW j q hq P2 hP2 pre hpre a r s vs hvs wE e he hew hE hn
  have hb := eAdv_bounds wE n e he hew
  have hElen := hc.Elen
  rw [hE, fld_len _ _ hew] at hElen
  have hc3 := vrE_ok c hc (fld wE (eAdv wE n e)) (fld_bits _ _) (by rw [fld_len _ _ hb.2]; exact hElen) 0 (c.m + n)
  have hP23 : c.P = 2 ∨ c.P = 3 := by have := hc.P; simpa using this
  have hG := goodW_reg Wf (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
    (by have := sAdv_pos n (j, q) hq; obtain ⟨q', hq'⟩ : ∃ q', (sAdv n (j, q)).2 = q' + 1 := ⟨(sAdv n (j, q)).2 - 1, by omega⟩
        simp [hq', List.replicate_succ]) hP2
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have sP2 : Sym4 P2 := by have := hP2.sym4; simp at this; exact this.2
  have h2 := cursorTail { c with m := 0, n := c.m + n, E := fld wE (eAdv wE n e) } hc3 vs hvs
    (Wf ++ 1 :: (List.replicate (sAdv n (j, q)).1 2 ++ List.replicate (sAdv n (j, q)).2 3 ++ 1 :: P2) ++
      tailB pre ++ [1, 1, 3, 3, c.P, 1]) a r s (by simp [ALL, hW.sym4, sP2, sPre] <;> omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact (h1.trans h2).of_eq rfl (by simp [VR.b, VR.u])

/-! ### Output cursor: the loop over all accumulator units -/

theorem sAdv_add : ∀ (m n : Nat) (p : Nat × Nat), sAdv (m + n) p = sAdv n (sAdv m p)
  | 0, n, p => by simp [sAdv]
  | m + 1, n, p => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [sAdv]; exact sAdv_add m n _

theorem eAdv_add (wE : Nat) : ∀ (m n e : Nat), eAdv wE (m + n) e = eAdv wE n (eAdv wE m e)
  | 0, n, e => by simp [eAdv]
  | m + 1, n, e => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [eAdv]; exact eAdv_add wE m n _

theorem outTape_noB (c : VR) (hc : c.Ok) (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) :
    NoB (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++
        List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))) := by
  have hPc : c.P ∈ NB := by have := hc.P; simp at this; simp [NB]; omega
  simp only [NoB_app_iff, NoB_cons_iff, List.cons_append, List.nil_append]
  exact ⟨⟨⟨⟨⟨⟨hP.noB, tailB_noB pre (fun x hx => (hpre x hx).1)⟩, by simp [NB], by simp [NB], by simp [NB],
    by simp [NB], hPc, by simp [NB]⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩,
    by simp [NB], hc.E.noB, by simp [NB], hc.b.noB, by simp [NB], hc.u.noB, tailVR_noB vs hvs⟩


theorem outLoop (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (hm : c.m = 0) (hn : c.n = n)
    (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s wE : Nat) (hwE : 2 ≤ wE) :
    ∀ (r a : Nat) (p : Nat × Nat) (e : Nat) (vs : List VR), (∀ w ∈ vs, w.Ok) → 1 ≤ p.2 → 1 ≤ e → e ≤ wE →
    znttLogic.Reach
      (hd QNTT.RFL (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2) ++ tailB pre ++
        [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
        1 :: (fld wE e ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))) [])
      (hd QNTT.RFL (Wf ++ 1 :: (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3 ++
        1 :: P2) ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate (a + r) 2 ++ List.replicate 1 3 ++
        List.replicate s 2 ++ 1 :: (fld wE (eAdv wE (r * n) e) ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (stepN r vs))))) [])
  | 0, a, p, e, vs, hvs, hq, he, hew => by
    simpa [sAdv, eAdv, stepN] using LTM.Reach.refl znttLogic _
  | r + 1, a, p, e, vs, hvs, hq, he, hew => by
    have hElen := hc.Elen
    have hc' : ({ c with E := fld wE e } : VR).Ok :=
      { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld wE e).length; rw [fld_len _ _ hew]; exact hwE }
    have hG := goodW_reg Wf (List.replicate p.1 2 ++ List.replicate p.2 3) P2 hW
      (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
      (by obtain ⟨q', hq'⟩ : ∃ q', p.2 = q' + 1 := ⟨p.2 - 1, by omega⟩; simp [hq', List.replicate_succ]) hP2
    have h0 := rflScan (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2) ++ tailB pre ++
        [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1 + 1) 3 ++ List.replicate s 2 ++
        1 :: (fld wE e ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))) []
      (outTape_noB { c with E := fld wE e } hc' _ hG pre hpre a (r + 1) s vs hvs) Sym4.nil
    have h1 := rfO { c with E := fld wE e } hc' hF hO _ hG pre hpre a (r + 1) s vs hvs
    have h2 := outUnit n { c with E := fld wE e } hc' hF hO Wf hW p.1 p.2 hq P2 hP2 pre hpre a r s vs hvs wE e he hew rfl hn
    have hb := eAdv_bounds wE n e he hew
    have hq' := sAdv_pos n p hq
    have hIH := outLoop n c hc hF hO hm hn Wf hW P2 hP2 pre hpre s wE hwE r (a + 1)
      (sAdv n p) (eAdv wE n e) (stepList vs) (stepList_ok vs hvs) hq' hb.1 hb.2
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, VR.b, VR.u, hm, hn, Nat.zero_add] at h0 h1 h2 hIH ⊢
    have e1 : (r + 1) * n = n + r * n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have e2 : a + 1 + r = a + (r + 1) := by omega
    have e3 : ∀ x : List Nat, ({ c with E := x, m := 0, n := c.m + n } : VR).b = c.b := by
      intro x; simp [VR.b, hm, hn]
    refine (h0.trans (h1.trans (h2.trans hIH))).of_eq rfl ?_
    rw [e1, sAdv_add, eAdv_add, e2]
    simp [stepN]


/-- The next cursor record: decremented, `F := 3`, and for an output node `E` reset to `1`. -/
def VR.curG (w : VR) : VR :=
  if w.O = 3 then { w.cur with E := fld w.E.length 1 } else w.cur

theorem VR.curG_nonout (w : VR) (h : w.O = 2) : w.curG = w.cur := by
  simp [VR.curG, h]

theorem curG_tl (w : VR) (hO : w.O = 3) (z n : Nat) (hn : w.k = n + 1) (hlen : w.E.length = w.k + z)
    (_hE : w.E = fld (w.k + z) w.k) :
    (VR.curG w).tl = ({ w with E := 3 :: List.replicate (z + n) 2 } : VR).dec.tl := by
  have h1 : fld w.E.length 1 = 3 :: List.replicate (z + n) 2 := by
    rw [hlen]; simp [fld, hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  unfold VR.curG VR.cur VR.dec
  rw [if_pos hO]
  by_cases hc : w.c = 0 <;> simp [hc, VR.tl, VR.b, VR.u, h1]

/-- `FA0` on the next record (either kind). -/
theorem fa0G (A : List Nat) (w : VR) (hw : w.Ok) (ws : List VR) (hws : ∀ x ∈ ws, x.Ok) (hA : Sym4 A)
    (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)))
      (hd QNTT.RFL (A ++ [3, w.O, w.P] ++ 1 :: (w.curG.tl ++ tailVR (ws.map VR.dec))) []) := by
  have hwd : w.toRc.DE := ⟨w.toRcA_ok hw _ (fld_bits _ _), w.toRcA_rest _⟩
  have hws' : ∀ x ∈ ws.map VR.toRc, x.DE := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v.toRcA_ok (hws v hv) _ (fld_bits _ _), v.toRcA_rest _⟩
  have hOw := hw.O
  simp at hOw
  rcases hOw with hO | hO
  · have b6 := fa0N A w.toRc hwd (by simpa [VR.toRc, VR.toRcA] using hO) (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, VR.dec_toRc_tl w hw, tailD_toRc ws hws] at b6
    simp only [VR.toRc, VR.toRcA] at b6
    refine b6.of_eq rfl ?_
    simp [VR.curG, hO, VR.cur, VR.tl, VR.b, VR.u]
  · obtain ⟨z, hk1, hE⟩ := hcmp hO
    obtain ⟨n, hn⟩ : ∃ n, w.k = n + 1 := ⟨w.k - 1, by omega⟩
    have b6 := fa0O A w.toRc hwd (by simpa [VR.toRc, VR.toRcA] using hO) n (w.w - w.k) z
      (by simp [VR.toRc, VR.toRcA, fld, hn]) (by simp [VR.toRc, VR.toRcA, hE, fld, hn]) (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, tailD_toRc ws hws] at b6
    have hlen : w.E.length = w.k + z := by rw [hE]; simp [fld]
    have hw' : ({ w with E := 3 :: List.replicate (z + n) 2 } : VR).Ok :=
      { hw with
        E := by exact BitsD.cons (by simp) (BitsD.rep _ _ (by simp))
        Elen := by simp; have := hw.Elen; omega }
    have e1 := VR.dec_toRc_tl _ hw'
    have e2 : ({ w with E := 3 :: List.replicate (z + n) 2 } : VR).toRc =
      { F := w.toRc.F, O := w.toRc.O, Pf := w.toRc.Pf, acc := w.toRc.acc, E := 3 :: List.replicate (z + n) 2,
        b0 := w.toRc.b0, br := w.toRc.br, u0 := w.toRc.u0, ur := w.toRc.ur } := rfl
    rw [e2] at e1
    rw [e1] at b6
    refine b6.of_eq rfl ?_
    rw [curG_tl w hO z n hn hlen hE]
    simp [VR.toRc, VR.toRcA]


theorem bu1oZero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1o (A ++ [3]) (2 :: R)) (hd QNTT.CA0 (A ++ [3]) (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu1oM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BU1o (A ++ [3]) (1 :: R)) (hd QNTT.CA0 (A ++ [3]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bu1oAny (A : List Nat) (s : Nat) (T : List Nat) (hA : Sym4 A) (hT : Sym4 T) :
    znttLogic.Reach (hdR QNTT.BU1o (A ++ [3]) (List.replicate s 2 ++ 1 :: T))
      (hd QNTT.CA0 (A ++ [3]) (List.replicate s 2 ++ 1 :: T)) := by
  cases s with
  | zero => simpa using bu1oM A T hA hT
  | succ s =>
    have := bu1oZero A (List.replicate s 2 ++ 1 :: T) hA ((BitsD.rep s 2 (by simp)).sym4.app (sym4_M hT))
    simpa [List.replicate_succ, VR.toRcA] using this

def curTapeG (Pm : List Nat) (pre : List Rc) (c : VR) (a r s : Nat) (vs : List VR) : List Nat :=
  Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P, 1] ++ List.replicate a 2 ++ List.replicate (r + 1) 3 ++ List.replicate s 2 ++
    1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))

theorem curTapeG_eq (Pm : List Nat) (pre : List Rc) (c : VR) (hO : c.O = 2) (a r s : Nat) (vs : List VR) :
    curTapeG Pm pre c a r s vs = curTape Pm pre c a r s vs := by
  simp [curTapeG, curTape, hO]

theorem curTapeG_noB (c : VR) (hc : c.Ok) (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a r s : Nat) (vs : List VR) (hvs : ∀ w ∈ vs, w.Ok) :
    NoB (curTapeG Pm pre c a r s vs) := by
  have hPc : c.P ∈ NB := by have := hc.P; simp at this; simp [NB]; omega
  have hOc : c.O ∈ NB := by have := hc.O; simp at this; simp [NB]; omega
  simp only [curTapeG, NoB_app_iff, NoB_cons_iff, List.cons_append, List.nil_append]
  exact ⟨⟨⟨⟨⟨⟨hP.noB, tailB_noB pre (fun x hx => (hpre x hx).1)⟩, by simp [NB], by simp [NB], by simp [NB],
    hOc, hPc, by simp [NB]⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩, noB_rep _ _ (by simp)⟩,
    by simp [NB], hc.E.noB, by simp [NB], hc.b.noB, by simp [NB], hc.u.noB, tailVR_noB vs hvs⟩

theorem curToCA0 (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2 ∨ c.O = 3) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a s : Nat) (vs : List VR)
    (hvs : ∀ x ∈ vs, x.Ok) :
    znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s vs) [])
      (hd QNTT.CA0 (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P, 1] ++ List.replicate a 2 ++ [3])
        (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))))) := by
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hacc : BitsD (List.replicate a 2 ++ List.replicate (0 + 1) 3 ++ List.replicate s 2) :=
    bd_app (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) (BitsD.rep _ _ (by simp))
  have hcur : (c.toRcA (List.replicate a 2 ++ List.replicate (0 + 1) 3 ++ List.replicate s 2)).Ok :=
    c.toRcA_ok hc _ hacc
  have hvs' : ∀ x ∈ vs.map VR.toRc, x.Ok := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact v.toRcA_ok (hvs v hv) _ (fld_bits _ _)
  have hLe : curTapeG Pm pre c a 0 s vs = Pm ++ tailB (pre ++ (c.toRcA (List.replicate a 2 ++
      List.replicate (0 + 1) 3 ++ List.replicate s 2)) :: vs.map VR.toRc) := by
    rw [tailB_append]
    simp only [tailB]
    rw [tailB_toRc vs hvs]
    simp [curTapeG, VR.toRcA_body c hc, hF, List.append_assoc]
  have hA := rfFind (curTapeG Pm pre c a 0 s vs) Pm (curTapeG_noB c hc Pm hP pre hpre a 0 s vs hvs) hP pre hpre _ hcur hF
    (vs.map VR.toRc) hvs' hLe
  rw [VR.toRcA_tl c hc, tailB_toRc vs hvs] at hA
  have hX : Sym4 (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P, 1]) :=
    (sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P (sym4_M Sym4.nil))))))
  have sU := hc.u.sym4
  have sB := hc.b.sym4
  have sE := hc.E.sym4
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))) :=
    sE.app (sym4_M (sB.app (sym4_M (sU.app (tailVR_sym4 vs hvs)))))
  have sT' : Sym4 (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))) :=
    (s2 s).app (sym4_M sT)
  have sTail := tailVR_sym4 vs hvs
  rcases hO with hO | hO
  · have hX2 : Sym4 (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) := by
      have := hX; rwa [hO] at this
    have hA' : znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s vs) [])
        (hdR QNTT.BU0n (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) (List.replicate a 2 ++ 3 :: (List.replicate s 2 ++
          1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))) := by
      have := hA.1 hO
      simpa [List.replicate_succ, VR.toRcA] using this
    have b1 := bu0Skip (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1]) a
      (3 :: (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      hX2 (sym4_B (by simp) sT')
    have b2 := bu0Hit (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1] ++ List.replicate a 2)
      (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))))
      (hX2.app (s2 a)) sT'
    have b3 := bu1Any (Pm ++ tailB pre ++ [1, 1, 3, 2, c.P, 1] ++ List.replicate a 2) s
      (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))) (hX2.app (s2 a)) sT
    rw [hO]
    simpa using hA'.trans (b1.trans (b2.trans b3))
  · have hX2 : Sym4 (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) := by
      have := hX; rwa [hO] at this
    have hA' : znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s vs) [])
        (hdR QNTT.BU0o (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) (List.replicate a 2 ++ 3 :: (List.replicate s 2 ++
          1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))) := by
      have := hA.2 hO
      simpa [List.replicate_succ, VR.toRcA] using this
    have b1 := bu0oSkip (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1]) a
      (3 :: (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs)))))
      hX2 (sym4_B (by simp) sT')
    have b2 := bu0oHit (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2)
      (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))))
      (hX2.app (s2 a)) sT'
    have b3 := bu1oAny (Pm ++ tailB pre ++ [1, 1, 3, 3, c.P, 1] ++ List.replicate a 2) s
      (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR vs))) (hX2.app (s2 a)) sT
    rw [hO]
    simpa using hA'.trans (b1.trans (b2.trans b3))

theorem colAdvanceG (c w : VR) (ws : List VR) (hc : c.Ok) (hw : w.Ok) (hws : ∀ x ∈ ws, x.Ok) (hF : c.F = 3)
    (hO : c.O = 2 ∨ c.O = 3) (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a s : Nat) :
    znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s (w :: ws)) [])
      (hd QNTT.RFL (curTapeG Pm (pre ++ [c.done a s]) w.curG 0 (w.k - 1) (w.w - w.k) (ws.map VR.dec)) []) := by
  have hvs : ∀ x ∈ w :: ws, x.Ok := fun x hx => by
    simp at hx; rcases hx with rfl | hx
    · exact hw
    · exact hws x hx
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hA := curToCA0 c hc hF hO Pm hP pre hpre a s (w :: ws) hvs
  have sU := hc.u.sym4
  have sB := hc.b.sym4
  have sE := hc.E.sym4
  have sW : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))) := by
    refine sE.app (sym4_M (sB.app (sym4_M (sU.app ?_))))
    exact tailVR_sym4 (w :: ws) hvs
  have b4 := ca0Sweep (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P]) (List.replicate a 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))
    ((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P Sym4.nil))))))
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) ((s2 s).app (sym4_M sT))
  have b5 := caNext c hc (Pm ++ tailB pre) (List.replicate a 2 ++ 3 :: List.replicate s 2)
    ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) (sPm.app sPre)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
    (by cases a <;> simp [List.replicate_succ]) sW
  have b6 := fa0G (Pm ++ tailB pre ++ [1, 1, 2, c.O, c.P, 1] ++ (List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) w hw ws hws
    (((((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P (sym4_M Sym4.nil))))))).app
      (BitsD.sym4 (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)))).app
      (sym4_M (sE.app (sym4_M (sB.app (sym4_M (sU.app (sym4_M (sym4_M Sym4.nil))))))))))
    hcmp
  have hdone : (c.done a s).body = [2, c.O, c.P] ++ 1 :: ((List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) := by
    have e : (c.done a s).tl = (c.toRcA (List.replicate a 2 ++ 3 :: List.replicate s 2)).tl := rfl
    rw [Rc.body_eq, e, VR.toRcA_tl c hc]
    rfl
  simp only [tailB_append, tailB, hdone, List.append_nil, curTapeG, List.append_assoc, List.cons_append,
    List.nil_append, List.replicate_succ] at hA b4 b5 b6 ⊢
  refine hA.trans (b4.trans (b5.trans (b6.of_eq rfl ?_)))
  have hk : w.curG.O = w.O ∧ w.curG.P = w.P ∧ w.curG.w = w.w ∧ w.curG.k = w.k := by
    by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, VR.dec, h] <;> split <;> simp_all
  obtain ⟨k', hk'⟩ : ∃ k', w.k = k' + 1 := ⟨w.k - 1, by have := hw.k1; omega⟩
  simp [VR.tl, fld, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2, hk', List.replicate_succ]


/-- A full column step for a non-output cursor record: broadcast all `r + 1` units, then advance. -/
theorem colStepN (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r s : Nat) (vs : List VR)
    (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) :
    znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c 0 r s vs) [])
      (hd QNTT.RFL (curTapeG Pm (pre ++ [c.done r s]) w.curG 0 (w.k - 1) (w.w - w.k) (ws.map VR.dec)) []) := by
  have h1 := cursorLoop c hc hF hO Pm hP pre hpre s r 0 vs hvs
  rw [hw, Nat.zero_add] at h1
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  have h2 := colAdvanceG c w ws hc (hok w (by simp)) (fun x hx => hok x (by simp [hx])) hF (Or.inl hO) hcmp Pm hP pre
    hpre r s
  rw [curTapeG_eq _ _ _ hO]
  rw [curTapeG_eq _ _ _ hO] at h2
  exact h1.trans h2

/-- A full column step for an output cursor record (`c.E = fld wE e`): broadcast all units (advancing `E` and the `S`
register in `Pm`), then advance. -/
theorem colStepO (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (hm : c.m = 0) (hn : c.n = n)
    (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s wE : Nat) (hwE : 2 ≤ wE)
    (r : Nat) (p : Nat × Nat) (e : Nat) (hp : 1 ≤ p.2) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e)
    (vs : List VR) (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) :
    znttLogic.Reach
      (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
      (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3 ++ 1 :: P2))
        (pre ++ [({ c with E := fld wE (eAdv wE (r * n) e) } : VR).done r s]) w.curG 0 (w.k - 1) (w.w - w.k)
        (ws.map VR.dec)) []) := by
  have h1 := outLoop n c hc hF hO hm hn Wf hW P2 hP2 pre hpre s wE hwE r 0 p e vs hvs hp he hew
  have hb := eAdv_bounds wE (r * n) e he hew
  have hElen := hc.Elen
  rw [hE, fld_len _ _ hew] at hElen
  have hc' : ({ c with E := fld wE (eAdv wE (r * n) e) } : VR).Ok :=
    { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
      Elen := by show 2 ≤ (fld wE (eAdv wE (r * n) e)).length; rw [fld_len _ _ hb.2]; exact hElen }
  have hG := goodW_reg Wf (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
    (by have := sAdv_pos (r * n) p hp; obtain ⟨q', hq'⟩ : ∃ q', (sAdv (r * n) p).2 = q' + 1 := ⟨(sAdv (r * n) p).2 - 1, by omega⟩
        simp [hq', List.replicate_succ]) hP2
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  have h2 := colAdvanceG ({ c with E := fld wE (eAdv wE (r * n) e) } : VR) w ws hc' (hok w (by simp))
    (fun x hx => hok x (by simp [hx])) hF (Or.inr hO) hcmp _ hG pre hpre r s
  rw [hw, Nat.zero_add] at h1
  refine (LTM.Reach.of_eq h1 ?_ ?_).trans h2
  · simp [curTapeG, hE, hO, List.append_assoc]
  · simp [curTapeG, hO, VR.b, VR.u, List.append_assoc]


/-! ### Pass end (`PE*`) -/

theorem pe0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE0 L R) (hdR QNTT.PE1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe1Bit (A : List Nat) (b : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) (hb : b ∈ [2, 3]) :
    znttLogic.Reach (hdR QNTT.PE1 A (b :: R)) (hdR QNTT.PE1 (A ++ [b]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PE1 A (1 :: R)) (hdR QNTT.PE2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe2Bit (A : List Nat) (b : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) (hb : b ∈ [2, 3]) :
    znttLogic.Reach (hdR QNTT.PE2 A (b :: R)) (hdR QNTT.PE1 (A ++ [b]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe2M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PE2 (A ++ [1]) (1 :: R)) (hd QNTT.PE3 (A ++ [1]) (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe3M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE3 (A ++ [1]) (1 :: R)) (hd QNTT.PE4 A (1 :: 1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe4Zeros (A R : List Nat) (b : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE4 (A ++ List.replicate b 2) R) (hd QNTT.PE4 A (List.replicate b 2 ++ R)) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate b 2, R] :=
    Valid.cons hA (Valid.cons (repSet b 2) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, List.replicate b 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe4One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE4 (A ++ [3]) R) (hd QNTT.PE5 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe5More (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE5 (A ++ [3]) R) (hd QNTT.SC A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe5Last (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PE5 (A ++ [1]) R) (hd QNTT.FL0 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pe1Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.PE1 A (u ++ rest)) (hdR QNTT.PE1 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := pe1Bit A b (u ++ rest) hA (hu'.sym4.app hr) hb
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have s1 : Sym4 [1] := sym4_cell 1 (by simp)
    have h1 := pe1M A (b :: u ++ rest) hA ((Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) hu'.sym4).app hr)
    have h1' := pe2Bit (A ++ [1]) b (u ++ rest) (hA.app s1) (hu'.sym4.app hr) hb
    have h2 := ih (A ++ [1, b]) rest (hA.app sb) hr
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
    exact h1.trans (h1'.trans h2)

/-- Pass end, more passes to come: scan to `Nn`, unmark its last `1`; the head is left in `SC`. -/
theorem peMore (Pm0 : List Nat) (a b : Nat) (rest : List Nat) (hP : GoodW (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2))
    (hrest : NoB rest) :
    znttLogic.Reach (hd QNTT.PE0 (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2 ++ 1 :: 1 :: rest) [])
      (hd QNTT.SC (Pm0 ++ List.replicate a 3) (3 :: 2 :: (List.replicate b 2 ++ 1 :: 1 :: rest))) := by
  have hrs : Sym4 rest := hrest.sym4
  have sP := hP.sym4
  have s1 : Sym4 [1] := sym4_cell 1 (by simp)
  have e : Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2 ++ 1 :: 1 :: rest =
      (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) ++ ([1, 1] ++ rest) := by simp
  have hNB : NoB ((Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) ++ ([1, 1] ++ rest)) := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hP.noB x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · simp at hx; subst hx; simp [NB]
      · exact hrest x hx
  rw [e]
  have h0 := pe0Scan _ [] hNB Sym4.nil
  simp only [List.append_nil] at h0
  have h1 := pe1Good hP [] ([1, 1] ++ rest) Sym4.nil ((sym4_M (sym4_M hrs)))
  have h2 := pe1M (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) (1 :: rest) sP (sym4_M hrs)
  have h3 := pe2M (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) rest sP hrs
  have h4 := pe3M (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) rest sP hrs
  have sX : Sym4 (Pm0 ++ List.replicate a 3) := by
    have : Sym4 (Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := sP
    intro x hx; apply this; simp only [List.mem_append] at hx ⊢; rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · refine Or.inl (Or.inr ?_); exact List.mem_replicate.2 ⟨by omega, (List.mem_replicate.1 hx).2⟩
  have s3 : Sym4 [3] := sym4_cell 3 (by simp)
  have sR : Sym4 (1 :: 1 :: rest) := sym4_M (sym4_M hrs)
  have e2 : Pm0 ++ List.replicate (a + 2) 3 ++ List.replicate b 2 =
      (Pm0 ++ List.replicate a 3 ++ [3] ++ [3]) ++ List.replicate b 2 := by simp [List.replicate_succ', List.append_assoc]
  have h5 := pe4Zeros (Pm0 ++ List.replicate a 3 ++ [3] ++ [3]) (1 :: 1 :: rest) b ((sX.app s3).app s3) sR
  have h6 := pe4One (Pm0 ++ List.replicate a 3 ++ [3]) (List.replicate b 2 ++ 1 :: 1 :: rest) (sX.app s3)
    ((BitsD.rep b 2 (by simp)).sym4.app sR)
  have h7 := pe5More (Pm0 ++ List.replicate a 3) (2 :: (List.replicate b 2 ++ 1 :: 1 :: rest)) sX
    (Sym4.cons (by simp [ALL]) ((BitsD.rep b 2 (by simp)).sym4.app sR))
  rw [← e2] at h5
  simp only [List.nil_append] at h0 h1
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))

/-- Pass end, last pass: `Nn` had a single `1`; the head is left in `FL0` on the last cell of the field before `Nn`. -/
theorem peLast (Pm1 : List Nat) (b : Nat) (rest : List Nat) (hP : GoodW (Pm1 ++ [1] ++ [3] ++ List.replicate b 2))
    (hrest : NoB rest) :
    znttLogic.Reach (hd QNTT.PE0 (Pm1 ++ [1] ++ [3] ++ List.replicate b 2 ++ 1 :: 1 :: rest) [])
      (hd QNTT.FL0 Pm1 (1 :: 2 :: (List.replicate b 2 ++ 1 :: 1 :: rest))) := by
  have hrs : Sym4 rest := hrest.sym4
  have sP := hP.sym4
  have s1 : Sym4 [1] := sym4_cell 1 (by simp)
  have e : Pm1 ++ [1] ++ [3] ++ List.replicate b 2 ++ 1 :: 1 :: rest =
      (Pm1 ++ [1] ++ [3] ++ List.replicate b 2) ++ ([1, 1] ++ rest) := by simp
  have hNB : NoB ((Pm1 ++ [1] ++ [3] ++ List.replicate b 2) ++ ([1, 1] ++ rest)) := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hP.noB x hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · simp at hx; subst hx; simp [NB]
      · exact hrest x hx
  rw [e]
  have h0 := pe0Scan _ [] hNB Sym4.nil
  simp only [List.append_nil] at h0
  have h1 := pe1Good hP [] ([1, 1] ++ rest) Sym4.nil ((sym4_M (sym4_M hrs)))
  have h2 := pe1M (Pm1 ++ [1] ++ [3] ++ List.replicate b 2) (1 :: rest) sP (sym4_M hrs)
  have h3 := pe2M (Pm1 ++ [1] ++ [3] ++ List.replicate b 2) rest sP hrs
  have h4 := pe3M (Pm1 ++ [1] ++ [3] ++ List.replicate b 2) rest sP hrs
  have sX : Sym4 Pm1 := by
    intro x hx; apply sP; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hx))
  have s3 : Sym4 [3] := sym4_cell 3 (by simp)
  have s1 : Sym4 [1] := sym4_cell 1 (by simp)
  have sR : Sym4 (1 :: 1 :: rest) := sym4_M (sym4_M hrs)
  have e2 : Pm1 ++ [1] ++ [3] ++ List.replicate b 2 = (Pm1 ++ [1] ++ [3]) ++ List.replicate b 2 := rfl
  have h5 := pe4Zeros (Pm1 ++ [1] ++ [3]) (1 :: 1 :: rest) b ((sX.app s1).app s3) sR
  have h6 := pe4One (Pm1 ++ [1]) (List.replicate b 2 ++ 1 :: 1 :: rest) (sX.app s1)
    ((BitsD.rep b 2 (by simp)).sym4.app sR)
  have h7 := pe5Last Pm1 (2 :: (List.replicate b 2 ++ 1 :: 1 :: rest)) sX
    (Sym4.cons (by simp [ALL]) ((BitsD.rep b 2 (by simp)).sym4.app sR))
  simp only [List.nil_append] at h0 h1
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))



/-! ### After the pass: `SC*`, `PM*` (move the input flag), `FL*` -/

theorem fl0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.FL0 L R) (hdR QNTT.FL1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fl1Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FL1 A (f ++ R)) (hdR QNTT.FL1 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fl1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FL1 A (1 :: R)) (hdR QNTT.FL2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem fl2Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FL2 A (2 :: R)) (hd QNTT.SU0 A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU0 L R) (hdR QNTT.SU1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc0Scan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SC L R) (hdR QNTT.SC1 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc1Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SC1 A (f ++ R)) (hdR QNTT.SC1 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SC1 A (1 :: R)) (hdR QNTT.SC2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc2One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SC2 A (3 :: R)) (hdR QNTT.SC2 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc2M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SC2 A (1 :: R)) (hdR QNTT.PM0 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem sc2Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SC2 A (2 :: R)) (hd QNTT.ODL A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0 A (f ++ R)) (hdR QNTT.PM0 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0MM1 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0 A (1 :: R)) (hdR QNTT.PM0m (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0mM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0m A (1 :: R)) (hdR QNTT.PM2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0mBit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0m A (2 :: R)) (hdR QNTT.PM0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0mBit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0m A (3 :: R)) (hdR QNTT.PM0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm2Bit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM2 A (2 :: R)) (hdR QNTT.PM2 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm2Bit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM2 A (3 :: R)) (hdR QNTT.PM2 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm2M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM2 A (1 :: R)) (hd QNTT.PM3 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm4Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM4 A (f ++ R)) (hdR QNTT.PM4 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm4M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM4 A (1 :: R)) (hdR QNTT.PM4m (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm4mM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM4m A (1 :: R)) (hdR QNTT.PM6 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm4mBit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM4m A (2 :: R)) (hdR QNTT.PM4 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm4mBit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM4m A (3 :: R)) (hdR QNTT.PM4 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm6Bit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM6 A (2 :: R)) (hdR QNTT.PM6 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm6Bit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM6 A (3 :: R)) (hdR QNTT.PM6 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm6M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM6 A (1 :: R)) (hd QNTT.PM7 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm3Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PM3 (A ++ [2]) R) (hdR QNTT.PM0 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm3One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.PM3 (A ++ [3]) R) (hdR QNTT.PM4 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm7Set (A : List Nat) (b : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) (hb : b ∈ [2, 3]) :
    znttLogic.Reach (hd QNTT.PM7 (A ++ [b]) R) (hd QNTT.RZ0 A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simp at hb; rcases hb with rfl | rfl
  · exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
  · exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
      (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
      (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm0Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.PM0 A (u ++ rest)) (hdR QNTT.PM0 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := pm0Block A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have s1 : Sym4 [1] := sym4_cell 1 (by simp)
    have hbs : Sym4 (b :: u ++ rest) := (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) hu'.sym4).app hr
    have h1 := pm0MM1 A (b :: u ++ rest) hA hbs
    simp at hb
    rcases hb with rfl | rfl
    · have h1' := pm0mBit2 (A ++ [1]) (u ++ rest) (hA.app s1) (hu'.sym4.app hr)
      have h2 := ih (A ++ [1, 2]) rest (hA.app sb) hr
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
      exact h1.trans (h1'.trans h2)
    · have h1' := pm0mBit3 (A ++ [1]) (u ++ rest) (hA.app s1) (hu'.sym4.app hr)
      have h2 := ih (A ++ [1, 3]) rest (hA.app sb) hr
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
      exact h1.trans (h1'.trans h2)

theorem pm4Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.PM4 A (u ++ rest)) (hdR QNTT.PM4 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := pm4Block A [b] (u ++ rest) hA (by intro x hx; simp at hx; subst hx; exact hb) (hu'.sym4.app hr)
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have s1 : Sym4 [1] := sym4_cell 1 (by simp)
    have hbs : Sym4 (b :: u ++ rest) := (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) hu'.sym4).app hr
    have h1 := pm4M A (b :: u ++ rest) hA hbs
    simp at hb
    rcases hb with rfl | rfl
    · have h1' := pm4mBit2 (A ++ [1]) (u ++ rest) (hA.app s1) (hu'.sym4.app hr)
      have h2 := ih (A ++ [1, 2]) rest (hA.app sb) hr
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
      exact h1.trans (h1'.trans h2)
    · have h1' := pm4mBit3 (A ++ [1]) (u ++ rest) (hA.app s1) (hu'.sym4.app hr)
      have h2 := ih (A ++ [1, 3]) rest (hA.app sb) hr
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
      exact h1.trans (h1'.trans h2)

theorem pm2Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM2 A (f ++ R)) (hdR QNTT.PM2 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem pm6Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM6 A (f ++ R)) (hdR QNTT.PM6 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


theorem sc2Ones (q : Nat) : ∀ (A R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach (hdR QNTT.SC2 A (List.replicate q 3 ++ R)) (hdR QNTT.SC2 (A ++ List.replicate q 3) R) := by
  induction q with
  | zero => intro A R _ _; simpa using LTM.Reach.refl znttLogic _
  | succ q ih =>
    intro A R hA hR
    have s3 : Sym4 [3] := sym4_cell 3 (by simp)
    have h1 := sc2One A (List.replicate q 3 ++ R) hA ((BitsD.rep q 3 (by simp)).sym4.app hR)
    have h2 := ih (A ++ [3]) R (hA.app s3) hR
    simpa [List.replicate_succ, List.append_assoc] using h1.trans h2

theorem hdrBits (r : Rc) (hr : r.Ok) (p : Nat) (hp : p ∈ [2, 3]) : BitsD [r.F, r.O, p] := by
  intro x hx; simp at hx; rcases hx with rfl | rfl | rfl
  · exact hr.F
  · exact hr.O
  · exact hp

theorem Sym4.pre {u v : List Nat} (h : Sym4 (u ++ v)) : Sym4 u := by
  intro x hx; exact h x (List.mem_append.2 (Or.inl hx))

theorem Sym4.suf {u v : List Nat} (h : Sym4 (u ++ v)) : Sym4 v := by
  intro x hx; exact h x (List.mem_append.2 (Or.inr hx))

/-- `PM0` passes a record whose input flag is `0`. -/
theorem pmSkip (A : List Nat) (r : Rc) (hr : r.Ok) (hacc : r.acc ≠ []) (h2 : r.Pf = 2) (R : List Nat)
    (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0 A (1 :: 1 :: (r.body ++ R))) (hdR QNTT.PM0 (A ++ [1, 1] ++ r.body) R) := by
  have hH := hdrBits r hr 2 (by simp)
  have e : r.body = [r.F, r.O, 2] ++ 1 :: r.tl := by rw [Rc.body_eq, h2]
  have sTl : Sym4 r.tl := r.tl_sym4 hr
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have aF : r.F ∈ ALL := by have := hr.F; simp at this; rcases this with h | h <;> simp [h, ALL]
  have aO : r.O ∈ ALL := by have := hr.O; simp at this; rcases this with h | h <;> simp [h, ALL]
  rw [e]
  have b1 := pm0MM1 A (1 :: ([r.F, r.O, 2] ++ 1 :: r.tl ++ R)) hA (by simp [a1, aF, aO, a2, sTl, hR])
  have b2 := pm0mM (A ++ [1]) ([r.F, r.O, 2] ++ 1 :: r.tl ++ R) (by simp [hA, a1]) (by simp [a1, aF, aO, a2, sTl, hR])
  have b3 := pm2Block (A ++ [1] ++ [1]) [r.F, r.O, 2] (1 :: r.tl ++ R) (by simp [hA, a1]) hH (by simp [a1, sTl, hR])
  have b4 := pm2M (A ++ [1] ++ [1] ++ [r.F, r.O, 2]) (r.tl ++ R) (by simp [hA, a1, aF, aO, a2]) (by simp [sTl, hR])
  have b5 := pm3Zero (A ++ [1] ++ [1] ++ [r.F, r.O]) (1 :: (r.tl ++ R)) (by simp [hA, a1, aF, aO]) (by simp [a1, sTl, hR])
  have b6 := pm0Good (Rc.tl_good r hr hacc) (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2]) R (by simp [hA, a1, aF, aO, a2]) hR
  simp only [List.append_assoc, List.cons_append, List.nil_append] at b1 b2 b3 b4 b5 b6 ⊢
  exact b1.trans (b2.trans (b3.trans (b4.trans (b5.trans b6))))


theorem pmPre : ∀ (pre : List Rc), (∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.Pf = 2) → ∀ (A R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach (hdR QNTT.PM0 A (tailB pre ++ R)) (hdR QNTT.PM0 (A ++ tailB pre) R)
  | [], _, A, R, _, _ => by simpa [tailB] using LTM.Reach.refl znttLogic _
  | r :: rs, h, A, R, hA, hR => by
    have hr := h r (by simp)
    have hrs : ∀ x ∈ rs, x.Ok ∧ x.acc ≠ [] ∧ x.Pf = 2 := fun x hx => h x (by simp [hx])
    have sRs : Sym4 (tailB rs ++ R) := (tailB_sym4 rs (fun x hx => (hrs x hx).1)).app hR
    have b1 := pmSkip A r hr.1 hr.2.1 hr.2.2 (tailB rs ++ R) hA sRs
    have s11 : Sym4 [1, 1] := sym4_M (sym4_M Sym4.nil)
    have b2 := pmPre rs hrs (A ++ [1, 1] ++ r.body) R ((hA.app s11).app (r.body_sym4 hr.1)) hR
    simp only [tailB, List.append_assoc, List.cons_append, List.nil_append] at b1 b2 ⊢
    exact b1.trans b2

/-- The active record (input flag `1`) loses the flag; the next record gets it; on to `RZ0` at the next pass. -/
theorem pmAct (A : List Nat) (r r2 : Rc) (hr : r.Ok) (hacc : r.acc ≠ []) (h3 : r.Pf = 3) (hr2 : r2.Ok)
    (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.PM0 A (1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ R))))
      (hd QNTT.RZ0 (A ++ [1, 1, r.F, r.O, 2] ++ 1 :: r.tl ++ [1, 1, r2.F, r2.O]) (3 :: 1 :: (r2.tl ++ R))) := by
  have hH := hdrBits r hr 3 (by simp)
  have hH2 := hdrBits r2 hr2 r2.Pf hr2.Pf
  have e : r.body = [r.F, r.O, 3] ++ 1 :: r.tl := by rw [Rc.body_eq, h3]
  have e2 : r2.body = [r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl := Rc.body_eq r2
  have sTl : Sym4 r.tl := r.tl_sym4 hr
  have sTl2 : Sym4 r2.tl := r2.tl_sym4 hr2
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have aF : r.F ∈ ALL := by have := hr.F; simp at this; rcases this with h | h <;> simp [h, ALL]
  have aO : r.O ∈ ALL := by have := hr.O; simp at this; rcases this with h | h <;> simp [h, ALL]
  have aF2 : r2.F ∈ ALL := by have := hr2.F; simp at this; rcases this with h | h <;> simp [h, ALL]
  have aO2 : r2.O ∈ ALL := by have := hr2.O; simp at this; rcases this with h | h <;> simp [h, ALL]
  have aP2 : r2.Pf ∈ ALL := by have := hr2.Pf; simp at this; rcases this with h | h <;> simp [h, ALL]
  have hP2 : r2.Pf ∈ [2, 3] := hr2.Pf
  rw [e, e2]
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have b1 := pm0MM1 A (1 :: ([r.F, r.O, 3] ++ 1 :: r.tl ++ 1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R))) hA
    (by simp [*])
  have b2 := pm0mM (A ++ [1]) ([r.F, r.O, 3] ++ 1 :: r.tl ++ 1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R))
    (by simp [*]) (by simp [*])
  have b3 := pm2Block (A ++ [1] ++ [1]) [r.F, r.O, 3] (1 :: r.tl ++ 1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R))
    (by simp [*]) hH (by simp [*])
  have b4 := pm2M (A ++ [1] ++ [1] ++ [r.F, r.O, 3]) (r.tl ++ 1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R))
    (by simp [*]) (by simp [*])
  have b5 := pm3One (A ++ [1] ++ [1] ++ [r.F, r.O]) (1 :: (r.tl ++ 1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R)))
    (by simp [*]) (by simp [*])
  have b6 := pm4Good (Rc.tl_good r hr hacc) (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2])
    (1 :: 1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R)) (by simp [*]) (by simp [*])
  have b7 := pm4M (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2] ++ 1 :: r.tl) (1 :: ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R))
    (by simp [*]) (by simp [*])
  have b8 := pm4mM (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2] ++ 1 :: r.tl ++ [1]) ([r2.F, r2.O, r2.Pf] ++ 1 :: r2.tl ++ R)
    (by simp [*]) (by simp [*])
  have b9 := pm6Block (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2] ++ 1 :: r.tl ++ [1] ++ [1]) [r2.F, r2.O, r2.Pf]
    (1 :: r2.tl ++ R) (by simp [*]) hH2 (by simp [*])
  have b10 := pm6M (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2] ++ 1 :: r.tl ++ [1] ++ [1] ++ [r2.F, r2.O, r2.Pf]) (r2.tl ++ R)
    (by simp [*]) (by simp [*])
  have b11 := pm7Set (A ++ [1] ++ [1] ++ [r.F, r.O] ++ [2] ++ 1 :: r.tl ++ [1] ++ [1] ++ [r2.F, r2.O]) r2.Pf
    (1 :: (r2.tl ++ R)) (by simp [*]) (by simp [*]) hP2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ⊢
  exact b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans (b8.trans (b9.trans (b10.trans b11)))))))))


theorem Rc.tl_noB (r : Rc) (hr : r.Ok) : NoB r.tl := by
  intro x hx; apply r.body_noB hr x; rw [Rc.body_eq]; simp [hx]

/-- More passes: `S = 0` is checked in `SC`, the input flag moves on to the next record, back to `RZ1`. -/
theorem scPm (Wf : List Nat) (hW : BitsD Wf) (q : Nat) (P2 : List Nat) (hP2 : GoodW (1 :: P2))
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.Pf = 2) (r r2 : Rc) (hr : r.Ok) (hacc : r.acc ≠ [])
    (h3 : r.Pf = 3) (hr2 : r2.Ok) (post : List Rc) (hpost : ∀ x ∈ post, x.Ok) (X Y : List Nat)
    (hXY : X ++ Y = Wf ++ 1 :: (List.replicate q 3 ++ 1 :: P2) ++ tailB (pre ++ r :: r2 :: post))
    (hX : NoB X) (hY : Sym4 Y) :
    znttLogic.Reach (hd QNTT.SC X Y)
      (hdR QNTT.RZ1 [] (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: P2) ++
        tailB (pre ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post))) := by
  have sW := hW.sym4
  have sQ : Sym4 (List.replicate q 3) := (BitsD.rep q 3 (by simp)).sym4
  have sP2 : Sym4 P2 := by have := hP2.sym4; simp at this; exact this.2
  have hGP2 : GoodW P2 := by
    cases hP2 with
    | bit hb _ => simp at hb
    | mb hb h => exact GoodW.bit hb h
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have sPost : Sym4 (tailB post) := tailB_sym4 post hpost
  have sr := r.body_sym4 hr
  have sr2 := r2.body_sym4 hr2
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have e : Wf ++ 1 :: (List.replicate q 3 ++ 1 :: P2) ++ tailB (pre ++ r :: r2 :: post) =
      Wf ++ (1 :: (List.replicate q 3 ++ (1 :: (P2 ++ (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post))))))) := by
    simp [tailB_append, tailB]
  have h0 := sc0Scan X Y hX hY
  rw [hXY, e] at h0
  have b1 := sc1Block [] Wf (1 :: (List.replicate q 3 ++ (1 :: (P2 ++ (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post)))))))
    Sym4.nil hW (by simp [*])
  have b2 := sc1M ([] ++ Wf) (List.replicate q 3 ++ (1 :: (P2 ++ (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post))))))
    (by simp [*]) (by simp [*])
  have b3 := sc2Ones q ([] ++ Wf ++ [1]) (1 :: (P2 ++ (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post)))))
    (by simp [*]) (by simp [*])
  have b4 := sc2M ([] ++ Wf ++ [1] ++ List.replicate q 3) (P2 ++ (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post))))
    (by simp [*]) (by simp [*])
  have b5 := pm0Good hGP2 ([] ++ Wf ++ [1] ++ List.replicate q 3 ++ [1]) (tailB pre ++ 1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post)))
    (by simp [*]) (by simp [*])
  have b6 := pmPre pre hpre ([] ++ Wf ++ [1] ++ List.replicate q 3 ++ [1] ++ P2) (1 :: 1 :: (r.body ++ 1 :: 1 :: (r2.body ++ tailB post)))
    (by simp [*]) (by simp [*])
  have b7 := pmAct ([] ++ Wf ++ [1] ++ List.replicate q 3 ++ [1] ++ P2 ++ tailB pre) r r2 hr hacc h3 hr2 (tailB post)
    (by simp [*]) sPost
  have nW := hW.noB
  have nQ : NoB (List.replicate q 3) := noB_rep q 3 (by simp)
  have nP2 := hGP2.noB
  have nPre := tailB_noB pre (fun x hx => (hpre x hx).1)
  have nTl := r.tl_noB hr
  have nTl2 := r2.tl_noB hr2
  have nb : ∀ c ∈ [2, 3], c ∈ NB := fun c hc => by simp at hc; rcases hc with rfl | rfl <;> simp [NB]
  have nF := nb r.F hr.F
  have nO := nb r.O hr.O
  have nF2 := nb r2.F hr2.F
  have nO2 := nb r2.O hr2.O
  have n1 : (1 : Nat) ∈ NB := by simp [NB]
  have n2 : (2 : Nat) ∈ NB := by simp [NB]
  have n3 : (3 : Nat) ∈ NB := by simp [NB]
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have sTl2 : Sym4 r2.tl := r2.tl_sym4 hr2
  have b8 := rz0Scan ([] ++ Wf ++ [1] ++ List.replicate q 3 ++ [1] ++ P2 ++ tailB pre ++ [1, 1, r.F, r.O, 2] ++ 1 :: r.tl ++ [1, 1, r2.F, r2.O]) (3 :: 1 :: (r2.tl ++ tailB post))
    (by simp [NoB_app_iff, NoB_cons_iff, *]) (by simp [*])
  have e2 : Wf ++ 1 :: (List.replicate q 3 ++ 1 :: P2) ++ tailB (pre ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post) =
      ([] ++ Wf ++ [1] ++ List.replicate q 3 ++ [1] ++ P2 ++ tailB pre ++ [1, 1, r.F, r.O, 2] ++ 1 :: r.tl ++ [1, 1, r2.F, r2.O]) ++
        (3 :: 1 :: (r2.tl ++ tailB post)) := by
    simp [tailB_append, tailB, Rc.body_eq, Rc.tl]
  rw [e2]
  simp only [List.nil_append] at h0 b1 b2 b3 b4 b5 b6 b7 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h0 b1 b2 b3 b4 b5 b6 b7 b8 ⊢
  exact h0.trans (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans b8)))))))


/-- Last pass: `S` starts with a `0` (nonzero): `FL0` .. `SU0` .. `SU1`. -/
theorem flOk (Wf : List Nat) (hW : BitsD Wf) (S T X Y : List Nat) (hS : BitsD S) (hT : Sym4 T)
    (j : Nat) (hSe : ∃ S', S = 2 :: S')
    (hXY : X ++ Y = Wf ++ 1 :: (S ++ T)) (hX : NoB X) (hY : Sym4 Y) (hTn : NoB T) :
    znttLogic.Reach (hd QNTT.FL0 X Y) (hdR QNTT.SU1 [] (Wf ++ 1 :: (S ++ T))) := by
  obtain ⟨S', rfl⟩ := hSe
  have sW := hW.sym4
  have sS : Sym4 S' := (BitsD.sym4 (fun x hx => hS x (by simp [hx])))
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 := fl0Scan X Y hX hY
  rw [hXY] at h0
  have b1 := fl1Block [] Wf (1 :: (2 :: S' ++ T)) Sym4.nil hW (by simp [*])
  have b2 := fl1M ([] ++ Wf) (2 :: S' ++ T) (by simp [*]) (by simp [*])
  have b3 := fl2Zero ([] ++ Wf ++ [1]) (S' ++ T) (by simp [*]) (by simp [*])
  have b4 := su0Scan ([] ++ Wf ++ [1]) (2 :: (S' ++ T)) (by
    intro x hx; simp only [List.nil_append, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hW.noB x hx
    · subst hx; simp [NB]) (by simp [*])
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h0 b1 b2 b3 b4 ⊢
  exact h0.trans (b1.trans (b2.trans (b3.trans b4)))



/-! ### Success: `SU*` (erase the records, `n += 1`, `P := 1`) -/

theorem su3Sweep (A f : List Nat) (hA : Sym4 A) (hf : NoB f) :
    znttLogic.Reach (hdR QNTT.SU3 A f) (hd QNTT.SU4 (A ++ List.replicate f.length 0) []) := by
  have hV : Valid [ALL, NB] [A, f] := Valid.cons hA (Valid.cons hf (Valid.nil _))
  simpa using checkFT (env := [A, f]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .blk 1 (.const 0)]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)
theorem su1Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU1 A (f ++ R)) (hdR QNTT.SU1 (A ++ f) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU1 A (1 :: R)) (hdR QNTT.SU2 (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su2Bit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU2 A (2 :: R)) (hdR QNTT.SU1 (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su2Bit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU2 A (3 :: R)) (hdR QNTT.SU1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su2Erase (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU2 A (1 :: R)) (hdR QNTT.SU3 (A ++ [0]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 0]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su4Blanks (A R : List Nat) (n : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU4 (A ++ List.replicate n 0) R) (hd QNTT.SU4 A (List.replicate n 0 ++ R)) := by
  have hV : Valid [ALL, [0], ALL] [A, List.replicate n 0, R] :=
    Valid.cons hA (Valid.cons (repSet n 0) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, List.replicate n 0, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su4M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU4 (A ++ [1]) R) (hd QNTT.SUX A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem suxZero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SUX (A ++ [2]) R) (hdR QNTT.SUY (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 2]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem suyM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SUY A (1 :: R)) (hd QNTT.SU5 A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su5Bits (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU5 (A ++ f) R) (hd QNTT.SU5 A (List.replicate f.length 3 ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id])
    (rs' := [.blk 1 (.const 3), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su5M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU5 (A ++ [1]) R) (hd QNTT.SU6 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su6Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU6 (A ++ f) R) (hd QNTT.SU6 A (f ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id])
    (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su6M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU6 (A ++ [1]) R) (hd QNTT.SU7 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su7Block (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU7 (A ++ f) R) (hd QNTT.SU7 A (f ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  exact checkTT (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id])
    (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su7M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU7 (A ++ [1]) R) (hd QNTT.SU8 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su8Erase (A f R : List Nat) (hA : Sym4 A) (hf : NoB f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU8 (A ++ f) R) (hd QNTT.SU8 A (List.replicate f.length 0 ++ R)) := by
  have hV : Valid [ALL, NB, ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id])
    (rs' := [.blk 1 (.const 0), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su8End (R : List Nat) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU8 [] R) (hdR QNTT.SU9 [] R) := by
  have hV : Valid [ALL] [R] := Valid.cons hR (Valid.nil _)
  exact checkTF (env := [R]) (E := []) (k := 4) hV trivial
    (ls := []) (rs := [.blk 0 .id]) (ls' := []) (rs' := [.blk 0 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su9Blanks (A R : List Nat) (n : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU9 A (List.replicate n 0 ++ R)) (hdR QNTT.SU9 (A ++ List.replicate n 0) R) := by
  have hV : Valid [ALL, [0], ALL] [A, List.replicate n 0, R] :=
    Valid.cons hA (Valid.cons (repSet n 0) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate n 0, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su9M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.SU9 A (1 :: R)) (hd QNTT.SU10 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su10Set (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU10 (A ++ [0]) R) (hdR QNTT.PA0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 0]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem su1Bit (A : List Nat) (b : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) (hb : b ∈ [2, 3]) :
    znttLogic.Reach (hdR QNTT.SU1 A (b :: R)) (hdR QNTT.SU1 (A ++ [b]) R) := by
  have := su1Block A [b] R hA (by intro x hx; simp at hx; subst hx; exact hb) hR
  simpa using this

theorem su2Bit (A : List Nat) (b : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) (hb : b ∈ [2, 3]) :
    znttLogic.Reach (hdR QNTT.SU2 A (b :: R)) (hdR QNTT.SU1 (A ++ [b]) R) := by
  simp at hb; rcases hb with rfl | rfl
  · exact su2Bit2 A R hA hR
  · exact su2Bit3 A R hA hR

theorem su1Good {u : List Nat} (hu : GoodW u) :
    ∀ (A rest : List Nat), Sym4 A → Sym4 rest →
    znttLogic.Reach (hdR QNTT.SU1 A (u ++ rest)) (hdR QNTT.SU1 (A ++ u) rest) := by
  induction hu with
  | nil => intro A rest _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [b] := by
      intro y hy; simp at hy; subst hy; simp at hb; rcases hb with rfl | rfl <;> simp [ALL]
    have h1 := su1Bit A b (u ++ rest) hA (hu'.sym4.app hr) hb
    have h2 := ih (A ++ [b]) rest (hA.app sb) hr
    simpa using h1.trans h2
  | @mb b u hb hu' ih =>
    intro A rest hA hr
    have sb : Sym4 [1, b] := by
      intro y hy; simp at hy; simp at hb; rcases hy with rfl | rfl <;> (try rcases hb with rfl | rfl) <;> simp [ALL]
    have s1 : Sym4 [1] := sym4_cell 1 (by simp)
    have h1 := su1M A (b :: u ++ rest) hA ((Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) hu'.sym4).app hr)
    have h1' := su2Bit (A ++ [1]) b (u ++ rest) (hA.app s1) (hu'.sym4.app hr) hb
    have h2 := ih (A ++ [1, b]) rest (hA.app sb) hr
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h1' h2 ⊢
    exact h1.trans (h1'.trans h2)


/-- Success (`Nn` fully marked): `SU1 .. SU10`: erase the records, `Nn := 1^(|Nn|+1)`, erase `W`, `S`; `P := 1`. -/
theorem suOk (Wf S Kf Cf Nl recs : List Nat) (hW : BitsD Wf) (hS : BitsD S) (hK : BitsD Kf) (hC : BitsD Cf)
    (hN : BitsD Nl)
    (hP : GoodW (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))))
    (hrecs : NoB recs) :
    znttLogic.Reach (hdR QNTT.SU1 [] (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2])))) ++ 1 :: 1 :: recs))
      (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl.length + 2) 3 ++ List.replicate (recs.length + 1) 0))))) := by
  have sW := hW.sym4
  have sS := hS.sym4
  have sK := hK.sym4
  have sC := hC.sym4
  have sN := hN.sym4
  have sR : Sym4 recs := hrecs.sym4
  have a0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have sZ : ∀ n, Sym4 (List.replicate n 0) := fun n => by
    intro x hx; simp [List.mem_replicate] at hx; simp [hx, ALL]
  have s3 : ∀ n, Sym4 (List.replicate n 3) := fun n => (BitsD.rep n 3 (by simp)).sym4
  have h1 := su1Good hP [] (1 :: 1 :: recs) Sym4.nil (by simp [*])
  have h2 := su1M ([] ++ (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))) ) (1 :: recs) (by simp [*]) (by simp [*])
  have h3 := su2Erase ([] ++ (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))) ++ [1]) recs (by simp [*]) sR
  have h4 := su3Sweep ([] ++ (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))) ++ [1] ++ [0]) recs (by simp [*]) hrecs
  have h5 := su4Blanks (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))  ++ [1]) [] (recs.length + 1) (by simp [*]) Sym4.nil
  have h6 := su4M (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (Nl ++ [2]))))) (List.replicate (recs.length + 1) 0 ++ []) (by simp [*]) (by simp [a0])
  have h7 := suxZero (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: Nl)))) (1 :: (List.replicate (recs.length + 1) 0 ++ [])) (by simp [*]) (by simp [*])
  have h8 := suyM (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: Nl)))  ++ [3]) (List.replicate (recs.length + 1) 0 ++ []) (by simp [*]) (by simp [a0])
  have h9 := su5Bits (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: Cf)) ++ [1]) (Nl ++ [3]) (3 :: (List.replicate (recs.length + 1) 0 ++ []))
    (by simp [*]) (by intro x hx; simp at hx; rcases hx with hx | rfl; exact hN x hx; simp) (by simp [*])
  have h10 := su5M (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: Cf))) (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))
    (by simp [*]) (by simp [*])
  have h11 := su6Block (Wf ++ 1 :: (S ++ 1 :: (Kf ++ [1]))) Cf (1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ [])))
    (by simp [*]) hC (by simp [*])
  have h12 := su6M (Wf ++ 1 :: (S ++ 1 :: Kf)) (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ [])))
    (by simp [*]) (by simp [*])
  have h13 := su7Block (Wf ++ 1 :: (S ++ [1])) Kf (1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))
    (by simp [*]) hK (by simp [*])
  have h14 := su7M (Wf ++ 1 :: S) (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))
    (by simp [*]) (by simp [*])
  have nf : NoB (Wf ++ 1 :: S) := by
    intro x hx; simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hW.noB x hx
    · simp [NB]
    · exact hS.noB x hx
  have h15 := su8Erase [] (Wf ++ 1 :: S) (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))) Sym4.nil nf
    (by simp [*])
  have h16 := su8End (List.replicate (Wf ++ 1 :: S).length 0 ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))) (by simp [*])
  have h17 := su9Blanks [] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))) (Wf ++ 1 :: S).length Sym4.nil (by simp [*])
  have h18 := su9M (List.replicate (Wf ++ 1 :: S).length 0) (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ [])))) (sZ _) (by simp [*])
  obtain ⟨m, hm⟩ : ∃ m, (Wf ++ 1 :: S).length = m + 1 := ⟨(Wf ++ 1 :: S).length - 1, by simp; omega⟩
  rw [hm] at h15 h16 h17 h18
  have h19 := su10Set (List.replicate m 0) (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))) (sZ _) (by simp [*])
  rw [← List.replicate_succ'] at h19
  have h20 := ZP.F.hdR_zeros QNTT.PA0 (List.replicate m 0) [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (Nl ++ [3]).length 3 ++ 3 :: (List.replicate (recs.length + 1) 0 ++ []))))) (fun a ha => by
    simp [List.mem_replicate] at ha; simp [ZP.F.B0, ha])
  rw [h20] at h19
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.length_append, List.length_singleton, List.replicate_succ, List.append_nil] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 ⊢
  have hz3 : ∀ (n : Nat) (Z : List Nat), List.replicate n 3 ++ 3 :: Z = 3 :: (List.replicate n 3 ++ Z) := by
    intro n Z; induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih]
  simp only [hz3] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans (h13.trans (h14.trans (h15.trans (h16.trans (h17.trans (h18.trans h19)))))))))))))))))



/-! ### Beep: `BX*` (`C += 1`) -/

theorem suxOne (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SUX (A ++ [3]) R) (hdR QNTT.BX1 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 3]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bx1M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BX1 A (1 :: R)) (hd QNTT.BX2 A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bx2Ones (A R : List Nat) (k : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BX2 (A ++ List.replicate k 3) R) (hd QNTT.BX2 A (List.replicate k 3 ++ R)) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate k 3, R] :=
    Valid.cons hA (Valid.cons (repSet k 3) (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, List.replicate k 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bx2M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.BX2 (A ++ [1]) R) (hdR QNTT.BX3 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem bx3One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.BX3 A (3 :: R)) (hd QNTT.SU6 A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)


/-- `SU1` over the parameters, erase the records: ends in `SUX` on the last cell of `Nn`. -/
theorem suPre (Pm recs : List Nat) (hP : GoodW Pm) (hrecs : NoB recs) :
    znttLogic.Reach (hdR QNTT.SU1 [] (Pm ++ 1 :: 1 :: recs))
      (hd QNTT.SUX Pm (1 :: List.replicate (recs.length + 1) 0)) := by
  have sP := hP.sym4
  have sR : Sym4 recs := hrecs.sym4
  have a0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h1 := su1Good hP [] (1 :: 1 :: recs) Sym4.nil (by simp [*])
  have h2 := su1M ([] ++ Pm) (1 :: recs) (by simp [*]) (by simp [*])
  have h3 := su2Erase ([] ++ Pm ++ [1]) recs (by simp [*]) sR
  have h4 := su3Sweep ([] ++ Pm ++ [1] ++ [0]) recs (by simp [*]) hrecs
  have h5 := su4Blanks (Pm ++ [1]) [] (recs.length + 1) (by simp [*]) Sym4.nil
  have h6 := su4M Pm (List.replicate (recs.length + 1) 0 ++ []) sP (by simp [a0])
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.length_append, List.length_singleton,
    List.replicate_succ, List.append_nil, List.length_map] at h1 h2 h3 h4 h5 h6 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- From the last cell of `C` (`SU6`) to `PA0`: erase `W`, `S`, `P := 1`. -/
theorem suTail (Wf S Kf Cf R : List Nat) (hW : BitsD Wf) (hS : BitsD S) (hK : BitsD Kf) (hC : BitsD Cf)
    (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.SU6 (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: Cf))) R)
      (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ R)))) := by
  have sW := hW.sym4
  have sS := hS.sym4
  have sK := hK.sym4
  have sC := hC.sym4
  have a0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have sZ : ∀ n, Sym4 (List.replicate n 0) := fun n => by
    intro x hx; simp [List.mem_replicate] at hx; simp [hx, ALL]
  have h11 := su6Block (Wf ++ 1 :: (S ++ 1 :: (Kf ++ [1]))) Cf R (by simp [*]) hC hR
  have h12 := su6M (Wf ++ 1 :: (S ++ 1 :: Kf)) (Cf ++ R) (by simp [*]) (by simp [*])
  have h13 := su7Block (Wf ++ 1 :: (S ++ [1])) Kf (1 :: (Cf ++ R)) (by simp [*]) hK (by simp [*])
  have h14 := su7M (Wf ++ 1 :: S) (Kf ++ 1 :: (Cf ++ R)) (by simp [*]) (by simp [*])
  have nf : NoB (Wf ++ 1 :: S) := by
    intro x hx; simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hW.noB x hx
    · simp [NB]
    · exact hS.noB x hx
  have h15 := su8Erase [] (Wf ++ 1 :: S) (1 :: (Kf ++ 1 :: (Cf ++ R))) Sym4.nil nf (by simp [*])
  have h16 := su8End (List.replicate (Wf ++ 1 :: S).length 0 ++ 1 :: (Kf ++ 1 :: (Cf ++ R))) (by simp [*])
  have h17 := su9Blanks [] (1 :: (Kf ++ 1 :: (Cf ++ R))) (Wf ++ 1 :: S).length Sym4.nil (by simp [*])
  have h18 := su9M (List.replicate (Wf ++ 1 :: S).length 0) (Kf ++ 1 :: (Cf ++ R)) (sZ _) (by simp [*])
  obtain ⟨m, hm⟩ : ∃ m, (Wf ++ 1 :: S).length = m + 1 := ⟨(Wf ++ 1 :: S).length - 1, by simp; omega⟩
  rw [hm] at h15 h16 h17 h18
  have h19 := su10Set (List.replicate m 0) (1 :: (Kf ++ 1 :: (Cf ++ R))) (sZ _) (by simp [*])
  rw [← List.replicate_succ'] at h19
  have h20 := ZP.F.hdR_zeros QNTT.PA0 (List.replicate m 0) [3] (1 :: (Kf ++ 1 :: (Cf ++ R))) (fun a ha => by
    simp [List.mem_replicate] at ha; simp [ZP.F.B0, ha])
  rw [h20] at h19
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.length_append, List.length_singleton,
    List.replicate_succ] at h11 h12 h13 h14 h15 h16 h17 h18 h19 ⊢
  exact h11.trans (h12.trans (h13.trans (h14.trans (h15.trans (h16.trans (h17.trans (h18.trans h19)))))))


/-- Beep (`Nn` all ones, unmarked): `C += 1`, `Nn` shifts right by one cell; then as in the success case. -/
theorem beepOk (Wf S Kf Cf recs : List Nat) (L : Nat) (hW : BitsD Wf) (hS : BitsD S) (hK : BitsD Kf) (hC : BitsD Cf)
    (hP : GoodW (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: List.replicate (L + 1) 3)))))
    (hrecs : NoB recs) :
    znttLogic.Reach (hdR QNTT.SU1 [] (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: List.replicate (L + 1) 3))) ++ 1 :: 1 :: recs))
      (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: ((Cf ++ [3]) ++ 1 :: (List.replicate (L + 1) 3 ++ List.replicate (recs.length + 1) 0))))) := by
  have sW := hW.sym4
  have sS := hS.sym4
  have sK := hK.sym4
  have sC := hC.sym4
  have a0 : (0 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have sZ : ∀ n, Sym4 (List.replicate n 0) := fun n => by
    intro x hx; simp [List.mem_replicate] at hx; simp [hx, ALL]
  have s3 : ∀ n, Sym4 (List.replicate n 3) := fun n => (BitsD.rep n 3 (by simp)).sym4
  have hz3 : ∀ (n : Nat) (Z : List Nat), List.replicate n 3 ++ 3 :: Z = 3 :: (List.replicate n 3 ++ Z) := by
    intro n Z; induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, ih]
  have h1 := suPre _ recs hP hrecs
  have e0 : Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ 1 :: List.replicate (L + 1) 3))) =
      (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ [1])))) ++ List.replicate L 3 ++ [3] := by
    simp [List.replicate_succ', List.append_assoc]
  rw [e0] at h1
  have h2 := suxOne ((Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ [1])))) ++ List.replicate L 3) (1 :: List.replicate (recs.length + 1) 0)
    (by simp [*]) (by simp [*])
  have h3 := bx1M ((Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ [1])))) ++ List.replicate L 3 ++ [3]) (List.replicate (recs.length + 1) 0)
    (by simp [*]) (sZ _)
  have h4 := bx2Ones (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: (Cf ++ [1])))) (3 :: List.replicate (recs.length + 1) 0) (L + 1)
    (by simp [*]) (by simp [*])
  have h5 := bx2M (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: Cf))) (List.replicate (L + 1) 3 ++ 3 :: List.replicate (recs.length + 1) 0)
    (by simp [*]) (by simp [*])
  have h6 := bx3One (Wf ++ 1 :: (S ++ 1 :: (Kf ++ 1 :: Cf)) ++ [3]) (List.replicate L 3 ++ 3 :: List.replicate (recs.length + 1) 0)
    (by simp [*]) (by simp [*])
  have h7 := suTail Wf S Kf (Cf ++ [3]) (1 :: (List.replicate L 3 ++ 3 :: List.replicate (recs.length + 1) 0)) hW hS hK
    (by intro x hx; simp at hx; rcases hx with hx | rfl; exact hC x hx; simp) (by simp [*])
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.replicate_succ, hz3, List.append_nil] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))


/-! ## Odometer primitives -/

theorem odlScan (L R : List Nat) (hL : NoB L) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.ODL L R) (hdR QNTT.OD0 [] (L ++ R)) := by
  have hV : Valid [NB, ALL] [L, R] := Valid.cons hL (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [L, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id]) (ls' := []) (rs' := [.blk 0 .id, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0Bit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0 A (2 :: R)) (hdR QNTT.OD0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0Bit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0 A (3 :: R)) (hdR QNTT.OD0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0 A (1 :: R)) (hdR QNTT.OD0m (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0mBit2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0m A (2 :: R)) (hdR QNTT.OD0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0mBit3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0m A (3 :: R)) (hdR QNTT.OD0 (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem od0mM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.OD0m A (1 :: R)) (hdR QNTT.ODH (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odhSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODH A (f ++ 1 :: R)) (hdR QNTT.ODa (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odaSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODa A (f ++ 1 :: R)) (hdR QNTT.ODe (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odeSkip (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODe A (f ++ 1 :: R)) (hdR QNTT.ODI (A ++ f ++ [1]) R) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkFF (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .sym 1, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id, .sym 1]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odi3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODI A (3 :: R)) (hdR QNTT.ODJ (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odm3 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM A (3 :: R)) (hdR QNTT.ODJ (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odjZero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ A (2 :: R)) (hd QNTT.WI0 A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odjM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ A (1 :: R)) (hd QNTT.ODR A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odmM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM A (1 :: R)) (hdR QNTT.ODH (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odnM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODN A (1 :: R)) (hdR QNTT.ODM (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odw2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODW A (2 :: R)) (hdR QNTT.ODN (A ++ [3]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 3]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odjOnes (A R : List Nat) (j : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ A (List.replicate j 3 ++ R)) (hdR QNTT.ODJ (A ++ List.replicate j 3) R) := by
  have hV : Valid [ALL, [3], ALL] [A, List.replicate j 3, R] :=
    Valid.cons hA (Valid.cons (repSet j 3) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate j 3, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odnZeros (A R : List Nat) (j : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODN A (List.replicate j 2 ++ R)) (hdR QNTT.ODN (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] :=
    Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odrBits (A f R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.ODR (A ++ f) R) (hd QNTT.ODR A (List.replicate f.length 2 ++ R)) := by
  have hV : Valid [ALL, [2, 3], ALL] [A, f, R] := Valid.cons hA (Valid.cons hf (Valid.cons hR (Valid.nil _)))
  simpa using checkTT (env := [A, f, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id]) (ls' := [.blk 0 .id])
    (rs' := [.blk 1 (.const 2), .blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odrM (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hd QNTT.ODR (A ++ [1]) R) (hdR QNTT.ODW (A ++ [1]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkTF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 1 .id]) (ls' := [.blk 0 .id, .sym 1]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odjEnd (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.ODJ A []) (hd QNTT.ODR A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem odnEnd (A : List Nat) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.ODN A []) (hd QNTT.BEEP A []) := by
  have hV : Valid [ALL] [A] := Valid.cons hA (Valid.nil _)
  exact checkFT (env := [A]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := []) (ls' := [.blk 0 .id]) (rs' := [])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem beepStepZ (A R : List Nat) :
    znttLogic.zstep (hd QNTT.BEEP (A ++ [1]) R) = some (hd QNTT.SU0 A (1 :: R)) := by
  have e1 : (⟨QNTT.BEEP, [Item.blk 0 .id, .sym 1].reverse, [.blk 1 .id], true⟩ : SC).den [A, R]
      = hd QNTT.BEEP (A ++ [1]) R := den_tape (by osimp) (by osimp)
  have e2 : (⟨QNTT.SU0, [Item.blk 0 .id].reverse, [.sym 1, .blk 1 .id], true⟩ : SC).den [A, R]
      = hd QNTT.SU0 A (1 :: R) := den_tape (by osimp) (by osimp)
  rw [← e1, ← e2]
  exact cstep_zstep (by decide +kernel)

/-- The restoring walk from the parameters to the first record separator. -/
theorem od0Walk {u v : List Nat} (h : Rest u v) :
    ∀ (A R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach (hdR QNTT.OD0 A (u ++ R)) (hdR QNTT.OD0 (A ++ v) R) := by
  induction h with
  | nil => intro A R _ _; simpa using LTM.Reach.refl znttLogic _
  | @bit b u v hb h ih =>
    intro A R hA hR
    have h1 : znttLogic.Reach (hdR QNTT.OD0 A (b :: (u ++ R))) (hdR QNTT.OD0 (A ++ [3]) (u ++ R)) := by
      simp at hb; rcases hb with rfl | rfl
      · exact od0Bit2 A _ hA (h.sym4_src.app hR)
      · exact od0Bit3 A _ hA (h.sym4_src.app hR)
    have h2 := ih (A ++ [3]) R (hA.app (by intro y hy; simp at hy; subst hy; simp [ALL])) hR
    simpa using h1.trans h2
  | @mb b u v hb h ih =>
    intro A R hA hR
    have h1 := od0M A (b :: (u ++ R)) hA (Sym4.cons (by simp at hb; rcases hb with rfl | rfl <;> simp [ALL]) (h.sym4_src.app hR))
    have hA1 : Sym4 (A ++ [1]) := hA.app (by intro y hy; simp at hy; subst hy; simp [ALL])
    have h1' : znttLogic.Reach (hdR QNTT.OD0m (A ++ [1]) (b :: (u ++ R))) (hdR QNTT.OD0 (A ++ [1] ++ [3]) (u ++ R)) := by
      simp at hb; rcases hb with rfl | rfl
      · exact od0mBit2 _ _ hA1 (h.sym4_src.app hR)
      · exact od0mBit3 _ _ hA1 (h.sym4_src.app hR)
    have h2 := ih (A ++ [1] ++ [3]) R (hA1.app (by intro y hy; simp at hy; subst hy; simp [ALL])) hR
    simpa using h1.trans (h1'.trans h2)

theorem odiZeros (A R : List Nat) (j : Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODI A (List.replicate j 2 ++ R)) (hdR QNTT.ODI (A ++ List.replicate j 2) R) := by
  have hV : Valid [ALL, [2], ALL] [A, List.replicate j 2, R] :=
    Valid.cons hA (Valid.cons (repSet j 2) (Valid.cons hR (Valid.nil _)))
  exact checkFF (env := [A, List.replicate j 2, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.blk 1 .id, .blk 2 .id])
    (ls' := [.blk 0 .id, .blk 1 .id]) (rs' := [.blk 2 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Inside one record's digit string: skip the leading zeros and the run of ones of the
counter, then increment the first `0` (the no-carry case) by entering `WI0`. -/
theorem odInc (A : List Nat) (z o : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODI A (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R)))
      (hd QNTT.WI0 (A ++ List.replicate z 2 ++ 3 :: List.replicate o 3) (3 :: R)) := by
  have h1 := odiZeros A (3 :: (List.replicate o 3 ++ 2 :: R)) z hA
    (Sym4.cons (by simp [ALL]) (Sym4.app (sym4_rep o 3 (by simp [ALL])) (Sym4.cons (by simp [ALL]) hR)))
  have hA1 : Sym4 (A ++ List.replicate z 2) := hA.app (sym4_rep z 2 (by simp [ALL]))
  have h2 := odi3 (A ++ List.replicate z 2) (List.replicate o 3 ++ 2 :: R) hA1
    (Sym4.app (sym4_rep o 3 (by simp [ALL])) (Sym4.cons (by simp [ALL]) hR))
  have hA2 : Sym4 (A ++ List.replicate z 2 ++ [3]) := hA1.app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h3 := odjOnes (A ++ List.replicate z 2 ++ [3]) (2 :: R) o hA2 (Sym4.cons (by simp [ALL]) hR)
  have hA3 : Sym4 (A ++ List.replicate z 2 ++ [3] ++ List.replicate o 3) := hA2.app (sym4_rep o 3 (by simp [ALL]))
  have h4 := odjZero _ R hA3 hR
  simpa using h1.trans (h2.trans (h3.trans h4))

/-- Carry out of a digit string `f` (length `n+1`) that ends at an `M`: the string is reset to
zeros, its first cell becomes `1`, and the scan continues at the next separator (`ODM`). -/
theorem odCarry (P0 f R : List Nat) (n : Nat) (hP : Sym4 P0) (hf : BitsD f) (hn : f.length = n + 1)
    (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: f) (1 :: R))
      (hdR QNTT.ODM (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1]) R) := by
  have hA : Sym4 (P0 ++ 1 :: f) := hP.app (Sym4.cons (by simp [ALL]) (fun y hy => by
    have := hf y hy; simp at this; rcases this with rfl | rfl <;> simp [ALL]))
  have hP1 : Sym4 (P0 ++ [1]) := hP.app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have hrep : ∀ k, Sym4 (List.replicate k 2) := fun k => sym4_rep k 2 (by simp [ALL])
  have h1 := odjM (P0 ++ 1 :: f) R hA hR
  have h2 := odrBits (P0 ++ [1]) f (1 :: R) hP1 hf (Sym4.cons (by simp [ALL]) hR)
  have h3 := odrM P0 (List.replicate f.length 2 ++ 1 :: R) hP ((hrep _).app (Sym4.cons (by simp [ALL]) hR))
  rw [hn, List.replicate_succ] at h3
  have h4 := odw2 (P0 ++ [1]) (List.replicate n 2 ++ 1 :: R) hP1 ((hrep _).app (Sym4.cons (by simp [ALL]) hR))
  have hP2 : Sym4 (P0 ++ [1] ++ [3]) := hP1.app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h5 := odnZeros (P0 ++ [1] ++ [3]) (1 :: R) n hP2 (Sym4.cons (by simp [ALL]) hR)
  have hP3 : Sym4 (P0 ++ [1] ++ [3] ++ List.replicate n 2) := hP2.app (hrep _)
  have h6 := odnM _ R hP3 hR
  rw [hn, List.replicate_succ] at h2
  have h1' : znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: f) (1 :: R)) (hd QNTT.ODR (P0 ++ [1] ++ f) (1 :: R)) := by
    simpa using h1
  simpa using h1'.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem beepStepC (A R : List Nat) (c : Nat) (hc : c ∈ [1, 2, 3]) :
    znttLogic.zstep (hd QNTT.BEEP (A ++ [c]) R) = some (hd QNTT.SU0 A (c :: R)) := by
  have e1 : (⟨QNTT.BEEP, [Item.blk 0 .id, .sym c].reverse, [.blk 1 .id], true⟩ : SC).den [A, R]
      = hd QNTT.BEEP (A ++ [c]) R := den_tape (by osimp) (by osimp)
  have e2 : (⟨QNTT.SU0, [Item.blk 0 .id].reverse, [.sym c, .blk 1 .id], true⟩ : SC).den [A, R]
      = hd QNTT.SU0 A (c :: R) := den_tape (by osimp) (by osimp)
  rw [← e1, ← e2]
  simp at hc
  rcases hc with rfl | rfl | rfl <;> exact cstep_zstep (by decide +kernel)

/-- The odometer at a record whose witness string `b` is `0^z 1^(o+1) 0 …`: header, `acc` and `E`
are skipped and the string is incremented without carry. -/
theorem odRecInc (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (z o : Nat) (R : List Nat)
    (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc) (hE : BitsD E) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R))))))
      (hd QNTT.WI0 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate z 2 ++ 3 :: List.replicate o 3))))
        (3 :: R)) := by
  have hf : BitsD [F, O, Pf] := by
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hrep : ∀ k a, a ∈ ALL → Sym4 (List.replicate k a) := fun k a h => sym4_rep k a h
  have hZ : Sym4 (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R)) :=
    (hrep z 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) ((hrep o 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)))
  have hEs : Sym4 (E ++ 1 :: (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R))) :=
    hE.sym4.app (Sym4.cons (by simp [ALL]) hZ)
  have hAs : Sym4 (acc ++ 1 :: (E ++ 1 :: (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R)))) :=
    hacc.sym4.app (Sym4.cons (by simp [ALL]) hEs)
  have h1 := odhSkip A [F, O, Pf] _ hA hf hAs
  have hA1 : Sym4 (A ++ [F, O, Pf] ++ [1]) := (hA.app hf.sym4).app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h2 := odaSkip _ acc _ hA1 hacc hEs
  have hA2 : Sym4 (A ++ [F, O, Pf] ++ [1] ++ acc ++ [1]) := (hA1.app hacc.sym4).app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h3 := odeSkip _ E _ hA2 hE hZ
  have hA3 : Sym4 (A ++ [F, O, Pf] ++ [1] ++ acc ++ [1] ++ E ++ [1]) := (hA2.app hE.sym4).app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h4 := odInc _ z o R hA3 hR
  simpa using h1.trans (h2.trans (h3.trans h4))

theorem odm2 (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM A (2 :: R)) (hdR QNTT.ODI (A ++ [2]) R) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  simpa using checkFF (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id, .sym 2]) (rs' := [.blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-- Carry out of the witness string into the next string `u = 0^(z+1) 1^(o+1) 0 …`, then
increment that without carry. -/
theorem odCarryInc (P0 f R : List Nat) (n z o : Nat) (hP : Sym4 P0) (hf : BitsD f) (hn : f.length = n + 1)
    (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODJ (P0 ++ 1 :: f) (1 :: (List.replicate (z + 1) 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R))))
      (hd QNTT.WI0 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ 1 :: (List.replicate (z + 1) 2 ++ 3 :: List.replicate o 3))
        (3 :: R)) := by
  have hrep : ∀ k a, a ∈ ALL → Sym4 (List.replicate k a) := fun k a h => sym4_rep k a h
  have hU : Sym4 (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R)) :=
    (hrep z 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) ((hrep o 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hR)))
  have h1 := odCarry P0 f (2 :: (List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ 2 :: R))) n hP hf hn
    (Sym4.cons (by simp [ALL]) hU)
  have hA : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1]) := by
    have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
    have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
    have h3 : Sym4 (3 :: List.replicate n 2) := Sym4.cons a3 (hrep n 2 (by simp [ALL]))
    have h4 : Sym4 [1] := fun y hy => by simp at hy; subst hy; exact a1
    simpa using (hP.app (Sym4.cons a1 h3)).app h4
  have h2 := odm2 _ _ hA hU
  have hA2 : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1] ++ [2]) := hA.app (by intro y hy; simp at hy; subst hy; simp [ALL])
  have h3 := odInc _ z o R hA2 hR
  simpa [List.replicate_succ] using h1.trans (h2.trans h3)

/-- The same when the next string starts with `1`: `u = 1^(o+1) 0 …`. -/
theorem odCarryInc0 (P0 f R : List Nat) (n o : Nat) (hP : Sym4 P0) (hf : BitsD f) (hn : f.length = n + 1)
    (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODJ (P0 ++ 1 :: f) (1 :: 3 :: (List.replicate o 3 ++ 2 :: R)))
      (hd QNTT.WI0 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ 1 :: 3 :: List.replicate o 3) (3 :: R)) := by
  have hrep : ∀ k a, a ∈ ALL → Sym4 (List.replicate k a) := fun k a h => sym4_rep k a h
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have a3 : (3 : Nat) ∈ ALL := by simp [ALL]
  have hU : Sym4 (List.replicate o 3 ++ 2 :: R) :=
    (hrep o 3 a3).app (Sym4.cons a2 hR)
  have h1 := odCarry P0 f (3 :: (List.replicate o 3 ++ 2 :: R)) n hP hf hn (Sym4.cons a3 hU)
  have hA : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1]) := by
    have h3 : Sym4 (3 :: List.replicate n 2) := Sym4.cons a3 (hrep n 2 a2)
    have h4 : Sym4 [1] := fun y hy => by simp at hy; subst hy; exact a1
    simpa using (hP.app (Sym4.cons a1 h3)).app h4
  have h2 := odm3 _ _ hA hU
  have hA2 : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1] ++ [3]) := hA.app (fun y hy => by simp at hy; subst hy; exact a3)
  have h3 := odjOnes _ (2 :: R) o hA2 (Sym4.cons a2 hR)
  have hA3 : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1] ++ [3] ++ List.replicate o 3) := hA2.app (hrep o 3 a3)
  have h4 := odjZero _ R hA3 hR
  simpa using h1.trans (h2.trans (h3.trans h4))

/-- Carry out of the last string of a record into the next record's header (`ODH`). -/
theorem odCarryNext (P0 f R : List Nat) (n : Nat) (hP : Sym4 P0) (hf : BitsD f) (hn : f.length = n + 1)
    (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: f) (1 :: 1 :: R))
      (hdR QNTT.ODH (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1, 1]) R) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h1 := odCarry P0 f (1 :: R) n hP hf hn (Sym4.cons a1 hR)
  have hA : Sym4 (P0 ++ 1 :: 3 :: List.replicate n 2 ++ [1]) := by
    have h3 : Sym4 (3 :: List.replicate n 2) :=
      Sym4.cons (by simp [ALL]) (sym4_rep n 2 (by simp [ALL]))
    have h4 : Sym4 [1] := fun y hy => by simp at hy; subst hy; exact a1
    simpa using (hP.app (Sym4.cons a1 h3)).app h4
  have h2 := odmM _ R hA hR
  simpa using h1.trans h2

/-- Carry out of the very last string of the tape: the odometer has overflowed and beeps. -/
theorem odCarryEnd (P0 f : List Nat) (n : Nat) (hP : Sym4 P0) (hf : BitsD f) (hn : f.length = n + 1) :
    znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: f) [])
      (hd QNTT.BEEP (P0 ++ 1 :: 3 :: List.replicate n 2) []) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hrep : ∀ k, Sym4 (List.replicate k 2) := fun k => sym4_rep k 2 (by simp [ALL])
  have hA : Sym4 (P0 ++ 1 :: f) := hP.app (Sym4.cons a1 (fun y hy => by
    have := hf y hy; simp at this; rcases this with rfl | rfl <;> simp [ALL]))
  have hP1 : Sym4 (P0 ++ [1]) := hP.app (fun y hy => by simp at hy; subst hy; exact a1)
  have h1 := odjEnd (P0 ++ 1 :: f) hA
  have h1' : znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: f) []) (hd QNTT.ODR (P0 ++ [1] ++ f) []) := by
    simpa using h1
  have h2 := odrBits (P0 ++ [1]) f [] hP1 hf Sym4.nil
  have h3 := odrM P0 (List.replicate f.length 2) hP (hrep _)
  rw [hn, List.replicate_succ] at h3 h2
  rw [List.append_nil] at h2
  have h4 := odw2 (P0 ++ [1]) (List.replicate n 2) hP1 (hrep _)
  have hP2 : Sym4 (P0 ++ [1] ++ [3]) := hP1.app (fun y hy => by simp at hy; subst hy; simp [ALL])
  have h5 := odnZeros (P0 ++ [1] ++ [3]) [] n hP2 Sym4.nil
  rw [List.append_nil] at h5
  have hP3 : Sym4 (P0 ++ [1] ++ [3] ++ List.replicate n 2) := hP2.app (hrep _)
  have h6 := odnEnd _ hP3
  simpa using h1'.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-! ## The odometer's abstract successor (mixed radix) -/

/-- Digits `(d, r)` with `d < r`, least significant first. -/
def odoNext : List (Nat × Nat) → Option (List (Nat × Nat))
  | [] => none
  | (d, r) :: rest =>
    if d + 1 < r then some ((d + 1, r) :: rest)
    else (odoNext rest).map ((0, r) :: ·)

def odoVal : List (Nat × Nat) → Nat
  | [] => 0
  | (d, r) :: rest => d + r * odoVal rest

def odoSize : List (Nat × Nat) → Nat
  | [] => 1
  | (_, r) :: rest => r * odoSize rest

def OdoWF (l : List (Nat × Nat)) : Prop := ∀ p ∈ l, p.1 < p.2

theorem odoNext_val : ∀ (l l' : List (Nat × Nat)), OdoWF l → odoNext l = some l' →
    odoVal l' = odoVal l + 1 := by
  intro l
  induction l with
  | nil => intro l' _ h; simp [odoNext] at h
  | cons p rest ih =>
    obtain ⟨d, r⟩ := p
    intro l' hwf h
    have hd : d < r := hwf (d, r) (by simp)
    have hrest : OdoWF rest := fun q hq => hwf q (by simp [hq])
    by_cases hc : d + 1 < r
    · simp [odoNext, hc] at h; subst h
      simp [odoVal]; omega
    · simp [odoNext, hc] at h
      obtain ⟨l'', hl'', rfl⟩ := h
      have := ih l'' hrest hl''
      have hdr : d + 1 = r := by omega
      simp [odoVal, this, Nat.mul_add]
      omega

/-- No successor exactly when every digit is maximal. -/
theorem odoNext_none : ∀ l : List (Nat × Nat), OdoWF l → odoNext l = none →
    ∀ p ∈ l, p.1 + 1 = p.2 := by
  intro l
  induction l with
  | nil => intro _ _ p hp; simp at hp
  | cons q rest ih =>
    obtain ⟨d, r⟩ := q
    intro hwf h p hp
    have hd : d < r := hwf (d, r) (by simp)
    have hrest : OdoWF rest := fun q hq => hwf q (by simp [hq])
    by_cases hc : d + 1 < r
    · simp [odoNext, hc] at h
    · simp [odoNext, hc] at h
      simp at hp; rcases hp with rfl | hp
      · simp; omega
      · exact ih hrest h p hp

/-- Thermometer encoding of a digit `d < r`: `1^(d+1) 0^(r-d-1)`. -/
def therm (d r : Nat) : List Nat := List.replicate (d + 1) 3 ++ List.replicate (r - (d + 1)) 2

/-- `odRecInc` on thermometer digits: the `b` string `d < r - 1` becomes `d + 1`. -/
theorem odRecIncTherm (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (d r : Nat) (R : List Nat)
    (hdr : d + 1 < r) (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc)
    (hE : BitsD E) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (therm d r ++ R)))))
      (hd QNTT.WI0 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: List.replicate (d + 1) 3)))
        (3 :: (List.replicate (r - (d + 2)) 2 ++ R))) := by
  obtain ⟨m, hm⟩ : ∃ m, r - (d + 1) = m + 1 := ⟨r - (d + 2), by omega⟩
  have hm' : r - (d + 2) = m := by omega
  have h := odRecInc A F O Pf acc E 0 d (List.replicate m 2 ++ R) hA hF hacc hE
    ((sym4_rep m 2 (by simp [ALL])).app hR)
  rw [hm']
  have et : therm d r = List.replicate (d + 1) 3 ++ List.replicate (m + 1) 2 := by simp [therm, hm]
  rw [et]
  simpa [List.replicate_succ] using h

theorem bitsD_rep3 (k : Nat) : BitsD (List.replicate k 3) := by
  intro y hy; simp [List.mem_replicate] at hy; simp [hy.2]

/-- A maximal thermometer digit carries: it resets to `therm 0 r` and the scan moves to the next record. -/
theorem odCarryNextTherm (P0 : List Nat) (r : Nat) (R : List Nat) (hr : 1 ≤ r) (hP : Sym4 P0) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: List.replicate r 3) (1 :: 1 :: R))
      (hdR QNTT.ODH (P0 ++ 1 :: therm 0 r ++ [1, 1]) R) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have h := odCarryNext P0 (List.replicate (n + 1) 3) R n hP (bitsD_rep3 _) (by simp) hR
  simpa [therm] using h

/-- The overflow of the last thermometer digit: beep. -/
theorem odCarryEndTherm (P0 : List Nat) (r : Nat) (hr : 1 ≤ r) (hP : Sym4 P0) :
    znttLogic.Reach (hdR QNTT.ODJ (P0 ++ 1 :: List.replicate r 3) [])
      (hd QNTT.BEEP (P0 ++ 1 :: therm 0 r) []) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have h := odCarryEnd P0 (List.replicate (n + 1) 3) n hP (bitsD_rep3 _) (by simp)
  simpa [therm] using h

/-- A window string `0^z 1^k 0^m`; its digit is the right end `z + k` of the run of ones. -/
def winStr (z k m : Nat) : List Nat := List.replicate z 2 ++ List.replicate k 3 ++ List.replicate m 2

/-- Incrementing a window moves its right end by one (`m ≥ 1`). -/
theorem odWinInc (A : List Nat) (z k m : Nat) (R : List Nat) (hk : 1 ≤ k) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODI A (winStr z k (m + 1) ++ R))
      (hd QNTT.WI0 (A ++ List.replicate z 2 ++ List.replicate k 3) (3 :: (List.replicate m 2 ++ R))) := by
  obtain ⟨o, rfl⟩ : ∃ o, k = o + 1 := ⟨k - 1, by omega⟩
  have h := odInc A z o (List.replicate m 2 ++ R) hA ((sym4_rep m 2 (by simp [ALL])).app hR)
  simpa [winStr, List.replicate_succ] using h

/-- Record header, `acc`, `E` skipped and a full `b = 1^(n+1)` scanned: `ODJ` stands on the `M` after `b`. -/
theorem odRecToJ (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (n : Nat) (R : List Nat)
    (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc) (hE : BitsD E) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++ R)))))
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: List.replicate (n + 1) 3))) R) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hf : BitsD [F, O, Pf] := by
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hrep3 : ∀ k, Sym4 (List.replicate k 3) := fun k => sym4_rep k 3 (by simp [ALL])
  have hZ : Sym4 (List.replicate (n + 1) 3 ++ R) := (hrep3 _).app hR
  have hEs : Sym4 (E ++ 1 :: (List.replicate (n + 1) 3 ++ R)) := hE.sym4.app (Sym4.cons a1 hZ)
  have hAs : Sym4 (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++ R))) := hacc.sym4.app (Sym4.cons a1 hEs)
  have h1 := odhSkip A [F, O, Pf] _ hA hf hAs
  have hA1 : Sym4 (A ++ [F, O, Pf] ++ [1]) := (hA.app hf.sym4).app (fun y hy => by simp at hy; subst hy; exact a1)
  have h2 := odaSkip _ acc _ hA1 hacc hEs
  have hA2 : Sym4 (A ++ [F, O, Pf] ++ [1] ++ acc ++ [1]) := (hA1.app hacc.sym4).app (fun y hy => by simp at hy; subst hy; exact a1)
  have h3 := odeSkip _ E _ hA2 hE hZ
  have hA3 : Sym4 (A ++ [F, O, Pf] ++ [1] ++ acc ++ [1] ++ E ++ [1]) := (hA2.app hE.sym4).app (fun y hy => by simp at hy; subst hy; exact a1)
  have h4 := odi3 _ (List.replicate n 3 ++ R) hA3 ((hrep3 _).app hR)
  have hA4 : Sym4 (A ++ [F, O, Pf] ++ [1] ++ acc ++ [1] ++ E ++ [1] ++ [3]) := hA3.app (fun y hy => by simp at hy; subst hy; simp [ALL])
  have h5 := odjOnes _ R n hA4 hR
  simpa [List.replicate_succ] using h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem bitsD_winStr (z k m : Nat) : BitsD (winStr z k m) := by
  intro y hy; simp [winStr, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- `ODM` on the first cell of a window `u` with a zero left to flip: increment (`m ≥ 1`). -/
theorem odmWinInc (P0 : List Nat) (z k m : Nat) (R : List Nat) (hk : 1 ≤ k) (hP : Sym4 P0) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM P0 (winStr z k (m + 1) ++ R))
      (hd QNTT.WI0 (P0 ++ List.replicate z 2 ++ List.replicate k 3) (3 :: (List.replicate m 2 ++ R))) := by
  obtain ⟨o, rfl⟩ : ∃ o, k = o + 1 := ⟨k - 1, by omega⟩
  have hrep : ∀ j a, a ∈ ALL → Sym4 (List.replicate j a) := fun j a h => sym4_rep j a h
  have hU : Sym4 (List.replicate o 3 ++ 2 :: (List.replicate m 2 ++ R)) :=
    (hrep o 3 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) ((hrep m 2 (by simp [ALL])).app hR))
  cases z with
  | zero =>
    have h1 := odm3 P0 (List.replicate o 3 ++ 2 :: (List.replicate m 2 ++ R)) hP hU
    have hA : Sym4 (P0 ++ [3]) := hP.app (fun y hy => by simp at hy; subst hy; simp [ALL])
    have h2 := odjOnes _ (2 :: (List.replicate m 2 ++ R)) o hA (Sym4.cons (by simp [ALL]) ((hrep m 2 (by simp [ALL])).app hR))
    have hA2 : Sym4 (P0 ++ [3] ++ List.replicate o 3) := hA.app (hrep o 3 (by simp [ALL]))
    have h3 := odjZero _ (List.replicate m 2 ++ R) hA2 ((hrep m 2 (by simp [ALL])).app hR)
    simpa [winStr, List.replicate_succ] using h1.trans (h2.trans h3)
  | succ s =>
    have hU' : Sym4 (List.replicate s 2 ++ 3 :: (List.replicate o 3 ++ 2 :: (List.replicate m 2 ++ R))) :=
      (hrep s 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hU)
    have h1 := odm2 P0 (List.replicate s 2 ++ 3 :: (List.replicate o 3 ++ 2 :: (List.replicate m 2 ++ R))) hP hU'
    have hA : Sym4 (P0 ++ [2]) := hP.app (fun y hy => by simp at hy; subst hy; simp [ALL])
    have h2 := odInc (P0 ++ [2]) s o (List.replicate m 2 ++ R) hA ((hrep m 2 (by simp [ALL])).app hR)
    simpa [winStr, List.replicate_succ] using h1.trans h2

/-- Scan a whole window `u` (any `m`-free part) from `ODM` to `ODJ` on the cell after it. -/
theorem odmToJ (A : List Nat) (z k : Nat) (R : List Nat) (hk : 1 ≤ k) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM A (List.replicate z 2 ++ List.replicate k 3 ++ R))
      (hdR QNTT.ODJ (A ++ List.replicate z 2 ++ List.replicate k 3) R) := by
  obtain ⟨o, rfl⟩ : ∃ o, k = o + 1 := ⟨k - 1, by omega⟩
  have hrep : ∀ j a, a ∈ ALL → Sym4 (List.replicate j a) := fun j a h => sym4_rep j a h
  have hO : Sym4 (List.replicate o 3 ++ R) := (hrep o 3 (by simp [ALL])).app hR
  cases z with
  | zero =>
    have h1 := odm3 A (List.replicate o 3 ++ R) hA hO
    have hA1 : Sym4 (A ++ [3]) := hA.app (fun y hy => by simp at hy; subst hy; simp [ALL])
    have h2 := odjOnes _ R o hA1 hR
    simpa [List.replicate_succ] using h1.trans h2
  | succ s =>
    have hU : Sym4 (List.replicate s 2 ++ 3 :: (List.replicate o 3 ++ R)) :=
      (hrep s 2 (by simp [ALL])).app (Sym4.cons (by simp [ALL]) hO)
    have h1 := odm2 A _ hA hU
    have hA1 : Sym4 (A ++ [2]) := hA.app (fun y hy => by simp at hy; subst hy; simp [ALL])
    have h2 := odiZeros _ (3 :: (List.replicate o 3 ++ R)) s hA1 (Sym4.cons (by simp [ALL]) hO)
    have hA2 : Sym4 (A ++ [2] ++ List.replicate s 2) := hA1.app (hrep s 2 (by simp [ALL]))
    have h3 := odi3 _ (List.replicate o 3 ++ R) hA2 hO
    have hA3 : Sym4 (A ++ [2] ++ List.replicate s 2 ++ [3]) := hA2.app (fun y hy => by simp at hy; subst hy; simp [ALL])
    have h4 := odjOnes _ R o hA3 hR
    simpa [List.replicate_succ] using h1.trans (h2.trans (h3.trans h4))

/-- A full `u` window carries into the next record. -/
theorem odmWinNext (P0 : List Nat) (z k : Nat) (R : List Nat) (hk : 1 ≤ k) (hP : Sym4 P0) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.ODM (P0 ++ [1]) (winStr z k 0 ++ 1 :: 1 :: R))
      (hdR QNTT.ODH (P0 ++ 1 :: 3 :: List.replicate (z + k - 1) 2 ++ [1, 1]) R) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hP1 : Sym4 (P0 ++ [1]) := hP.app (fun y hy => by simp at hy; subst hy; exact a1)
  have h1 := odmToJ (P0 ++ [1]) z k (1 :: 1 :: R) hk hP1 (Sym4.cons a1 (Sym4.cons a1 hR))
  have h2 := odCarryNext P0 (List.replicate z 2 ++ List.replicate k 3) R (z + k - 1) hP
    (by intro y hy; simp [List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp)
    (by simp; omega) hR
  simpa [winStr] using h1.trans (by simpa using h2)

/-- A full `u` window at the last record overflows: beep. -/
theorem odmWinEnd (P0 : List Nat) (z k : Nat) (hk : 1 ≤ k) (hP : Sym4 P0) :
    znttLogic.Reach (hdR QNTT.ODM (P0 ++ [1]) (winStr z k 0))
      (hd QNTT.BEEP (P0 ++ 1 :: 3 :: List.replicate (z + k - 1) 2) []) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hP1 : Sym4 (P0 ++ [1]) := hP.app (fun y hy => by simp at hy; subst hy; exact a1)
  have h1 := odmToJ (P0 ++ [1]) z k [] hk hP1 Sym4.nil
  have h2 := odCarryEnd P0 (List.replicate z 2 ++ List.replicate k 3) (z + k - 1) hP
    (by intro y hy; simp [List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp)
    (by simp; omega)
  simpa [winStr] using h1.trans (by simpa using h2)

/-- A whole record whose `b` and `u` digits are both maximal: both reset, the carry moves on. -/
theorem odRecCarryNext (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (n z k : Nat) (R : List Nat)
    (hk : 1 ≤ k) (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc) (hE : BitsD E)
    (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: (winStr z k 0 ++ 1 :: 1 :: R))))))
      (hdR QNTT.ODH (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (3 :: List.replicate n 2 ++
        1 :: 3 :: List.replicate (z + k - 1) 2 ++ [1, 1])))) R) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hf : BitsD [F, O, Pf] := by
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hU : Sym4 (winStr z k 0 ++ 1 :: 1 :: R) :=
    (bitsD_winStr z k 0).sym4.app (Sym4.cons a1 (Sym4.cons a1 hR))
  have h1 := odRecToJ A F O Pf acc E n (1 :: (winStr z k 0 ++ 1 :: 1 :: R)) hA hF hacc hE (Sym4.cons a1 hU)
  have hP0 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) :=
    (hA.app hf.sym4).app (Sym4.cons a1 (hacc.sym4.app (Sym4.cons a1 hE.sym4)))
  have h2 := odCarry (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) (List.replicate (n + 1) 3)
    (winStr z k 0 ++ 1 :: 1 :: R) n hP0 (bitsD_rep3 _) (by simp) hU
  have hP1 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2) :=
    hP0.app (Sym4.cons a1 (Sym4.cons (by simp [ALL]) (sym4_rep n 2 (by simp [ALL]))))
  have h3 := odmWinNext _ z k R hk hP1 hR
  have h1' : znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: (winStr z k 0 ++ 1 :: 1 :: R))))))
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: (winStr z k 0 ++ 1 :: 1 :: R))) := by simpa using h1
  have h2' : znttLogic.Reach
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: (winStr z k 0 ++ 1 :: 1 :: R)))
      (hdR QNTT.ODM (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2 ++ [1])
        (winStr z k 0 ++ 1 :: 1 :: R)) := by simpa using h2
  simpa using h1'.trans (h2'.trans (by simpa using h3))

/-- A record whose `b` is maximal and whose `u` can still grow: `b` resets, `u` moves one step. -/
theorem odRecCarryInc (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (n z k m : Nat) (R : List Nat)
    (hk : 1 ≤ k) (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc) (hE : BitsD E)
    (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: (winStr z k (m + 1) ++ R))))))
      (hd QNTT.WI0 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (3 :: List.replicate n 2 ++
        1 :: (List.replicate z 2 ++ List.replicate k 3))))) (3 :: (List.replicate m 2 ++ R))) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hf : BitsD [F, O, Pf] := by
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hU : Sym4 (winStr z k (m + 1) ++ R) := (bitsD_winStr z k (m + 1)).sym4.app hR
  have h1 := odRecToJ A F O Pf acc E n (1 :: (winStr z k (m + 1) ++ R)) hA hF hacc hE (Sym4.cons a1 hU)
  have hP0 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) :=
    (hA.app hf.sym4).app (Sym4.cons a1 (hacc.sym4.app (Sym4.cons a1 hE.sym4)))
  have h2 := odCarry (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) (List.replicate (n + 1) 3)
    (winStr z k (m + 1) ++ R) n hP0 (bitsD_rep3 _) (by simp) hU
  have hP1 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2) :=
    hP0.app (Sym4.cons a1 (Sym4.cons (by simp [ALL]) (sym4_rep n 2 (by simp [ALL]))))
  have h3 := odmWinInc (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2 ++ [1]) z k m R hk
    (hP1.app (fun y hy => by simp at hy; subst hy; exact a1)) hR
  have h1' : znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: (winStr z k (m + 1) ++ R))))))
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: (winStr z k (m + 1) ++ R))) := by simpa using h1
  have h2' : znttLogic.Reach
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: (winStr z k (m + 1) ++ R)))
      (hdR QNTT.ODM (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2 ++ [1])
        (winStr z k (m + 1) ++ R)) := by simpa using h2
  have key := h1'.trans (h2'.trans h3)
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using key

/-- The last record with both digits maximal: the odometer overflows and beeps. -/
theorem odRecCarryEnd (A : List Nat) (F O Pf : Nat) (acc E : List Nat) (n z k : Nat)
    (hk : 1 ≤ k) (hA : Sym4 A) (hF : [F, O, Pf].all (· ∈ [2, 3]) = true) (hacc : BitsD acc) (hE : BitsD E) :
    znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: winStr z k 0)))))
      (hd QNTT.BEEP (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (3 :: List.replicate n 2 ++
        1 :: 3 :: List.replicate (z + k - 1) 2)))) []) := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hf : BitsD [F, O, Pf] := by
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hU : Sym4 (winStr z k 0) := (bitsD_winStr z k 0).sym4
  have h1 := odRecToJ A F O Pf acc E n (1 :: winStr z k 0) hA hF hacc hE (Sym4.cons a1 hU)
  have hP0 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) :=
    (hA.app hf.sym4).app (Sym4.cons a1 (hacc.sym4.app (Sym4.cons a1 hE.sym4)))
  have h2 := odCarry (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E)) (List.replicate (n + 1) 3)
    (winStr z k 0) n hP0 (bitsD_rep3 _) (by simp) hU
  have hP1 : Sym4 (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2) :=
    hP0.app (Sym4.cons a1 (Sym4.cons (by simp [ALL]) (sym4_rep n 2 (by simp [ALL]))))
  have h3 := odmWinEnd (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2) z k hk hP1
  have h1' : znttLogic.Reach
      (hdR QNTT.ODH A ([F, O, Pf] ++ 1 :: (acc ++ 1 :: (E ++ 1 :: (List.replicate (n + 1) 3 ++
        1 :: winStr z k 0)))))
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: winStr z k 0)) := by simpa using h1
  have h2' : znttLogic.Reach
      (hdR QNTT.ODJ (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: List.replicate (n + 1) 3)
        (1 :: winStr z k 0))
      (hdR QNTT.ODM (A ++ [F, O, Pf] ++ 1 :: (acc ++ 1 :: E) ++ 1 :: 3 :: List.replicate n 2 ++ [1])
        (winStr z k 0)) := by simpa using h2
  have key := h1'.trans (h2'.trans h3)
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using key

/-! ## Odometer on a record list -/

structure ORec where
  F : Nat
  O : Nat
  Pf : Nat
  acc : List Nat
  E : List Nat
  d : Nat
  r : Nat
  z : Nat
  k : Nat
  m : Nat

def ORec.tape (o : ORec) : List Nat :=
  [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (therm o.d o.r ++ 1 :: winStr o.z o.k o.m)))

def sepRest : List ORec → List Nat
  | [] => []
  | o :: os => 1 :: 1 :: (o.tape ++ sepRest os)

def tapeL : List ORec → List Nat
  | [] => []
  | o :: os => o.tape ++ sepRest os

structure ORec.Ok (o : ORec) : Prop where
  hF : [o.F, o.O, o.Pf].all (· ∈ [2, 3]) = true
  acc : BitsD o.acc
  E : BitsD o.E
  d : o.d + 1 ≤ o.r
  k : 1 ≤ o.k
  Elen : 2 ≤ o.E.length

def ORec.next (o : ORec) : Sum ORec ORec :=
  if o.d + 1 < o.r then .inl { o with d := o.d + 1 }
  else if 1 ≤ o.m then .inl { o with d := 0, k := o.k + 1, m := o.m - 1 }
  else .inr { o with d := 0, z := 0, k := 1, m := o.z + o.k - 1 }

def odoStepR : List ORec → Option (List ORec)
  | [] => none
  | o :: os =>
    match o.next with
    | .inl o' => some (o' :: os)
    | .inr o' => (odoStepR os).map (o' :: ·)


theorem ORec.Ok.sym4 {o : ORec} (h : o.Ok) : Sym4 o.tape := by
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hf : BitsD [o.F, o.O, o.Pf] := by
    have hF := h.hF
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hth : BitsD (therm o.d o.r) := by
    intro y hy; simp [therm, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  unfold ORec.tape
  exact hf.sym4.app (Sym4.cons a1 (h.acc.sym4.app (Sym4.cons a1 (h.E.sym4.app (Sym4.cons a1
    (hth.sym4.app (Sym4.cons a1 (bitsD_winStr _ _ _).sym4)))))))

theorem sepRest_sym4 : ∀ os : List ORec, (∀ o ∈ os, o.Ok) → Sym4 (sepRest os)
  | [], _ => Sym4.nil
  | o :: os, h => by
    have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
    exact Sym4.cons a1 (Sym4.cons a1 ((h o (by simp)).sym4.app
      (sepRest_sym4 os (fun x hx => h x (by simp [hx])))))

theorem tapeL_sym4 (os : List ORec) (h : ∀ o ∈ os, o.Ok) : Sym4 (tapeL os) := by
  cases os with
  | nil => exact Sym4.nil
  | cons o os => exact (h o (by simp)).sym4.app (sepRest_sym4 os (fun x hx => h x (by simp [hx])))

theorem odoInc1 (o o' : ORec) (os : List ORec) (A : List Nat) (hO : o.Ok) (hos : ∀ x ∈ os, x.Ok)
    (hA : Sym4 A) (hc : o.d + 1 < o.r) (ho' : o' = { o with d := o.d + 1 }) :
    ∃ X R, X ++ 3 :: R = A ++ tapeL (o' :: os) ∧
      znttLogic.Reach (hdR QNTT.ODH A (tapeL (o :: os))) (hd QNTT.WI0 X (3 :: R)) := by
  subst ho'
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have hR : Sym4 (1 :: (winStr o.z o.k o.m ++ sepRest os)) :=
    Sym4.cons a1 ((bitsD_winStr _ _ _).sym4.app (sepRest_sym4 os hos))
  have h := odRecIncTherm A o.F o.O o.Pf o.acc o.E o.d o.r _ hc hA hO.hF hO.acc hO.E hR
  have e : tapeL (o :: os) = [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (therm o.d o.r ++
      (1 :: (winStr o.z o.k o.m ++ sepRest os))))) := by simp [tapeL, ORec.tape]
  rw [e]
  refine ⟨_, _, ?_, h⟩
  simp [tapeL, ORec.tape, therm, List.replicate_succ']

theorem odoInc2 (o o' : ORec) (os : List ORec) (A : List Nat) (hO : o.Ok) (hos : ∀ x ∈ os, x.Ok)
    (hA : Sym4 A) (hc : ¬ o.d + 1 < o.r) (hm : 1 ≤ o.m)
    (ho' : o' = { o with d := 0, k := o.k + 1, m := o.m - 1 }) :
    ∃ X R, X ++ 3 :: R = A ++ tapeL (o' :: os) ∧
      znttLogic.Reach (hdR QNTT.ODH A (tapeL (o :: os))) (hd QNTT.WI0 X (3 :: R)) := by
  subst ho'
  obtain ⟨n, hn⟩ : ∃ n, o.r = n + 1 := ⟨o.r - 1, by have := hO.d; omega⟩
  obtain ⟨m, hm'⟩ : ∃ m, o.m = m + 1 := ⟨o.m - 1, by omega⟩
  have hd : o.d = n := by have := hO.d; omega
  have h := odRecCarryInc A o.F o.O o.Pf o.acc o.E n o.z o.k m (sepRest os) hO.k hA hO.hF hO.acc hO.E
    (sepRest_sym4 os hos)
  have e : tapeL (o :: os) = [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (List.replicate (n + 1) 3 ++
      1 :: (winStr o.z o.k (m + 1) ++ sepRest os)))) := by
    simp [tapeL, ORec.tape, therm, hd, hn, hm']
  rw [e]
  refine ⟨_, _, ?_, h⟩
  simp [tapeL, ORec.tape, therm, winStr, hn, hm', List.replicate_succ']

def ORec.reset (o : ORec) : ORec := { o with d := 0, z := 0, k := 1, m := o.z + o.k - 1 }

theorem odoCarryN (o o2 : ORec) (os2 : List ORec) (A : List Nat) (hO : o.Ok) (hos : ∀ x ∈ o2 :: os2, x.Ok)
    (hA : Sym4 A) (hc : ¬ o.d + 1 < o.r) (hm : ¬ 1 ≤ o.m) :
    znttLogic.Reach (hdR QNTT.ODH A (tapeL (o :: o2 :: os2)))
      (hdR QNTT.ODH (A ++ o.reset.tape ++ [1, 1]) (tapeL (o2 :: os2))) := by
  obtain ⟨n, hn⟩ : ∃ n, o.r = n + 1 := ⟨o.r - 1, by have := hO.d; omega⟩
  have hd : o.d = n := by have := hO.d; omega
  have hm0 : o.m = 0 := by omega
  have h := odRecCarryNext A o.F o.O o.Pf o.acc o.E n o.z o.k (tapeL (o2 :: os2)) hO.k hA hO.hF hO.acc hO.E
    (tapeL_sym4 _ hos)
  have e : tapeL (o :: o2 :: os2) = [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (List.replicate (n + 1) 3 ++
      1 :: (winStr o.z o.k 0 ++ 1 :: 1 :: tapeL (o2 :: os2))))) := by
    simp [tapeL, sepRest, ORec.tape, therm, hd, hn, hm0]
  rw [e]
  have e2 : A ++ o.reset.tape ++ [1, 1] = A ++ [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (3 :: List.replicate n 2 ++
        1 :: 3 :: List.replicate (o.z + o.k - 1) 2 ++ [1, 1]))) := by
    simp [ORec.reset, ORec.tape, therm, winStr, hn, List.replicate_succ]
  rw [e2]
  exact h

theorem odoCarryE (o : ORec) (A : List Nat) (hO : o.Ok)
    (hA : Sym4 A) (hc : ¬ o.d + 1 < o.r) (hm : ¬ 1 ≤ o.m) :
    znttLogic.Reach (hdR QNTT.ODH A (tapeL [o])) (hd QNTT.BEEP (A ++ o.reset.tape) []) := by
  obtain ⟨n, hn⟩ : ∃ n, o.r = n + 1 := ⟨o.r - 1, by have := hO.d; omega⟩
  have hd : o.d = n := by have := hO.d; omega
  have hm0 : o.m = 0 := by omega
  have h := odRecCarryEnd A o.F o.O o.Pf o.acc o.E n o.z o.k hO.k hA hO.hF hO.acc hO.E
  have e : tapeL [o] = [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (List.replicate (n + 1) 3 ++
      1 :: winStr o.z o.k 0))) := by
    simp [tapeL, sepRest, ORec.tape, therm, hd, hn, hm0]
  rw [e]
  have e2 : A ++ o.reset.tape = A ++ [o.F, o.O, o.Pf] ++ 1 :: (o.acc ++ 1 :: (o.E ++ 1 :: (3 :: List.replicate n 2 ++
        1 :: 3 :: List.replicate (o.z + o.k - 1) 2))) := by
    simp [ORec.reset, ORec.tape, therm, winStr, hn, List.replicate_succ]
  rw [e2]
  exact h


theorem ORec.Ok.reset {o : ORec} (h : o.Ok) : o.reset.Ok :=
  ⟨h.hF, h.acc, h.E, by have := h.d; simp [ORec.reset]; omega, by simp [ORec.reset], h.Elen⟩

def resetAll : List ORec → List ORec
  | [] => []
  | o :: os => o.reset :: resetAll os

theorem sepRest_resetAll_cons (o : ORec) (os : List ORec) :
    tapeL (resetAll (o :: os)) = o.reset.tape ++ sepRest (resetAll os) := rfl

theorem odoWalk : ∀ (os : List ORec) (o : ORec) (A : List Nat), (∀ x ∈ o :: os, x.Ok) → Sym4 A →
    (∀ os', odoStepR (o :: os) = some os' → ∃ X R, X ++ 3 :: R = A ++ tapeL os' ∧
      znttLogic.Reach (hdR QNTT.ODH A (tapeL (o :: os))) (hd QNTT.WI0 X (3 :: R))) ∧
    (odoStepR (o :: os) = none →
      znttLogic.Reach (hdR QNTT.ODH A (tapeL (o :: os))) (hd QNTT.BEEP (A ++ tapeL (resetAll (o :: os))) []))
  := by
  intro os
  induction os with
  | nil =>
    intro o A hok hA
    have hO := hok o (by simp)
    constructor
    · intro os' h
      unfold odoStepR at h
      by_cases hc : o.d + 1 < o.r
      · simp [ORec.next, hc] at h; subst h
        exact odoInc1 o _ [] A hO (by simp) hA hc rfl
      · by_cases hm : 1 ≤ o.m
        · simp [ORec.next, hc, hm] at h; subst h
          exact odoInc2 o _ [] A hO (by simp) hA hc hm rfl
        · simp [ORec.next, hc, hm, odoStepR] at h
    · intro h
      unfold odoStepR at h
      by_cases hc : o.d + 1 < o.r
      · simp [ORec.next, hc] at h
      · by_cases hm : 1 ≤ o.m
        · simp [ORec.next, hc, hm] at h
        · have := odoCarryE o A hO hA hc hm
          simpa [resetAll, tapeL, sepRest] using this
  | cons o2 os2 ih =>
    intro o A hok hA
    have hO := hok o (by simp)
    have hos : ∀ x ∈ o2 :: os2, x.Ok := fun x hx => hok x (by simp [hx])
    constructor
    · intro os' h
      unfold odoStepR at h
      by_cases hc : o.d + 1 < o.r
      · simp [ORec.next, hc] at h; subst h
        exact odoInc1 o _ (o2 :: os2) A hO hos hA hc rfl
      · by_cases hm : 1 ≤ o.m
        · simp [ORec.next, hc, hm] at h; subst h
          exact odoInc2 o _ (o2 :: os2) A hO hos hA hc hm rfl
        · simp [ORec.next, hc, hm] at h
          obtain ⟨l, hl, rfl⟩ := h
          have hA' : Sym4 (A ++ o.reset.tape ++ [1, 1]) :=
            (hA.app hO.reset.sym4).app (fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [ALL])
          obtain ⟨X, R, hXR, hr⟩ := (ih o2 _ hos hA').1 l hl
          refine ⟨X, R, ?_, (odoCarryN o o2 os2 A hO hos hA hc hm).trans hr⟩
          rw [hXR]
          have hne : l ≠ [] := by
            intro hl0; subst hl0
            cases os2 <;> simp [odoStepR, ORec.next] at hl <;> split at hl <;> simp_all
          obtain ⟨l1, ls, rfl⟩ := List.exists_cons_of_ne_nil hne
          simp [tapeL, sepRest, ORec.reset]
    · intro h
      unfold odoStepR at h
      by_cases hc : o.d + 1 < o.r
      · simp [ORec.next, hc] at h
      · by_cases hm : 1 ≤ o.m
        · simp [ORec.next, hc, hm] at h
        · simp [ORec.next, hc, hm] at h
          have hA' : Sym4 (A ++ o.reset.tape ++ [1, 1]) :=
            (hA.app hO.reset.sym4).app (fun y hy => by simp at hy; rcases hy with rfl | rfl <;> simp [ALL])
          have hr := (ih o2 _ hos hA').2 h
          have := (odoCarryN o o2 os2 A hO hos hA hc hm).trans hr
          simpa [resetAll, tapeL, sepRest] using this


def ORec.digs (o : ORec) : List (Nat × Nat) := [(o.d, o.r), (o.z + o.k - 1, o.z + o.k + o.m)]
def digsL (os : List ORec) : List (Nat × Nat) := os.flatMap ORec.digs

theorem odoStepR_digs : ∀ (os os' : List ORec), (∀ x ∈ os, x.Ok) → odoStepR os = some os' →
    odoNext (digsL os) = some (digsL os') := by
  intro os
  induction os with
  | nil => intro os' _ h; simp [odoStepR] at h
  | cons o os ih =>
    intro os' hok h
    have hO := hok o (by simp)
    have hd := hO.d
    have hk := hO.k
    unfold odoStepR at h
    by_cases hc : o.d + 1 < o.r
    · simp [ORec.next, hc] at h; subst h
      simp [digsL, ORec.digs, odoNext, hc]
    · by_cases hm : 1 ≤ o.m
      · simp [ORec.next, hc, hm] at h; subst h
        have hdr : o.d + 1 = o.r := by omega
        have h1 : ¬ (o.d + 1 < o.r) := hc
        have h2 : o.z + o.k - 1 + 1 < o.z + o.k + o.m := by omega
        have h3 : o.z + (o.k + 1) - 1 = o.z + o.k - 1 + 1 := by omega
        have h4 : o.z + (o.k + 1) + (o.m - 1) = o.z + o.k + o.m := by omega
        simp [digsL, ORec.digs, odoNext, h1, h2, h3, h4]
      · simp [ORec.next, hc, hm] at h
        obtain ⟨l, hl, rfl⟩ := h
        have := ih l (fun x hx => hok x (by simp [hx])) hl
        have hm0 : o.m = 0 := by omega
        have h1 : ¬ (o.d + 1 < o.r) := hc
        have h2 : ¬ (o.z + o.k - 1 + 1 < o.z + o.k + o.m) := by omega
        have h5 : o.z + o.k - 1 + 1 = o.z + o.k := by omega
        simp [digsL, ORec.digs, ORec.reset, odoNext, h1, h2] at this ⊢
        simp [h2, this, hm0]
        omega


/-! ## The pass loop -/

theorem stepN_length (r : Nat) : ∀ vs : List VR, (stepN r vs).length = vs.length := by
  induction r with
  | zero => intro vs; simp [stepN]
  | succ r ih => intro vs; rw [stepN, ih]; cases vs <;> simp [stepList]

def OutM (vs : List VR) : Prop := ∀ x ∈ vs, x.O = 3 → x.m = 0

theorem vis_om (v : VR) : v.vis.O = v.O ∧ (v.vis.m = 0 ∨ v.vis.m = v.m) := by
  unfold VR.vis; split <;> simp

theorem inc_om (v : VR) : v.inc.O = v.O ∧ v.inc.m = v.m := by simp [VR.inc]

theorem stepList_outM : ∀ vs : List VR, OutM vs → OutM (stepList vs)
  | [], _ => by simp [stepList, OutM]
  | v :: vs, h => by
    intro w hw
    simp only [stepList, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨x, hx, rfl⟩
    · intro h3
      obtain ⟨o1, o2⟩ := vis_om v.inc
      obtain ⟨i1, i2⟩ := inc_om v
      rw [o1, i1] at h3
      have := h v (by simp) h3
      rcases o2 with h0 | h0
      · exact h0
      · rw [h0, i2]; exact this
    · intro h3
      obtain ⟨o1, o2⟩ := vis_om x
      rw [o1] at h3
      have := h x (by simp [hx]) h3
      rcases o2 with h0 | h0
      · exact h0
      · rw [h0]; exact this

theorem stepN_outM (r : Nat) : ∀ vs : List VR, OutM vs → OutM (stepN r vs) := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_outM vs h)

theorem dec_outM (vs : List VR) (h : OutM vs) : OutM (vs.map VR.dec) := by
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  have := h x hx
  unfold VR.dec; split <;> simp_all


def CurInv (c : VR) : Prop :=
  c.Ok ∧ c.F = 3 ∧ (c.O = 3 → c.m = 0 ∧ ∃ e, 1 ≤ e ∧ e ≤ c.E.length ∧ c.E = fld c.E.length e)

theorem curG_inv (w : VR) (hw : w.Ok) (hm : w.O = 3 → w.m = 0) : CurInv w.curG := by
  by_cases h : w.O = 3
  · have hcur := w.cur_ok hw
    have hlen := hw.Elen
    have h1 : 1 ≤ w.E.length := by omega
    have hl : (fld w.E.length 1).length = w.E.length := fld_len _ _ h1
    have hG : w.curG = { w.cur with E := fld w.E.length 1 } := by simp [VR.curG, h]
    rw [hG]
    refine ⟨{ hcur with E := fld_bits _ _, Elen := by show 2 ≤ (fld w.E.length 1).length; omega }, by simp [VR.cur], ?_⟩
    intro _
    refine ⟨by simp [VR.cur, VR.dec]; split <;> simp [hm h], 1, Nat.le_refl _, ?_, ?_⟩
    · show 1 ≤ (fld w.E.length 1).length; omega
    · show fld w.E.length 1 = fld (fld w.E.length 1).length 1
      rw [hl]
  · have hG : w.curG = w.cur := by simp [VR.curG, h]
    rw [hG]
    refine ⟨w.cur_ok hw, by simp [VR.cur], ?_⟩
    intro h3
    exfalso
    have : w.cur.O = w.O := by simp [VR.cur, VR.dec]; split <;> simp
    exact h (this ▸ h3)


def PassCmp : Nat → Nat → List VR → Prop
  | 0, _, _ => True
  | n + 1, r, vs =>
    match stepN r vs with
    | [] => True
    | w :: ws => (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec)

theorem pm_good (Wf P2 : List Nat) (hW : BitsD Wf) (hP2 : GoodW (1 :: P2)) (p : Nat × Nat) (hp : 1 ≤ p.2) :
    GoodW (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) := by
  refine goodW_reg Wf (List.replicate p.1 2 ++ List.replicate p.2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))) ?_ hP2
  obtain ⟨q', hq'⟩ : ∃ q', p.2 = q' + 1 := ⟨p.2 - 1, by omega⟩
  simp [hq', List.replicate_succ]


def PreOk (pre : List Rc) : Prop := ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2

theorem preOk_done (pre : List Rc) (hpre : PreOk pre) (c : VR) (hc : c.Ok) (a s : Nat) :
    PreOk (pre ++ [c.done a s]) := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact hpre x hx
  · simp at hx; subst hx
    exact ⟨c.done_ok hc a s, by simp [VR.done, VR.toRcA], by simp [VR.done]⟩

theorem passLoop (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (c' : VR) (r' s' : Nat), CurInv c' ∧ PreOk pre' ∧ 1 ≤ p'.2 ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: P2)) pre' c' 0 r' s' []) []) := by
  intro n
  induction n with
  | zero =>
    intro vs c pre p r s hlen hc hvs hom hpre hp hcmp
    have : vs = [] := List.length_eq_zero_iff.mp hlen
    subst this
    exact ⟨p, pre, c, r, s, hc, hpre, hp, LTM.Reach.refl _ _⟩
  | succ n ih =>
    intro vs c pre p r s hlen hc hvs hom hpre hp hcmp
    obtain ⟨hcOk, hF, hOut⟩ := hc
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hwsOk : ∀ x ∈ ws, x.Ok := fun x hx => hok x (by simp [hx])
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have hcmp' : (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec) := by
      have := hcmp; simp only [PassCmp, hw] at this; exact this
    have hinv := curG_inv w hwOk hwm
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact y.dec_ok (hwsOk y hy)
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hPm := pm_good Wf P2 hW hP2 p hp
    by_cases hO : c.O = 2
    · have h1 := colStepN c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hcmp'.1
      obtain ⟨p', pre', c', r', s', hi, hp', hq, hr⟩ :=
        ih (ws.map VR.dec) w.curG (pre ++ [c.done r s]) p (w.k - 1) (w.w - w.k) hlenws hinv hwsOk' homws
          (preOk_done pre hpre c hcOk r s) hp hcmp'.2
      exact ⟨p', pre', c', r', s', hi, hp', hq, h1.trans hr⟩
    · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
      obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
      have hElen := hcOk.Elen
      have h1 := colStepO c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e hp he hew hE vs hvs w ws
        hw hcmp'.1
      have hb := eAdv_bounds c.E.length (r * c.n) e he hew
      have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).Ok :=
        { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
          Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen }
      obtain ⟨p', pre', c', r', s', hi, hp', hq, hr⟩ :=
        ih (ws.map VR.dec) w.curG _ (sAdv (r * c.n) p) (w.k - 1) (w.w - w.k) hlenws hinv hwsOk' homws
          (preOk_done pre hpre _ hc' r s) (sAdv_pos _ p hp) hcmp'.2
      exact ⟨p', pre', c', r', s', hi, hp', hq, h1.trans hr⟩


/-! ## The last record of a pass -/

theorem stepN_nil (r : Nat) : stepN r [] = [] := by
  induction r with
  | zero => simp [stepN]
  | succ r ih => simp [stepN, stepList, ih]

theorem lastEnd (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2 ∨ c.O = 3) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r s : Nat) :
    znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c r 0 s []) [])
      (hd QNTT.PE0 (Pm ++ tailB (pre ++ [c.done r s])) []) := by
  have h2 := curToCA0 c hc hF hO Pm hP pre hpre r s [] (by simp)
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have sE := hc.E.sym4
  have sB := hc.b.sym4
  have sU := hc.u.sym4
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR []))) := by
    simpa [tailVR] using sE.app (sym4_M (sB.app (sym4_M sU)))
  have b3 := ca0Sweep (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P]) (List.replicate r 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR []))))
    ((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P Sym4.nil))))))
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) ((s2 s).app (sym4_M sT))
  have b4 := caLast c hc (Pm ++ tailB pre) (List.replicate r 2 ++ 3 :: List.replicate s 2) (sPm.app sPre)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
    (by cases r <;> simp [List.replicate_succ])
  have hdone : (c.done r s).body = [2, c.O, c.P] ++ 1 :: ((List.replicate r 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) := by
    have e : (c.done r s).tl = (c.toRcA (List.replicate r 2 ++ 3 :: List.replicate s 2)).tl := rfl
    rw [Rc.body_eq, e, VR.toRcA_tl c hc]
    rfl
  simp only [tailB_append, tailB, hdone, List.append_nil, curTapeG, tailVR, List.map_nil, List.flatten_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at h2 b3 b4 ⊢
  refine h2.trans (b3.trans (b4.of_eq rfl ?_))
  simp

theorem lastStepN (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r s : Nat) :
    znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c 0 r s []) [])
      (hd QNTT.PE0 (Pm ++ tailB (pre ++ [c.done r s])) []) := by
  have h1 := cursorLoop c hc hF hO Pm hP pre hpre s r 0 [] (by simp)
  rw [stepN_nil, Nat.zero_add] at h1
  rw [curTapeG_eq _ _ _ hO]
  exact h1.trans (by simpa [curTapeG_eq _ _ _ hO] using lastEnd c hc hF (Or.inl hO) Pm hP pre hpre r s)


theorem lastStepO (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (hm : c.m = 0) (hn : c.n = n)
    (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s wE : Nat) (hwE : 2 ≤ wE)
    (r : Nat) (p : Nat × Nat) (e : Nat) (hp : 1 ≤ p.2) (he : 1 ≤ e) (hew : e ≤ wE) (hE : c.E = fld wE e) :
    znttLogic.Reach
      (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s []) [])
      (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3 ++ 1 :: P2)) ++
        tailB (pre ++ [({ c with E := fld wE (eAdv wE (r * n) e) } : VR).done r s])) []) := by
  have h1 := outLoop n c hc hF hO hm hn Wf hW P2 hP2 pre hpre s wE hwE r 0 p e [] (by simp) hp he hew
  have hb := eAdv_bounds wE (r * n) e he hew
  have hElen := hc.Elen
  rw [hE, fld_len _ _ hew] at hElen
  have hc' : ({ c with E := fld wE (eAdv wE (r * n) e) } : VR).Ok :=
    { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
      Elen := by show 2 ≤ (fld wE (eAdv wE (r * n) e)).length; rw [fld_len _ _ hb.2]; exact hElen }
  have hG := goodW_reg Wf (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
    (by have := sAdv_pos (r * n) p hp; obtain ⟨q', hq'⟩ : ∃ q', (sAdv (r * n) p).2 = q' + 1 := ⟨(sAdv (r * n) p).2 - 1, by omega⟩
        simp [hq', List.replicate_succ]) hP2
  have h2 := lastEnd ({ c with E := fld wE (eAdv wE (r * n) e) } : VR) hc' hF (Or.inr hO) _ hG pre hpre r s
  simp only [stepN_nil, Nat.zero_add] at h1
  refine (LTM.Reach.of_eq h1 ?_ ?_).trans h2
  · simp [curTapeG, hE, hO, List.append_assoc]
  · simp [curTapeG, hO, VR.b, VR.u, List.append_assoc, tailVR]


/-- One whole evaluation pass, ending in the check `SC` (more passes follow: `Nn = 1^(a+2) 0^b`). -/
theorem passMore (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs →
    ∃ (p' : Nat × Nat) (pre' : List Rc), PreOk pre' ∧ pre' ≠ [] ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre')) ) := by
  intro n vs c pre p r s hlen hc hvs hom hpre hp hcmp
  obtain ⟨p', pre', c', r', s', hc', hpre', hp', h1⟩ :=
    passLoop Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2 n vs c pre p r s hlen hc hvs hom hpre hp hcmp
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peMore (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) a b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], preOk_done pre' hpre' c' hcOk r' s', by simp, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen' }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, hpo, by simp, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩


/-- One whole evaluation pass, the last one (`Nn = 1 0^b`), ending in `FL0`. -/
theorem passLast (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (b : Nat)
    (hP2 : GoodW (1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs →
    ∃ (p' : Nat × Nat) (pre' : List Rc), PreOk pre' ∧ pre' ≠ [] ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre'))) := by
  intro n vs c pre p r s hlen hc hvs hom hpre hp hcmp
  obtain ⟨p', pre', c', r', s', hc', hpre', hp', h1⟩ :=
    passLoop Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2 n vs c pre p r s hlen hc hvs hom hpre hp hcmp
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peLast (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], preOk_done pre' hpre' c' hcOk r' s', by simp, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen' }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, hpo, by simp, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩



/-! ## Failure entries into `ODL` -/

theorem fl2One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.FL2 A (3 :: R)) (hd QNTT.ODL A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp5Zero (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP5 A (2 :: R)) (hd QNTT.ODL A (2 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 2, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 2, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cp5M (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CP5 A (1 :: R)) (hd QNTT.ODL A (1 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 1, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

theorem cpe3One (A R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach (hdR QNTT.CPE3 A (3 :: R)) (hd QNTT.ODL A (3 :: R)) := by
  have hV : Valid [ALL, ALL] [A, R] := Valid.cons hA (Valid.cons hR (Valid.nil _))
  exact checkFT (env := [A, R]) (E := []) (k := 4) hV trivial
    (ls := [.blk 0 .id]) (rs := [.sym 3, .blk 1 .id]) (ls' := [.blk 0 .id]) (rs' := [.sym 3, .blk 1 .id])
    (by decide +kernel) (by osimp) (by osimp) (by osimp) (by osimp)

/-! ## Bridge: odometer records to cursor records -/

/-- The record of an odometer assignment right after witness initialisation, with input flag `x`. -/
def ORec.toRc (o : ORec) (x : Nat) : Rc :=
  { F := o.F, O := o.O, Pf := x, acc := o.acc, E := 3 :: 3 :: List.replicate (o.E.length - 2) 2,
    b0 := (therm o.d o.r).headD 2, br := (therm o.d o.r).tail,
    u0 := (winStr o.z o.k o.m).headD 2, ur := (winStr o.z o.k o.m).tail }

/-- The same record in cursor form at the start of a pass. -/
def ORec.vr (o : ORec) (x : Nat) : VR :=
  { F := 2, O := o.O, P := x, w := o.acc.length, k := if x = 3 then 2 else 1,
    E := 3 :: 3 :: List.replicate (o.E.length - 2) 2, m := 0, n := o.d, s := o.r - (o.d + 1),
    a := 0, c := o.z + o.k - 1, t := o.m }

theorem restoreU_win (z k m : Nat) (hk : 1 ≤ k) :
    restoreU (winStr z k m) = List.replicate (z + k) 3 ++ List.replicate m 2 := by
  obtain ⟨o, rfl⟩ : ∃ o, k = o + 1 := ⟨k - 1, by omega⟩
  have h := restoreU_rep z (List.replicate o 3 ++ List.replicate m 2)
  have e1 : winStr z (o + 1) m = List.replicate z 2 ++ 3 :: (List.replicate o 3 ++ List.replicate m 2) := by
    simp [winStr, List.replicate_succ]
  rw [e1, h]
  have : List.replicate (z + (o + 1)) 3 = List.replicate z 3 ++ 3 :: List.replicate o 3 := by
    rw [← List.replicate_append_replicate]; simp [List.replicate_succ]
  rw [this]; simp


theorem toRc_rest (o : ORec) (x : Nat) (hk : 1 ≤ o.k) : (o.toRc x).Rest := by
  obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
  refine ⟨o.z, List.replicate j 3 ++ List.replicate o.m 2, ?_⟩
  have : (o.toRc x).u0 :: (o.toRc x).ur = winStr o.z o.k o.m := by
    simp only [ORec.toRc]
    cases h : winStr o.z o.k o.m with
    | nil => simp [winStr, hj, List.replicate_succ] at h
    | cons a l => simp
  rw [this, hj]
  simp [winStr, List.replicate_succ]

theorem accI_fld (x L : Nat) (hx : x ∈ [2, 3]) (hL : 2 ≤ L) :
    accI x L = fld L (if x = 3 then 2 else 1) := by
  simp at hx
  rcases hx with rfl | rfl
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    simp [accI, fld]
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    simp [accI, fld, List.replicate_succ]

theorem toRc_ps_vr (o : ORec) (x : Nat) (hk : 1 ≤ o.k) (hacc : 2 ≤ o.acc.length) (hx : x ∈ [2, 3]) (hd : o.d + 1 ≤ o.r) :
    1 :: 1 :: (o.toRc x).ps.body = (o.vr x).recd := by
  rw [Rc.ps_body _ (toRc_rest o x hk)]
  have hb : (o.toRc x).b0 :: (o.toRc x).br = therm o.d o.r := by
    simp only [ORec.toRc]
    cases h : therm o.d o.r with
    | nil => simp [therm] at h
    | cons a l => simp
  have hu : (o.toRc x).u0 :: (o.toRc x).ur = winStr o.z o.k o.m := by
    simp only [ORec.toRc]
    cases h : winStr o.z o.k o.m with
    | nil => obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩; simp [winStr, hj, List.replicate_succ] at h
    | cons a l => simp
  have e1 : (o.toRc x).b0 :: ((o.toRc x).br ++ 1 :: restoreU ((o.toRc x).u0 :: (o.toRc x).ur)) =
      therm o.d o.r ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2) := by
    rw [hu, restoreU_win _ _ _ hk]
    have : (o.toRc x).b0 :: ((o.toRc x).br ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2)) =
        ((o.toRc x).b0 :: (o.toRc x).br) ++ 1 :: (List.replicate (o.z + o.k) 3 ++ List.replicate o.m 2) := by simp
    rw [this, hb]
  obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
  have hu2 : o.z + o.k - 1 + 1 = o.z + o.k := by omega
  simp only [VR.recd, VR.tl, VR.b, VR.u, ORec.vr, ORec.toRc] at e1 ⊢
  simp only [List.cons_append, List.nil_append, List.replicate_zero, hu2]
  rw [accI_fld x _ hx hacc]
  rw [e1]
  simp [therm]


def BrOk (p : ORec × Nat) : Prop := 1 ≤ p.1.k ∧ 2 ≤ p.1.acc.length ∧ p.2 ∈ [2, 3] ∧ p.1.d + 1 ≤ p.1.r

theorem tailP_vr : ∀ l : List (ORec × Nat), (∀ p ∈ l, BrOk p) →
    tailP (l.map fun p => p.1.toRc p.2) = tailVR (l.map fun p => p.1.vr p.2)
  | [], _ => by simp [tailP, tailVR]
  | p :: l, h => by
    have hp := h p (by simp)
    have := toRc_ps_vr p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have ih := tailP_vr l (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, tailP, tailVR, List.flatten_cons]
    simp only [tailVR] at ih
    rw [ih, ← this]
    rfl


/-- The first record as cursor, in `VR` form: `FAL` .. `RFL`. -/
theorem faG (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    znttLogic.Reach (hd QNTT.FAL L [])
      (hd QNTT.RFL (Pm ++ [1, 1] ++ [3, w.O, w.P] ++ 1 :: (w.curG.tl ++ tailVR (ws.map VR.dec))) []) := by
  have sPm := hP.sym4
  have sMM : Sym4 (Pm ++ [1, 1]) := sPm.app (sym4_M (sym4_M Sym4.nil))
  have sB : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have h1 := falScan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := fasGood hP [] (1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) Sym4.nil (sym4_M (sym4_M sB))
  have h3 := fasMM Pm ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sPm sB
  have h4 := fa0G (Pm ++ [1, 1]) w hw ws hws sMM hcmp
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
  rw [hLe]
  simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
  exact h1.trans (h2.trans (h3.trans h4))


theorem curTapeG_tl (Pm : List Nat) (pre : List Rc) (c : VR) (hk : 1 ≤ c.k) (hkw : c.k ≤ c.w) (hF : c.F = 3)
    (vs : List VR) :
    curTapeG Pm pre c 0 (c.k - 1) (c.w - c.k) vs = Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P] ++ 1 :: (c.tl ++ tailVR vs) := by
  obtain ⟨j, hj⟩ : ∃ j, c.k = j + 1 := ⟨c.k - 1, by omega⟩
  simp [curTapeG, VR.tl, fld, hj, List.replicate_succ]

theorem curG_kw (w : VR) : w.curG.k = w.k ∧ w.curG.w = w.w := by
  by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, VR.dec, h] <;> split <;> simp_all

/-- The first record as cursor: `FAL` to the cursor tape of `passLoop`. -/
theorem faG' (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hcmp : w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    znttLogic.Reach (hd QNTT.FAL L [])
      (hd QNTT.RFL (curTapeG Pm [] w.curG 0 (w.k - 1) (w.w - w.k) (ws.map VR.dec)) []) := by
  have h := faG L Pm hL hP w hw ws hws hcmp hLe
  have hcur : w.curG.F = 3 := by
    by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, h]
  obtain ⟨k1, k2⟩ := curG_kw w
  have hOk : w.curG.k ≥ 1 := by rw [k1]; exact hw.k1
  have hkw : w.curG.k ≤ w.curG.w := by rw [k1, k2]; exact hw.kw
  have := curTapeG_tl Pm [] w.curG hOk hkw hcur (ws.map VR.dec)
  rw [k1, k2] at this
  rw [this]
  have hk : w.curG.O = w.O ∧ w.curG.P = w.P := by
    by_cases h : w.O = 3 <;> simp [VR.curG, VR.cur, VR.dec, h] <;> split <;> simp_all
  rw [hk.1, hk.2]
  simpa [tailB] using h


/-- A finished record, re-armed for the next pass with input flag `x`. -/
def VR.nextPass (c : VR) (x : Nat) : VR :=
  { F := 2, O := c.O, P := x, w := c.w, k := if x = 3 then 2 else 1, E := c.E, m := c.m, n := c.n, s := c.s,
    a := 0, c := c.a + c.c, t := c.t }

def VR.doneX (c : VR) (r s x : Nat) : Rc :=
  { F := 2, O := c.O, Pf := x, acc := List.replicate r 2 ++ 3 :: List.replicate s 2, E := c.E,
    b0 := c.b.headD 2, br := c.b.tail, u0 := c.u.headD 2, ur := c.u.tail }

theorem doneX_eq (c : VR) (r s x : Nat) : ({ c.done r s with Pf := x } : Rc) = c.doneX r s x := rfl

theorem done_ps_vr (c : VR) (hc : c.Ok) (r s x : Nat) (hrs : r + 1 + s = c.w) (hw2 : 2 ≤ c.w) (hx : x ∈ [2, 3]) :
    1 :: 1 :: (c.doneX r s x).ps.body = (c.nextPass x).recd := by
  have hrest : (c.doneX r s x).Rest := by
    have := VR.toRcA_rest c (List.replicate r 2 ++ 3 :: List.replicate s 2)
    simpa [VR.doneX, VR.toRcA, Rc.Rest] using this
  rw [Rc.ps_body _ hrest]
  have hB : (c.doneX r s x).b0 :: (c.doneX r s x).br = c.b := by
    obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hc.bne
    simp [VR.doneX, hB]
  have hU : (c.doneX r s x).u0 :: (c.doneX r s x).ur = c.u := by
    obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hc.une
    simp [VR.doneX, hU]
  have hu : c.u = winStr c.a (c.c + 1) c.t := by simp [VR.u, winStr]
  have hlen : (c.doneX r s x).acc.length = c.w := by
    simp [VR.doneX]; omega
  have e1 : (c.doneX r s x).b0 :: ((c.doneX r s x).br ++ 1 :: restoreU ((c.doneX r s x).u0 :: (c.doneX r s x).ur)) =
      c.b ++ 1 :: (List.replicate (c.a + c.c + 1) 3 ++ List.replicate c.t 2) := by
    rw [hU, hu, restoreU_win _ _ _ (by omega)]
    rw [← hB]; simp; omega
  have hE : (c.doneX r s x).E = c.E := rfl
  have hO : (c.doneX r s x).O = c.O := rfl
  have hP : (c.doneX r s x).Pf = x := rfl
  rw [hE, hO, hP, hlen, accI_fld x _ hx hw2, e1]
  simp [VR.recd, VR.tl, VR.nextPass, VR.b, VR.u, List.replicate_succ]


theorem vis_P (v : VR) : v.vis.P = v.P := by unfold VR.vis; split <;> simp
theorem inc_P (v : VR) : v.inc.P = v.P := by simp [VR.inc]
theorem dec_P (v : VR) : v.dec.P = v.P := by unfold VR.dec; split <;> simp
theorem curG_P (v : VR) : v.curG.P = v.P := by
  unfold VR.curG VR.cur VR.dec; split <;> split <;> simp

theorem stepList_P : ∀ vs : List VR, (stepList vs).map VR.P = vs.map VR.P
  | [] => by simp [stepList]
  | v :: vs => by simp [stepList, vis_P, inc_P, Function.comp_def]

theorem stepN_P (r : Nat) : ∀ vs : List VR, (stepN r vs).map VR.P = vs.map VR.P := by
  induction r with
  | zero => intro vs; simp [stepN]
  | succ r ih => intro vs; rw [stepN, ih, stepList_P]

theorem vis_w (v : VR) : v.vis.w = v.w := by unfold VR.vis; split <;> simp
theorem inc_w (v : VR) : v.inc.w = v.w := by simp [VR.inc]
theorem dec_w (v : VR) : v.dec.w = v.w := by unfold VR.dec; split <;> simp
theorem stepList_w : ∀ vs : List VR, (stepList vs).map VR.w = vs.map VR.w
  | [] => by simp [stepList]
  | v :: vs => by simp [stepList, vis_w, inc_w, Function.comp_def]
theorem stepN_w (r : Nat) : ∀ vs : List VR, (stepN r vs).map VR.w = vs.map VR.w := by
  induction r with
  | zero => intro vs; simp [stepN]
  | succ r ih => intro vs; rw [stepN, ih, stepList_w]
theorem stepN_w2 (r : Nat) (vs : List VR) (h : ∀ x ∈ vs, 2 ≤ x.w) : ∀ x ∈ stepN r vs, 2 ≤ x.w := by
  intro x hx
  have h1 : x.w ∈ (stepN r vs).map VR.w := List.mem_map_of_mem hx
  rw [stepN_w] at h1
  simp only [List.mem_map] at h1
  obtain ⟨y, hy, he⟩ := h1
  rw [← he]; exact h y hy

def outRec (c : VR) (r : Nat) : VR :=
  if c.O = 2 then c else { c with E := fld c.E.length (eAdv c.E.length (r * c.n) (c.E.count 3)) }

def outP (c : VR) (r : Nat) (p : Nat × Nat) : Nat × Nat := if c.O = 2 then p else sAdv (r * c.n) p

structure LoopOut where
  cs : List (VR × Nat × Nat)
  c' : VR
  r' : Nat
  s' : Nat
  p' : Nat × Nat

/-- The pure run of a pass loop: the finished cursor records and the final cursor. -/
def loopRun : Nat → VR → List VR → Nat → Nat → Nat × Nat → LoopOut
  | 0, c, _, r, s, p => ⟨[], c, r, s, p⟩
  | n + 1, c, vs, r, s, p =>
    match stepN r vs with
    | [] => ⟨[], c, r, s, p⟩
    | w :: ws =>
      let o := loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
      ⟨(outRec c r, r, s) :: o.cs, o.c', o.r', o.s', o.p'⟩

theorem count3_fld (len e : Nat) (h : e ≤ len) : (fld len e).count 3 = e := by
  simp [fld, List.count_replicate]

/-- `passLoop` with the bookkeeping needed to chain passes: the finished records are `done` records. -/
theorem passLoop2 (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (c' : VR) (r' s' : Nat) (cs : List (VR × Nat × Nat)), CurInv c' ∧ PreOk pre' ∧
      1 ≤ p'.2 ∧ r' + 1 + s' = c'.w ∧ 2 ≤ c'.w ∧ pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧
      (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) ++ [c'.P] = c.P :: vs.map VR.P ∧
      loopRun n c vs r s p = ⟨cs, c', r', s', p'⟩ ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: P2)) pre' c' 0 r' s' []) []) := by
  intro n
  induction n with
  | zero =>
    intro vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
    have : vs = [] := List.length_eq_zero_iff.mp hlen
    subst this
    exact ⟨p, pre, c, r, s, [], hc, hpre, hp, hrs, hcw, by simp, by simp, by simp, by simp [loopRun], LTM.Reach.refl _ _⟩
  | succ n ih =>
    intro vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
    obtain ⟨hcOk, hF, hOut⟩ := hc
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hwsOk : ∀ x ∈ ws, x.Ok := fun x hx => hok x (by simp [hx])
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have hcmp' : (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec) := by
      have := hcmp; simp only [PassCmp, hw] at this; exact this
    have hinv := curG_inv w hwOk hwm
    have hrsw : w.k - 1 + 1 + (w.w - w.k) = w.curG.w := by
      have := (curG_kw w).2; have h1 := hwOk.k1; have h2 := hwOk.kw; omega
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact y.dec_ok (hwsOk y hy)
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hwall := stepN_w2 r vs hvw
    rw [hw] at hwall
    have hcw2 : 2 ≤ w.curG.w := by rw [(curG_kw w).2]; exact hwall w (by simp)
    have hvw2 : ∀ x ∈ ws.map VR.dec, 2 ≤ x.w := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      rw [dec_w]; exact hwall y (by simp [hy])
    have hPm := pm_good Wf P2 hW hP2 p hp
    by_cases hO : c.O = 2
    · have h1 := colStepN c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hcmp'.1
      obtain ⟨p', pre', c', r', s', cs, hi, hp', hq, hrs', hcw', hpe, hcs, hPc, hRun, hr⟩ :=
        ih (ws.map VR.dec) w.curG (pre ++ [c.done r s]) p (w.k - 1) (w.w - w.k) hrsw hlenws hinv hwsOk' homws
          (preOk_done pre hpre c hcOk r s) hp hcmp'.2 hcw2 hvw2
      exact ⟨p', pre', c', r', s', (c, r, s) :: cs, hi, hp', hq, hrs', hcw', by simp [hpe],
        fun t ht => by simp at ht; rcases ht with rfl | ht; exact ⟨hcOk, hrs, hcw⟩; exact hcs t ht, (by
          have hs := stepN_P r vs
          rw [hw] at hs
          simp only [List.map_cons, List.cons_append]
          rw [hPc]
          simp only [List.map_cons] at hs
          simp [curG_P, Function.comp_def, dec_P, hs]), (by
          simp only [loopRun, hw]
          simp [outRec, outP, hO, hRun]), h1.trans hr⟩
    · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
      obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
      have hElen := hcOk.Elen
      have h1 := colStepO c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e hp he hew hE vs hvs w ws
        hw hcmp'.1
      have hb := eAdv_bounds c.E.length (r * c.n) e he hew
      have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).Ok :=
        { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
          Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen }
      obtain ⟨p', pre', c', r', s', cs, hi, hp', hq, hrs', hcw', hpe, hcs, hPc, hRun, hr⟩ :=
        ih (ws.map VR.dec) w.curG _ (sAdv (r * c.n) p) (w.k - 1) (w.w - w.k) hrsw hlenws hinv hwsOk' homws
          (preOk_done pre hpre _ hc' r s) (sAdv_pos _ p hp) hcmp'.2 hcw2 hvw2
      exact ⟨p', pre', c', r', s', (({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR), r, s) :: cs,
        hi, hp', hq, hrs', hcw', by simp [hpe],
        fun t ht => by simp at ht; rcases ht with rfl | ht; exact ⟨hc', hrs, hcw⟩; exact hcs t ht, (by
          have hs := stepN_P r vs
          rw [hw] at hs
          simp only [List.map_cons, List.cons_append]
          rw [hPc]
          simp only [List.map_cons] at hs
          simp [curG_P, Function.comp_def, dec_P, hs]), (by
          have hcount : c.E.count 3 = e := by
            have := count3_fld c.E.length e hew
            rw [← hE] at this; exact this
          simp only [loopRun, hw]
          simp [outRec, outP, hO, hRun, hcount]), h1.trans hr⟩




/-- One whole evaluation pass, ending in the check `SC` (more passes follow: `Nn = 1^(a+2) 0^b`). -/
theorem passMore2 (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (cs : List (VR × Nat × Nat)), PreOk pre' ∧ pre' ≠ [] ∧ 1 ≤ p'.2 ∧
      pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre')) ) := by
  intro n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨p', pre', c', r', s', cs, hc', hpre', hp', hrs', hcw', hpe, hcs, hPc, hRun, h1⟩ :=
    passLoop2 Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2 n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peMore (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) a b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], cs ++ [(c', r', s')], preOk_done pre' hpre' c' hcOk r' s', by simp, hp',
      by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hcOk, hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by simp [outRec, hO], by simp [outP, hO]⟩, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen' }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, cs ++ [(({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR), r', s')],
      hpo, by simp, sAdv_pos _ p' hp', by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hc'', hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by
        have hcount : c'.E.count 3 = e := by
          have := count3_fld c'.E.length e hew
          rw [← hE] at this; exact this
        simp [outRec, hO, hcount], by simp [outP, hO]⟩, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩


/-- One whole evaluation pass, the last one (`Nn = 1 0^b`), ending in `FL0`. -/
theorem passLast2 (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (b : Nat)
    (hP2 : GoodW (1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat),
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → PreOk pre → 1 ≤ p.2 → PassCmp n r vs → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) →
    ∃ (p' : Nat × Nat) (pre' : List Rc) (cs : List (VR × Nat × Nat)), PreOk pre' ∧ pre' ≠ [] ∧ 1 ≤ p'.2 ∧
      pre' = pre ++ cs.map (fun t => t.1.done t.2.1 t.2.2) ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
          pre c 0 r s vs) [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre'))) := by
  intro n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨p', pre', c', r', s', cs, hc', hpre', hp', hrs', hcw', hpe, hcs, hPc, hRun, h1⟩ :=
    passLoop2 Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2 n vs c pre p r s hrs hlen hc hvs hom hpre hp hcmp hcw hvw
  obtain ⟨hcOk, hF, hOut⟩ := hc'
  have finish : ∀ (p'' : Nat × Nat) (pre'' : List Rc), PreOk pre'' → pre'' ≠ [] → 1 ≤ p''.2 →
      znttLogic.Reach
        (hd QNTT.PE0 ((Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2))) ++
          tailB pre'') [])
        (hd QNTT.FL0 (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q))
          (1 :: 2 :: (List.replicate b 2 ++ tailB pre''))) := by
    intro p'' pre'' hpre'' hne hp''
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hG := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p'' hp''
    have hxs : ∀ y ∈ x :: xs, y.Ok := fun y hy => (hpre'' y hy).1
    have hrest : NoB (x.body ++ tailB xs) := by
      have := tailB_noB (x :: xs) hxs
      simp only [tailB, NoB_cons_iff] at this
      exact this.2.2
    have h := peLast (Wf ++ 1 :: (List.replicate p''.1 2 ++ List.replicate p''.2 3 ++ 1 :: Q)) b
      (x.body ++ tailB xs) (by simpa [List.append_assoc] using hG) hrest
    simpa [tailB, List.append_assoc] using h
  by_cases hO : c'.O = 2
  · have hPm := pm_good Wf (Q ++ [1] ++ [3] ++ List.replicate b 2) hW hP2 p' hp'
    have h2 := lastStepN c' hcOk hF hO _ hPm pre' hpre' r' s'
    exact ⟨p', pre' ++ [c'.done r' s'], cs ++ [(c', r', s')], preOk_done pre' hpre' c' hcOk r' s', by simp, hp',
      by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hcOk, hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by simp [outRec, hO], by simp [outP, hO]⟩, h1.trans
      (h2.trans (finish p' _ (preOk_done pre' hpre' c' hcOk r' s') (by simp) hp'))⟩
  · have hO3 : c'.O = 3 := by have := hcOk.O; simp at this; omega
    obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
    have hElen := hcOk.Elen
    have h2 := lastStepO c'.n c' hcOk hF hO3 hm rfl Wf hW (Q ++ [1] ++ [3] ++ List.replicate b 2) hP2
      pre' hpre' s' c'.E.length hElen r' p' e hp' he hew hE
    have hb := eAdv_bounds c'.E.length (r' * c'.n) e he hew
    have hElen' := hcOk.Elen
    rw [hE, fld_len _ _ hew] at hElen'
    have hc'' : ({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR).Ok :=
      { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
        Elen := by show 2 ≤ (fld c'.E.length (eAdv c'.E.length (r' * c'.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen' }
    have hpo := preOk_done pre' hpre' _ hc'' r' s'
    exact ⟨sAdv (r' * c'.n) p', _, cs ++ [(({ c' with E := fld c'.E.length (eAdv c'.E.length (r' * c'.n) e) } : VR), r', s')],
      hpo, by simp, sAdv_pos _ p' hp', by simp [hpe], fun t ht => by simp at ht; rcases ht with ht | rfl; exact hcs t ht; exact ⟨hc'', hrs', hcw'⟩, (by simpa using hPc), ⟨⟨cs, c', r', s', p'⟩, hRun, by
        have hcount : c'.E.count 3 = e := by
          have := count3_fld c'.E.length e hew
          rw [← hE] at this; exact this
        simp [outRec, hO, hcount], by simp [outP, hO]⟩, h1.trans (h2.trans (finish _ _ hpo (by simp) (sAdv_pos _ p' hp')))⟩


theorem goodW_inv {x : Nat} {l : List Nat} (h : GoodW (x :: l)) :
    (x ∈ [2, 3] ∧ GoodW l) ∨ (x = 1 ∧ ∃ c w, l = c :: w ∧ c ∈ [2, 3] ∧ GoodW w) := by
  cases h with
  | bit hb h' => exact Or.inl ⟨hb, h'⟩
  | mb hb h' => exact Or.inr ⟨rfl, _, _, rfl, hb, h'⟩

theorem goodW_swap_tail : ∀ (n : Nat) (u : List Nat) (b b' : Nat) (v1 v2 : List Nat), u.length = n →
    b ∈ [2, 3] → b' ∈ [2, 3] → BitsD v1 → BitsD v2 →
    GoodW (u ++ b :: v1) → GoodW (u ++ b' :: v2) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro u b b' v1 v2 hn hb hb' h1 h2 h
    cases u with
    | nil => exact GoodW.bit hb' (GoodW.bits h2)
    | cons x u =>
      simp only [List.cons_append] at h ⊢
      rcases goodW_inv h with ⟨hx, h'⟩ | ⟨rfl, c, w, hw, hc, h'⟩
      · exact GoodW.bit hx (ih u.length (by simp at hn; omega) u b b' v1 v2 rfl hb hb' h1 h2 h')
      · cases u with
        | nil =>
          exact GoodW.mb hb' (GoodW.bits h2)
        | cons c' u' =>
          simp only [List.cons_append, List.cons.injEq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          exact GoodW.mb hc (ih u'.length (by simp at hn; omega) u' b b' v1 v2 rfl hb hb' h1 h2 h')


/-- After a non-final pass with `S = 0` (`p'.1 = 0`): the check `SC` passes, the input flag moves on, and we are back in `RZ1`. -/
theorem scBridge (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre0 : List Rc) (hpre0 : ∀ x ∈ pre0, x.Ok ∧ x.acc ≠ [] ∧ x.Pf = 2) (r r2 : Rc) (hr : r.Ok) (hacc : r.acc ≠ [])
    (h3 : r.Pf = 3) (hr2 : r2.Ok) (post : List Rc) (hpost : ∀ x ∈ post, x.Ok) :
    znttLogic.Reach
      (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
        (3 :: 2 :: (List.replicate b 2 ++ tailB (pre0 ++ r :: r2 :: post))))
      (hdR QNTT.RZ1 [] (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) ++
        tailB (pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post))) := by
  have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
    have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
      (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all [List.mem_replicate])
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all [List.mem_replicate])
      (by
        have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
            1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
          simp [List.replicate_succ, List.append_assoc]
          have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
            intro a L; induction a with
            | zero => simp
            | succ a ih => simp [List.replicate_succ, ih]
          rw [key, key]
        rw [e]; exact hP2)
    simpa [List.append_assoc] using this
  have nP := hP2.noB
  simp only [NoB_cons_iff, NoB_app_iff] at nP
  have n3 : (3 : Nat) ∈ NB := by simp [NB]
  have n1 : (1 : Nat) ∈ NB := by simp [NB]
  have hnX : NoB (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3) := by
    simp only [NoB_cons_iff, NoB_app_iff]
    exact ⟨⟨hW.noB, n1, noB_rep q 3 (by simp), n1, nP.2.1.1⟩, noB_rep a 3 (by simp)⟩
  have hsY : Sym4 (3 :: 2 :: (List.replicate b 2 ++ tailB (pre0 ++ r :: r2 :: post))) := by
    have sT : Sym4 (tailB (pre0 ++ r :: r2 :: post)) := tailB_sym4 _ (fun x hx => by
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact (hpre0 x hx).1
      · exact hr
      · exact hr2
      · exact hpost x hx)
    have s2 : Sym4 (List.replicate b 2) := (BitsD.rep b 2 (by simp)).sym4
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (s2.app sT))
  have := scPm Wf hW q (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2) hG pre0 hpre0 r r2 hr hacc h3 hr2 post hpost
    _ _ (by simp [List.append_assoc]) hnX hsY
  simpa [List.append_assoc] using this


/-- After a non-final pass with `S ≠ 0` (it starts with a `0`): refuted, `ODL` with the tape unchanged on the right. -/
theorem scFail (Wf : List Nat) (hW : BitsD Wf) (S' T X Y : List Nat) (hS : BitsD S') (hT : Sym4 T)
    (hXY : X ++ Y = Wf ++ 1 :: (2 :: S' ++ T)) (hX : NoB X) (hY : Sym4 Y) :
    znttLogic.Reach (hd QNTT.SC X Y) (hd QNTT.ODL (Wf ++ [1]) (2 :: (S' ++ T))) := by
  have sW := hW.sym4
  have sS : Sym4 S' := hS.sym4
  have a2 : (2 : Nat) ∈ ALL := by simp [ALL]
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have h0 := sc0Scan X Y hX hY
  rw [hXY] at h0
  have b1 := sc1Block [] Wf (1 :: (2 :: S' ++ T)) Sym4.nil hW (by simp [*])
  have b2 := sc1M ([] ++ Wf) (2 :: S' ++ T) (by simp [*]) (by simp [*])
  have b3 := sc2Zero ([] ++ Wf ++ [1]) (S' ++ T) (by simp [*]) (by simp [*])
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h0 b1 b2 b3 ⊢
  exact h0.trans (b1.trans (b2.trans b3))


theorem goodW_rest : ∀ {u : List Nat}, GoodW u → ∃ v, Rest u v := by
  intro u h
  induction h with
  | nil => exact ⟨[], Rest.nil⟩
  | bit hb _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨_, Rest.bit hb hv⟩
  | mb hb _ ih => obtain ⟨v, hv⟩ := ih; exact ⟨_, Rest.mb hb hv⟩


/-- A failed assignment: from `ODL` on `Pm ++ 1 :: 1 :: tapeL (o :: os)` to the next assignment (`WI0`) or the overflow `BEEP`. -/
theorem odFail (u : List Nat) (hu : GoodW u) (o : ORec) (os : List ORec) (hos : ∀ x ∈ o :: os, x.Ok)
    (L R : List Nat) (hXY : L ++ R = u ++ 1 :: 1 :: tapeL (o :: os)) (hL : NoB L) (hR : Sym4 R) :
    ∃ v, Rest u v ∧
      (∀ os', odoStepR (o :: os) = some os' → ∃ X R', X ++ 3 :: R' = (v ++ [1, 1]) ++ tapeL os' ∧
        znttLogic.Reach (hd QNTT.ODL L R) (hd QNTT.WI0 X (3 :: R'))) ∧
      (odoStepR (o :: os) = none →
        znttLogic.Reach (hd QNTT.ODL L R) (hd QNTT.BEEP ((v ++ [1, 1]) ++ tapeL (resetAll (o :: os))) [])) := by
  obtain ⟨v, hv⟩ := goodW_rest hu
  refine ⟨v, hv, ?_⟩
  have sT : Sym4 (tapeL (o :: os)) := tapeL_sym4 _ (fun x hx => hos x hx)
  have a1 : (1 : Nat) ∈ ALL := by simp [ALL]
  have s1 : Sym4 (1 :: tapeL (o :: os)) := Sym4.cons a1 sT
  have h0 := odlScan L R hL hR
  rw [hXY] at h0
  have h1 := od0Walk hv [] (1 :: 1 :: tapeL (o :: os)) Sym4.nil (Sym4.cons a1 s1)
  have h2 := od0M ([] ++ v) (1 :: tapeL (o :: os)) (by simpa using hv.sym4_dst) s1
  have h3 := od0mM ([] ++ v ++ [1]) (tapeL (o :: os)) (by simpa using hv.sym4_dst.app (sym4_cell 1 (by simp))) sT
  have hw := odoWalk os o ([] ++ v ++ [1] ++ [1]) hos
    (by simpa using hv.sym4_dst.app (Sym4.cons a1 (Sym4.cons a1 Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append] at h0 h1 h2 h3 hw ⊢
  have hc := h0.trans (h1.trans (h2.trans h3))
  refine ⟨fun os' h => ?_, fun h => ?_⟩
  · obtain ⟨X, R', e, hr⟩ := hw.1 os' h
    exact ⟨X, R', by simpa using e, hc.trans hr⟩
  · have := hw.2 h
    simpa using hc.trans this


/-- A record list whose flags read `2^j 3 x :: l` splits around the input flag. -/
theorem flagSplit : ∀ (j : Nat) (pre : List Rc) (l : List Nat), pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l → l ≠ [] →
    ∃ pre0 r r2 post, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 := by
  intro j
  induction j with
  | zero =>
    intro pre l h hl
    cases pre with
    | nil => simp at h
    | cons r rs =>
      cases rs with
      | nil => simp at h; simp [h] at hl
      | cons r2 post =>
        simp [List.replicate] at h
        exact ⟨[], r, r2, post, by simp, by simp, h.1⟩
  | succ j ih =>
    intro pre l h hl
    cases pre with
    | nil => simp [List.replicate_succ] at h
    | cons x rs =>
      simp only [List.replicate_succ, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨hx, h'⟩ := h
      obtain ⟨pre0, r, r2, post, he, h0, h3⟩ := ih rs l h' hl
      refine ⟨x :: pre0, r, r2, post, by simp [he], ?_, h3⟩
      intro y hy; simp at hy; rcases hy with rfl | hy
      · exact hx
      · exact h0 y hy


/-- `SC` after a pass with `S = 0`, given the flag pattern of the finished records. -/
theorem scStep (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ []) (j : Nat) (l : List Nat)
    (hfl : pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l) (hl : l ≠ []) :
    ∃ pre0 r r2 post, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre)))
        (hdR QNTT.RZ1 [] (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) ++
          tailB (pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post))) := by
  obtain ⟨pre0, r, r2, post, he, h0, h3⟩ := flagSplit j pre l hfl hl
  refine ⟨pre0, r, r2, post, he, h0, h3, ?_⟩
  have mem : ∀ x, x ∈ pre0 ∨ x = r ∨ x = r2 ∨ x ∈ post → x ∈ pre := by
    intro x hx; rw [he]; simpa using hx
  have := scBridge Wf hW Q a b q hP2 pre0 (fun x hx => ⟨(hpre x (mem x (Or.inl hx))).1, (hpre x (mem x (Or.inl hx))).2, h0 x hx⟩)
    r r2 (hpre r (mem r (Or.inr (Or.inl rfl)))).1 (hpre r (mem r (Or.inr (Or.inl rfl)))).2 h3
    (hpre r2 (mem r2 (Or.inr (Or.inr (Or.inl rfl))))).1 post (fun x hx => (hpre x (mem x (Or.inr (Or.inr (Or.inr hx))))).1)
  rw [he]; exact this


/-- The pass start from `RZ1` at the left end. -/
theorem passStartRZ1 (Pm : List Nat) (hP : GoodW Pm) (r : Rc) (hr : r.PS)
    (rs : List Rc) (hrs : ∀ x ∈ rs, x.PS) :
    znttLogic.Reach (hdR QNTT.RZ1 [] (Pm ++ 1 :: 1 :: (r.body ++ tailB rs)))
      (hd QNTT.FAL (Pm ++ [1, 1] ++ r.ps.body ++ tailP rs) []) := by
  have sT : Sym4 (r.body ++ tailB rs) :=
    (r.body_sym4 hr.ok).app (tailB_sym4 rs (fun x hx => (hrs x hx).ok))
  have h2 := rz1Good hP [] (1 :: 1 :: (r.body ++ tailB rs)) Sym4.nil (sym4_M (sym4_M sT))
  have h3 := rz1MM Pm (r.body ++ tailB rs) hP.sym4 sT
  have h4 := passStart rs hrs r hr (Pm ++ [1, 1]) (hP.sym4.app (sym4_M (sym4_M Sym4.nil)))
  simp only [List.nil_append, List.append_assoc, List.cons_append, List.append_nil] at h2 h3 h4 ⊢
  exact h2.trans (h3.trans h4)


theorem Rc.PS.withPf {r : Rc} (h : r.PS) (x : Nat) (hx : x ∈ [2, 3]) : ({ r with Pf := x } : Rc).PS :=
  { ok := { h.ok with Pf := hx }, acc2 := h.acc2, rest := h.rest }

/-- From `SC` after a pass with `S = 0` to the start of the next pass (`FAL`). -/
theorem scStart (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (pre : List Rc) (hps : ∀ x ∈ pre, x.PS) (j : Nat) (l : List Nat)
    (hfl : pre.map Rc.Pf = List.replicate j 2 ++ 3 :: l) (hl : l ≠ []) (hq : 1 ≤ q) :
    ∃ pre0 r r2 post r0 rs, pre = pre0 ++ r :: r2 :: post ∧ (∀ x ∈ pre0, x.Pf = 2) ∧ r.Pf = 3 ∧
      pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post = r0 :: rs ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB pre)))
        (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
          [1, 1] ++ r0.ps.body ++ tailP rs) []) := by
  obtain ⟨pre0, r, r2, post, he, hp0, hp3, h1⟩ := scStep Wf hW Q a b q hP2 pre
    (fun x hx => ⟨(hps x hx).ok, fun h => by have := (hps x hx).acc2; simp [h] at this⟩) j l hfl hl
  have mem : ∀ x, (x ∈ pre0 ∨ x = r ∨ x = r2 ∨ x ∈ post) → x ∈ pre := by
    intro x hx; rw [he]; simpa using hx
  have hpsN : ∀ x ∈ pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post, x.PS := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · exact hps x (mem x (Or.inl hx))
    · exact (hps r (mem r (Or.inr (Or.inl rfl)))).withPf 2 (by simp)
    · exact (hps r2 (mem r2 (Or.inr (Or.inr (Or.inl rfl))))).withPf 3 (by simp)
    · exact hps x (mem x (Or.inr (Or.inr (Or.inr hx))))
  obtain ⟨r0, rs, hr0⟩ : ∃ r0 rs, pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post = r0 :: rs := by
    cases pre0 with
    | nil => exact ⟨_, _, rfl⟩
    | cons x xs => exact ⟨x, xs ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post, rfl⟩
  refine ⟨pre0, r, r2, post, r0, rs, he, hp0, hp3, hr0, ?_⟩
  have hGP : GoodW (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) := by
    have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
      have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
        (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
        (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
        (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
        (by
          have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
              1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
            simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
            have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
              intro a L; induction a with
              | zero => simp
              | succ a ih => simp [List.replicate_succ, ih]
            rw [key, key]
          rw [e]; exact hP2)
      simpa [List.append_assoc] using this
    exact goodW_reg Wf (List.replicate q 3) _ hW (BitsD.rep q 3 (by simp))
      (by intro h; have := congrArg List.length h; simp at this; omega) hG
  have h2 := passStartRZ1 _ hGP r0 (hpsN r0 (by rw [hr0]; simp)) rs (fun x hx => hpsN x (by rw [hr0]; simp [hx]))
  rw [hr0] at h1
  simp only [tailB, List.append_assoc, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2


theorem VR.nextPass_ok (c : VR) (hc : c.Ok) (x : Nat) (hx : x ∈ [2, 3]) (hw2 : 2 ≤ c.w) : (c.nextPass x).Ok :=
  { F := by simp [VR.nextPass], O := hc.O, P := hx,
    k1 := by simp only [VR.nextPass]; split <;> omega,
    kw := by simp only [VR.nextPass]; split <;> omega,
    E := hc.E, Elen := hc.Elen }

theorem tailVR_doneX : ∀ l : List ((VR × Nat × Nat) × Nat),
    (∀ p ∈ l, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3]) →
    tailP (l.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) = tailVR (l.map fun p => p.1.1.nextPass p.2)
  | [], _ => by simp [tailP, tailVR]
  | p :: l, h => by
    have hp := h p (by simp)
    have := done_ps_vr p.1.1 hp.1 p.1.2.1 p.1.2.2 p.2 hp.2.1 hp.2.2.1 hp.2.2.2
    have ih := tailVR_doneX l (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, tailP, tailVR, List.flatten_cons]
    simp only [tailVR] at ih
    rw [ih, ← this]
    simp


/-- The start of the next pass: from `FAL` on the finished records (with their new input flags) to the first cursor. -/
theorem faNext (Pm : List Nat) (hP : GoodW Pm) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat))
    (h : ∀ p ∈ t0 :: ts, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3])
    (hcmp : (t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧
      (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k) :
    znttLogic.Reach
      (hd QNTT.FAL (Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])
      (hd QNTT.RFL (curTapeG Pm [] (t0.1.1.nextPass t0.2).curG 0 ((t0.1.1.nextPass t0.2).k - 1)
        ((t0.1.1.nextPass t0.2).w - (t0.1.1.nextPass t0.2).k)
        ((ts.map fun p => p.1.1.nextPass p.2).map VR.dec)) []) := by
  have h0 := h t0 (by simp)
  have hws : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    have := h p (by simp [hp]); exact VR.nextPass_ok _ this.1 _ this.2.2.2 this.2.2.1
  have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
  have e1 := done_ps_vr t0.1.1 h0.1 t0.1.2.1 t0.1.2.2 t0.2 h0.2.1 h0.2.2.1 h0.2.2.2
  have e2 := tailVR_doneX ts (fun p hp => h p (by simp [hp]))
  have hLe : Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2))) =
      Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) := by
    rw [e2]
    have := congrArg (fun l => Pm ++ l ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)) e1
    simp only [VR.recd, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    simpa using this.symm
  have hL : NoB (Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)))) := by
    have := NoB_app_iff.2 ⟨hP.noB, NoB_app_iff.2 ⟨hw.recd_noB, tailVR_noB _ hws⟩⟩
    simpa [VR.recd, List.append_assoc] using this
  rw [← hLe]
  exact faG' _ Pm hL hP _ hw _ hws hcmp rfl


def retagPf (r : Rc) (x : Nat) : Rc := { r with Pf := x }

theorem retag_self : ∀ post : List Rc, List.zipWith retagPf post (post.map Rc.Pf) = post
  | [] => rfl
  | x :: xs => by simp [List.zipWith, retagPf, retag_self xs]

theorem retagMove : ∀ (pre0 : List Rc) (j : Nat), pre0.map Rc.Pf = List.replicate j 2 →
    ∀ (r r2 : Rc) (post : List Rc) (l' : List Nat), post.map Rc.Pf = l' →
    List.zipWith retagPf (pre0 ++ r :: r2 :: post) (List.replicate (j + 1) 2 ++ 3 :: l') =
      pre0 ++ { r with Pf := 2 } :: { r2 with Pf := 3 } :: post
  | [], j, h, r, r2, post, l', hp => by
    have : j = 0 := by have := congrArg List.length h; simpa using this.symm
    subst this
    simp [List.zipWith, retagPf, ← hp, retag_self]
  | x :: xs, j, h, r, r2, post, l', hp => by
    cases j with
    | zero => simp at h
    | succ j =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨hx, hxs⟩ := h
      have ih := retagMove xs j (by simpa [List.replicate_succ] using hxs) r r2 post l' hp
      simp only [List.replicate_succ, List.cons_append, List.zipWith_cons_cons, List.cons_append] at ih ⊢
      rw [ih]
      have hx' : ({ x with Pf := 2 } : Rc) = x := by
        rcases x with ⟨F, O, Pf, acc, E, b0, br, u0, ur⟩
        simp at hx; subst hx; rfl
      simp [retagPf, hx']

theorem doneX_zip : ∀ (cs : List (VR × Nat × Nat)) (xs : List Nat), cs.length = xs.length →
    ((cs.zip xs).map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) =
      List.zipWith retagPf (cs.map fun t => t.1.done t.2.1 t.2.2) xs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, x :: xs, h => by
    have ih := doneX_zip cs xs (by simpa using h)
    simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons]
    rw [ih]
    simp [retagPf, VR.doneX, VR.done, VR.toRcA]


theorem flags_split : ∀ (pre0 : List Rc), (∀ x ∈ pre0, x.Pf = 2) → ∀ (j : Nat) (rest rest' : List Nat),
    pre0.map Rc.Pf ++ 3 :: rest = List.replicate j 2 ++ 3 :: rest' →
    pre0.map Rc.Pf = List.replicate j 2 ∧ rest = rest'
  | [], _, j, rest, rest', h => by
    cases j with
    | zero => simp at h; exact ⟨rfl, h⟩
    | succ j => simp [List.replicate_succ] at h
  | x :: xs, hx, j, rest, rest', h => by
    cases j with
    | zero => have := hx x (by simp); simp at h; omega
    | succ j =>
      simp only [List.map_cons, List.cons_append, List.replicate_succ, List.cons.injEq] at h
      have ih := flags_split xs (fun y hy => hx y (by simp [hy])) j rest rest' h.2
      refine ⟨?_, ih.2⟩
      simp [List.replicate_succ, ih.1, hx x (by simp)]

theorem VR.done_ps (c : VR) (hc : c.Ok) (r s : Nat) (hrs : r + 1 + s = c.w) (hw2 : 2 ≤ c.w) : (c.done r s).PS :=
  { ok := c.done_ok hc r s,
    acc2 := by simp [VR.done, VR.toRcA]; omega,
    rest := by
      have := VR.toRcA_rest c (List.replicate r 2 ++ 3 :: List.replicate s 2)
      simpa [VR.done, VR.toRcA, Rc.Rest] using this }

/-- `SC` after a non-final pass with `S = 0`, from the finished (`done`) records: the next pass starts at `FAL`
on the records with the moved input flags. -/
theorem scChain (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (cs : List (VR × Nat × Nat)) (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w)
    (j : Nat) (y : Nat) (l' : List Nat)
    (hfl : cs.map (fun t => t.1.P) = List.replicate j 2 ++ 3 :: y :: l') (hq : 1 ≤ q) :
    ∃ t0 ts, (cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧
      znttLogic.Reach
        (hd QNTT.SC (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: Q) ++ List.replicate a 3)
          (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
        (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
          [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
            tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) []) := by
  have hlen : cs.length = (List.replicate (j + 1) 2 ++ 3 :: l').length := by
    have := congrArg List.length hfl
    simp at this ⊢; omega
  obtain ⟨pre0, r, r2, post, r0, rs, he, hp0, hp3, hr0, h⟩ := scStart Wf hW Q a b q hP2
    (cs.map fun t => t.1.done t.2.1 t.2.2)
    (fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
      exact VR.done_ps _ (hcs t ht).1 _ _ (hcs t ht).2.1 (hcs t ht).2.2)
    j (y :: l') (by simpa [VR.done, VR.toRcA, Function.comp_def] using hfl) (by simp) hq
  have hfl' : pre0.map Rc.Pf ++ 3 :: r2.Pf :: post.map Rc.Pf = List.replicate j 2 ++ 3 :: y :: l' := by
    have := congrArg (List.map Rc.Pf) he
    rw [← hfl]
    simpa [VR.done, VR.toRcA, hp3, Function.comp_def] using this.symm
  obtain ⟨hP0, hrest⟩ := flags_split pre0 hp0 j _ _ hfl'
  have hPost : post.map Rc.Pf = l' := (by simpa using hrest : r2.Pf = y ∧ post.map Rc.Pf = l').2
  have hmove := retagMove pre0 j hP0 r r2 post l' hPost
  rw [← he, ← doneX_zip cs _ hlen] at hmove
  rw [hr0] at hmove
  obtain ⟨t0, ts, hz⟩ : ∃ t0 ts, cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts := by
    cases hz : cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') with
    | nil => rw [hz] at hmove; simp at hmove
    | cons t ts => exact ⟨t, ts, rfl⟩
  refine ⟨t0, ts, hz, ?_⟩
  rw [hz] at hmove
  simp only [List.map_cons, List.cons.injEq] at hmove
  obtain ⟨h1, h2⟩ := hmove
  rw [h1, h2]
  exact h


/-- One non-final pass from its start (no finished records yet): it either refutes (`S ≠ 0`, state `ODL`) or leads to the
start of the next pass (`FAL`, records `doneX` with the moved input flag). -/
theorem passCycle (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w)
    (j y : Nat) (l' : List Nat) (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: y :: l') :
    ∃ (p' : Nat × Nat) (cs : List (VR × Nat × Nat)), 1 ≤ p'.2 ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      ((p'.1 = 0 ∧ ∃ t0 ts, cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') = t0 :: ts ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.FAL ((Wf ++ 1 :: (List.replicate p'.2 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
            [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
              tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])) ∨
       (∃ k, p'.1 = k + 1 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.ODL (Wf ++ [1]) (2 :: (List.replicate k 2 ++ List.replicate p'.2 3 ++
            1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))))) := by
  obtain ⟨p', pre', cs, hpre', hne, hp', hpe, hcs, hPc, hLo, h1⟩ :=
    passMore2 Wf hW Q a b hP2 n vs c [] p r s hrs hlen hc hvs hom (by intro x hx; simp at hx) hp hcmp hcw hvw
  simp only [List.nil_append] at hpe
  subst hpe
  refine ⟨p', cs, hp', hcs, hPc, hLo, ?_⟩
  rcases hk : p'.1 with _ | k
  · left
    refine ⟨rfl, ?_⟩
    have hfl' : cs.map (fun t => t.1.P) = List.replicate j 2 ++ 3 :: y :: l' := by rw [hPc]; exact hfl
    obtain ⟨t0, ts, hz, h2⟩ := scChain Wf hW Q a b p'.2 hP2 cs (fun t ht => hcs t ht) j y l' hfl' hp'
    refine ⟨t0, ts, hz, ?_⟩
    rw [hk] at h1
    simp only [List.replicate_zero, List.nil_append] at h1
    exact h1.trans h2
  · right
    refine ⟨k, rfl, ?_⟩
    rw [hk] at h1
    have nP := hP2.noB
    simp only [NoB_cons_iff, NoB_app_iff] at nP
    have n1 : (1 : Nat) ∈ NB := by simp [NB]
    have n3 : (3 : Nat) ∈ NB := by simp [NB]
    have hQ : Sym4 Q := by
      have := hP2.sym4
      simp only [Sym4_cons_iff, Sym4_app_iff] at this
      exact this.2.1.1
    have nQ : NoB Q := nP.2.1.1
    have s3 : ∀ j, Sym4 (List.replicate j 3) := fun j => (BitsD.rep j 3 (by simp)).sym4
    have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
    have sT : Sym4 (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_sym4 _ (fun x hx => (hpre' x hx).1)
    have hX : NoB (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3) := by
      have n2 : (2 : Nat) ∈ NB := by simp [NB]
      simp only [NoB_cons_iff, NoB_app_iff]
      exact ⟨⟨hW.noB, n1, ⟨noB_rep _ 2 (by simp), noB_rep _ 3 (by simp)⟩, n1, nQ⟩, noB_rep a 3 (by simp)⟩
    have hY : Sym4 (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) :=
      Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) ((s2 b).app sT))
    have hT : Sym4 (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
      Sym4.cons (by simp [ALL]) ((hQ.app (s3 a)).app hY)
    have h2 := scFail Wf hW (List.replicate k 2 ++ List.replicate p'.2 3)
      (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q) ++ List.replicate a 3)
      (3 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))
      (bd_app (BitsD.rep k 2 (by simp)) (BitsD.rep _ 3 (by simp))) hT
      (by simp [List.replicate_succ, List.append_assoc]) hX hY
    simp only [List.replicate_succ, List.cons_append, List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2


/-- The last pass from its start: `S ≠ 0` succeeds (`SU1`), `S = 0` refutes (`ODL`). -/
theorem lastCycle (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (b : Nat)
    (hP2 : GoodW (1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) :
    ∃ (p' : Nat × Nat) (cs : List (VR × Nat × Nat)), 1 ≤ p'.2 ∧ (∀ t ∈ cs, t.1.Ok ∧ t.2.1 + 1 + t.2.2 = t.1.w ∧ 2 ≤ t.1.w) ∧
      cs.map (fun t => t.1.P) = c.P :: vs.map VR.P ∧
      (∃ lo : LoopOut, loopRun n c vs r s p = lo ∧ cs = lo.cs ++ [(outRec lo.c' lo.r', lo.r', lo.s')] ∧
        p' = outP lo.c' lo.r' lo.p') ∧
      ((∃ k, p'.1 = k + 1 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hdR QNTT.SU1 [] (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++
            1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))))) ∨
       (p'.1 = 0 ∧
        znttLogic.Reach
          (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ [1] ++ [3] ++ List.replicate b 2)))
            [] c 0 r s vs) [])
          (hd QNTT.ODL (Wf ++ [1]) (List.replicate p'.2 3 ++
            1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))))) := by
  obtain ⟨p', pre', cs, hpre', hne, hp', hpe, hcs, hPc, hLo, h1⟩ :=
    passLast2 Wf hW Q b hP2 n vs c [] p r s hrs hlen hc hvs hom (by intro x hx; simp at hx) hp hcmp hcw hvw
  simp only [List.nil_append] at hpe
  subst hpe
  refine ⟨p', cs, hp', hcs, hPc, hLo, ?_⟩
  have n1 : (1 : Nat) ∈ NB := by simp [NB]
  have n2 : (2 : Nat) ∈ NB := by simp [NB]
  have n3 : (3 : Nat) ∈ NB := by simp [NB]
  have nQ : NoB Q := fun x hx => hP2.noB x (by simp [hx])
  have hQ : Sym4 Q := nQ.sym4
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have sT : Sym4 (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_sym4 _ (fun x hx => (hpre' x hx).1)
  have nT : NoB (tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := tailB_noB _ (fun x hx => (hpre' x hx).1)
  have hY : Sym4 (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) :=
    Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) ((s2 b).app sT))
  have hTn : NoB (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) := by
    simp only [NoB_cons_iff, NoB_app_iff]
    exact ⟨n1, nQ, n1, n2, noB_rep b 2 (by simp), nT⟩
  have hT : Sym4 (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
    Sym4.cons (by simp [ALL]) (hQ.app hY)
  have hX0 : ∀ S : List Nat, NoB S → NoB (Wf ++ 1 :: (S ++ 1 :: Q)) := fun S hS => by
    simp only [NoB_cons_iff, NoB_app_iff]; exact ⟨hW.noB, n1, hS, n1, nQ⟩
  have sR : ∀ S : List Nat, Sym4 S → Sym4 (S ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
    fun S hS => hS.app hT
  rcases hk : p'.1 with _ | k
  · right
    refine ⟨rfl, ?_⟩
    rw [hk] at h1
    simp only [List.replicate_zero, List.nil_append] at h1
    have hX := hX0 (List.replicate p'.2 3) (noB_rep _ 3 (by simp))
    obtain ⟨q, hq⟩ : ∃ q, p'.2 = q + 1 := ⟨p'.2 - 1, by omega⟩
    have h0 := fl0Scan (Wf ++ 1 :: (List.replicate p'.2 3 ++ 1 :: Q))
      (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))) hX hY
    have sR3 : Sym4 (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))) :=
      (BitsD.rep q 3 (by simp)).sym4.app hT
    have b1 := fl1Block [] Wf (1 :: 3 :: (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))
      Sym4.nil hW (Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) sR3))
    have b2 := fl1M ([] ++ Wf) (3 :: (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))))
      (by simpa using hW.sym4) (Sym4.cons (by simp [ALL]) sR3)
    have b3 := fl2One ([] ++ Wf ++ [1]) (List.replicate q 3 ++ 1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (by simpa using hW.sym4.app (Sym4.cons (by simp [ALL]) Sym4.nil)) sR3
    rw [hq] at h1 h0 ⊢
    simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append] at h0 b1 b2 b3 h1 ⊢
    exact h1.trans (h0.trans (b1.trans (b2.trans b3)))
  · left
    refine ⟨k, rfl, ?_⟩
    rw [hk] at h1
    have hSn : NoB (List.replicate (k + 1) 2 ++ List.replicate p'.2 3) :=
      NoB_app_iff.2 ⟨noB_rep _ 2 (by simp), noB_rep _ 3 (by simp)⟩
    have h2 := flOk Wf hW (List.replicate (k + 1) 2 ++ List.replicate p'.2 3)
      (1 :: (Q ++ 1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2))))
      (Wf ++ 1 :: (List.replicate (k + 1) 2 ++ List.replicate p'.2 3 ++ 1 :: Q))
      (1 :: 2 :: (List.replicate b 2 ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)))
      (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp))) hT 0
      ⟨List.replicate k 2 ++ List.replicate p'.2 3, by simp [List.replicate_succ]⟩
      (by simp) (hX0 _ hSn) hY hTn
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact h1.trans h2


theorem outRec_m (c : VR) (r : Nat) : (outRec c r).m = c.m ∧ (outRec c r).O = c.O := by
  unfold outRec; split <;> simp

theorem loopRun_m : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, t.1.O = 3 → t.1.m = 0) ∧
    ((loopRun n c vs r s p).c'.O = 3 → (loopRun n c vs r s p).c'.m = 0) := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hom hl
    simp [loopRun, hc.2.2]
    exact fun h => (hc.2.2 h).1
  | succ n ih =>
    intro c vs r s p hc hvs hom hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact y.dec_ok (hok y (by simp [hy]))
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (curG_inv w hwOk hwm) hwsOk' homws hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · intro h3
      rw [(outRec_m c r).2] at h3
      rw [(outRec_m c r).1]
      exact (hc.2.2 h3).1
    · exact ih'.1 t ht


def nxtW (t0 : (VR × Nat × Nat) × Nat) : VR := t0.1.1.nextPass t0.2
def nxtC (t0 : (VR × Nat × Nat) × Nat) : VR := (nxtW t0).curG
def nxtVs (ts : List ((VR × Nat × Nat) × Nat)) : List VR := (ts.map fun q => q.1.1.nextPass q.2).map VR.dec
def nxtR (t0 : (VR × Nat × Nat) × Nat) : Nat := (nxtW t0).k - 1
def nxtS (t0 : (VR × Nat × Nat) × Nat) : Nat := (nxtW t0).w - (nxtW t0).k

theorem goodW_pmNext (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b q : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) (hq : 1 ≤ q) :
    GoodW (Wf ++ 1 :: (List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) := by
  have hG : GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
    have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
      (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
      (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
      (by
        have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
            1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
          simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
          have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
            intro a L; induction a with
            | zero => simp
            | succ a ih => simp [List.replicate_succ, ih]
          rw [key, key]
        rw [e]; exact hP2)
    simpa [List.append_assoc] using this
  exact goodW_reg Wf (List.replicate q 3) _ hW (BitsD.rep q 3 (by simp))
    (by intro h; have := congrArg List.length h; simp at this; omega) hG

theorem vis_m0 (v : VR) (h : v.m = 0) : v.vis.m = 0 := by unfold VR.vis; split <;> simp [h]
theorem inc_m0 (v : VR) (h : v.m = 0) : v.inc.m = 0 := by simpa [VR.inc] using h
theorem dec_m0 (v : VR) (h : v.m = 0) : v.dec.m = 0 := by unfold VR.dec; split <;> simp [h]
theorem curG_m0 (v : VR) (h : v.m = 0) : v.curG.m = 0 := by
  unfold VR.curG VR.cur VR.dec; split <;> split <;> simp [h]

theorem stepList_m0 : ∀ vs : List VR, (∀ v ∈ vs, v.m = 0) → ∀ w ∈ stepList vs, w.m = 0
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    intro w hw
    simp only [stepList, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨x, hx, rfl⟩
    · exact vis_m0 _ (inc_m0 _ (h v (by simp)))
    · exact vis_m0 _ (h x (by simp [hx]))

theorem stepN_m0 (r : Nat) : ∀ (vs : List VR), (∀ v ∈ vs, v.m = 0) → ∀ w ∈ stepN r vs, w.m = 0 := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_m0 vs h)

theorem nextPass_m (c : VR) (x : Nat) : (c.nextPass x).m = c.m := rfl

theorem loopRun_m0 : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, t.1.m = 0) ∧ (loopRun n c vs r s p).c'.m = 0 := by
  intro n
  induction n with
  | zero => intro c vs r s p hc hvs hl; simp [loopRun, hc]
  | succ n ih =>
    intro c vs r s p hc hvs hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hmz := stepN_m0 r vs hvs
    rw [hw] at hmz
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
      (curG_m0 _ (hmz w (by simp)))
      (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact dec_m0 _ (hmz y (by simp [hy])))
      hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · rw [(outRec_m c r).1]; exact hc
    · exact ih'.1 t ht


/-- A finished record as an odometer record. -/
def VR.toO (t : VR) (r s : Nat) : ORec :=
  { F := 2, O := t.O, Pf := t.P, acc := List.replicate r 2 ++ 3 :: List.replicate s 2, E := t.E,
    d := t.n, r := t.n + 1 + t.s, z := t.a, k := t.c + 1, m := t.t }

theorem VR.done_body_toO (t : VR) (ht : t.Ok) (hm : t.m = 0) (r s : Nat) :
    (t.done r s).body = (t.toO r s).tape := by
  have h1 := t.toRcA_tl ht (List.replicate r 2 ++ 3 :: List.replicate s 2)
  have h2 : (t.done r s).tl = (t.toRcA (List.replicate r 2 ++ 3 :: List.replicate s 2)).tl := rfl
  rw [Rc.body_eq, h2, h1]
  simp only [VR.done, VR.toRcA, ORec.tape, VR.toO]
  have hb : t.b = therm t.n (t.n + 1 + t.s) := by
    simp [VR.b, therm, hm]
  have hu : t.u = winStr t.a (t.c + 1) t.t := by simp [VR.u, winStr]
  rw [hb, hu]

theorem tailB_toO : ∀ (cs : List (VR × Nat × Nat)), (∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0) →
    tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (cs.map fun t => t.1.toO t.2.1 t.2.2)
  | [], _ => by simp [tailB, sepRest]
  | t :: cs, h => by
    have ih := tailB_toO cs (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, tailB, sepRest, ih]
    rw [VR.done_body_toO _ (h t (by simp)).1 (h t (by simp)).2]

theorem toO_ok (t : VR) (ht : t.Ok) (r s : Nat) (hrs : r + 1 + s = t.w) : (t.toO r s).Ok :=
  { hF := by
      have h1 := ht.O; have h2 := ht.P
      simp at h1 h2
      simp [VR.toO]; omega,
    acc := bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all),
    E := ht.E, d := by simp [VR.toO], k := by simp [VR.toO], Elen := by simpa [VR.toO] using ht.Elen }


/-- One non-final pass followed by the start of the next: either refuted (`ODL`) or the next pass's first cursor
with all invariants of the next pass. -/
theorem passStep (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w)
    (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (j y : Nat) (l' : List Nat) (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: y :: l')
    (hcmpN : ∀ t0 ts, (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts →
      (t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧
        (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k) :
    (∀ t ∈ ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]), t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) ∧ ((∃ k q, znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL (Wf ++ [1]) (2 :: (List.replicate k 2 ++ List.replicate q 3 ++
          1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++
            tailB (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
              (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.done t.2.1 t.2.2))))))) ∨
    (∃ (q : Nat) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat)), 1 ≤ q ∧ q = (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2 ∧
      (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)))
          [] (nxtC t0) 0 (nxtR t0) (nxtS t0) (nxtVs ts)) []) ∧
      nxtR t0 + 1 + nxtS t0 = (nxtC t0).w ∧ (nxtVs ts).length = n ∧ CurInv (nxtC t0) ∧ (∀ x ∈ nxtVs ts, x.Ok) ∧ OutM (nxtVs ts) ∧
      2 ≤ (nxtC t0).w ∧ (∀ x ∈ nxtVs ts, 2 ≤ x.w) ∧ (nxtC t0).m = 0 ∧ (∀ x ∈ nxtVs ts, x.m = 0) ∧
      (nxtC t0).P :: (nxtVs ts).map VR.P = List.replicate (j + 1) 2 ++ 3 :: l')) := by
  obtain ⟨p', cs, hp', hcs, hPc, hLo, hcyc⟩ := passCycle Wf hW Q a b hP2 n vs c p r s hrs hlen hc hvs hom hp hcmp hcw hvw j y l' hfl
  obtain ⟨lo, hlo, hcsEq, hpEq⟩ := hLo
  rw [hlo, ← hcsEq] at hcmpN ⊢
  have hMz : ∀ t ∈ cs, t.1.O = 3 → t.1.m = 0 := by
    have hm := loopRun_m n c vs r s p hc hvs hom hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · intro h3
      rw [(outRec_m lo.c' lo.r').2] at h3
      rw [(outRec_m lo.c' lo.r').1]
      exact hm.2 h3
  have hxs : ∀ x ∈ List.replicate (j + 1) 2 ++ 3 :: l', x ∈ [2, 3] := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | rfl | hx
    · simp
    · simp
    · have h1 : x ∈ c.P :: vs.map VR.P := by rw [hfl]; simp [hx]
      simp only [List.mem_cons, List.mem_map] at h1
      rcases h1 with rfl | ⟨v, hv, rfl⟩
      · exact hc.1.P
      · exact (hvs v hv).P
  have hmzs : ∀ t ∈ cs, t.1.m = 0 := by
    have hm := loopRun_m0 n c vs r s p hm0 hvm hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · rw [(outRec_m lo.c' lo.r').1]; exact hm.2
  refine ⟨fun t ht => ⟨(hcs t ht).1, hmzs t ht, (hcs t ht).2.1⟩, ?_⟩
  rcases hcyc with ⟨hk, t0, ts, hz, hfal⟩ | ⟨k, hk, hodl⟩
  · right
    have hzl : (cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).length = n + 1 := by
      have h1 := congrArg List.length hPc
      have h2 := congrArg List.length hfl
      simp at h1 h2 ⊢
      omega
    rw [hz] at hzl
    simp only [List.length_cons] at hzl
    have hmem : ∀ q ∈ t0 :: ts, q ∈ cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') := by
      intro q hq; rw [hz]; exact hq
    have hh : ∀ q ∈ t0 :: ts, q.1.1.Ok ∧ q.1.2.1 + 1 + q.1.2.2 = q.1.1.w ∧ 2 ≤ q.1.1.w ∧ q.2 ∈ [2, 3] := by
      intro q hq
      have := List.of_mem_zip (hmem q hq)
      have h3 := hcs q.1 this.1
      exact ⟨h3.1, h3.2.1, h3.2.2, hxs _ this.2⟩
    have h0 := hh t0 (by simp)
    have hGP := goodW_pmNext Wf hW Q a b p'.2 hP2 hp'
    have hcmp0 := hcmpN t0 ts hz
    have hfn := faNext _ hGP t0 ts hh hcmp0
    have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
    have hmz : (t0.1.1.nextPass t0.2).O = 3 → (t0.1.1.nextPass t0.2).m = 0 := by
      intro h3
      exact hMz t0.1 (List.of_mem_zip (hmem t0 (by simp))).1 (by simpa [VR.nextPass] using h3)
    refine ⟨p'.2, t0, ts, hp', by rw [hpEq], hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [nxtC, nxtW, nxtR, nxtS, nxtVs]
    · simp only [List.replicate_zero, List.nil_append]
      exact hfal.trans hfn
    · have := (curG_kw (t0.1.1.nextPass t0.2)).2
      have h1 := hw.k1; have h2 := hw.kw
      omega
    · simpa using hzl
    · exact curG_inv _ hw hmz
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
      have hq' := hh q (List.mem_cons_of_mem _ hq)
      exact VR.dec_ok _ (VR.nextPass_ok _ hq'.1 _ hq'.2.2.2 hq'.2.2.1)
    · apply dec_outM
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      intro h3
      exact hMz q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1 (by simpa [VR.nextPass] using h3)
    · rw [(curG_kw (t0.1.1.nextPass t0.2)).2]
      simpa [VR.nextPass] using h0.2.2.1
    · intro x hx
      simp only [nxtVs, List.mem_map] at hx
      obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
      have hq' := hh q (List.mem_cons_of_mem _ hq)
      rw [dec_w]
      simpa [VR.nextPass] using hq'.2.2.1
    · exact curG_m0 _ (by simpa [VR.nextPass] using hmzs t0.1 (List.of_mem_zip (hmem t0 (by simp))).1)
    · intro x hx
      simp only [nxtVs, List.mem_map] at hx
      obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
      exact dec_m0 _ (by simpa [VR.nextPass] using hmzs q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1)
    · have hs : ((cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).map Prod.snd) = List.replicate (j + 1) 2 ++ 3 :: l' := by
        rw [List.map_snd_zip]
        have h1 := congrArg List.length hPc
        have h2 := congrArg List.length hfl
        simp at h1 h2 ⊢
        omega
      rw [hz] at hs
      simp only [List.map_cons] at hs
      rw [← hs]
      simp [nxtC, nxtW, nxtVs, curG_P, dec_P, VR.nextPass, Function.comp_def]
  · left
    exact ⟨k, p'.2, hodl⟩


def passCsOf (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) : List (VR × Nat × Nat) :=
  (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
    (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]

def passQOf (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) : Nat :=
  (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2

/-- The semantic input of `m` further passes (the last one included): the compare condition of each pass. -/
def Sem : Nat → Nat → VR → List VR → Nat → Nat → Nat × Nat → Nat → List Nat → Prop
  | 0, n, _, vs, r, _, _, _, _ => PassCmp n r vs
  | m + 1, n, c, vs, r, s, p, j, L =>
    PassCmp n r vs ∧ ∀ t0 ts, (passCsOf n c vs r s p).zip (List.replicate (j + 1) 2 ++ 3 :: L.tail) = t0 :: ts →
      ((nxtW t0).O = 3 → ∃ z, 1 ≤ (nxtW t0).k ∧ (nxtW t0).E = fld ((nxtW t0).k + z) (nxtW t0).k) ∧
      Sem m n (nxtC t0) (nxtVs ts) (nxtR t0) (nxtS t0) (0, passQOf n c vs r s p) (j + 1) L.tail

/-- Tails of the tape for `m` further passes. -/
def NnTail (m b : Nat) : List Nat := List.replicate (m + 1) 3 ++ List.replicate b 2

/-- Shape of a refuted configuration: a good prefix and the finished records. -/
def OdlOut (L R : List Nat) : Prop :=
  ∃ (u : List Nat) (pre' : List Rc), GoodW u ∧ (∀ x ∈ pre', x.Ok) ∧ pre' ≠ [] ∧ L ++ R = u ++ tailB pre'

theorem goodW_shiftNn (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) :
    GoodW (1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := by
  have := goodW_swap_tail (1 :: (Q ++ List.replicate a 3)).length (1 :: (Q ++ List.replicate a 3)) 3 3
    (3 :: List.replicate b 2) (2 :: List.replicate b 2) rfl (by simp) (by simp)
    (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
    (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)
    (by
      have e : (1 :: (Q ++ List.replicate a 3)) ++ 3 :: 3 :: List.replicate b 2 =
          1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2) := by
        simp only [List.replicate_succ, List.cons_append, List.append_assoc, List.nil_append]
        have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = 3 :: (List.replicate a 3 ++ L) := by
          intro a L; induction a with
          | zero => simp
          | succ a ih => simp [List.replicate_succ, ih]
        rw [key, key]
      rw [e]; exact hP2)
  simpa [List.append_assoc] using this


/-- The digit data of a record, invariant under the pass machinery. -/
def VR.dg (v : VR) : Nat × Nat × Nat × Nat × Nat := (v.n, v.s, v.a + v.c, v.t, v.w)

theorem dg_inc (v : VR) : v.inc.dg = v.dg ∧ v.inc.m = v.m := ⟨rfl, rfl⟩

theorem dg_vis (v : VR) (h : v.m = 0) : v.vis.dg = v.dg ∧ v.vis.m = 0 := by
  unfold VR.vis; split <;> simp [VR.dg, h, *]

theorem dg_dec (v : VR) : v.dec.dg = v.dg ∧ v.dec.m = v.m := by
  unfold VR.dec; split
  · simp
  · simp [VR.dg]; omega

theorem dg_curG (v : VR) : v.curG.dg = v.dg ∧ v.curG.m = v.m := by
  have h : v.cur.dg = v.dg ∧ v.cur.m = v.m := by
    unfold VR.cur; simpa [VR.dg] using dg_dec v
  unfold VR.curG; split
  · simpa [VR.dg] using h
  · exact h

theorem dg_stepN : ∀ (r : Nat) (vs : List VR), (∀ x ∈ vs, x.m = 0) →
    ∀ w ∈ stepN r vs, (∃ x ∈ vs, w.dg = x.dg) ∧ w.m = 0 := by
  intro r
  induction r with
  | zero => intro vs h w hw; exact ⟨⟨w, hw, rfl⟩, h w hw⟩
  | succ r ih =>
    intro vs h w hw
    have h1 : ∀ x ∈ stepList vs, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
      intro x hx
      unfold stepList at hx
      cases vs with
      | nil => simp at hx
      | cons v vs' =>
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · have := dg_vis v.inc (by show v.m = 0; exact h v (by simp))
          exact ⟨⟨v, by simp, by rw [this.1]; rfl⟩, this.2⟩
        · have := dg_vis y (h y (by simp [hy]))
          exact ⟨⟨y, by simp [hy], this.1⟩, this.2⟩
    have := ih (stepList vs) (fun x hx => (h1 x hx).2) w hw
    obtain ⟨⟨x, hx, e⟩, hm⟩ := this
    exact ⟨⟨(h1 x hx).1.choose, (h1 x hx).1.choose_spec.1, by rw [e]; exact (h1 x hx).1.choose_spec.2⟩, hm⟩

theorem dg_loopRun : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    ∀ t ∈ (loopRun n c vs r s p).cs, ∃ x ∈ c :: vs, t.1.dg = x.dg := by
  intro n
  induction n with
  | zero => intro c vs r s p _ _ t ht; simp [loopRun] at ht
  | succ n ih =>
    intro c vs r s p hc hvs t ht
    unfold loopRun at ht
    split at ht
    · simp at ht
    · rename_i w ws hw
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨c, by simp, by unfold outRec; split <;> simp [VR.dg]⟩
      · have hall : ∀ x ∈ w :: ws, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
          intro x hx; rw [← hw] at hx; exact dg_stepN r vs hvs x hx
        have hwm := (hall w (by simp)).2
        have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
          (by rw [(dg_curG w).2]; exact hwm)
          (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
              rw [(dg_dec y).2]; exact (hall y (by simp [hy])).2) t ht
        obtain ⟨x, hx, e⟩ := this
        simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall w (by simp)
          exact ⟨z, by simp [hz], by rw [e, (dg_curG w).1, e2]⟩
        · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall y (by simp [hy])
          exact ⟨z, by simp [hz], by rw [e, (dg_dec y).1, e2]⟩

theorem dg_loopRun_c : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    ∃ x ∈ c :: vs, (loopRun n c vs r s p).c'.dg = x.dg ∧ (loopRun n c vs r s p).c'.m = 0 := by
  intro n
  induction n with
  | zero => intro c vs r s p hc hvs; exact ⟨c, by simp, by simp [loopRun], by simp [loopRun, hc]⟩
  | succ n ih =>
    intro c vs r s p hc hvs
    unfold loopRun
    split
    · exact ⟨c, by simp, rfl, hc⟩
    · rename_i w ws hw
      have hall : ∀ x ∈ w :: ws, (∃ y ∈ vs, x.dg = y.dg) ∧ x.m = 0 := by
        intro x hx; rw [← hw] at hx; exact dg_stepN r vs hvs x hx
      have hwm := (hall w (by simp)).2
      obtain ⟨x, hx, e, hm⟩ := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
          (by rw [(dg_curG w).2]; exact hwm)
          (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
              rw [(dg_dec y).2]; exact (hall y (by simp [hy])).2)
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall w (by simp)
        exact ⟨z, by simp [hz], by show (loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)).c'.dg = _; rw [e, (dg_curG w).1, e2], hm⟩
      · obtain ⟨⟨z, hz, e2⟩, _⟩ := hall y (by simp [hy])
        exact ⟨z, by simp [hz], by show (loopRun n w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)).c'.dg = _; rw [e, (dg_dec y).1, e2], hm⟩

theorem dg_outRec (c : VR) (r : Nat) : (outRec c r).dg = c.dg := by
  unfold outRec; split <;> simp [VR.dg]

theorem dg_nextPass (c : VR) (x : Nat) : (c.nextPass x).dg = c.dg ∧ (c.nextPass x).m = c.m := by
  simp [VR.nextPass, VR.dg]


theorem dg_stepList_pos : ∀ vs : List VR, (∀ x ∈ vs, x.m = 0) →
    (stepList vs).map VR.dg = vs.map VR.dg ∧ ∀ x ∈ stepList vs, x.m = 0
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    have hv : v.m = 0 := h v (by simp)
    have h1 := dg_vis v.inc (by show v.m = 0; exact hv)
    refine ⟨?_, ?_⟩
    · simp only [stepList, List.map_cons, List.map_map, h1.1]
      rw [(dg_inc v).1]
      congr 1
      exact List.map_congr_left (fun y hy => (dg_vis y (h y (by simp [hy]))).1)
    · intro x hx
      simp only [stepList, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact h1.2
      · exact (dg_vis y (h y (by simp [hy]))).2

theorem dg_stepN_pos (r : Nat) : ∀ vs : List VR, (∀ x ∈ vs, x.m = 0) →
    (stepN r vs).map VR.dg = vs.map VR.dg ∧ ∀ x ∈ stepN r vs, x.m = 0 := by
  induction r with
  | zero => intro vs h; exact ⟨by simp [stepN], by simpa [stepN] using h⟩
  | succ r ih =>
    intro vs h
    have h1 := dg_stepList_pos vs h
    have h2 := ih (stepList vs) h1.2
    exact ⟨by rw [stepN, h2.1, h1.1], by rw [stepN]; exact h2.2⟩

theorem dg_loopRun_pos : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    c.m = 0 → (∀ x ∈ vs, x.m = 0) → vs.length = n →
    (loopRun n c vs r s p).cs.map (fun t => t.1.dg) ++ [(loopRun n c vs r s p).c'.dg] = (c :: vs).map VR.dg := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hl
    have : vs = [] := List.length_eq_zero_iff.mp hl
    subst this; simp [loopRun]
  | succ n ih =>
    intro c vs r s p hc hvs hl
    have hlen := stepN_length r vs
    obtain ⟨hmap, hmz⟩ := dg_stepN_pos r vs hvs
    unfold loopRun
    split
    · rename_i hw
      rw [hw] at hlen; simp at hlen; omega
    · rename_i w ws hw
      rw [hw] at hmap hmz
      have hwm : w.m = 0 := hmz w (by simp)
      have hwsm : ∀ x ∈ ws, x.m = 0 := fun x hx => hmz x (by simp [hx])
      have hlws : (ws.map VR.dec).length = n := by
        rw [hw] at hlen; simp at hlen ⊢; omega
      have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p)
        (by rw [(dg_curG w).2]; exact hwm)
        (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
            rw [(dg_dec y).2]; exact hwsm y hy) hlws
      simp only [List.map_cons] at hmap
      simp only [List.map_cons, List.cons_append, List.map_map] at this ⊢
      rw [dg_outRec]
      have e : ws.map (VR.dg ∘ VR.dec) = ws.map VR.dg := List.map_congr_left (fun y _ => (dg_dec y).1)
      rw [(dg_curG w).1, e] at this
      rw [this, ← hmap]


theorem loopRun_cs_length : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    vs.length = n → (loopRun n c vs r s p).cs.length = n := by
  intro n
  induction n with
  | zero => intro c vs r s p hl; simp [loopRun]
  | succ n ih =>
    intro c vs r s p hl
    have hlen := stepN_length r vs
    unfold loopRun
    split
    · rename_i hw; rw [hw] at hlen; simp at hlen; omega
    · rename_i w ws hw
      rw [hw] at hlen; simp at hlen
      have := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (by simp; omega)
      simpa using this

theorem dg_runAll_pos (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : c.m = 0)
    (hvs : ∀ x ∈ vs, x.m = 0) (hl : vs.length = n) :
    (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.dg) = (c :: vs).map VR.dg := by
  have h := dg_loopRun_pos n c vs r s p hc hvs hl
  simp only [List.map_append, List.map_cons, List.map_nil, dg_outRec]
  simpa using h


/-- Digit data of an odometer record. -/
def ORec.dgO (o : ORec) : Nat × Nat × Nat × Nat × Nat := (o.d, o.r - o.d - 1, o.z + o.k - 1, o.m, o.acc.length)

theorem toO_dgO (t : VR) (r s : Nat) (h : r + 1 + s = t.w) : (t.toO r s).dgO = t.dg := by
  simp [VR.toO, ORec.dgO, VR.dg]; omega

def TapeOut (T : List Nat) : Prop :=
  ∃ (u : List Nat) (pre' : List Rc), GoodW u ∧ (∀ x ∈ pre', x.Ok) ∧ pre' ≠ [] ∧ T = u ++ tailB pre'

theorem tapeOut_of (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat)) (hcs : ∀ t ∈ cs, t.1.Ok)
    (hne : cs ≠ []) : TapeOut (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) :=
  ⟨u, _, hu, fun x hx => by
      simp only [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx; exact t.1.done_ok (hcs t ht) _ _,
    by simpa using hne, rfl⟩

def TapeOutO (T : List Nat) : Prop :=
  ∃ (u : List Nat) (o : ORec) (os : List ORec), GoodW u ∧ (∀ x ∈ o :: os, x.Ok) ∧ T = u ++ sepRest (o :: os)

theorem tapeOutO_of (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ []) :
    TapeOutO (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨u, t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, hu, ?_, by simp⟩
    intro x hx
    simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨q, hq, rfl⟩
    · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
    · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2

def TapeOutD (D : List (Nat × Nat × Nat × Nat × Nat)) (T : List Nat) : Prop :=
  ∃ (u : List Nat) (o : ORec) (os : List ORec), GoodW u ∧ (∀ x ∈ o :: os, x.Ok) ∧
    (∀ x ∈ o :: os, x.dgO ∈ D) ∧ T = u ++ sepRest (o :: os)

theorem TapeOutD.toO {D T} (h : TapeOutD D T) : TapeOutO T := by
  obtain ⟨u, o, os, a, b, _, c⟩ := h; exact ⟨u, o, os, a, b, c⟩

theorem TapeOutD.mono {D D' T} (h : TapeOutD D T) (hs : ∀ x ∈ D, x ∈ D') : TapeOutD D' T := by
  obtain ⟨u, o, os, a, b, c, d⟩ := h; exact ⟨u, o, os, a, b, fun x hx => hs _ (c x hx), d⟩

theorem tapeOutD_of (D : List (Nat × Nat × Nat × Nat × Nat)) (u : List Nat) (hu : GoodW u) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ [])
    (hD : ∀ t ∈ cs, t.1.dg ∈ D) :
    TapeOutD D (u ++ tailB (cs.map fun t => t.1.done t.2.1 t.2.2)) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨u, t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, hu, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · rw [toO_dgO _ _ _ (hcs t (by simp)).2.2]; exact hD t (by simp)
      · rw [toO_dgO _ _ _ (hcs q (by simp [hq])).2.2]; exact hD q (by simp [hq])

theorem tapeOutD_ex (D : List (Nat × Nat × Nat × Nat × Nat)) (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ [])
    (hD : ∀ t ∈ cs, t.1.dg ∈ D) :
    ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (∀ x ∈ o :: os, x.dgO ∈ D) ∧
      tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (o :: os) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · rw [toO_dgO _ _ _ (hcs t (by simp)).2.2]; exact hD t (by simp)
      · rw [toO_dgO _ _ _ (hcs q (by simp [hq])).2.2]; exact hD q (by simp [hq])

/-- The successful outcome: parameters `Wf 1 S 1 Q'' 1 2^b'`, then the finished records. -/
def SuOut (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Q'' : List Nat) (b : Nat) (T : List Nat) : Prop :=
  ∃ (S0 : List Nat) (o : ORec) (os : List ORec), BitsD S0 ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Q'' ++ 1 :: List.replicate b 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    T = (Wf ++ 1 :: (S0 ++ 1 :: (Q'' ++ 1 :: List.replicate b 2))) ++ sepRest (o :: os)

/-- The refuted outcome: parameters `Wf 1 S0 1 Qp 3^a' 2 2^b'` (`a' + 1 + b' = N`), then the finished records. -/
def OdOut (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Qp : List Nat) (N : Nat) (R' : List Nat) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ a' + 1 + b' = N ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ 2 :: List.replicate b' 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    (Wf ++ [1]) ++ R' = (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ 2 :: List.replicate b' 2))) ++ sepRest (o :: os)

theorem OdOut.toO {D Wf Qp N R'} (h : OdOut D Wf Qp N R') : TapeOutO ((Wf ++ [1]) ++ R') := by
  obtain ⟨S0, a', b', o, os, a, b, c, g, ok, d, e⟩ := h
  exact ⟨_, o, os, g, ok, e⟩

theorem tapeOutP_ex (cs : List (VR × Nat × Nat))
    (hcs : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) (hne : cs ≠ []) :
    ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = cs.map (fun t => t.1.dg) ∧
      tailB (cs.map fun t => t.1.done t.2.1 t.2.2) = sepRest (o :: os) := by
  rw [tailB_toO cs (fun t ht => ⟨(hcs t ht).1, (hcs t ht).2.1⟩)]
  cases cs with
  | nil => exact absurd rfl hne
  | cons t cs' =>
    refine ⟨t.1.toO t.2.1 t.2.2, cs'.map fun t => t.1.toO t.2.1 t.2.2, ?_, ?_, by simp⟩
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨q, hq, rfl⟩
      · exact toO_ok _ (hcs t (by simp)).1 _ _ (hcs t (by simp)).2.2
      · exact toO_ok _ (hcs q (by simp [hq])).1 _ _ (hcs q (by simp [hq])).2.2
    · simp only [List.map_cons, List.map_map]
      congr 1
      · exact toO_dgO _ _ _ (hcs t (by simp)).2.2
      · apply List.map_congr_left
        intro q hq
        exact toO_dgO _ _ _ (hcs q (by simp [hq])).2.2

theorem dg_runAll (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : c.m = 0)
    (hvs : ∀ x ∈ vs, x.m = 0) :
    ∀ t ∈ (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')], t.1.dg ∈ (c :: vs).map VR.dg := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · obtain ⟨x, hx, e⟩ := dg_loopRun n c vs r s p hc hvs t ht
    rw [e]; exact List.mem_map_of_mem hx
  · obtain ⟨x, hx, e, _⟩ := dg_loopRun_c n c vs r s p hc hvs
    show (outRec _ _).dg ∈ _
    rw [dg_outRec, e]; exact List.mem_map_of_mem hx

theorem nn_eq (a b : Nat) : List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2 = NnTail a (b + 1) := by
  have key : ∀ (a : Nat) (L : List Nat), List.replicate a 3 ++ 3 :: L = List.replicate (a + 1) 3 ++ L := by
    intro a L; induction a with
    | zero => simp
    | succ a ih => simp [List.replicate_succ, ih]
  rw [key]; simp [NnTail, List.replicate_succ]


/-- All passes of one assignment: the whole run either refutes (`ODL`) or succeeds (`SU1`), with a good prefix and the
finished records in both cases. -/
theorem passesRun (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat) :
    ∀ (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat),
    GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)) →
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → 1 ≤ p.2 → 2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) → c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L → m ≤ L.length → Sem m n c vs r s p j L →
    (∃ R', OdOut ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (m + 1 + b) R' ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL (Wf ++ [1]) R')) ∨
    (∃ T, SuOut ((c :: vs).map VR.dg) Wf Q'' (b + m + 1) T ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hdR QNTT.SU1 [] T)) := by
  intro m
  induction m with
  | zero =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hp hcw hvw hm0 hvm hfl hL hsem
    have e : (Q'' ++ [1]) ++ NnTail 0 b = Q'' ++ [1] ++ [3] ++ List.replicate b 2 := by simp [NnTail]
    rw [e] at hP2 ⊢
    obtain ⟨p', cs, hp', hcs, hPc, hLo, hlast⟩ := lastCycle Wf hW Q'' b hP2 n vs c p r s hrs hlen hc hvs hom hp hsem hcw hvw
    have hne : cs ≠ [] := by
      intro h; rw [h] at hPc; simp at hPc
    have hmzs : ∀ t ∈ cs, t.1.m = 0 := by
      obtain ⟨lo, hlo, hcsEq, hpEq⟩ := hLo
      have hm := loopRun_m0 n c vs r s p hm0 hvm hlen
      rw [hlo] at hm
      intro t ht
      rw [hcsEq] at ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact hm.1 t ht
      · rw [(outRec_m lo.c' lo.r').1]; exact hm.2
    have hD : cs.map (fun t => t.1.dg) = (c :: vs).map VR.dg := by
      obtain ⟨lo, hlo, hcsEq, _⟩ := hLo
      have := dg_runAll_pos n c vs r s p hm0 hvm hlen
      rw [hlo] at this; rw [hcsEq]; exact this
    have hcs' : ∀ t ∈ cs, t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w :=
      fun t ht => ⟨(hcs t ht).1, hmzs t ht, (hcs t ht).2.1⟩
    have hP2' : GoodW (1 :: (Q'' ++ 1 :: 2 :: List.replicate b 2)) := by
      have := goodW_swap_tail (1 :: (Q'' ++ [1])).length (1 :: (Q'' ++ [1])) 3 2
        (List.replicate b 2) (List.replicate b 2) rfl (by simp) (by simp)
        (BitsD.rep b 2 (by simp)) (BitsD.rep b 2 (by simp))
        (by simpa [List.append_assoc] using hP2)
      simpa [List.append_assoc] using this
    rcases hlast with ⟨k, hk, h1⟩ | ⟨hk, h1⟩
    · right
      have hu := goodW_reg Wf (List.replicate (k + 1) 2 ++ List.replicate p'.2 3) _ hW
        (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)))
        (by intro h; have := congrArg List.length h; simp at this) hP2'
      obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex cs hcs' hne
      refine ⟨_, ⟨List.replicate (k + 1) 2 ++ List.replicate p'.2 3, o, os,
        bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)), ?_, hok, hdg.trans hD, rfl⟩, ?_⟩
      · simpa [List.replicate_succ, List.append_assoc] using hu
      · rw [hex] at h1
        simpa [List.replicate_succ, List.append_assoc] using h1
    · left
      have hu := goodW_reg Wf (List.replicate p'.2 3) _ hW (BitsD.rep _ 3 (by simp))
        (by intro h; have := congrArg List.length h; simp at this; omega) hP2'
      obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex cs hcs' hne
      refine ⟨(List.replicate p'.2 3 ++ 1 :: ((Q'' ++ [1]) ++ List.replicate 0 3 ++ 2 :: List.replicate b 2)) ++
        sepRest (o :: os), ⟨List.replicate p'.2 3, 0, b, o, os, BitsD.rep _ 3 (by simp),
        by intro h; have := congrArg List.length h; simp at this; omega, by omega, ?_, hok, hdg.trans hD, ?_⟩, ?_⟩
      · simpa [List.append_assoc] using hu
      · simp [List.append_assoc]
      · rw [hex] at h1
        simpa [List.append_assoc] using h1
  | succ a ih =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hp hcw hvw hm0 hvm hfl hL hsem
    obtain ⟨y, l', rfl⟩ : ∃ y l', L = y :: l' := by
      cases L with
      | nil => simp at hL
      | cons y l' => exact ⟨y, l', rfl⟩
    have e : (Q'' ++ [1]) ++ NnTail (a + 1) b = (Q'' ++ [1]) ++ List.replicate (a + 2) 3 ++ List.replicate b 2 := by
      simp [NnTail, List.append_assoc]
    rw [e] at hP2 ⊢
    obtain ⟨hcmp, hsem'⟩ := hsem
    have hstep := passStep Wf hW (Q'' ++ [1]) a b hP2 n vs c p r s hrs hlen hc hvs hom hp hcmp hcw hvw hm0 hvm j y l' hfl
      (fun t0 ts hz => (hsem' t0 ts (by simpa [passCsOf] using hz)).1)
    obtain ⟨hcsOk, hst⟩ := hstep
    rcases hst with ⟨k, q, h1⟩ | ⟨q, t0, ts, hq, hqe, hz, h1, hrs1, hlen1, hc1, hvs1, hom1, hcw1, hvw1, hm1, hvm1, hfl1⟩
    · left
      have hP2'' : GoodW (1 :: ((Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := goodW_shiftNn _ a b hP2
      have hu := goodW_reg Wf (List.replicate (k + 1) 2 ++ List.replicate q 3) _ hW
        (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)))
        (by intro h; have := congrArg List.length h; simp at this) (by simpa [List.append_assoc] using hP2'')
      have hne : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
          (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) ≠ [] := by simp
      obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex _ hcsOk hne
      refine ⟨((2 :: List.replicate k 2) ++ List.replicate q 3 ++ 1 :: ((Q'' ++ [1]) ++ List.replicate (a + 1) 3 ++
          2 :: List.replicate b 2)) ++ sepRest (o :: os),
        ⟨(2 :: List.replicate k 2) ++ List.replicate q 3, a + 1, b, o, os,
          bd_app (BitsD.cons (by simp) (BitsD.rep _ 2 (by simp))) (BitsD.rep _ 3 (by simp)),
          by intro h; have := congrArg List.length h; simp at this, by omega, ?_, hok, hdg.trans (dg_runAll_pos n c vs r s p hm0 hvm hlen), ?_⟩, ?_⟩
      · rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using hu
      · simp [List.append_assoc]
      · rw [hex] at h1
        rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using h1
    · have hs2 := (hsem' t0 ts (by simpa [passCsOf] using hz)).2
      have hP2' : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail a (b + 1))) := by
        rw [← nn_eq]
        simpa [List.append_assoc] using goodW_shiftNn (Q'' ++ [1]) a b hP2
      have hih := ih (b + 1) n (nxtVs ts) (nxtC t0) (0, q) (nxtR t0) (nxtS t0) (j + 1) l' hP2' hrs1 hlen1 hc1 hvs1 hom1
        hq hcw1 hvw1 hm1 hvm1 (by simpa using hfl1) (by simpa using hL) (by rw [hqe]; exact hs2)
      have e2 : (Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2 = (Q'' ++ [1]) ++ NnTail a (b + 1) := by
        rw [List.append_assoc, nn_eq]
      rw [e2] at h1
      simp only [List.replicate_zero, List.nil_append] at h1 hih
      have hEq : (nxtC t0 :: nxtVs ts).map VR.dg = (c :: vs).map VR.dg := by
        have hcl : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).length = n + 1 := by
          simp [loopRun_cs_length n c vs r s p hlen]
        have hzl : (List.replicate (j + 1) 2 ++ 3 :: l').length = n + 1 := by
          have := congrArg List.length hfl
          simp at this ⊢; omega
        have hmf := List.map_fst_zip (l₁ := (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) (l₂ := List.replicate (j + 1) 2 ++ 3 :: l') (by omega)
        rw [hz] at hmf
        have hp := dg_runAll_pos n c vs r s p hm0 hvm hlen
        rw [← hp, ← hmf]
        simp [nxtC, nxtVs, nxtW, dg_curG, dg_nextPass, dg_dec, List.map_map, Function.comp_def]
      rcases hih with ⟨R', ho, hr⟩ | ⟨T, ho, hr⟩
      · exact Or.inl ⟨R', by rw [hEq] at ho; rwa [show a + 1 + (b + 1) = a + 1 + 1 + b by omega] at ho, h1.trans hr⟩
      · exact Or.inr ⟨T, by rw [hEq] at ho; rwa [show b + 1 + a + 1 = b + (a + 1) + 1 by omega] at ho, h1.trans hr⟩



theorem tapeOutO_sym4 {T : List Nat} (h : TapeOutO T) : Sym4 T := by
  obtain ⟨u, o, os, hu, hos, rfl⟩ := h
  have : sepRest (o :: os) = 1 :: 1 :: tapeL (o :: os) := rfl
  exact hu.sym4.app (by
    rw [this]
    exact Sym4.cons (by simp [ALL]) (Sym4.cons (by simp [ALL]) (tapeL_sym4 _ hos)))

/-- A refuted assignment moves to the next one (`WI0`) or overflows (`BEEP`). -/
theorem odlNext (Wf : List Nat) (hW : BitsD Wf) (R' : List Nat) (hT : TapeOutO ((Wf ++ [1]) ++ R')) :
    (∃ u v os' X R'', Rest u v ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ A, znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.BEEP A [])) := by
  have sT := tapeOutO_sym4 hT
  have hR : Sym4 R' := (Sym4_app_iff.1 sT).2
  have hL : NoB (Wf ++ [1]) := NoB_app_iff.2 ⟨hW.noB, by intro x hx; simp at hx; simp [hx, NB]⟩
  obtain ⟨u, o, os, hu, hos, hXY⟩ := hT
  have hXY' : (Wf ++ [1]) ++ R' = u ++ 1 :: 1 :: tapeL (o :: os) := hXY
  obtain ⟨v, hv, h1, h2⟩ := odFail u hu o os hos _ _ hXY' hL hR
  cases hs : odoStepR (o :: os) with
  | some os' =>
    obtain ⟨X, R'', e, hr⟩ := h1 os' hs
    exact Or.inl ⟨u, v, os', X, R'', hv, e, hr⟩
  | none => exact Or.inr ⟨_, h2 hs⟩


/-- One whole assignment, from the first cursor of the first pass: the next assignment (`WI0`), the overflow (`BEEP`),
or success (`SU1`). -/
theorem assignRun (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat)
    (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat)
    (hP2 : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs) (hp : 1 ≤ p.2)
    (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L) (hL : m ≤ L.length) (hsem : Sem m n c vs r s p j L) :
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) []
    (∃ u v os' X R'', Rest u v ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ A, znttLogic.Reach st (hd QNTT.BEEP A [])) ∨
    (∃ T, SuOut ((c :: vs).map VR.dg) Wf Q'' (b + m + 1) T ∧ znttLogic.Reach st (hdR QNTT.SU1 [] T)) := by
  intro st
  rcases passesRun Wf hW Q'' m b n vs c p r s j L hP2 hrs hlen hc hvs hom hp hcw hvw hm0 hvm hfl hL hsem with
    ⟨R', hT, hr⟩ | ⟨T, hT, hr⟩
  · rcases odlNext Wf hW R' hT.toO with ⟨u, v, os', X, R'', hv, e, h⟩ | ⟨A, h⟩
    · exact Or.inl ⟨u, v, os', X, R'', hv, e, hr.trans h⟩
    · exact Or.inr (Or.inl ⟨A, hr.trans h⟩)
  · exact Or.inr (Or.inr ⟨T, hT, hr⟩)




theorem ORec.Ok.noB {o : ORec} (h : o.Ok) : NoB o.tape := by
  have a1 : (1 : Nat) ∈ NB := by simp [NB]
  have hf : BitsD [o.F, o.O, o.Pf] := by
    have hF := h.hF
    intro y hy; simp at hF hy; rcases hy with rfl | rfl | rfl <;> simp [hF]
  have hth : BitsD (therm o.d o.r) := by
    intro y hy; simp [therm, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  unfold ORec.tape
  refine NoB_app_iff.2 ⟨hf.noB, ?_⟩
  simp only [NoB_cons_iff, NoB_app_iff]
  exact ⟨a1, h.acc.noB, a1, h.E.noB, a1, hth.noB, a1, (bitsD_winStr _ _ _).noB⟩

theorem sepRest_noB : ∀ os : List ORec, (∀ o ∈ os, o.Ok) → NoB (sepRest os)
  | [], _ => by simp [sepRest, NoB]
  | o :: os, h => by
    have a1 : (1 : Nat) ∈ NB := by simp [NB]
    simp only [sepRest, NoB_cons_iff, NoB_app_iff]
    exact ⟨a1, a1, (h o (by simp)).noB, sepRest_noB os (fun x hx => h x (by simp [hx]))⟩

theorem tapeL_noB (os : List ORec) (h : ∀ o ∈ os, o.Ok) : NoB (tapeL os) := by
  cases os with
  | nil => simp [tapeL, NoB]
  | cons o os => exact NoB_app_iff.2 ⟨(h o (by simp)).noB, sepRest_noB os (fun x hx => h x (by simp [hx]))⟩

/-- Success: the machine erases the records and restarts at `PA0` with `Nn` lengthened by the finished marks. -/
theorem sucRestart (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Kf Cf : List Nat) (B : Nat) (T : List Nat)
    (hW : BitsD Wf) (hK : BitsD Kf) (hC : BitsD Cf) (h : SuOut D Wf (Kf ++ 1 :: Cf) (B + 1) T) :
    ∃ N : Nat, znttLogic.Reach (hdR QNTT.SU1 [] T)
      (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (B + 2) 3 ++ List.replicate (N + 1) 0))))) := by
  obtain ⟨S0, o, os, hS, hg, hok, hd, rfl⟩ := h
  have hr := suOk Wf S0 Kf Cf (List.replicate B 2) (tapeL (o :: os)) hW hS hK hC (BitsD.rep B 2 (by simp))
    (by simpa [List.replicate_succ', List.append_assoc] using hg) (tapeL_noB _ hok)
  refine ⟨(tapeL (o :: os)).length, ?_⟩
  simp only [List.length_replicate] at hr
  simpa [sepRest, tapeL, List.replicate_succ', List.append_assoc] using hr


theorem ORec.vr_ok (o : ORec) (ho : o.Ok) (x : Nat) (hx : x ∈ [2, 3]) (hacc : 2 ≤ o.acc.length) :
    (o.vr x).Ok := by
  have hO : o.O ∈ [2, 3] := by
    have := ho.hF; simp at this; simpa using this.2.1
  refine { F := by simp [ORec.vr], O := hO, P := hx, k1 := ?_, kw := ?_, E := ?_, Elen := ?_ }
  · simp [ORec.vr]; split <;> omega
  · simp [ORec.vr]; split <;> omega
  · intro y hy
    simp [ORec.vr, List.mem_replicate] at hy
    rcases hy with rfl | h
    · simp
    · simp [h.2]
  · simp [ORec.vr]

theorem vr_cmp (o : ORec) :
    (o.vr 3).O = 3 → ∃ z, 1 ≤ (o.vr 3).k ∧ (o.vr 3).E = fld ((o.vr 3).k + z) (o.vr 3).k := by
  intro _
  refine ⟨o.E.length - 2, by simp [ORec.vr], ?_⟩
  simp [ORec.vr, fld]


/-- First assignment: `WI0` (witness initialisation) through the pass start to the cursor on record 0 (`RFL`). -/
theorem firstEntry (L R Pm Pm' : List Nat) (hL : NoB L) (hRest : Rest Pm Pm') (hP' : GoodW Pm')
    (r : Rc) (hr : r.Ok) (rs : List Rc) (hrs : ∀ x ∈ rs, x.Ok)
    (hLR : L ++ R = Pm ++ 1 :: 1 :: (r.body ++ tailB rs))
    (o : ORec) (os : List ORec) (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (hk : ∀ x ∈ o :: os, 1 ≤ x.k) (hdr : ∀ x ∈ o :: os, x.d + 1 ≤ x.r)
    (h0 : r.initB 3 = (o.toRc 3).body) (h1 : tailI rs = tailB (os.map fun x => x.toRc 2))
    (hPS0 : (o.toRc 3).PS) (hPS : ∀ x ∈ os, (x.toRc 2).PS) :
    znttLogic.Reach (hd QNTT.WI0 L R)
      (hd QNTT.RFL (curTapeG Pm' [] (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k)
        ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hwi := witnessInit L R Pm Pm' hL hRest r hr rs hrs hLR
  rw [h0, h1] at hwi
  have hrs0 : ∀ x ∈ os.map (fun x => x.toRc 2), x.PS := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact hPS y hy
  have hN1 : NoB [1, 1] := by intro a ha; simp at ha; simp [ha, NB]
  have hL2 : NoB (Pm' ++ [1, 1] ++ (o.toRc 3).body ++ tailB (os.map fun x => x.toRc 2)) := by
    simp only [NoB_app_iff]
    exact ⟨⟨⟨hP'.noB, hN1⟩, Rc.body_noB _ hPS0.ok⟩, tailB_noB _ (fun x hx => (hrs0 x hx).ok)⟩
  have hps := passStartAll (Pm' ++ [1, 1] ++ (o.toRc 3).body ++ tailB (os.map fun x => x.toRc 2)) Pm'
    hL2 hP' (o.toRc 3) hPS0 (os.map fun x => x.toRc 2) hrs0 (by simp)
  have hBr : ∀ p ∈ (os.map fun x => (x, 2)), BrOk p := by
    intro p hp; simp only [List.mem_map] at hp; obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨hk y (by simp [hy]), hacc y (by simp [hy]), by simp, hdr y (by simp [hy])⟩
  have e1 := toRc_ps_vr o 3 (hk o (by simp)) (hacc o (by simp)) (by simp) (hdr o (by simp))
  have e2 := tailP_vr (os.map fun x => (x, 2)) hBr
  simp only [List.map_map, Function.comp_def] at e2
  have hw : (o.vr 3).Ok := ORec.vr_ok o (hok o (by simp)) 3 (by simp) (hacc o (by simp))
  have hws : ∀ x ∈ (os.map fun x => x.vr 2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact ORec.vr_ok y (hok y (by simp [hy])) 2 (by simp) (hacc y (by simp [hy]))
  have hLe : Pm' ++ [1, 1] ++ (o.toRc 3).ps.body ++ tailP (os.map fun x => x.toRc 2) =
      Pm' ++ 1 :: 1 :: ([(o.vr 3).F, (o.vr 3).O, (o.vr 3).P] ++ 1 :: ((o.vr 3).tl ++ tailVR (os.map fun x => x.vr 2))) := by
    have : tailP (os.map fun x => x.toRc 2) = tailVR (os.map fun x => x.vr 2) := e2
    rw [this]
    have e1' : 1 :: 1 :: (o.toRc 3).ps.body = (o.vr 3).recd := e1
    simp only [VR.recd] at e1'
    have e3 : (o.toRc 3).ps.body = (o.vr 3).F :: (o.vr 3).O :: (o.vr 3).P :: 1 :: (o.vr 3).tl := by
      simpa using e1'
    rw [e3]; simp
  have hNL : NoB (Pm' ++ [1, 1] ++ (o.toRc 3).ps.body ++ tailP (os.map fun x => x.toRc 2)) := by
    rw [hLe]
    simp only [NoB_app_iff, NoB_cons_iff]
    refine ⟨hP'.noB, by simp [NB], by simp [NB], ?_⟩
    have h3 := hw.hdr3.noB
    simp only [NoB_cons_iff] at h3
    exact ⟨⟨h3.1, h3.2.1, h3.2.2.1, by intro a ha; simp at ha⟩, by simp [NB], hw.tl_noB, tailVR_noB _ hws⟩
  have hf := faG' _ Pm' hNL hP' (o.vr 3) hw _ hws (vr_cmp o) hLe
  exact hwi.trans (hps.trans hf)



/-- The record produced by the build, with header second cell `h1` and pointer size `j'`. -/
def recRc (j h1 j' : Nat) : Rc :=
  { F := 2, O := h1, Pf := 2, acc := 3 :: List.replicate j 2, E := 3 :: List.replicate j 2,
    b0 := 3, br := List.replicate j 2, u0 := 3, ur := List.replicate j' 2 }

theorem recH_body (j h1 j' : Nat) : recH h1 j j' 3 = 1 :: 1 :: (recRc j h1 j').body := by
  simp [recH, recRc, Rc.body, Rc.tlr, Rc.tl0, Dcopy, List.replicate_succ]

theorem recsFlat_tailB (j : Nat) (ps : List (Nat × Nat)) :
    recsFlat j 3 ps = tailB (ps.map fun q => recRc j q.1 q.2) := by
  induction ps with
  | nil => simp [recsFlat, tailB]
  | cons q ps ih =>
    simp only [recsFlat, List.map_cons, List.flatten_cons, tailB] at ih ⊢
    rw [ih, recH_body]; rfl

/-- The odometer record of a build record (`d = 0`, window at the start). -/
def recO (j : Nat) (q : Nat × Nat) : ORec :=
  { F := 2, O := q.1, Pf := 2, acc := 3 :: List.replicate j 2, E := 3 :: List.replicate j 2,
    d := 0, r := j + 1, z := 0, k := 1, m := q.2 }

theorem recO_init (j : Nat) (q : Nat × Nat) (x : Nat) (hj : 1 ≤ j) :
    (recRc j q.1 q.2).initB x = ((recO j q).toRc x).body := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp [Rc.initB, Rc.body, Rc.tlr, Rc.tl0, recRc, recO, ORec.toRc, therm, winStr, List.replicate_succ]

theorem recO_tail (j : Nat) (hj : 1 ≤ j) (ps : List (Nat × Nat)) :
    tailI (ps.map fun q => recRc j q.1 q.2) = tailB (ps.map fun q => (recO j q).toRc 2) := by
  induction ps with
  | nil => simp [tailI, tailB]
  | cons q ps ih =>
    simp only [List.map_cons, tailI, tailB] at ih ⊢
    rw [ih, recO_init j q 2 hj]


theorem Rest.app {u v w z : List Nat} (h : Rest u v) (h2 : Rest w z) : Rest (u ++ w) (v ++ z) := by
  induction h with
  | nil => simpa using h2
  | bit hb _ ih => exact Rest.bit hb ih
  | mb hb _ ih => exact Rest.mb hb ih

theorem Rest.goodW {u v : List Nat} (h : Rest u v) : GoodW v := by
  induction h with
  | nil => exact GoodW.nil
  | bit hb _ ih => exact GoodW.bit (by simp) ih
  | mb hb _ ih => exact GoodW.mb (by simp) ih

theorem rest_rep (a : Nat) : Rest (List.replicate a 3) (List.replicate a 3) := by
  induction a with
  | zero => exact Rest.nil
  | succ a ih => exact Rest.bit (by simp) ih

theorem rest_blk (a : Nat) : Rest (1 :: List.replicate (a + 1) 3) (1 :: List.replicate (a + 1) 3) := by
  simpa [List.replicate_succ] using Rest.mb (b := 3) (by simp) (rest_rep a)


theorem bd32 (j : Nat) : BitsD (3 :: List.replicate j 2) := BitsD.cons (by simp) (BitsD.rep _ _ (by simp))

theorem recRc_ok (j h1 j' : Nat) (hj : 1 ≤ j) (h : h1 ∈ [2, 3]) : (recRc j h1 j').Ok :=
  { F := by simp [recRc], O := h, Pf := by simp [recRc], acc := bd32 j, E := bd32 j,
    Elen := by simp [recRc]; omega, b0 := by simp [recRc], br := BitsD.rep _ _ (by simp),
    u0 := by simp [recRc], ur := BitsD.rep _ _ (by simp) }

theorem recO_ok (j : Nat) (q : Nat × Nat) (hj : 1 ≤ j) (h : q.1 ∈ [2, 3]) : (recO j q).Ok :=
  { hF := by simp [recO] at h ⊢; simpa using h, acc := bd32 j, E := bd32 j,
    d := by simp [recO], k := by simp [recO], Elen := by simp [recO]; omega }

theorem recO_ps (j : Nat) (q : Nat × Nat) (x : Nat) (hj : 1 ≤ j) (h : q.1 ∈ [2, 3]) (hx : x ∈ [2, 3]) :
    ((recO j q).toRc x).PS := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk : 1 ≤ (recO (i + 1) q).k := by simp [recO]
  refine ⟨⟨by simp [ORec.toRc, recO], by simpa [ORec.toRc, recO] using h, hx,
      by simpa [ORec.toRc, recO] using bd32 (i + 1), ?_, by simp [ORec.toRc, recO],
      by simp [ORec.toRc, recO, therm], ?_, by simp [ORec.toRc, recO, winStr], ?_⟩,
    by simp [ORec.toRc, recO], toRc_rest _ x hk⟩
  · intro y hy; simp [ORec.toRc, recO, List.mem_replicate] at hy
    rcases hy with rfl | h
    · simp
    · simp [h.2]
  · intro y hy; simp [ORec.toRc, recO, therm, List.mem_replicate] at hy; simp [hy]
  · intro y hy; simp [ORec.toRc, recO, winStr, List.mem_replicate] at hy; simp [hy]

theorem roundsPs_ne (n : Nat) : ∀ (c w0 : Nat) (ps : List (Nat × Nat)), (ps ≠ [] ∨ 0 < c) →
    roundsPs n c w0 ps ≠ [] := by
  intro c
  induction c with
  | zero =>
    intro w0 ps h
    rcases h with h | h
    · simpa [roundsPs] using h
    · omega
  | succ c ih =>
    intro w0 ps _
    simp only [roundsPs]
    refine ih _ _ (Or.inl ?_)
    simp [newRecs]


/-- From the record build to the first-pass cursor: the build's records are the odometer records `recO`. -/
theorem buildEntry (j c n : Nat) (hj : 1 ≤ j) (hc : 0 < c) :
    ∃ (o : ORec) (os : List ORec), o :: os = (roundsPs n c 1 []).map (recO j) ∧
    znttLogic.Reach
      (hd QNTT.WX [0, 3] (1 :: (List.replicate (j + 1) 3 ++ 1 :: (List.replicate (2 + 1) 3 ++ 1 ::
        (List.replicate c 3 ++ 1 :: List.replicate (n + 1) 3)))))
      (hd QNTT.RFL (curTapeG (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) []
        (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hb := recordBuild j 2 c n hc
  have hok := roundsPs_ok n c 1 [] (by simp)
  obtain ⟨q, ps, hqs⟩ : ∃ q ps, roundsPs n c 1 [] = q :: ps := by
    cases h : roundsPs n c 1 [] with
    | nil => exact absurd h (roundsPs_ne n c 1 [] (Or.inr hc))
    | cons q ps => exact ⟨q, ps, rfl⟩
  rw [hqs] at hb hok
  have hq : ∀ x ∈ q :: ps, x.1 ∈ [2, 3] := hok
  refine ⟨recO j q, ps.map (recO j), by simp [hqs], ?_⟩
  have hRest : Rest (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := ((rest_rep (wEnd n (c' + 1) 1 + 1)).app (rest_blk (j' + 1))).app
      ((rest_blk 2).app ((rest_blk c').app (rest_blk n)))
    have e : Pfx (wEnd n (c' + 1) 1 + 1) (j' + 1) 2 ++ List.replicate (0 + (c' + 1)) 3 ++ 1 :: List.replicate (n + 1) 3 =
        List.replicate (wEnd n (c' + 1) 1 + 1) 3 ++ (1 :: List.replicate (j' + 1 + 1) 3) ++
          ((1 :: List.replicate (2 + 1) 3) ++ ((1 :: List.replicate (c' + 1) 3) ++ (1 :: List.replicate (n + 1) 3))) := by
      simp [Pfx, List.append_assoc]
    rw [e]; exact this
  have hq0 : q.1 ∈ [2, 3] := hq q (by simp)
  have hqs' : ∀ x ∈ ps, x.1 ∈ [2, 3] := fun x hx => hq x (by simp [hx])
  have hrs : ∀ x ∈ ps.map (fun x => recRc j x.1 x.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact recRc_ok j _ _ hj (hqs' y hy)
  have hL : NoB (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3) := by
    simp only [Pfx, NoB_app_iff, NoB_cons_iff, NoB_rep_iff]; simp [NB]
  have hLR : (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3) ++
      (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (2 + 1) (q :: ps))) =
      (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) ++ 1 :: 1 :: ((recRc j q.1 q.2).body ++ tailB (ps.map fun x => recRc j x.1 x.2)) := by
    rw [recsFlat_tailB]
    simp [tailB, List.append_assoc]
  have hos : ∀ x ∈ recO j q :: ps.map (recO j), x.Ok := by
    intro x hx; simp only [List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact recO_ok j q hj hq0
    · exact recO_ok j y hj (hqs' y hy)
  have hfe := firstEntry (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3)
    (1 :: (List.replicate (n + 1) 3 ++ recsFlat j (2 + 1) (q :: ps))) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) (Pfx (wEnd n c 1 + 1) j 2 ++ List.replicate (0 + c) 3 ++ 1 :: List.replicate (n + 1) 3) hL hRest hRest.goodW
    (recRc j q.1 q.2) (recRc_ok j _ _ hj hq0) (ps.map fun x => recRc j x.1 x.2) hrs hLR
    (recO j q) (ps.map (recO j)) hos
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO] <;> omega)
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO])
    (by intro x hx; simp only [List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩ <;> simp [recO])
    (recO_init j q 3 hj)
    (by rw [recO_tail j hj ps]; simp [Function.comp_def])
    (recO_ps j q 3 hj hq0 (by simp))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
        exact recO_ps j y 2 hj (hqs' y hy) (by simp))
  exact hb.trans hfe



theorem rest_map {u v : List Nat} (h : Rest u v) : v = u.map (fun x => if x = 1 then 1 else 3) := by
  induction h with
  | nil => rfl
  | bit hb _ ih =>
    simp at hb; rcases hb with rfl | rfl <;> simp [ih]
  | mb hb _ ih =>
    simp at hb; rcases hb with rfl | rfl <;> simp [ih]

/-- The overflow state (the machine's beep) steps left over the last cell, then the erase sweep restarts. -/
theorem beepToSU1 (A : List Nat) (hA : NoB A) (hne : A ≠ []) :
    ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧ znttLogic.Reach X (hdR QNTT.SU1 [] A) := by
  obtain ⟨A', c, rfl⟩ : ∃ A' c, A = A' ++ [c] := by
    rcases List.eq_nil_or_concat A with h | ⟨A', c, h⟩
    · exact absurd h hne
    · exact ⟨A', c, by simpa using h⟩
  have hc : c ∈ [1, 2, 3] := by
    have := hA c (by simp); simpa [NB] using this
  have hA' : NoB A' := fun x hx => hA x (by simp [hx])
  have h2 := su0Scan A' [c] hA' (by
    intro x hx; simp at hx; subst hx; simp at hc; rcases hc with rfl | rfl | rfl <;> simp [ALL])
  exact ⟨_, beepStepC A' [] c hc, by simpa using h2⟩

theorem bits_map {w : List Nat} (h : BitsD w) : BitsD (w.map (fun x => if x = 1 then 1 else 3)) := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := h x hx; simp at this; rcases this with rfl | rfl <;> simp

theorem resetAll_ok : ∀ os : List ORec, (∀ x ∈ os, x.Ok) → ∀ x ∈ resetAll os, x.Ok
  | [], _ => by simp [resetAll]
  | o :: os, h => by
    intro x hx
    simp only [resetAll, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (h o (by simp)).reset
    · exact resetAll_ok os (fun y hy => h y (by simp [hy])) x hx

/-- A refuted assignment moves to the next one (`WI0`), or overflows: `BEEP`, the beep step, and the erase sweep
restarting at `PA0` with `C` grown by one (`beepOk`). -/
theorem odlNext2 (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Kf Cf : List Nat) (hW : BitsD Wf) (hK : BitsD Kf) (hC : BitsD Cf)
    (N : Nat) (R' : List Nat) (hT : OdOut D Wf ((Kf ++ 1 :: Cf) ++ [1]) N R') :
    (∃ u v os' X R'', Rest u v ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), znttLogic.Reach (hd QNTT.ODL (Wf ++ [1]) R') (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 :: (List.replicate N 3 ++ List.replicate (n0 + 1) 0)))))) := by
  have hT' := hT.toO
  have sT := tapeOutO_sym4 hT'
  have hR : Sym4 R' := (Sym4_app_iff.1 sT).2
  have hL : NoB (Wf ++ [1]) := NoB_app_iff.2 ⟨hW.noB, by intro x hx; simp at hx; simp [hx, NB]⟩
  obtain ⟨S0, a', b', o, os, hS0, hS0ne, hN, hg, hos, hdg, hXY⟩ := hT
  have hXY' : (Wf ++ [1]) ++ R' = (Wf ++ 1 :: (S0 ++ 1 :: ((Kf ++ 1 :: Cf) ++ [1] ++ List.replicate a' 3 ++ 2 :: List.replicate b' 2))) ++
      1 :: 1 :: tapeL (o :: os) := hXY
  obtain ⟨v, hv, h1, h2⟩ := odFail _ hg o os hos _ _ hXY' hL hR
  cases hs : odoStepR (o :: os) with
  | some os' =>
    obtain ⟨X, R'', e, hr⟩ := h1 os' hs
    exact Or.inl ⟨_, v, os', X, R'', hv, e, hr⟩
  | none =>
    right
    have hb := h2 hs
    have hvm := rest_map hv
    have hgv : GoodW v := hv.goodW
    have hrep : List.replicate a' 3 ++ 3 :: List.replicate b' 3 = List.replicate N 3 := by
      subst hN
      rw [show (3 :: List.replicate b' 3) = List.replicate (b' + 1) 3 from rfl, List.replicate_append_replicate]
      congr 1; omega
    have hvE : v = Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
        (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: List.replicate N 3))) := by
      rw [hvm, ← hrep]
      simp [List.map_append, List.map_replicate, List.append_assoc]
    obtain ⟨L, rfl⟩ : ∃ L, N = L + 1 := ⟨N - 1, by omega⟩
    have hrk : ∀ x ∈ resetAll (o :: os), x.Ok := resetAll_ok _ hos
    have hnb : NoB (tapeL (resetAll (o :: os))) := tapeL_noB _ hrk
    have hAeq : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) =
        (Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
            List.replicate (L + 1) 3)))) ++ 1 :: 1 :: tapeL (resetAll (o :: os)) := by
      rw [hvE]; simp [List.append_assoc]
    have hnbA : NoB ((v ++ [1, 1]) ++ tapeL (resetAll (o :: os))) := by
      have h1 : NoB v := hgv.noB
      exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨h1, by intro x hx; simp at hx; simp [hx, NB]⟩, hnb⟩
    have hne : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) ≠ [] := by simp
    obtain ⟨X, hX, hXr⟩ := beepToSU1 _ hnbA hne
    have hbo := beepOk (Wf.map (fun x => if x = 1 then 1 else 3)) (S0.map (fun x => if x = 1 then 1 else 3))
      (Kf.map (fun x => if x = 1 then 1 else 3)) (Cf.map (fun x => if x = 1 then 1 else 3))
      (tapeL (resetAll (o :: os))) L (bits_map hW) (bits_map hS0) (bits_map hK) (bits_map hC)
      (by rw [← hvE]; exact hgv) hnb
    refine ⟨_, (tapeL (resetAll (o :: os))).length, hb, X, hX, ?_⟩
    rw [hAeq] at hXr
    exact hXr.trans hbo

/-- One whole assignment with explicit continuations: the next assignment (`WI0`), the overflow (beep, then restart
at `PA0` with `C` grown), or success (`SU1`, restart at `PA0`). -/
theorem assignRun' (Wf : List Nat) (hW : BitsD Wf) (Kf Cf : List Nat) (hK : BitsD Kf) (hC : BitsD Cf)
    (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat)
    (hP2 : GoodW (1 :: (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs) (hp : 1 ≤ p.2)
    (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L) (hL : m ≤ L.length) (hsem : Sem m n c vs r s p j L) :
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b))) [] c 0 r s vs) []
    (∃ u v os' X R'', Rest u v ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (m + 1 + b) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut ((c :: vs).map VR.dg) Wf (Kf ++ 1 :: Cf) (b + m + 1) T ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (b + m + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  intro st
  rcases passesRun Wf hW (Kf ++ 1 :: Cf) m b n vs c p r s j L hP2 hrs hlen hc hvs hom hp hcw hvw hm0 hvm hfl hL hsem with
    ⟨R', hT, hr⟩ | ⟨T, hT, hr⟩
  · rcases odlNext2 _ Wf Kf Cf hW hK hC _ R' hT with ⟨u, v, os', X, R'', hv, e, h⟩ | ⟨A, n0, hb, X, hX, hXr⟩
    · exact Or.inl ⟨u, v, os', X, R'', hv, e, hr.trans h⟩
    · exact Or.inr (Or.inl ⟨A, n0, hr.trans hb, X, hX, hXr⟩)
  · obtain ⟨N, hN⟩ := sucRestart _ Wf Kf Cf (b + m) T hW hK hC hT
    exact Or.inr (Or.inr ⟨N, T, hT, hr, hN⟩)


/-- An odometer record as a tape record. -/
def orcRc (o : ORec) : Rc :=
  { F := o.F, O := o.O, Pf := o.Pf, acc := o.acc, E := o.E, b0 := (therm o.d o.r).headD 2,
    br := (therm o.d o.r).tail, u0 := (winStr o.z o.k o.m).headD 2, ur := (winStr o.z o.k o.m).tail }

theorem therm_cons (d r : Nat) : (therm d r).headD 2 :: (therm d r).tail = therm d r := by
  cases h : therm d r with
  | nil => simp [therm] at h
  | cons a l => simp

theorem winStr_cons (z k m : Nat) (hk : 1 ≤ k) : (winStr z k m).headD 2 :: (winStr z k m).tail = winStr z k m := by
  cases h : winStr z k m with
  | nil => obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp [winStr, hj, List.replicate_succ] at h
  | cons a l => simp

theorem orcRc_body (o : ORec) (hk : 1 ≤ o.k) : (orcRc o).body = o.tape := by
  have hT : (therm o.d o.r) ≠ [] := by simp [therm]
  have hW : (winStr o.z o.k o.m) ≠ [] := by
    obtain ⟨j, hj⟩ : ∃ j, o.k = j + 1 := ⟨o.k - 1, by omega⟩
    simp [winStr, hj, List.replicate_succ]
  simp only [Rc.body, Rc.tlr, Rc.tl0, orcRc, ORec.tape]
  generalize therm o.d o.r = Tm at hT ⊢
  generalize winStr o.z o.k o.m = Wm at hW ⊢
  cases Tm with
  | nil => exact absurd rfl hT
  | cons a T =>
    cases Wm with
    | nil => exact absurd rfl hW
    | cons b U => simp

theorem orcRc_init (o : ORec) (x : Nat) : (orcRc o).initB x = (o.toRc x).body := by
  simp only [Rc.initB, Rc.body, Rc.tlr, Rc.tl0, orcRc, ORec.toRc]


theorem therm_bits (d r : Nat) : BitsD (therm d r) := by
  intro y hy; simp [therm, List.mem_replicate] at hy; rcases hy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem ORec.Ok.hF3 {o : ORec} (h : o.Ok) : o.F ∈ [2, 3] ∧ o.O ∈ [2, 3] ∧ o.Pf ∈ [2, 3] := by
  have := h.hF; simp at this; simpa using this

theorem bits_headD {l : List Nat} (h : BitsD l) : l.headD 2 ∈ [2, 3] := by
  cases l with
  | nil => simp
  | cons a l => exact h a (by simp)

theorem bits_tail {l : List Nat} (h : BitsD l) : BitsD l.tail := by
  cases l with
  | nil => exact h
  | cons a l => intro x hx; exact h x (List.mem_cons_of_mem a hx)

theorem orcRc_ok (o : ORec) (ho : o.Ok) : (orcRc o).Ok := by
  obtain ⟨hF, hO, hP⟩ := ho.hF3
  exact ⟨hF, hO, hP, ho.acc, ho.E, ho.Elen, bits_headD (therm_bits o.d o.r), bits_tail (therm_bits o.d o.r),
    bits_headD (bitsD_winStr o.z o.k o.m), bits_tail (bitsD_winStr o.z o.k o.m)⟩

theorem toRc_ps (o : ORec) (ho : o.Ok) (hacc : 2 ≤ o.acc.length) (x : Nat) (hx : x ∈ [2, 3]) : (o.toRc x).PS := by
  obtain ⟨hF, hO, hP⟩ := ho.hF3
  refine ⟨⟨hF, hO, hx, ho.acc, ?_, by simp [ORec.toRc],
    bits_headD (therm_bits o.d o.r), bits_tail (therm_bits o.d o.r),
    bits_headD (bitsD_winStr o.z o.k o.m), bits_tail (bitsD_winStr o.z o.k o.m)⟩, hacc, toRc_rest o x ho.k⟩
  intro y hy; simp [ORec.toRc, List.mem_replicate] at hy
  rcases hy with rfl | h
  · simp
  · simp [h.2]

theorem tailB_orc : ∀ os : List ORec, (∀ x ∈ os, 1 ≤ x.k) → tailB (os.map orcRc) = sepRest os
  | [], _ => by simp [tailB, sepRest]
  | o :: os, h => by
    simp only [List.map_cons, tailB, sepRest]
    rw [orcRc_body o (h o (by simp)), tailB_orc os (fun x hx => h x (by simp [hx]))]

theorem tailI_orc : ∀ os : List ORec, tailI (os.map orcRc) = tailB (os.map fun x => x.toRc 2)
  | [] => by simp [tailI, tailB]
  | o :: os => by
    simp only [List.map_cons, tailI, tailB]
    rw [orcRc_init, tailI_orc os]

/-- The next assignment: from `WI0` on the reset records to the first-pass cursor. -/
theorem nextEntry (X R'' v : List Nat) (hNoB : NoB X) (hv : Rest v v) (o : ORec) (os : List ORec)
    (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (e : X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL (o :: os)) :
    znttLogic.Reach (hd QNTT.WI0 X (3 :: R''))
      (hd QNTT.RFL (curTapeG v [] (o.vr 3).curG 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k)
        ((os.map fun x => x.vr 2).map VR.dec)) []) := by
  have hks : ∀ x ∈ os, 1 ≤ x.k := fun x hx => (hok x (by simp [hx])).k
  have hr := orcRc_ok o (hok o (by simp))
  have hrs : ∀ x ∈ os.map orcRc, x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
    exact orcRc_ok y (hok y (by simp [hy]))
  have hLR : X ++ 3 :: R'' = v ++ 1 :: 1 :: ((orcRc o).body ++ tailB (os.map orcRc)) := by
    rw [e, orcRc_body o (hok o (by simp)).k, tailB_orc os hks]
    simp [tapeL, sepRest, List.append_assoc]
  exact firstEntry X (3 :: R'') v v hNoB hv hv.goodW (orcRc o) hr (os.map orcRc) hrs hLR o os hok hacc
    (fun x hx => (hok x hx).k) (fun x hx => (hok x hx).d) (orcRc_init o 3) (tailI_orc os)
    (toRc_ps o (hok o (by simp)) (hacc o (by simp)) 3 (by simp))
    (fun x hx => toRc_ps x (hok x (by simp [hx])) (hacc x (by simp [hx])) 2 (by simp))


/-! ## Compare mismatch: refutation at the output compare -/


/-- `cpRound`s while the accumulator is the smaller: `n` rounds leave one accumulator mark and `d + 2` marks of `E`. -/
theorem cmpLt (A : List Nat) (d : Nat) : ∀ (n a s z : Nat) (R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate (a + n) 2 ++ 3 :: List.replicate s 2 ++
        1 :: (List.replicate (d + 2) 3 ++ List.replicate (z + n) 2) ++ 1 :: R)) := by
  intro n
  induction n with
  | zero => intro a s z R hA hR; simpa using (LTM.Reach.refl _ _)
  | succ n ih =>
    intro a s z R hA hR
    have h := cpRound A a (n + d + 1) z (List.replicate n 3 ++ List.replicate s 2) R hA
      (bd_app (BitsD.rep n 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
    have ih' := ih (a + 1) s (z + 1) R hA hR
    rw [show a + 1 + n = a + (n + 1) by omega, show z + 1 + n = z + (n + 1) by omega] at ih'
    rw [show n + 1 + d + 2 = n + d + 3 by omega]
    simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h ih' ⊢
    exact h.trans ih'

/-- Accumulator smaller than `E`: refuted at `CPE3`. -/
theorem cpLtEnd (A : List Nat) (a s d z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: List.replicate s 2 ++
        1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate z 2 ++ 1 :: R))) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sS : Sym4 (List.replicate s 2) := (BitsD.rep s 2 (by simp)).sym4
  have sA2 : Sym4 (List.replicate a 2) := (BitsD.rep a 2 (by simp)).sym4
  have sD : Sym4 (List.replicate d 3) := (BitsD.rep d 3 (by simp)).sym4
  have g1 := cp0Skip (A ++ [1]) a (3 :: (List.replicate s 2 ++ 1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R))) sP
    (by simp [ALL, sS, sZ, sD, hR])
  have g2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (List.replicate s 2 ++ 1 :: (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R))
    (by simp [ALL, hA, sA2]) (by simp [ALL, sS, sZ, sD, hR])
  have g3 := cpe1 (A ++ [1] ++ List.replicate a 2 ++ [3]) s (List.replicate (d + 2) 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2]) (by simp [ALL, sZ, sD, hR])
  have g4 := cpe2One (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1])
    (List.replicate (d + 1) 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, sD, hR])
  have g5 := cpe3One (A ++ [1] ++ List.replicate a 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
    (List.replicate d 3 ++ List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sA2, sS]) (by simp [ALL, sZ, sD, hR])
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ] at g1 g2 g3 g4 g5 ⊢
  exact g1.trans (g2.trans (g3.trans (g4.trans g5)))

/-- Accumulator larger than `E`: refuted at `CP5`. -/
theorem cpGtEnd (A : List Nat) (a : Nat) (f : List Nat) (z : Nat) (R : List Nat) (hA : Sym4 A) (hf : BitsD f) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ 3 :: 3 :: f ++ 1 :: (3 :: List.replicate z 2 ++ 1 :: R)))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3])
        (List.replicate z 2 ++ 1 :: R)) := by
  have sP : Sym4 (A ++ [1]) := hA.app (sym4_cell 1 (by simp))
  have sQ : Sym4 (A ++ [1] ++ List.replicate a 2) := sP.app (BitsD.rep a 2 (by simp)).sym4
  have hf3 : BitsD (3 :: f) := BitsD.cons (by simp) hf
  have sZ : Sym4 (List.replicate z 2) := (BitsD.rep z 2 (by simp)).sym4
  have sf : Sym4 f := hf.sym4
  have h1 := cp0Skip (A ++ [1]) a (3 :: 3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sP
    (by simp [ALL, sf, hR, sZ])
  have h2 := cp0Hit (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sZ])
  have h3 := cp1Two (A ++ [1] ++ List.replicate a 2) (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R)) sQ
    (by simp [ALL, sf, hR, sZ])
  have h4 := cp2Mark (A ++ [1] ++ List.replicate a 2) (3 :: (f ++ 1 :: ((3 :: List.replicate z 2) ++ 1 :: R))) sQ
    (by simp [ALL, sf, hR, sZ])
  have h5 := cp3Skip (A ++ [1] ++ List.replicate a 2 ++ [2]) (3 :: f) ((3 :: List.replicate z 2) ++ 1 :: R)
    (by simp [ALL, hA, sQ]) hf3 (by simp [ALL, hR, sZ])
  have h6 := cp4One (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1]) (List.replicate z 2 ++ 1 :: R)
    (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
  have h7 : znttLogic.Reach (hdR QNTT.CP5 (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) (List.replicate z 2 ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) (List.replicate z 2 ++ 1 :: R)) := by
    cases z with
    | zero =>
      have := cp5M (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3]) R (by simp [ALL, hA, sQ, sf]) hR
      simpa only [List.replicate_zero, List.nil_append] using this
    | succ k =>
      have := cp5Zero (A ++ [1] ++ List.replicate a 2 ++ [2] ++ (3 :: f) ++ [1] ++ [3])
        (List.replicate k 2 ++ 1 :: R) (by simp [ALL, hA, sQ, sf]) (by simp [ALL, hR, sZ])
      simpa only [List.replicate_succ, List.cons_append] using this
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

theorem cmpGt (A : List Nat) (d : Nat) : ∀ (e a s z : Nat) (R : List Nat), Sym4 A → Sym4 R →
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate (a + e) 2 ++ List.replicate (d + 2) 3 ++ List.replicate s 2 ++
        1 :: (3 :: List.replicate (z + e) 2) ++ 1 :: R)) := by
  intro e
  induction e with
  | zero => intro a s z R hA hR; simpa using (LTM.Reach.refl _ _)
  | succ e ih =>
    intro a s z R hA hR
    have h := cpRound A a e z (List.replicate (e + d + 1) 3 ++ List.replicate s 2) R hA
      (bd_app (BitsD.rep _ 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
    have ih' := ih (a + 1) s (z + 1) R hA hR
    rw [show a + 1 + e = a + (e + 1) by omega, show z + 1 + e = z + (e + 1) by omega] at ih'
    rw [show e + 1 + d + 2 = e + d + 3 by omega]
    simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h ih' ⊢
    exact h.trans ih'

theorem cmpAccLt (A : List Nat) (n d a s z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate (a + n) 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate (z + n) 2 ++ 1 :: R))) :=
  (cmpLt A d n a s z R hA hR).trans (cpLtEnd A (a + n) s d (z + n) R hA hR)

theorem cmpAccGt (A : List Nat) (e d a s z : Nat) (R : List Nat) (hA : Sym4 A) (hR : Sym4 R) :
    znttLogic.Reach
      (hdR QNTT.CP0 (A ++ [1]) (List.replicate a 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
        1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: R))
      (hd QNTT.ODL (A ++ [1] ++ List.replicate (a + e) 2 ++ [2] ++ (3 :: (List.replicate d 3 ++ List.replicate s 2)) ++ [1] ++ [3])
        (List.replicate (z + e) 2 ++ 1 :: R)) := by
  have h1 := cmpGt A d e a s z R hA hR
  have h2 := cpGtEnd A (a + e) (List.replicate d 3 ++ List.replicate s 2) (z + e) R hA
    (bd_app (BitsD.rep d 3 (by simp)) (BitsD.rep s 2 (by simp))) hR
  simp only [List.append_assoc, List.cons_append, List.replicate_succ] at h1 h2 ⊢
  exact h1.trans h2


theorem fa0OLt (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 3) (n d s z : Nat)
    (hacc : w.acc = List.replicate (n + 1) 3 ++ List.replicate s 2)
    (hE : w.E = List.replicate (n + d + 2) 3 ++ List.replicate z 2)
    (ws : List Rc) (hws : ∀ x ∈ ws, x.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.ODL (A ++ [3, 3, w.Pf] ++ [1] ++ List.replicate n 2 ++ [3] ++ List.replicate s 2 ++ [1] ++ [3])
        (3 :: (List.replicate d 3 ++ List.replicate (z + n) 2 ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)))) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have sA3 : Sym4 (A ++ [3]) := hA.app (sym4_cell 3 (by simp))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1o (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) sA3 (sym4_B ho.Pf (sym4_M sTl))
  have h6 := faoSkip (A ++ [3] ++ [3]) [w.Pf] (w.tl ++ tailB ws) (sA3.app (sym4_cell 3 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have sR' : Sym4 (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    have := sTl
    simp only [Rc.tl] at this
    simp [hacc, hE] at this
    simpa using this.2.2.2.2.2.2
  have hwt : w.tl ++ tailB ws = List.replicate 0 2 ++ List.replicate (n + 1) 3 ++ List.replicate s 2 ++
      1 :: (List.replicate (n + d + 2) 3 ++ List.replicate z 2) ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    simp [Rc.tl, hacc, hE]
  rw [hwt] at h4 h5 h6 ⊢
  have h7 := cmpAccLt (A ++ [3] ++ [3] ++ [w.Pf]) n d 0 s z (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)
    ((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil)) sR'
  simp only [hO, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 ⊢
  refine h4.trans (h5.trans (h6.trans (h7.of_eq rfl ?_)))
  simp [Rc.tl, hacc, List.replicate_succ, Nat.add_comm, Nat.add_left_comm]

theorem fa0OGt (A : List Nat) (w : Rc) (hw : w.DE) (hO : w.O = 3) (e d s z : Nat)
    (hacc : w.acc = List.replicate (e + d + 2) 3 ++ List.replicate s 2)
    (hE : w.E = List.replicate (e + 1) 3 ++ List.replicate z 2)
    (ws : List Rc) (hws : ∀ x ∈ ws, x.DE) (hA : Sym4 A) :
    znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.Pf] ++ 1 :: (w.tl ++ tailB ws)))
      (hd QNTT.ODL (A ++ [3, 3, w.Pf] ++ [1] ++ List.replicate e 2 ++ [2] ++ (3 :: (List.replicate d 3 ++ List.replicate s 2)) ++ [1] ++ [3])
        (List.replicate (z + e) 2 ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws))) := by
  have ho := hw.ok
  have sTl : Sym4 (w.tl ++ tailB ws) := (w.tl_sym4 ho).app (tailB_sym4 ws (fun x hx => (hws x hx).ok))
  have sA3 : Sym4 (A ++ [3]) := hA.app (sym4_cell 3 (by simp))
  have h4 := fa0Mark A w.F (w.O :: w.Pf :: 1 :: (w.tl ++ tailB ws)) ho.F hA
    (sym4_B ho.O (sym4_B ho.Pf (sym4_M sTl)))
  have h5 := fa1o (A ++ [3]) (w.Pf :: 1 :: (w.tl ++ tailB ws)) sA3 (sym4_B ho.Pf (sym4_M sTl))
  have h6 := faoSkip (A ++ [3] ++ [3]) [w.Pf] (w.tl ++ tailB ws) (sA3.app (sym4_cell 3 (by simp)))
    (fun y hy => by simp at hy; subst hy; exact ho.Pf) sTl
  have sR' : Sym4 (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    have := sTl
    simp only [Rc.tl] at this
    simp [hacc, hE] at this
    simpa using this.2.2.2.2.2.2
  have hwt : w.tl ++ tailB ws = List.replicate 0 2 ++ List.replicate (e + d + 2) 3 ++ List.replicate s 2 ++
      1 :: (List.replicate (e + 1) 3 ++ List.replicate z 2) ++ 1 :: (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws) := by
    simp [Rc.tl, hacc, hE]
  rw [hwt] at h4 h5 h6 ⊢
  have h7 := cmpAccGt (A ++ [3] ++ [3] ++ [w.Pf]) e d 0 s z (w.b0 :: (w.br ++ 1 :: w.u0 :: w.ur) ++ tailB ws)
    ((sA3.app (sym4_cell 3 (by simp))).app (sym4_B ho.Pf Sym4.nil)) sR'
  simp only [hO, List.append_assoc, List.cons_append, List.nil_append] at h4 h5 h6 h7 ⊢
  refine h4.trans (h5.trans (h6.trans (h7.of_eq rfl ?_)))
  simp [Rc.tl, hacc, List.replicate_succ, Nat.add_comm, Nat.add_left_comm]


/-- The refuted outcome, generalised: the parameter region `Nn` is `3^a' 2^b'`, and the tape is given whole. -/
def OdOut' (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Qp : List Nat) (N : Nat) (T : List Nat) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ a' + b' = N ∧ 1 ≤ N ∧
    GoodW (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ List.replicate b' 2))) ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    T = (Wf ++ 1 :: (S0 ++ 1 :: (Qp ++ List.replicate a' 3 ++ List.replicate b' 2))) ++ sepRest (o :: os)

theorem OdOut'.toO {D Wf Qp N T} (h : OdOut' D Wf Qp N T) : TapeOutO T := by
  obtain ⟨S0, a', b', o, os, a, b, c, c1, g, ok, d, e⟩ := h
  exact ⟨_, o, os, g, ok, e⟩

theorem OdOut'.noB {D Wf Qp N T} (h : OdOut' D Wf Qp N T) : NoB T := by
  obtain ⟨S0, a', b', o, os, a, b, c, c1, g, ok, d, e⟩ := h
  rw [e]
  have sr : sepRest (o :: os) = 1 :: 1 :: tapeL (o :: os) := rfl
  refine NoB_app_iff.2 ⟨g.noB, ?_⟩
  rw [sr]
  exact fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp [NB]
    · simp [NB]
    · exact tapeL_noB _ ok x hx

theorem OdOut.to' {D Wf Qp N R'} (h : OdOut D Wf Qp N R') : OdOut' D Wf Qp N ((Wf ++ [1]) ++ R') := by
  obtain ⟨S0, a', b', o, os, hS, hne, hN, hg, hos, hd, e⟩ := h
  refine ⟨S0, a', b' + 1, o, os, hS, hne, by omega, by omega, by simpa [List.replicate_succ] using hg, hos, hd, ?_⟩
  simpa [List.replicate_succ] using e

def StepNone (D : List (Nat × Nat × Nat × Nat × Nat)) : Prop :=
  ∃ (o : ORec) (os : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧ odoStepR (o :: os) = none

def StepInfo (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Kf Cf : List Nat) (N : Nat) (v : List Nat) (os' : List ORec) : Prop :=
  ∃ (S0 : List Nat) (a' b' : Nat) (o : ORec) (os : List ORec), BitsD S0 ∧ S0 ≠ [] ∧ a' + b' = N ∧ 1 ≤ N ∧
    (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧ odoStepR (o :: os) = some os' ∧
    v = (Wf ++ 1 :: (S0 ++ 1 :: ((Kf ++ 1 :: Cf) ++ [1] ++ List.replicate a' 3 ++ List.replicate b' 2))).map
      (fun x => if x = 1 then 1 else 3)

theorem odlNext3 (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Kf Cf : List Nat) (hW : BitsD Wf) (hK : BitsD Kf) (hC : BitsD Cf)
    (N : Nat) (L R' : List Nat) (hT : OdOut' D Wf ((Kf ++ 1 :: Cf) ++ [1]) N (L ++ R')) :
    (∃ u v os' X R'', Rest u v ∧ StepInfo D Wf Kf Cf N v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach (hd QNTT.ODL L R') (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone D ∧ znttLogic.Reach (hd QNTT.ODL L R') (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 :: (List.replicate N 3 ++ List.replicate (n0 + 1) 0)))))) := by
  have hT' := hT.toO
  have sT := tapeOutO_sym4 hT'
  have hR : Sym4 R' := (Sym4_app_iff.1 sT).2
  have hL : NoB L := (NoB_app_iff.1 hT.noB).1
  obtain ⟨S0, a', b', o, os, hS0, hS0ne, hN, hN1, hg, hos, hdg, hXY⟩ := hT
  have hXY' : L ++ R' = (Wf ++ 1 :: (S0 ++ 1 :: ((Kf ++ 1 :: Cf) ++ [1] ++ List.replicate a' 3 ++ List.replicate b' 2))) ++
      1 :: 1 :: tapeL (o :: os) := hXY
  obtain ⟨v, hv, h1, h2⟩ := odFail _ hg o os hos _ _ hXY' hL hR
  cases hs : odoStepR (o :: os) with
  | some os' =>
    obtain ⟨X, R'', e, hr⟩ := h1 os' hs
    exact Or.inl ⟨_, v, os', X, R'', hv, ⟨S0, a', b', o, os, hS0, hS0ne, hN, hN1, hos, hdg, hs, by
      rw [rest_map hv]⟩, e, hr⟩
  | none =>
    right
    have hb := h2 hs
    have hvm := rest_map hv
    have hgv : GoodW v := hv.goodW
    have hrep : List.replicate a' 3 ++ List.replicate b' 3 = List.replicate N 3 := by
      subst hN
      rw [List.replicate_append_replicate]
    have hvE : v = Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
        (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: List.replicate N 3))) := by
      rw [hvm, ← hrep]
      simp [List.map_append, List.map_replicate, List.append_assoc]
    obtain ⟨L0, rfl⟩ : ∃ L0, N = L0 + 1 := ⟨N - 1, by omega⟩
    have hrk : ∀ x ∈ resetAll (o :: os), x.Ok := resetAll_ok _ hos
    have hnb : NoB (tapeL (resetAll (o :: os))) := tapeL_noB _ hrk
    have hAeq : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) =
        (Wf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (S0.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 :: (Cf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
            List.replicate (L0 + 1) 3)))) ++ 1 :: 1 :: tapeL (resetAll (o :: os)) := by
      rw [hvE]; simp [List.append_assoc]
    have hnbA : NoB ((v ++ [1, 1]) ++ tapeL (resetAll (o :: os))) := by
      have h1 : NoB v := hgv.noB
      exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨h1, by intro x hx; simp at hx; simp [hx, NB]⟩, hnb⟩
    have hne : (v ++ [1, 1]) ++ tapeL (resetAll (o :: os)) ≠ [] := by simp
    obtain ⟨X, hX, hXr⟩ := beepToSU1 _ hnbA hne
    have hbo := beepOk (Wf.map (fun x => if x = 1 then 1 else 3)) (S0.map (fun x => if x = 1 then 1 else 3))
      (Kf.map (fun x => if x = 1 then 1 else 3)) (Cf.map (fun x => if x = 1 then 1 else 3))
      (tapeL (resetAll (o :: os))) L0 (bits_map hW) (bits_map hS0) (bits_map hK) (bits_map hC)
      (by rw [← hvE]; exact hgv) hnb
    refine ⟨_, (tapeL (resetAll (o :: os))).length, ⟨o, os, hos, hdg, hs⟩, hb, X, hX, ?_⟩
    rw [hAeq] at hXr
    exact hXr.trans hbo



theorem VR.toRc_bu (v : VR) (hv : v.Ok) :
    v.toRc.b0 :: (v.toRc.br ++ 1 :: v.toRc.u0 :: v.toRc.ur) = v.b ++ 1 :: v.u := by
  obtain ⟨b0, br, hB⟩ := List.exists_cons_of_ne_nil hv.bne
  obtain ⟨u0, ur, hU⟩ := List.exists_cons_of_ne_nil hv.une
  simp [VR.toRc, VR.toRcA, hB, hU]

theorem fa0GFail (A : List Nat) (w : VR) (hw : w.Ok) (ws : List VR) (hws : ∀ x ∈ ws, x.Ok) (hA : Sym4 A)
    (hO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hdR QNTT.FA0 A ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) (hd QNTT.ODL L R) ∧
      L ++ R = A ++ [3, w.O, w.P] ++ 1 :: (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have hwd : w.toRc.DE := ⟨w.toRcA_ok hw _ (fld_bits _ _), w.toRcA_rest _⟩
  have hws' : ∀ x ∈ ws.map VR.toRc, x.DE := by
    intro x hx; simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v.toRcA_ok (hws v hv) _ (fld_bits _ _), v.toRcA_rest _⟩
  have hkw := hw.kw
  have hk1 := hw.k1
  obtain ⟨n, hn⟩ : ∃ n, w.k = n + 1 := ⟨w.k - 1, by omega⟩
  have hbu := VR.toRc_bu w hw
  have hO' : w.toRc.O = 3 := by simpa [VR.toRc, VR.toRcA] using hO
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- e < k: E is smaller
    obtain ⟨d, hd⟩ : ∃ d, w.k = e + d + 1 := ⟨w.k - e - 1, by omega⟩
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have b6 := fa0OGt A w.toRc hwd hO' e' d (w.w - w.k) z
      (by have hk : w.k = e' + d + 2 := by omega
          simp [VR.toRc, VR.toRcA, fld, hk]) (by simp [VR.toRc, VR.toRcA, hE, fld, he'])
      (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, hbu] at b6
    have hlen : w.E.length = e + z := by rw [hE]; simp [fld]
    refine ⟨_, _, List.replicate e' 2 ++ 2 :: 3 :: (List.replicate d 3 ++ List.replicate (w.w - w.k) 2),
      3 :: List.replicate (z + e') 2, ?_, ?_, ?_, ?_, b6.of_eq rfl rfl, ?_⟩
    · exact bd_app (BitsD.rep _ _ (by simp)) (BitsD.cons (by simp) (BitsD.cons (by simp)
        (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))))
    · exact BitsD.cons (by simp) (BitsD.rep _ _ (by simp))
    · simp; omega
    · simp [hlen]; omega
    · simp [VR.toRc, VR.toRcA, hO, List.append_assoc]
  · obtain ⟨d, hd⟩ : ∃ d, e = w.k + d + 1 := ⟨e - w.k - 1, by omega⟩
    have b6 := fa0OLt A w.toRc hwd hO' n d (w.w - w.k) z
      (by simp [VR.toRc, VR.toRcA, fld, hn]) (by have he2 : e = n + d + 2 := by omega
                                                 simp [VR.toRc, VR.toRcA, hE, fld, he2])
      (ws.map VR.toRc) hws' hA
    rw [VR.toRc_tl w hw, tailB_toRc ws hws, hbu] at b6
    have hlen : w.E.length = e + z := by rw [hE]; simp [fld]
    refine ⟨_, _, List.replicate n 2 ++ 3 :: List.replicate (w.w - w.k) 2,
      3 :: 3 :: (List.replicate d 3 ++ List.replicate (z + n) 2), ?_, ?_, ?_, ?_, b6.of_eq rfl rfl, ?_⟩
    · exact bd_app (BitsD.rep _ _ (by simp)) (BitsD.cons (by simp) (BitsD.rep _ _ (by simp)))
    · exact BitsD.cons (by simp) (BitsD.cons (by simp) (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp))))
    · simp; omega
    · simp [hlen]; omega
    · simp [VR.toRc, VR.toRcA, hO, List.append_assoc]


theorem colAdvanceGF (c w : VR) (ws : List VR) (hc : c.Ok) (hw : w.Ok) (hws : ∀ x ∈ ws, x.Ok) (hF : c.F = 3)
    (hO : c.O = 2 ∨ c.O = 3) (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k)
    (Pm : List Nat) (hP : GoodW Pm) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (a s : Nat) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c a 0 s (w :: ws)) []) (hd QNTT.ODL L R) ∧
      L ++ R = Pm ++ tailB (pre ++ [c.done a s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have hvs : ∀ x ∈ w :: ws, x.Ok := fun x hx => by
    simp at hx; rcases hx with rfl | hx
    · exact hw
    · exact hws x hx
  have sPm := hP.sym4
  have sPre : Sym4 (tailB pre) := tailB_sym4 pre (fun x hx => (hpre x hx).1)
  have s2 : ∀ j, Sym4 (List.replicate j 2) := fun j => (BitsD.rep j 2 (by simp)).sym4
  have hA := curToCA0 c hc hF hO Pm hP pre hpre a s (w :: ws) hvs
  have sU := hc.u.sym4
  have sB := hc.b.sym4
  have sE := hc.E.sym4
  have sW : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have sT : Sym4 (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))) := by
    refine sE.app (sym4_M (sB.app (sym4_M (sU.app ?_))))
    exact tailVR_sym4 (w :: ws) hvs
  have b4 := ca0Sweep (Pm ++ tailB pre ++ [1, 1, 3, c.O, c.P]) (List.replicate a 2 ++ [3])
    (List.replicate s 2 ++ 1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ tailVR (w :: ws)))))
    ((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P Sym4.nil))))))
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; simp [hx])) ((s2 s).app (sym4_M sT))
  have b5 := caNext c hc (Pm ++ tailB pre) (List.replicate a 2 ++ 3 :: List.replicate s 2)
    ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) (sPm.app sPre)
    (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all))
    (by cases a <;> simp [List.replicate_succ]) sW
  obtain ⟨L, R, acc2, E2, h1, h2, h3, h4, b6, hLR⟩ := fa0GFail
    (Pm ++ tailB pre ++ [1, 1, 2, c.O, c.P, 1] ++ (List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: (c.u ++ [1, 1])))) w hw ws hws
    (((((sPm.app sPre).app (sym4_M (sym4_M (sym4_B (by simp) (sym4_B hc.O (sym4_B hc.P (sym4_M Sym4.nil))))))).app
      (BitsD.sym4 (bd_app (BitsD.rep _ _ (by simp)) (fun x hx => by simp at hx; rcases hx with rfl | hx <;> simp_all)))).app
      (sym4_M (sE.app (sym4_M (sB.app (sym4_M (sU.app (sym4_M (sym4_M Sym4.nil))))))))))
    hwO e z he hE hne
  have hdone : (c.done a s).body = [2, c.O, c.P] ++ 1 :: ((List.replicate a 2 ++ 3 :: List.replicate s 2) ++
      1 :: (c.E ++ 1 :: (c.b ++ 1 :: c.u))) := by
    have e : (c.done a s).tl = (c.toRcA (List.replicate a 2 ++ 3 :: List.replicate s 2)).tl := rfl
    rw [Rc.body_eq, e, VR.toRcA_tl c hc]
    rfl
  refine ⟨L, R, acc2, E2, h1, h2, h3, h4, ?_, ?_⟩
  · simp only [tailB_append, tailB, hdone, List.append_nil, curTapeG, List.append_assoc, List.cons_append,
      List.nil_append, List.replicate_succ] at hA b4 b5 b6 ⊢
    exact hA.trans (b4.trans (b5.trans b6))
  · rw [hLR]
    simp [tailB_append, tailB, hdone, List.append_assoc]


theorem colStepNF (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 2) (Pm : List Nat) (hP : GoodW Pm)
    (pre : List Rc) (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (r s : Nat) (vs : List VR)
    (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.RFL (curTapeG Pm pre c 0 r s vs) []) (hd QNTT.ODL L R) ∧
      L ++ R = Pm ++ tailB (pre ++ [c.done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have h1 := cursorLoop c hc hF hO Pm hP pre hpre s r 0 vs hvs
  rw [hw, Nat.zero_add] at h1
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ := colAdvanceGF c w ws hc (hok w (by simp))
    (fun x hx => hok x (by simp [hx])) hF (Or.inl hO) hwO e z he hE hne Pm hP pre hpre r s
  rw [curTapeG_eq _ _ _ hO]
  rw [curTapeG_eq _ _ _ hO] at hr
  exact ⟨L, R, a2, E2, k1, k2, k3, k4, h1.trans hr, hLR⟩

theorem colStepOF (n : Nat) (c : VR) (hc : c.Ok) (hF : c.F = 3) (hO : c.O = 3) (hm : c.m = 0) (hn : c.n = n)
    (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) (pre : List Rc)
    (hpre : ∀ x ∈ pre, x.Ok ∧ x.acc ≠ [] ∧ x.F = 2) (s wE : Nat) (hwE : 2 ≤ wE)
    (r : Nat) (p : Nat × Nat) (e0 : Nat) (hp : 1 ≤ p.2) (he0 : 1 ≤ e0) (hew : e0 ≤ wE) (hE0 : c.E = fld wE e0)
    (vs : List VR) (hvs : ∀ x ∈ vs, x.Ok) (w : VR) (ws : List VR) (hw : stepN r vs = w :: ws)
    (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k) :
    ∃ (L R acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.ODL L R) ∧
      L ++ R = (Wf ++ 1 :: (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3 ++ 1 :: P2)) ++
        tailB (pre ++ [({ c with E := fld wE (eAdv wE (r * n) e0) } : VR).done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have h1 := outLoop n c hc hF hO hm hn Wf hW P2 hP2 pre hpre s wE hwE r 0 p e0 vs hvs hp he0 hew
  have hb := eAdv_bounds wE (r * n) e0 he0 hew
  have hElen := hc.Elen
  rw [hE0, fld_len _ _ hew] at hElen
  have hc' : ({ c with E := fld wE (eAdv wE (r * n) e0) } : VR).Ok :=
    { F := hc.F, O := hc.O, P := hc.P, k1 := hc.k1, kw := hc.kw, E := fld_bits _ _,
      Elen := by show 2 ≤ (fld wE (eAdv wE (r * n) e0)).length; rw [fld_len _ _ hb.2]; exact hElen }
  have hG := goodW_reg Wf (List.replicate (sAdv (r * n) p).1 2 ++ List.replicate (sAdv (r * n) p).2 3) P2 hW
    (bd_app (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)))
    (by have := sAdv_pos (r * n) p hp; obtain ⟨q', hq'⟩ : ∃ q', (sAdv (r * n) p).2 = q' + 1 := ⟨(sAdv (r * n) p).2 - 1, by omega⟩
        simp [hq', List.replicate_succ]) hP2
  have hok := stepN_ok r vs hvs
  rw [hw] at hok
  obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ := colAdvanceGF ({ c with E := fld wE (eAdv wE (r * n) e0) } : VR) w ws hc'
    (hok w (by simp)) (fun x hx => hok x (by simp [hx])) hF (Or.inr hO) hwO e z he hE hne _ hG pre hpre r s
  rw [hw, Nat.zero_add] at h1
  refine ⟨L, R, a2, E2, k1, k2, k3, k4, (LTM.Reach.of_eq h1 ?_ ?_).trans hr, hLR⟩
  · simp [curTapeG, hE0, hO, List.append_assoc]
  · simp [curTapeG, hO, VR.b, VR.u, List.append_assoc]


/-- The output-node `E` register is a unary-marked string. -/
def EF (x : VR) : Prop := x.O = 3 → ∃ e, 1 ≤ e ∧ e ≤ x.E.length ∧ x.E = fld x.E.length e

theorem EF_of {x y : VR} (hE : x.E = y.E) (hO : x.O = y.O) (h : EF y) : EF x := by
  intro h3
  rw [hO] at h3
  obtain ⟨e, h1, h2, h4⟩ := h h3
  exact ⟨e, h1, by rw [hE]; exact h2, by rw [hE]; exact h4⟩

theorem vis_EO (v : VR) : v.vis.E = v.E ∧ v.vis.O = v.O := by unfold VR.vis; split <;> simp
theorem dec_EO (v : VR) : v.dec.E = v.E ∧ v.dec.O = v.O := by unfold VR.dec; split <;> simp

theorem stepList_EF : ∀ vs : List VR, (∀ x ∈ vs, EF x) → ∀ x ∈ stepList vs, EF x
  | [], _ => by simp [stepList]
  | v :: vs, h => by
    intro x hx
    simp only [stepList, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact EF_of ((vis_EO _).1) ((vis_EO _).2) (EF_of rfl rfl (h v (by simp)) : EF v.inc)
    · exact EF_of ((vis_EO _).1) ((vis_EO _).2) (h y (by simp [hy]))

theorem stepN_EF (r : Nat) : ∀ vs : List VR, (∀ x ∈ vs, EF x) → ∀ x ∈ stepN r vs, EF x := by
  induction r with
  | zero => intro vs h; simpa [stepN] using h
  | succ r ih => intro vs h; exact ih _ (stepList_EF vs h)

theorem dec_EF (vs : List VR) (h : ∀ x ∈ vs, EF x) : ∀ x ∈ vs.map VR.dec, EF x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact EF_of (dec_EO y).1 (dec_EO y).2 (h y hy)

theorem EF_mismatch (w : VR) (hw : w.Ok) (hEF : EF w) (hO : w.O = 3)
    (hn : ¬ (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)) :
    ∃ e z, 1 ≤ e ∧ w.E = fld (e + z) e ∧ e ≠ w.k := by
  obtain ⟨e, h1, h2, h3⟩ := hEF hO
  have h5 : e + (w.E.length - e) = w.E.length := by omega
  refine ⟨e, w.E.length - e, h1, by rw [h5]; exact h3, ?_⟩
  intro hk
  apply hn
  intro _
  subst hk
  exact ⟨w.E.length - w.k, hw.k1, by rw [h5]; exact h3⟩

/-- A cursor-form record as an odometer record (digits are `therm`/`winStr`). -/
def VR.toOc (v : VR) : ORec :=
  { F := v.F, O := v.O, Pf := v.P, acc := fld v.w v.k, E := v.E,
    d := v.n, r := v.n + 1 + v.s, z := v.a, k := v.c + 1, m := v.t }

theorem VR.recd_toOc (v : VR) (hm : v.m = 0) : v.recd = 1 :: 1 :: v.toOc.tape := by
  have hb : v.b = therm v.n (v.n + 1 + v.s) := by simp [VR.b, therm, hm]
  have hu : v.u = winStr v.a (v.c + 1) v.t := by simp [VR.u, winStr]
  simp only [VR.recd, VR.tl, VR.toOc, ORec.tape, hb, hu]
  simp

theorem VR.toOc_ok (v : VR) (hv : v.Ok) : v.toOc.Ok :=
  { hF := by
      have h1 := hv.F; have h2 := hv.O; have h3 := hv.P
      simp at h1 h2 h3
      simp [VR.toOc]; omega,
    acc := fld_bits _ _, E := hv.E, d := by simp [VR.toOc], k := by simp [VR.toOc], Elen := hv.Elen }

theorem VR.toOc_dg (v : VR) (hv : v.Ok) : v.toOc.dgO = v.dg := by
  have := fld_len v.w v.k hv.kw
  simp [VR.toOc, ORec.dgO, VR.dg, this]; omega

theorem sepRest_append : ∀ (l1 l2 : List ORec), sepRest (l1 ++ l2) = sepRest l1 ++ sepRest l2
  | [], l2 => by simp [sepRest]
  | o :: os, l2 => by simp [sepRest, sepRest_append os l2]

theorem tailVR_sepRest : ∀ (vs : List VR), (∀ x ∈ vs, x.m = 0) → tailVR vs = sepRest (vs.map VR.toOc)
  | [], _ => by simp [tailVR, sepRest]
  | v :: vs, h => by
    have := tailVR_sepRest vs (fun x hx => h x (by simp [hx]))
    simp only [tailVR, List.map_cons, List.flatten_cons, sepRest] at this ⊢
    rw [VR.recd_toOc v (h v (by simp)), this]
    simp


theorem failSep (Pm : List Nat) (pre : List Rc) (os0 : List ORec) (hpre : tailB pre = sepRest os0)
    (hos0 : ∀ y ∈ os0, y.Ok) (x : VR) (hx : x.Ok) (hxm : x.m = 0) (r s : Nat) (hrs : r + 1 + s = x.w)
    (w : VR) (hw : w.Ok) (hwm : w.m = 0) (ws : List VR) (hws : ∀ y ∈ ws, y.Ok) (hwsm : ∀ y ∈ ws, y.m = 0)
    (acc2 E2 : List Nat) (hacc : BitsD acc2) (hE2 : BitsD E2) (hl1 : acc2.length = w.w) (hl2 : E2.length = w.E.length) :
    ∃ os : List ORec, (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = os0.map ORec.dgO ++ x.dg :: w.dg :: ws.map VR.dg ∧
      Pm ++ tailB (pre ++ [x.done r s]) ++ [1, 1, 3, w.O, w.P, 1] ++
        (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) = Pm ++ sepRest os := by
  let w' : ORec := ⟨3, w.O, w.P, acc2, E2, w.n, w.n + 1 + w.s, w.a, w.c + 1, w.t⟩
  have hw'ok : w'.Ok := by
    refine { hF := ?_, acc := hacc, E := hE2, d := by simp [w'], k := by simp [w'], Elen := ?_ }
    · have h2 := hw.O; have h3 := hw.P
      simp at h2 h3
      simp [w']; omega
    · show 2 ≤ E2.length
      rw [hl2]; exact hw.Elen
  refine ⟨os0 ++ x.toO r s :: w' :: ws.map VR.toOc, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_append, List.mem_cons, List.mem_map] at hy
    rcases hy with hy | rfl | rfl | ⟨v, hv, rfl⟩
    · exact hos0 y hy
    · exact toO_ok x hx r s hrs
    · exact hw'ok
    · exact VR.toOc_ok v (hws v hv)
  · simp only [List.map_append, List.map_cons, List.map_map]
    have e1 := toO_dgO x r s hrs
    have e2 : w'.dgO = w.dg := by simp [w', ORec.dgO, VR.dg, hl1]; omega
    have e3 : ws.map (ORec.dgO ∘ VR.toOc) = ws.map VR.dg :=
      List.map_congr_left (fun v hv => VR.toOc_dg v (hws v hv))
    rw [e1, e2, e3]
  · have hb : w.b = therm w.n (w.n + 1 + w.s) := by simp [VR.b, therm, hwm]
    have hu : w.u = winStr w.a (w.c + 1) w.t := by simp [VR.u, winStr]
    rw [tailVR_sepRest ws hwsm, tailB_append]
    simp only [tailB, List.append_nil, hpre, sepRest_append, sepRest, List.append_assoc, List.cons_append,
      List.nil_append, VR.done_body_toO x hx hxm r s, ORec.tape, w', hb, hu]


theorem passLoopF (Wf : List Nat) (hW : BitsD Wf) (P2 : List Nat) (hP2 : GoodW (1 :: P2)) :
    ∀ (n : Nat) (vs : List VR) (c : VR) (pre : List Rc) (p : Nat × Nat) (r s : Nat) (os0 : List ORec)
      (D : List (Nat × Nat × Nat × Nat × Nat)),
    vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → (∀ x ∈ vs, EF x) → PreOk pre → 1 ≤ p.2 →
    r + 1 + s = c.w → c.m = 0 → (∀ x ∈ vs, x.m = 0) → tailB pre = sepRest os0 → (∀ y ∈ os0, y.Ok) →
    os0.map ORec.dgO ++ (c :: vs).map VR.dg = D → ¬ PassCmp n r vs →
    ∃ (L R : List Nat) (os : List ORec) (p' : Nat × Nat), (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = D ∧ 1 ≤ p'.2 ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: P2)) pre c 0 r s vs) [])
        (hd QNTT.ODL L R) ∧
      L ++ R = (Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: P2)) ++ sepRest os := by
  intro n
  induction n with
  | zero =>
    intro vs c pre p r s os0 D _ _ _ _ _ _ _ _ _ _ _ _ _ hcmp
    exact absurd trivial (by simpa [PassCmp] using hcmp)
  | succ n ih =>
    intro vs c pre p r s os0 D hlen hc hvs hom hEF hpre hp hrs hcm hvm hpos hos0 hD hcmp
    obtain ⟨hcOk, hF, hOut⟩ := hc
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hwsOk : ∀ x ∈ ws, x.Ok := fun x hx => hok x (by simp [hx])
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    obtain ⟨hdgs, hmz⟩ := dg_stepN_pos r vs hvm
    rw [hw] at hdgs hmz
    have hwm0 : w.m = 0 := hmz w (by simp)
    have hwsm0 : ∀ x ∈ ws, x.m = 0 := fun x hx => hmz x (by simp [hx])
    have hEFs := stepN_EF r vs hEF
    rw [hw] at hEFs
    have hPm := pm_good Wf P2 hW hP2 p hp
    have hcmp2 : ¬ ((w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k) ∧ PassCmp n (w.k - 1) (ws.map VR.dec)) := by
      simpa [PassCmp, hw] using hcmp
    by_cases hh : (w.O = 3 → ∃ z, 1 ≤ w.k ∧ w.E = fld (w.k + z) w.k)
    · -- compare succeeds: continue
      have hcmp3 : ¬ PassCmp n (w.k - 1) (ws.map VR.dec) := fun h => hcmp2 ⟨hh, h⟩
      have hinv := curG_inv w hwOk hwm
      have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact y.dec_ok (hwsOk y hy)
      have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
      have hkw := curG_kw w
      have hk1 := hwOk.k1; have hkw' := hwOk.kw
      have hrs' : w.k - 1 + 1 + (w.w - w.k) = w.curG.w := by rw [hkw.2]; omega
      have hm' : w.curG.m = 0 := curG_m0 w hwm0
      have hvm' : ∀ x ∈ ws.map VR.dec, x.m = 0 := by
        intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact dec_m0 y (hwsm0 y hy)
      have hdgE : (w.curG :: ws.map VR.dec).map VR.dg = (w :: ws).map VR.dg := by
        simp only [List.map_cons, List.map_map]
        rw [(dg_curG w).1]
        congr 1
        exact List.map_congr_left (fun y _ => (dg_dec y).1)
      by_cases hO : c.O = 2
      · have h1 := colStepN c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hh
        have hpo := preOk_done pre hpre c hcOk r s
        have hos' : tailB (pre ++ [c.done r s]) = sepRest (os0 ++ [c.toO r s]) := by
          rw [tailB_append, sepRest_append]
          simp only [tailB, sepRest, List.append_nil, hpos, VR.done_body_toO c hcOk hcm r s]
        have hD' : (os0 ++ [c.toO r s]).map ORec.dgO ++ (w.curG :: ws.map VR.dec).map VR.dg = D := by
          rw [hdgE, hdgs, ← hD, List.map_append, List.map_cons, List.map_nil, toO_dgO c r s hrs]
          simp
        obtain ⟨L, R, os, p', k1, k2, k3, k4, k5⟩ :=
          ih (ws.map VR.dec) w.curG (pre ++ [c.done r s]) p (w.k - 1) (w.w - w.k) (os0 ++ [c.toO r s]) D hlenws hinv
            hwsOk' homws (dec_EF ws (fun x hx => hEFs x (by simp [hx]))) hpo hp hrs' hm' hvm' hos'
            (by intro y hy; simp only [List.mem_append, List.mem_singleton] at hy
                rcases hy with hy | rfl
                · exact hos0 y hy
                · exact toO_ok c hcOk r s hrs) hD' hcmp3
        exact ⟨L, R, os, p', k1, k2, k3, h1.trans k4, k5⟩
      · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
        obtain ⟨hm, e, he, hew, hE⟩ := hOut hO3
        have hElen := hcOk.Elen
        have h1 := colStepO c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e hp he hew hE vs hvs w ws
          hw hh
        have hb := eAdv_bounds c.E.length (r * c.n) e he hew
        have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).Ok :=
          { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
            Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e)).length; rw [fld_len _ _ hb.2]; exact hElen }
        have hpo := preOk_done pre hpre _ hc' r s
        have hrs'' : r + 1 + s = ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).w := hrs
        have hcm' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).m = 0 := hcm
        have hos' : tailB (pre ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).done r s]) =
            sepRest (os0 ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).toO r s]) := by
          rw [tailB_append, sepRest_append]
          simp only [tailB, sepRest, List.append_nil, hpos, VR.done_body_toO _ hc' hcm' r s]
        have hD' : (os0 ++ [({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e) } : VR).toO r s]).map ORec.dgO ++
            (w.curG :: ws.map VR.dec).map VR.dg = D := by
          rw [hdgE, hdgs, ← hD, List.map_append, List.map_cons, List.map_nil, toO_dgO _ r s hrs'']
          simp [VR.dg]
        obtain ⟨L, R, os, p', k1, k2, k3, k4, k5⟩ :=
          ih (ws.map VR.dec) w.curG _ (sAdv (r * c.n) p) (w.k - 1) (w.w - w.k) _ D hlenws hinv
            hwsOk' homws (dec_EF ws (fun x hx => hEFs x (by simp [hx]))) hpo (sAdv_pos _ p hp) hrs' hm' hvm' hos'
            (by intro y hy; simp only [List.mem_append, List.mem_singleton] at hy
                rcases hy with hy | rfl
                · exact hos0 y hy
                · exact toO_ok _ hc' r s hrs'') hD' hcmp3
        exact ⟨L, R, os, p', k1, k2, k3, h1.trans k4, k5⟩
    · -- compare fails now
      have hwO : w.O = 3 := Classical.byContradiction fun h => hh (fun h' => absurd h' h)
      obtain ⟨e, z, he, hE, hne⟩ := EF_mismatch w hwOk (hEFs w (by simp)) hwO hh
      by_cases hO : c.O = 2
      · obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ :=
          colStepNF c hcOk hF hO _ hPm pre hpre r s vs hvs w ws hw hwO e z he hE hne
        obtain ⟨os, hos, hdos, hT⟩ := failSep _ pre os0 hpos hos0 c hcOk hcm r s hrs w hwOk hwm0 ws hwsOk hwsm0 a2 E2 k1 k2 k3 k4
        refine ⟨L, R, os, p, hos, ?_, hp, hr, ?_⟩
        · rw [hdos, ← hD, List.map_cons, ← hdgs]; simp
        · rw [hLR, hT]
      · have hO3 : c.O = 3 := by have := hcOk.O; simp at this; omega
        obtain ⟨hm, e0, he0, hew, hE0⟩ := hOut hO3
        have hElen := hcOk.Elen
        have hb := eAdv_bounds c.E.length (r * c.n) e0 he0 hew
        have hc' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).Ok :=
          { F := hcOk.F, O := hcOk.O, P := hcOk.P, k1 := hcOk.k1, kw := hcOk.kw, E := fld_bits _ _,
            Elen := by show 2 ≤ (fld c.E.length (eAdv c.E.length (r * c.n) e0)).length; rw [fld_len _ _ hb.2]; exact hElen }
        have hrs'' : r + 1 + s = ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).w := hrs
        have hcm' : ({ c with E := fld c.E.length (eAdv c.E.length (r * c.n) e0) } : VR).m = 0 := hcm
        obtain ⟨L, R, a2, E2, k1, k2, k3, k4, hr, hLR⟩ :=
          colStepOF c.n c hcOk hF hO3 hm rfl Wf hW P2 hP2 pre hpre s c.E.length hElen r p e0 hp he0 hew hE0 vs hvs w ws hw
            hwO e z he hE hne
        obtain ⟨os, hos, hdos, hT⟩ := failSep _ pre os0 hpos hos0 _ hc' hcm' r s hrs'' w hwOk hwm0 ws hwsOk hwsm0 a2 E2 k1 k2 k3 k4
        refine ⟨L, R, os, sAdv (r * c.n) p, hos, ?_, sAdv_pos _ p hp, hr, ?_⟩
        · rw [hdos, ← hD, List.map_cons, ← hdgs]; simp [VR.dg]
        · rw [hLR, hT]


theorem outRec_EF (c : VR) (hc : CurInv c) (r : Nat) : EF (outRec c r) := by
  intro h3
  unfold outRec at h3 ⊢
  by_cases h2 : c.O = 2
  · simp [h2] at h3
  · have hO3 : c.O = 3 := by have := hc.1.O; simp at this; omega
    obtain ⟨_, e, he1, he2, hE⟩ := hc.2.2 hO3
    simp only [h2, if_false] at h3 ⊢
    have hc3 : c.E.count 3 = e := by rw [hE, count3_fld _ _ he2]
    have hb := eAdv_bounds c.E.length (r * c.n) e he1 he2
    rw [hc3]
    have hl : (fld c.E.length (eAdv c.E.length (r * c.n) e)).length = c.E.length := fld_len _ _ hb.2
    exact ⟨eAdv c.E.length (r * c.n) e, hb.1, by simp only [hl]; exact hb.2, by simp only [hl]⟩

theorem loopRun_EF : ∀ (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat),
    CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → vs.length = n →
    (∀ t ∈ (loopRun n c vs r s p).cs, EF t.1) ∧
    EF (outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r') := by
  intro n
  induction n with
  | zero =>
    intro c vs r s p hc hvs hom hl
    simp only [loopRun]
    exact ⟨by simp, outRec_EF c hc r⟩
  | succ n ih =>
    intro c vs r s p hc hvs hom hl
    have hlen' := stepN_length r vs
    obtain ⟨w, ws, hw⟩ : ∃ w ws, stepN r vs = w :: ws := by
      cases h : stepN r vs with
      | nil => rw [h] at hlen'; simp at hlen'; omega
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hok := stepN_ok r vs hvs
    rw [hw] at hok
    have hwOk : w.Ok := hok w (by simp)
    have hout := stepN_outM r vs hom
    rw [hw] at hout
    have hwm : w.O = 3 → w.m = 0 := hout w (by simp)
    have hwsOk' : ∀ x ∈ ws.map VR.dec, x.Ok := by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx
      exact y.dec_ok (hok y (by simp [hy]))
    have homws : OutM (ws.map VR.dec) := dec_outM ws (fun x hx => hout x (by simp [hx]))
    have hlenws : (ws.map VR.dec).length = n := by
      rw [hw] at hlen'; simp at hlen'; simp; omega
    have ih' := ih w.curG (ws.map VR.dec) (w.k - 1) (w.w - w.k) (outP c r p) (curG_inv w hwOk hwm) hwsOk' homws hlenws
    simp only [loopRun, hw]
    refine ⟨?_, ih'.2⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact outRec_EF c hc r
    · exact ih'.1 t ht


theorem faGF (L Pm : List Nat) (hL : NoB L) (hP : GoodW Pm) (w : VR) (hw : w.Ok) (ws : List VR)
    (hws : ∀ x ∈ ws, x.Ok) (hwO : w.O = 3) (e z : Nat) (he : 1 ≤ e) (hE : w.E = fld (e + z) e) (hne : e ≠ w.k)
    (hLe : L = Pm ++ 1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) :
    ∃ (L' R' acc2 E2 : List Nat), BitsD acc2 ∧ BitsD E2 ∧ acc2.length = w.w ∧ E2.length = w.E.length ∧
      znttLogic.Reach (hd QNTT.FAL L []) (hd QNTT.ODL L' R') ∧
      L' ++ R' = Pm ++ [1, 1, 3, w.O, w.P, 1] ++ (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) := by
  have sPm := hP.sym4
  have sMM : Sym4 (Pm ++ [1, 1]) := sPm.app (sym4_M (sym4_M Sym4.nil))
  have sB : Sym4 ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) :=
    hw.hdr3.sym4.app (sym4_M (hw.tl_sym4.app (tailVR_sym4 ws hws)))
  have h1 := falScan L [] hL Sym4.nil
  rw [hLe] at h1
  have h2 := fasGood hP [] (1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws))) Sym4.nil (sym4_M (sym4_M sB))
  have h3 := fasMM Pm ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR ws)) sPm sB
  obtain ⟨L', R', a2, E2, k1, k2, k3, k4, h4, hLR⟩ := fa0GFail (Pm ++ [1, 1]) w hw ws hws sMM hwO e z he hE hne
  refine ⟨L', R', a2, E2, k1, k2, k3, k4, ?_, ?_⟩
  · simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 ⊢
    rw [hLe]
    simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    exact h1.trans (h2.trans (h3.trans h4))
  · rw [hLR]; simp

theorem failSep' (Pm : List Nat) (w : VR) (hw : w.Ok) (hwm : w.m = 0) (ws : List VR) (hws : ∀ y ∈ ws, y.Ok)
    (hwsm : ∀ y ∈ ws, y.m = 0) (acc2 E2 : List Nat) (hacc : BitsD acc2) (hE2 : BitsD E2) (hl1 : acc2.length = w.w)
    (hl2 : E2.length = w.E.length) :
    ∃ os : List ORec, (∀ y ∈ os, y.Ok) ∧ os.map ORec.dgO = w.dg :: ws.map VR.dg ∧
      Pm ++ [1, 1, 3, w.O, w.P, 1] ++ (acc2 ++ 1 :: (E2 ++ 1 :: (w.b ++ 1 :: (w.u ++ tailVR ws)))) = Pm ++ sepRest os := by
  let w' : ORec := ⟨3, w.O, w.P, acc2, E2, w.n, w.n + 1 + w.s, w.a, w.c + 1, w.t⟩
  have hw'ok : w'.Ok := by
    refine { hF := ?_, acc := hacc, E := hE2, d := by simp [w'], k := by simp [w'], Elen := ?_ }
    · have h2 := hw.O; have h3 := hw.P
      simp at h2 h3
      simp [w']; omega
    · show 2 ≤ E2.length
      rw [hl2]; exact hw.Elen
  refine ⟨w' :: ws.map VR.toOc, ?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.mem_map] at hy
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact hw'ok
    · exact VR.toOc_ok v (hws v hv)
  · have e2 : w'.dgO = w.dg := by simp [w', ORec.dgO, VR.dg, hl1]; omega
    have e3 : ws.map (ORec.dgO ∘ VR.toOc) = ws.map VR.dg :=
      List.map_congr_left (fun v hv => VR.toOc_dg v (hws v hv))
    simp only [List.map_cons, List.map_map]
    rw [e2, e3]
  · have hb : w.b = therm w.n (w.n + 1 + w.s) := by simp [VR.b, therm, hwm]
    have hu : w.u = winStr w.a (w.c + 1) w.t := by simp [VR.u, winStr]
    rw [tailVR_sepRest ws hwsm]
    simp only [sepRest, List.append_assoc, List.cons_append, List.nil_append, ORec.tape, w', hb, hu]

theorem faNextF (Pm : List Nat) (hP : GoodW Pm) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat))
    (h : ∀ p ∈ t0 :: ts, p.1.1.Ok ∧ p.1.2.1 + 1 + p.1.2.2 = p.1.1.w ∧ 2 ≤ p.1.1.w ∧ p.2 ∈ [2, 3])
    (hm : ∀ p ∈ t0 :: ts, p.1.1.m = 0)
    (hwO : (t0.1.1.nextPass t0.2).O = 3) (e z : Nat) (he : 1 ≤ e) (hE : (t0.1.1.nextPass t0.2).E = fld (e + z) e)
    (hne : e ≠ (t0.1.1.nextPass t0.2).k) :
    ∃ (L' R' : List Nat) (os : List ORec), (∀ y ∈ os, y.Ok) ∧
      os.map ORec.dgO = (t0 :: ts).map (fun q => q.1.1.dg) ∧
      znttLogic.Reach
        (hd QNTT.FAL (Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
          tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2)) [])
        (hd QNTT.ODL L' R') ∧ L' ++ R' = Pm ++ sepRest os := by
  have h0 := h t0 (by simp)
  have hws : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.Ok := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    have := h p (by simp [hp]); exact VR.nextPass_ok _ this.1 _ this.2.2.2 this.2.2.1
  have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
  have hwsm : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.m = 0 := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨p, hp, rfl⟩ := hx
    simpa [VR.nextPass] using hm p (by simp [hp])
  have hwm : (t0.1.1.nextPass t0.2).m = 0 := by simpa [VR.nextPass] using hm t0 (by simp)
  have e1 := done_ps_vr t0.1.1 h0.1 t0.1.2.1 t0.1.2.2 t0.2 h0.2.1 h0.2.2.1 h0.2.2.2
  have e2 := tailVR_doneX ts (fun p hp => h p (by simp [hp]))
  have hLe : Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2))) =
      Pm ++ [1, 1] ++ (t0.1.1.doneX t0.1.2.1 t0.1.2.2 t0.2).ps.body ++
        tailP (ts.map fun p => p.1.1.doneX p.1.2.1 p.1.2.2 p.2) := by
    rw [e2]
    have := congrArg (fun l => Pm ++ l ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)) e1
    simp only [VR.recd, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    simpa using this.symm
  have hL : NoB (Pm ++ 1 :: 1 :: ([(t0.1.1.nextPass t0.2).F, (t0.1.1.nextPass t0.2).O, (t0.1.1.nextPass t0.2).P] ++
      1 :: ((t0.1.1.nextPass t0.2).tl ++ tailVR (ts.map fun p => p.1.1.nextPass p.2)))) := by
    have := NoB_app_iff.2 ⟨hP.noB, NoB_app_iff.2 ⟨hw.recd_noB, tailVR_noB _ hws⟩⟩
    simpa [VR.recd, List.append_assoc] using this
  rw [← hLe]
  obtain ⟨L', R', a2, E2, k1, k2, k3, k4, hr, hLR⟩ := faGF _ Pm hL hP _ hw _ hws hwO e z he hE hne rfl
  have hn : ∀ x ∈ ts.map (fun p => p.1.1.nextPass p.2), x.m = 0 := hwsm
  obtain ⟨os, hos, hdos, hT⟩ := failSep' Pm (t0.1.1.nextPass t0.2) hw hwm _ hws hwsm a2 E2 k1 k2 k3 k4
  refine ⟨L', R', os, hos, ?_, hr, by rw [hLR, hT]⟩
  rw [hdos]
  simp [dg_nextPass, List.map_map, Function.comp_def]


theorem odOutF (D : List (Nat × Nat × Nat × Nat × Nat)) (Wf Qp : List Nat) (hW : BitsD Wf) (m b : Nat) (p' : Nat × Nat)
    (hp : 1 ≤ p'.2) (hG : GoodW (1 :: (Qp ++ NnTail m b))) (os : List ORec) (hos : ∀ y ∈ os, y.Ok) (hne : os ≠ [])
    (hD : os.map ORec.dgO = D) :
    OdOut' D Wf Qp (m + 1 + b)
      ((Wf ++ 1 :: (List.replicate p'.1 2 ++ List.replicate p'.2 3 ++ 1 :: (Qp ++ NnTail m b))) ++ sepRest os) := by
  obtain ⟨o, os', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hg := pm_good Wf (Qp ++ NnTail m b) hW hG p' hp
  refine ⟨List.replicate p'.1 2 ++ List.replicate p'.2 3, m + 1, b, o, os',
    bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)), ?_, rfl, by omega, ?_, hos, hD, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q, p'.2 = q + 1 := ⟨p'.2 - 1, by omega⟩
    simp [hq, List.replicate_succ]
  · simpa [NnTail, List.append_assoc] using hg
  · simp [NnTail, List.append_assoc]


/-- One non-final pass followed by the start of the next: either refuted (`ODL`) or the next pass's first cursor
with all invariants of the next pass. -/
theorem passStepF (Wf : List Nat) (hW : BitsD Wf) (Q : List Nat) (a b : Nat)
    (hP2 : GoodW (1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
    (n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s : Nat)
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hp : 1 ≤ p.2) (hcmp : PassCmp n r vs) (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w)
    (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (j y : Nat) (l' : List Nat) (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: y :: l')
    (hEFv : ∀ x ∈ vs, EF x) :
    (∀ t ∈ ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]), t.1.Ok ∧ t.1.m = 0 ∧ t.2.1 + 1 + t.2.2 = t.1.w) ∧ ((∃ k q, znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL (Wf ++ [1]) (2 :: (List.replicate k 2 ++ List.replicate q 3 ++
          1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: (List.replicate b 2 ++
            tailB (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
              (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.done t.2.1 t.2.2))))))) ∨
    (∃ (q : Nat) (t0 : (VR × Nat × Nat) × Nat) (ts : List ((VR × Nat × Nat) × Nat)), 1 ≤ q ∧ q = (outP (loopRun n c vs r s p).c' (loopRun n c vs r s p).r' (loopRun n c vs r s p).p').2 ∧
      (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip (List.replicate (j + 1) 2 ++ 3 :: l')) = t0 :: ts ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)))
          [] (nxtC t0) 0 (nxtR t0) (nxtS t0) (nxtVs ts)) []) ∧
      nxtR t0 + 1 + nxtS t0 = (nxtC t0).w ∧ (nxtVs ts).length = n ∧ CurInv (nxtC t0) ∧ (∀ x ∈ nxtVs ts, x.Ok) ∧ OutM (nxtVs ts) ∧
      2 ≤ (nxtC t0).w ∧ (∀ x ∈ nxtVs ts, 2 ≤ x.w) ∧ (nxtC t0).m = 0 ∧ (∀ x ∈ nxtVs ts, x.m = 0) ∧
      (nxtC t0).P :: (nxtVs ts).map VR.P = List.replicate (j + 1) 2 ++ 3 :: l') ∨
    (∃ (q : Nat) (L' R' : List Nat) (os : List ORec), 1 ≤ q ∧ (∀ y ∈ os, y.Ok) ∧
      os.map ORec.dgO = (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).map fun t => t.1.dg) ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: (Q ++ List.replicate (a + 2) 3 ++ List.replicate b 2)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R') ∧
      L' ++ R' = (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate q 3 ++ 1 :: (Q ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2))) ++
        sepRest os)) := by
  obtain ⟨p', cs, hp', hcs, hPc, hLo, hcyc⟩ := passCycle Wf hW Q a b hP2 n vs c p r s hrs hlen hc hvs hom hp hcmp hcw hvw j y l' hfl
  obtain ⟨lo, hlo, hcsEq, hpEq⟩ := hLo
  rw [hlo, ← hcsEq]
  have hMz : ∀ t ∈ cs, t.1.O = 3 → t.1.m = 0 := by
    have hm := loopRun_m n c vs r s p hc hvs hom hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · intro h3
      rw [(outRec_m lo.c' lo.r').2] at h3
      rw [(outRec_m lo.c' lo.r').1]
      exact hm.2 h3
  have hxs : ∀ x ∈ List.replicate (j + 1) 2 ++ 3 :: l', x ∈ [2, 3] := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩ | rfl | hx
    · simp
    · simp
    · have h1 : x ∈ c.P :: vs.map VR.P := by rw [hfl]; simp [hx]
      simp only [List.mem_cons, List.mem_map] at h1
      rcases h1 with rfl | ⟨v, hv, rfl⟩
      · exact hc.1.P
      · exact (hvs v hv).P
  have hmzs : ∀ t ∈ cs, t.1.m = 0 := by
    have hm := loopRun_m0 n c vs r s p hm0 hvm hlen
    rw [hlo] at hm
    intro t ht
    rw [hcsEq] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hm.1 t ht
    · rw [(outRec_m lo.c' lo.r').1]; exact hm.2
  refine ⟨fun t ht => ⟨(hcs t ht).1, hmzs t ht, (hcs t ht).2.1⟩, ?_⟩
  rcases hcyc with ⟨hk, t0, ts, hz, hfal⟩ | ⟨k, hk, hodl⟩
  · right
    have hzl : (cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).length = n + 1 := by
      have h1 := congrArg List.length hPc
      have h2 := congrArg List.length hfl
      simp at h1 h2 ⊢
      omega
    rw [hz] at hzl
    simp only [List.length_cons] at hzl
    have hmem : ∀ q ∈ t0 :: ts, q ∈ cs.zip (List.replicate (j + 1) 2 ++ 3 :: l') := by
      intro q hq; rw [hz]; exact hq
    have hh : ∀ q ∈ t0 :: ts, q.1.1.Ok ∧ q.1.2.1 + 1 + q.1.2.2 = q.1.1.w ∧ 2 ≤ q.1.1.w ∧ q.2 ∈ [2, 3] := by
      intro q hq
      have := List.of_mem_zip (hmem q hq)
      have h3 := hcs q.1 this.1
      exact ⟨h3.1, h3.2.1, h3.2.2, hxs _ this.2⟩
    have h0 := hh t0 (by simp)
    have hGP := goodW_pmNext Wf hW Q a b p'.2 hP2 hp'
    by_cases hcmp0 : (t0.1.1.nextPass t0.2).O = 3 → ∃ z, 1 ≤ (t0.1.1.nextPass t0.2).k ∧
      (t0.1.1.nextPass t0.2).E = fld ((t0.1.1.nextPass t0.2).k + z) (t0.1.1.nextPass t0.2).k
    · left
      have hfn := faNext _ hGP t0 ts hh hcmp0
      have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
      have hmz : (t0.1.1.nextPass t0.2).O = 3 → (t0.1.1.nextPass t0.2).m = 0 := by
        intro h3
        exact hMz t0.1 (List.of_mem_zip (hmem t0 (by simp))).1 (by simpa [VR.nextPass] using h3)
      refine ⟨p'.2, t0, ts, hp', by rw [hpEq], hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp only [nxtC, nxtW, nxtR, nxtS, nxtVs]
      · simp only [List.replicate_zero, List.nil_append]
        exact hfal.trans hfn
      · have := (curG_kw (t0.1.1.nextPass t0.2)).2
        have h1 := hw.k1; have h2 := hw.kw
        omega
      · simpa using hzl
      · exact curG_inv _ hw hmz
      · intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        have hq' := hh q (List.mem_cons_of_mem _ hq)
        exact VR.dec_ok _ (VR.nextPass_ok _ hq'.1 _ hq'.2.2.2 hq'.2.2.1)
      · apply dec_outM
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        intro h3
        exact hMz q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1 (by simpa [VR.nextPass] using h3)
      · rw [(curG_kw (t0.1.1.nextPass t0.2)).2]
        simpa [VR.nextPass] using h0.2.2.1
      · intro x hx
        simp only [nxtVs, List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        have hq' := hh q (List.mem_cons_of_mem _ hq)
        rw [dec_w]
        simpa [VR.nextPass] using hq'.2.2.1
      · exact curG_m0 _ (by simpa [VR.nextPass] using hmzs t0.1 (List.of_mem_zip (hmem t0 (by simp))).1)
      · intro x hx
        simp only [nxtVs, List.mem_map] at hx
        obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
        exact dec_m0 _ (by simpa [VR.nextPass] using hmzs q.1 (List.of_mem_zip (hmem q (List.mem_cons_of_mem _ hq))).1)
      · have hs : ((cs.zip (List.replicate (j + 1) 2 ++ 3 :: l')).map Prod.snd) = List.replicate (j + 1) 2 ++ 3 :: l' := by
          rw [List.map_snd_zip]
          have h1 := congrArg List.length hPc
          have h2 := congrArg List.length hfl
          simp at h1 h2 ⊢
          omega
        rw [hz] at hs
        simp only [List.map_cons] at hs
        rw [← hs]
        simp [nxtC, nxtW, nxtVs, curG_P, dec_P, VR.nextPass, Function.comp_def]
    · right
      have hwO : (t0.1.1.nextPass t0.2).O = 3 := Classical.byContradiction fun h => hcmp0 (fun h' => absurd h' h)
      have hw := VR.nextPass_ok _ h0.1 _ h0.2.2.2 h0.2.2.1
      have hEFl := loopRun_EF n c vs r s p hc hvs hom hlen
      rw [hlo] at hEFl
      have hEFcs : ∀ t ∈ cs, EF t.1 := by
        intro t ht
        rw [hcsEq] at ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hEFl.1 t ht
        · exact hEFl.2
      have hEF0 : EF (t0.1.1.nextPass t0.2) :=
        EF_of rfl rfl (hEFcs t0.1 (List.of_mem_zip (hmem t0 (by simp))).1)
      obtain ⟨e, z, he, hE, hne⟩ := EF_mismatch _ hw hEF0 hwO hcmp0
      have hmm : ∀ q ∈ t0 :: ts, q.1.1.m = 0 := fun q hq =>
        hmzs q.1 (List.of_mem_zip (hmem q hq)).1
      obtain ⟨L', R', os, hok, hdos, hr, hLR⟩ := faNextF _ hGP t0 ts hh hmm hwO e z he hE hne
      refine ⟨p'.2, L', R', os, hp', hok, ?_, hfal.trans hr, ?_⟩
      · rw [hdos]
        have hcl : cs.length = n + 1 := by
          have := congrArg List.length hPc
          simp at this ⊢; omega
        have hzl2 : (List.replicate (j + 1) 2 ++ 3 :: l').length = n + 1 := by
          have := congrArg List.length hfl
          simp at this ⊢; omega
        have hmf := List.map_fst_zip (l₁ := cs) (l₂ := List.replicate (j + 1) 2 ++ 3 :: l') (by omega)
        rw [hz] at hmf
        rw [← hmf]
        simp [List.map_map, Function.comp_def]
      · rw [hLR]; simp
  · left
    exact ⟨k, p'.2, hodl⟩




theorem nxt_EF (n : Nat) (c : VR) (vs : List VR) (r s : Nat) (p : Nat × Nat) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok)
    (hom : OutM vs) (hlen : vs.length = n) (L2 : List Nat) (t0 : (VR × Nat × Nat) × Nat)
    (ts : List ((VR × Nat × Nat) × Nat))
    (hz : (((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip L2) = t0 :: ts) :
    ∀ x ∈ nxtVs ts, EF x := by
  have hEFl := loopRun_EF n c vs r s p hc hvs hom hlen
  intro x hx
  simp only [nxtVs, List.mem_map] at hx
  obtain ⟨y, ⟨q, hq, rfl⟩, rfl⟩ := hx
  have hmem : q ∈ ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
        (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).zip L2 := by
    rw [hz]; exact List.mem_cons_of_mem _ hq
  have hq1 := (List.of_mem_zip hmem).1
  have hEFq : EF q.1.1 := by
    simp only [List.mem_append, List.mem_singleton] at hq1
    rcases hq1 with h | h
    · exact hEFl.1 q.1 h
    · rw [h]; exact hEFl.2
  exact EF_of (dec_EO _).1 (dec_EO _).2 (EF_of rfl rfl hEFq)

theorem failA (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat) (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat)
    (r s : Nat) (hP2 : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hEF : ∀ x ∈ vs, EF x) (hp : 1 ≤ p.2) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0) (hnc : ¬ PassCmp n r vs) :
    ∃ L' R' : List Nat, OdOut' ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (m + 1 + b) (L' ++ R') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R') := by
  obtain ⟨L, R, os, p', hok, hdos, hp', hr, hLR⟩ := passLoopF Wf hW ((Q'' ++ [1]) ++ NnTail m b) hP2 n vs c [] p r s []
    ((c :: vs).map VR.dg) hlen hc hvs hom hEF (by intro x hx; simp at hx) hp hrs hm0 hvm rfl
    (by intro y hy; simp at hy) (by simp) hnc
  refine ⟨L, R, ?_, hr⟩
  rw [hLR]
  exact odOutF _ Wf (Q'' ++ [1]) hW m b p' hp' hP2 os hok (by intro h; rw [h] at hdos; simp at hdos) hdos

/-- All passes of one assignment, without the semantic hypothesis: refuted (`ODL`, parsable tape) or successful (`SU1`). -/
theorem passesRunF (Wf : List Nat) (hW : BitsD Wf) (Q'' : List Nat) :
    ∀ (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat),
    GoodW (1 :: ((Q'' ++ [1]) ++ NnTail m b)) →
    r + 1 + s = c.w → vs.length = n → CurInv c → (∀ x ∈ vs, x.Ok) → OutM vs → (∀ x ∈ vs, EF x) → 1 ≤ p.2 →
    2 ≤ c.w → (∀ x ∈ vs, 2 ≤ x.w) → c.m = 0 → (∀ x ∈ vs, x.m = 0) →
    c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L → m ≤ L.length →
    (∃ L' R' : List Nat, OdOut' ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (m + 1 + b) (L' ++ R') ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hd QNTT.ODL L' R')) ∨
    (∃ T, SuOut ((c :: vs).map VR.dg) Wf Q'' (b + m + 1) T ∧
      znttLogic.Reach
        (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 :: ((Q'' ++ [1]) ++ NnTail m b)))
          [] c 0 r s vs) [])
        (hdR QNTT.SU1 [] T)) := by
  intro m
  induction m with
  | zero =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL
    by_cases hcmp : PassCmp n r vs
    · rcases passesRun Wf hW Q'' 0 b n vs c p r s j L hP2 hrs hlen hc hvs hom hp hcw hvw hm0 hvm hfl hL hcmp with
        ⟨R', hT, hr⟩ | hS
      · exact Or.inl ⟨Wf ++ [1], R', hT.to', hr⟩
      · exact Or.inr hS
    · exact Or.inl (failA Wf hW Q'' 0 b n vs c p r s hP2 hrs hlen hc hvs hom hEF hp hm0 hvm hcmp)
  | succ a ih =>
    intro b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL
    by_cases hc1 : PassCmp n r vs
    case neg => exact Or.inl (failA Wf hW Q'' (a + 1) b n vs c p r s hP2 hrs hlen hc hvs hom hEF hp hm0 hvm hc1)
    obtain ⟨y, l', rfl⟩ : ∃ y l', L = y :: l' := by
      cases L with
      | nil => simp at hL
      | cons y l' => exact ⟨y, l', rfl⟩
    have e : (Q'' ++ [1]) ++ NnTail (a + 1) b = (Q'' ++ [1]) ++ List.replicate (a + 2) 3 ++ List.replicate b 2 := by
      simp [NnTail, List.append_assoc]
    rw [e] at hP2 ⊢
    have hstep := passStepF Wf hW (Q'' ++ [1]) a b hP2 n vs c p r s hrs hlen hc hvs hom hp hc1 hcw hvw hm0 hvm j y l' hfl hEF
    obtain ⟨hcsOk, hst⟩ := hstep
    have hP2'' : GoodW (1 :: ((Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2)) := goodW_shiftNn _ a b hP2
    rcases hst with ⟨k, q, h1⟩ | ⟨q, t0, ts, hq, hqe, hz, h1, hrs1, hlen1, hc1', hvs1, hom1, hcw1, hvw1, hm1, hvm1, hfl1⟩ |
        ⟨q, L', R', os, hq, hok, hdos, h1, hLR⟩
    · obtain ⟨R', hO, hr⟩ : ∃ R', OdOut ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) (a + 1 + 1 + b) R' ∧
          znttLogic.Reach
            (hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
              ((Q'' ++ [1]) ++ List.replicate (a + 2) 3 ++ List.replicate b 2))) [] c 0 r s vs) [])
            (hd QNTT.ODL (Wf ++ [1]) R') := by
        have hu := goodW_reg Wf (List.replicate (k + 1) 2 ++ List.replicate q 3) _ hW
          (bd_app (BitsD.rep _ 2 (by simp)) (BitsD.rep _ 3 (by simp)))
          (by intro h; have := congrArg List.length h; simp at this) (by simpa [List.append_assoc] using hP2'')
        have hne : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) ≠ [] := by simp
        obtain ⟨o, os, hok, hdg, hex⟩ := tapeOutP_ex _ hcsOk hne
        refine ⟨((2 :: List.replicate k 2) ++ List.replicate q 3 ++ 1 :: ((Q'' ++ [1]) ++ List.replicate (a + 1) 3 ++
            2 :: List.replicate b 2)) ++ sepRest (o :: os),
          ⟨(2 :: List.replicate k 2) ++ List.replicate q 3, a + 1, b, o, os,
            bd_app (BitsD.cons (by simp) (BitsD.rep _ 2 (by simp))) (BitsD.rep _ 3 (by simp)),
            by intro h; have := congrArg List.length h; simp at this, by omega, ?_, hok,
            hdg.trans (dg_runAll_pos n c vs r s p hm0 hvm hlen), ?_⟩, ?_⟩
        · rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using hu
        · simp [List.append_assoc]
        · rw [hex] at h1
          rw [List.replicate_succ' (n := a) (a := 3)]; simpa [List.append_assoc, List.replicate_succ] using h1
      exact Or.inl ⟨Wf ++ [1], R', hO.to', hr⟩
    · have hEFn := nxt_EF n c vs r s p hc hvs hom hlen _ t0 ts hz
      have hP2' : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail a (b + 1))) := by
        rw [← nn_eq]
        simpa [List.append_assoc] using goodW_shiftNn (Q'' ++ [1]) a b hP2
      have hih := ih (b + 1) n (nxtVs ts) (nxtC t0) (0, q) (nxtR t0) (nxtS t0) (j + 1) l' hP2' hrs1 hlen1 hc1' hvs1 hom1
        hEFn hq hcw1 hvw1 hm1 hvm1 (by simpa using hfl1) (by simpa using hL)
      have e2 : (Q'' ++ [1]) ++ List.replicate a 3 ++ 3 :: 2 :: List.replicate b 2 = (Q'' ++ [1]) ++ NnTail a (b + 1) := by
        rw [List.append_assoc, nn_eq]
      rw [e2] at h1
      simp only [List.replicate_zero, List.nil_append] at h1 hih
      have hEq : (nxtC t0 :: nxtVs ts).map VR.dg = (c :: vs).map VR.dg := by
        have hcl : ((loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]).length = n + 1 := by
          simp [loopRun_cs_length n c vs r s p hlen]
        have hzl : (List.replicate (j + 1) 2 ++ 3 :: l').length = n + 1 := by
          have := congrArg List.length hfl
          simp at this ⊢; omega
        have hmf := List.map_fst_zip (l₁ := (loopRun n c vs r s p).cs ++ [(outRec (loopRun n c vs r s p).c' (loopRun n c vs r s p).r',
            (loopRun n c vs r s p).r', (loopRun n c vs r s p).s')]) (l₂ := List.replicate (j + 1) 2 ++ 3 :: l') (by omega)
        rw [hz] at hmf
        have hp := dg_runAll_pos n c vs r s p hm0 hvm hlen
        rw [← hp, ← hmf]
        simp [nxtC, nxtVs, nxtW, dg_curG, dg_nextPass, dg_dec, List.map_map, Function.comp_def]
      rcases hih with ⟨L', R', ho, hr⟩ | ⟨T, ho, hr⟩
      · exact Or.inl ⟨L', R', by rw [hEq] at ho; rwa [show a + 1 + (b + 1) = a + 1 + 1 + b by omega] at ho, h1.trans hr⟩
      · exact Or.inr ⟨T, by rw [hEq] at ho; rwa [show b + 1 + a + 1 = b + (a + 1) + 1 by omega] at ho, h1.trans hr⟩
    · have hP2n : GoodW (1 :: ((Q'' ++ [1]) ++ NnTail a (b + 1))) := by
        rw [← nn_eq]
        simpa [List.append_assoc] using hP2''
      have hdgE := dg_runAll_pos n c vs r s p hm0 hvm hlen
      have hne : os ≠ [] := by intro h; rw [h] at hdos; simp at hdos
      have hO := odOutF ((c :: vs).map VR.dg) Wf (Q'' ++ [1]) hW a (b + 1) (0, q) hq hP2n os hok hne (by rw [hdos, hdgE])
      refine Or.inl ⟨L', R', ?_, h1⟩
      rw [hLR]
      have := hO
      rw [show a + 1 + 1 + b = a + 1 + (b + 1) by omega]
      simpa [nn_eq, List.append_assoc] using this


/-- One whole assignment, `Sem`-free: the next assignment (`WI0`), the overflow (beep, restart at `PA0` with `C` grown),
or success (`SU1`, restart at `PA0`). -/
theorem assignRunF (Wf : List Nat) (hW : BitsD Wf) (Kf Cf : List Nat) (hK : BitsD Kf) (hC : BitsD Cf)
    (m b n : Nat) (vs : List VR) (c : VR) (p : Nat × Nat) (r s j : Nat) (L : List Nat)
    (hP2 : GoodW (1 :: (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b)))
    (hrs : r + 1 + s = c.w) (hlen : vs.length = n) (hc : CurInv c) (hvs : ∀ x ∈ vs, x.Ok) (hom : OutM vs)
    (hEF : ∀ x ∈ vs, EF x) (hp : 1 ≤ p.2)
    (hcw : 2 ≤ c.w) (hvw : ∀ x ∈ vs, 2 ≤ x.w) (hm0 : c.m = 0) (hvm : ∀ x ∈ vs, x.m = 0)
    (hfl : c.P :: vs.map VR.P = List.replicate j 2 ++ 3 :: L) (hL : m ≤ L.length) :
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail m b))) [] c 0 r s vs) []
    (∃ u v os' X R'', Rest u v ∧ StepInfo ((c :: vs).map VR.dg) Wf Kf Cf (m + 1 + b) v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone ((c :: vs).map VR.dg) ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (m + 1 + b) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut ((c :: vs).map VR.dg) Wf (Kf ++ 1 :: Cf) (b + m + 1) T ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (b + m + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  intro st
  rcases passesRunF Wf hW (Kf ++ 1 :: Cf) m b n vs c p r s j L hP2 hrs hlen hc hvs hom hEF hp hcw hvw hm0 hvm hfl hL with
    ⟨L', R', hT, hr⟩ | ⟨T, hT, hr⟩
  · rcases odlNext3 _ Wf Kf Cf hW hK hC _ L' R' hT with ⟨u, v, os', X, R'', hv, si, e, h⟩ | ⟨A, n0, sn, hb, X, hX, hXr⟩
    · exact Or.inl ⟨u, v, os', X, R'', hv, si, e, hr.trans h⟩
    · exact Or.inr (Or.inl ⟨A, n0, sn, hr.trans hb, X, hX, hXr⟩)
  · obtain ⟨N, hN⟩ := sucRestart _ Wf Kf Cf (b + m) T hW hK hC hT
    exact Or.inr (Or.inr ⟨N, T, hT, hr, hN⟩)


/-- Odometer measure on digit tuples. -/
def ph : List (Nat × Nat × Nat × Nat × Nat) → Nat
  | [] => 0
  | (d, e, z, m, _) :: gs => (m * (d + e + 1) + e) + (z + 1 + m) * (d + e + 1) * ph gs

theorem ph_step1 (d e zk m l : Nat) (X : List (Nat × Nat × Nat × Nat × Nat)) (he : 1 ≤ e) :
    ph ((d + 1, e - 1, zk, m, l) :: X) < ph ((d, e, zk, m, l) :: X) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  simp only [ph, Nat.add_sub_cancel]
  have : d + 1 + e' + 1 = d + (e' + 1) + 1 := by omega
  rw [this]; omega

theorem ph_step2 (d zk m' l : Nat) (X : List (Nat × Nat × Nat × Nat × Nat)) :
    ph ((0, d, zk + 1, m', l) :: X) < ph ((d, 0, zk, m' + 1, l) :: X) := by
  simp only [ph]
  have h1 : 0 + d + 1 = d + 0 + 1 := by omega
  have h2 : zk + 1 + 1 + m' = zk + 1 + (m' + 1) := by omega
  rw [h1, h2]
  have : m' * (d + 0 + 1) + d < (m' + 1) * (d + 0 + 1) + 0 := by
    rw [Nat.add_mul]; omega
  omega

theorem ph_step3 (d zk l : Nat) (X X2 : List (Nat × Nat × Nat × Nat × Nat)) (h : ph X2 < ph X) :
    ph ((0, d, 0, zk, l) :: X2) < ph ((d, 0, zk, 0, l) :: X) := by
  simp only [ph]
  have h1 : 0 + d + 1 = d + 0 + 1 := by omega
  rw [h1]
  have h3 : (d + 0 + 1) * (zk + 1) * (ph X2 + 1) ≤ (d + 0 + 1) * (zk + 1) * ph X := Nat.mul_le_mul_left _ h
  have h4 : zk * (d + 0 + 1) + d < (zk + 1) * (d + 0 + 1) := by rw [Nat.add_mul]; omega
  have e1 : (0 + 1 + zk) * (d + 0 + 1) = (d + 0 + 1) * (zk + 1) := by rw [Nat.mul_comm]; congr 1; omega
  have e2 : (zk + 1 + 0) * (d + 0 + 1) = (d + 0 + 1) * (zk + 1) := by rw [Nat.mul_comm]
  rw [e1, e2]
  rw [Nat.mul_add, Nat.mul_one] at h3
  have e3 : (d + 0 + 1) * (zk + 1) = (zk + 1) * (d + 0 + 1) := Nat.mul_comm _ _
  omega

theorem odo_dec : ∀ (os os' : List ORec), (∀ x ∈ os, x.Ok) → odoStepR os = some os' →
    ph (os'.map ORec.dgO) < ph (os.map ORec.dgO)
  | [], os', _, h => by simp [odoStepR] at h
  | o :: os, os', hok, h => by
    have ho := hok o (by simp)
    have hd := ho.d
    have hk := ho.k
    unfold odoStepR at h
    cases hn : o.next with
    | inl o' =>
      rw [hn] at h
      simp at h
      subst h
      simp only [ORec.next] at hn
      split at hn
      · injection hn with hn; subst hn
        have := ph_step1 o.d (o.r - o.d - 1) (o.z + o.k - 1) o.m o.acc.length (os.map ORec.dgO) (by omega)
        simp only [List.map_cons, ORec.dgO]
        have e : o.r - (o.d + 1) - 1 = o.r - o.d - 1 - 1 := by omega
        rw [e]
        exact this
      · split at hn
        · injection hn with hn; subst hn
          obtain ⟨m', hm'⟩ : ∃ m', o.m = m' + 1 := ⟨o.m - 1, by omega⟩
          have := ph_step2 o.d (o.z + o.k - 1) m' o.acc.length (os.map ORec.dgO)
          have e0 : o.r - o.d - 1 = 0 := by omega
          have e1 : o.r - 0 - 1 = o.d := by omega
          have e2 : o.z + (o.k + 1) - 1 = o.z + o.k - 1 + 1 := by omega
          have e3 : o.m - 1 = m' := by omega
          simp only [List.map_cons, ORec.dgO, e0, e1, e2, e3, hm'] at this ⊢
          exact this
        · injection hn
    | inr o' =>
      rw [hn] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨os2, hs2, rfl⟩ := h
      have ih := odo_dec os os2 (fun x hx => hok x (by simp [hx])) hs2
      simp only [ORec.next] at hn
      split at hn
      · injection hn
      · split at hn
        · injection hn
        · injection hn with hn; subst hn
          have h0 : o.m = 0 := by omega
          have e0 : o.r - o.d - 1 = 0 := by omega
          have := ph_step3 o.d (o.z + o.k - 1) o.acc.length (os.map ORec.dgO) (os2.map ORec.dgO) ih
          have e1 : o.r - 0 - 1 = o.d := by omega
          have e2 : 0 + 1 - 1 = 0 := by omega
          simp only [List.map_cons, ORec.dgO, e0, e1, h0, e2] at this ⊢
          exact this


theorem dec_m (v : VR) : v.dec.m = v.m := by unfold VR.dec; split <;> rfl
theorem dec_E (v : VR) : v.dec.E = v.E := by unfold VR.dec; split <;> rfl

theorem entryRun (Wf : List Nat) (hW : BitsD Wf) (Kf Cf : List Nat) (hK : BitsD Kf) (hC : BitsD Cf)
    (n : Nat) (o : ORec) (os : List ORec) (hlen : os.length = n)
    (hok : ∀ x ∈ o :: os, x.Ok) (hacc : ∀ x ∈ o :: os, 2 ≤ x.acc.length)
    (p : Nat × Nat) (hp : 1 ≤ p.2)
    (hP2 : GoodW (1 :: (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail n 0))) :
    let c := (o.vr 3).curG
    let vs := (os.map fun x => x.vr 2).map VR.dec
    let st := hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate p.1 2 ++ List.replicate p.2 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail n 0))) [] c 0 ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) vs) []
    (∃ u v os' X R'', Rest u v ∧ StepInfo ((c :: vs).map VR.dg) Wf Kf Cf (n + 1 + 0) v os' ∧ X ++ 3 :: R'' = (v ++ [1, 1]) ++ tapeL os' ∧
      znttLogic.Reach st (hd QNTT.WI0 X (3 :: R''))) ∨
    (∃ (A : List Nat) (n0 : Nat), StepNone ((c :: vs).map VR.dg) ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (n + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut ((c :: vs).map VR.dg) Wf (Kf ++ 1 :: Cf) (0 + n + 1) T ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (0 + n + 1 + 1) 3 ++
        List.replicate (N + 1) 0)))))) := by
  intro c vs st
  have ho := hok o (by simp)
  have ha := hacc o (by simp)
  have hw : (o.vr 3).Ok := ORec.vr_ok o ho 3 (by simp) ha
  have hvo : ∀ y ∈ os, (y.vr 2).Ok := fun y hy =>
    ORec.vr_ok y (hok y (by simp [hy])) 2 (by simp) (hacc y (by simp [hy]))
  have hm3 : (o.vr 3).m = 0 := by simp [ORec.vr]
  have hcI : CurInv c := curG_inv _ hw (fun _ => hm3)
  have hcw : c.w = (o.vr 3).w := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, dec_w]
  have hcm : c.m = 0 := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, dec_m, hm3]
  have hdp : ∀ v : VR, v.dec.P = v.P := fun v => by unfold VR.dec; split <;> rfl
  have hcP : c.P = 3 := by
    simp only [c, VR.curG]; split <;> simp [VR.cur, hdp, ORec.vr]
  have hvP : ∀ y ∈ os, ((y.vr 2).dec).P = 2 := fun y hy => by simp [hdp, ORec.vr]
  have hw3 : (o.vr 3).w = o.acc.length := by simp [ORec.vr]
  have hk := hw.k1
  have hkw := hw.kw
  have hmem : ∀ x ∈ vs, ∃ y ∈ os, x = (y.vr 2).dec := by
    intro x hx; simp only [vs, List.mem_map] at hx
    obtain ⟨z, ⟨y, hy, rfl⟩, rfl⟩ := hx; exact ⟨y, hy, rfl⟩
  have hvs : ∀ x ∈ vs, x.Ok := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; exact VR.dec_ok _ (hvo y hy)
  have hom : OutM vs := fun x hx hO => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; simp [dec_m, ORec.vr]
  have hEFv : ∀ x ∈ vs, EF x := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx
    intro _
    have hl := (hok y (by simp [hy])).Elen
    refine ⟨2, by omega, by simp [dec_E, ORec.vr], ?_⟩
    simp [dec_E, ORec.vr, fld, List.replicate_succ]
  have hvw : ∀ x ∈ vs, 2 ≤ x.w := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; rw [dec_w]; simpa [ORec.vr] using hacc y (by simp [hy])
  have hvm : ∀ x ∈ vs, x.m = 0 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hmem x hx; simp [dec_m, ORec.vr]
  have hfl : c.P :: vs.map VR.P = List.replicate 0 2 ++ 3 :: List.replicate n 2 := by
    rw [hcP]
    have : vs.map VR.P = List.replicate n 2 := by
      apply List.eq_replicate_iff.2
      refine ⟨by simp [vs, hlen], fun x hx => ?_⟩
      simp only [List.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hmem z hz; exact hvP y hy
    rw [this]; rfl
  exact assignRunF Wf hW Kf Cf hK hC n 0 n vs c p ((o.vr 3).k - 1) ((o.vr 3).w - (o.vr 3).k) 0
    (List.replicate n 2) hP2 (by omega) (by simp [vs, hlen]) hcI hvs hom hEFv hp (by omega) hvw hcm hvm hfl (by simp)


theorem entry_dg (o : ORec) (os : List ORec) (ho : o.Ok) (hos : ∀ x ∈ os, x.Ok)
    (_ha : 2 ≤ o.acc.length) :
    ((o.vr 3).curG :: ((os.map fun x => x.vr 2).map VR.dec)).map VR.dg = (o :: os).map ORec.dgO := by
  have h1 : ((o.vr 3).curG).dg = o.dgO := by
    rw [(dg_curG _).1]
    have := o.d; have hd := ho.d; have hk := ho.k
    simp [VR.dg, ORec.vr, ORec.dgO]; omega
  simp only [List.map_cons, h1]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp]
  rw [(dg_dec _).1]
  have hd := (hos x hx).d
  simp [VR.dg, ORec.vr, ORec.dgO]; omega

theorem odo_ok : ∀ (os os' : List ORec), (∀ x ∈ os, x.Ok) → odoStepR os = some os' →
    ∃ o2 os2, os' = o2 :: os2 ∧ os'.length = os.length ∧ (∀ x ∈ o2 :: os2, x.Ok) ∧
      (o2 :: os2).map (fun x => x.acc.length) = os.map (fun x => x.acc.length)
  | [], os', _, h => by simp [odoStepR] at h
  | o :: os, os', hok, h => by
    have ho := hok o (by simp)
    unfold odoStepR at h
    cases hn : o.next with
    | inl o' =>
      rw [hn] at h
      simp at h; subst h
      have hok' : o'.Ok ∧ o'.acc = o.acc := by
        simp only [ORec.next] at hn
        split at hn
        · injection hn with hn; subst hn
          exact ⟨{ ho with d := by simp only; have := ho.d; omega }, rfl⟩
        · split at hn
          · injection hn with hn; subst hn
            exact ⟨{ ho with d := by simp only; have := ho.d; omega, k := by simp only; omega }, rfl⟩
          · injection hn
      refine ⟨o', os, rfl, by simp, ?_, by simp [hok'.2]⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hok'.1
      · exact hok x (by simp [hx])
    | inr o' =>
      rw [hn] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨os2, hs2, rfl⟩ := h
      obtain ⟨o3, os3, rfl, hl, hk3, ha3⟩ := odo_ok os os2 (fun x hx => hok x (by simp [hx])) hs2
      have hok' : o'.Ok ∧ o'.acc = o.acc := by
        simp only [ORec.next] at hn
        split at hn
        · injection hn
        · split at hn
          · injection hn
          · injection hn with hn; subst hn
            exact ⟨{ ho with d := by simp only; have := ho.d; omega, k := by simp only; omega }, rfl⟩
      refine ⟨o', o3 :: os3, rfl, ?_, ?_, ?_⟩
      · simp at hl ⊢; omega
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hok'.1
        · exact hk3 x (by simpa using hx)
      · simp [hok'.2, ha3]


/-- One odometer step on digit tuples. -/
def DStep (D D2 : List (Nat × Nat × Nat × Nat × Nat)) : Prop :=
  ∃ (o : ORec) (os : List ORec) (o2 : ORec) (os2 : List ORec), (∀ x ∈ o :: os, x.Ok) ∧ (o :: os).map ORec.dgO = D ∧
    odoStepR (o :: os) = some (o2 :: os2) ∧ (o2 :: os2).map ORec.dgO = D2

inductive DIter : List (Nat × Nat × Nat × Nat × Nat) → List (Nat × Nat × Nat × Nat × Nat) → Prop
  | refl (D) : DIter D D
  | step {D D2 D3} : DStep D D2 → DIter D2 D3 → DIter D D3

theorem gw_par (k c n : Nat) (hk : 1 ≤ k) (hc : 1 ≤ c) :
    GoodW (1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ NnTail n 0)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have t3 : GoodW (1 :: List.replicate (n + 1) 3) :=
    GoodW.mb (b := 3) (by simp) (GoodW.bits (BitsD.rep n 3 (by simp)))
  have t2 : GoodW (1 :: (List.replicate (c' + 1) 3 ++ 1 :: List.replicate (n + 1) 3)) :=
    GoodW.mb (b := 3) (by simp) (GoodW.app (GoodW.bits (BitsD.rep c' 3 (by simp))) t3)
  have t1 : GoodW (1 :: (List.replicate (k' + 1) 3 ++ 1 :: (List.replicate (c' + 1) 3 ++ 1 :: List.replicate (n + 1) 3))) :=
    GoodW.mb (b := 3) (by simp) (GoodW.app (GoodW.bits (BitsD.rep k' 3 (by simp))) t2)
  simpa [NnTail, List.append_assoc] using t1

theorem map_f_bits {l : List Nat} (h : BitsD l) :
    l.map (fun x => if x = 1 then 1 else 3) = List.replicate l.length 3 := by
  apply List.eq_replicate_iff.2
  refine ⟨by simp, fun y hy => ?_⟩
  simp only [List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := h x hx
  simp at this
  rcases this with rfl | rfl <;> simp

theorem par_form (a k c n a' b' : Nat) (S0 : List Nat) (hS0 : BitsD S0) (hN : a' + b' = n + 1 + 0) :
    (List.replicate a 3 ++ 1 :: (S0 ++ 1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ List.replicate a' 3 ++ List.replicate b' 2))).map
      (fun x => if x = 1 then 1 else 3) =
    List.replicate a 3 ++ 1 :: (List.replicate S0.length 3 ++ 1 :: (((List.replicate k 3 ++ 1 :: List.replicate c 3) ++ [1]) ++ NnTail n 0)) := by
  simp only [List.map_append, List.map_cons, List.map_replicate, map_f_bits hS0, NnTail]
  simp [List.append_assoc]
  omega


def loopSt (Wf Kf Cf : List Nat) (n s : Nat) (o : ORec) (os : List ORec) :=
  hd QNTT.RFL (curTapeG (Wf ++ 1 :: (List.replicate 0 2 ++ List.replicate s 3 ++ 1 ::
          (((Kf ++ 1 :: Cf) ++ [1]) ++ NnTail n 0))) [] (o.vr 3).curG 0 ((o.vr 3).k - 1)
          ((o.vr 3).w - (o.vr 3).k) ((os.map fun x => x.vr 2).map VR.dec)) []

def LpOut (Wf Kf Cf : List Nat) (n : Nat) (st : ZC) (D : List (Nat × Nat × Nat × Nat × Nat)) : Prop :=
  (∃ (A : List Nat) (n0 : Nat), StepNone D ∧ znttLogic.Reach st (hd QNTT.BEEP A []) ∧
      ∃ X, znttLogic.zstep (hd QNTT.BEEP A []) = some X ∧
        znttLogic.Reach X (hdR QNTT.PA0 [3] (1 :: (Kf.map (fun x => if x = 1 then 1 else 3) ++ 1 ::
          ((Cf.map (fun x => if x = 1 then 1 else 3) ++ [3]) ++ 1 ::
            (List.replicate (n + 1 + 0) 3 ++ List.replicate (n0 + 1) 0)))))) ∨
    (∃ N : Nat, ∃ T, SuOut D Wf (Kf ++ 1 :: Cf) (0 + n + 1) T ∧
      znttLogic.Reach st (hdR QNTT.SU1 [] T) ∧
      znttLogic.Reach (hdR QNTT.SU1 [] T) (hdR QNTT.PA0 [3] (1 :: (Kf ++ 1 :: (Cf ++ 1 :: (List.replicate (0 + n + 1 + 1) 3 ++
        List.replicate (N + 1) 0))))))

theorem LpOut.pre {Wf Kf Cf n st st2 D} (h : znttLogic.Reach st st2) (h2 : LpOut Wf Kf Cf n st2 D) :
    LpOut Wf Kf Cf n st D := by
  rcases h2 with ⟨A, n0, sn, hb, X, hX, hr⟩ | ⟨N, T, hs, h1, h3⟩
  · exact Or.inl ⟨A, n0, sn, h.trans hb, X, hX, hr⟩
  · exact Or.inr ⟨N, T, hs, h.trans h1, h3⟩

theorem assignLoop (a k c : Nat) (hk : 1 ≤ k) (hc : 1 ≤ c) (n : Nat) :
    ∀ (B s : Nat) (o : ORec) (os : List ORec), ph ((o :: os).map ORec.dgO) = B → 1 ≤ s → os.length = n →
      (∀ x ∈ o :: os, x.Ok) → (∀ x ∈ o :: os, 2 ≤ x.acc.length) →
      ∃ D', DIter ((o :: os).map ORec.dgO) D' ∧
        LpOut (List.replicate a 3) (List.replicate k 3) (List.replicate c 3) n
          (loopSt (List.replicate a 3) (List.replicate k 3) (List.replicate c 3) n s o os) D' := by
  intro B
  induction B using Nat.strongRecOn with
  | _ B ih =>
  intro s o os hB hs hlen hok hacc
  have hP2 := gw_par k c n hk hc
  have hent := entryRun (List.replicate a 3) (BitsD.rep _ _ (by simp)) (List.replicate k 3) (List.replicate c 3)
    (BitsD.rep _ _ (by simp)) (BitsD.rep _ _ (by simp)) n o os hlen hok hacc (0, s) hs hP2
  have hD := entry_dg o os (hok o (by simp)) (fun x hx => hok x (by simp [hx])) (hacc o (by simp))
  dsimp only at hent
  rw [hD] at hent
  rcases hent with ⟨u, v, os', X, R'', hrest, si, e, hr⟩ | hbeep | hsucc
  · obtain ⟨S0, a', b', o1, os1, hS0, hS0ne, hN, hN1, hok1, hdg1, hst1, hv⟩ := si
    obtain ⟨o2, os2, rfl, hl2, hok2, hacc2⟩ := odo_ok (o1 :: os1) os' hok1 hst1
    have hdec := odo_dec (o1 :: os1) (o2 :: os2) hok1 hst1
    rw [hdg1] at hdec
    have hlen1 : (o1 :: os1).length = (o :: os).length := by
      simpa using congrArg List.length hdg1
    have hlen2 : os2.length = n := by
      simp at hl2 hlen1; omega
    have hvE := par_form a k c n a' b' S0 hS0 hN
    have hvE' := hv.trans hvE
    obtain ⟨s1, hs1⟩ : ∃ s1, S0.length = s1 + 1 := ⟨S0.length - 1, by
      have : S0 ≠ [] := hS0ne
      have := List.length_pos_iff.2 this; omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hvf : v = List.replicate a 3 ++ (1 :: List.replicate (s1 + 1) 3 ++ (1 :: List.replicate (k' + 1) 3 ++
        (1 :: List.replicate (c' + 1) 3 ++ (1 :: List.replicate (n + 1) 3)))) := by
      rw [hvE', hs1]; simp [NnTail, List.append_assoc]
    have hrv : Rest v v := by
      rw [hvf]
      exact Rest.app (rest_rep a) (Rest.app (rest_blk s1) (Rest.app (rest_blk k') (Rest.app (rest_blk c') (rest_blk n))))
    have hnb : NoB ((v ++ [1, 1]) ++ tapeL (o2 :: os2)) := by
      have h1 : NoB v := hrest.goodW.noB
      exact NoB_app_iff.2 ⟨NoB_app_iff.2 ⟨h1, by intro x hx; simp at hx; simp [hx, NB]⟩, tapeL_noB _ hok2⟩
    have hNoB : NoB X := by
      rw [← e] at hnb; exact (NoB_app_iff.1 hnb).1
    have hm : (o2 :: os2).map (fun x => x.acc.length) = (o :: os).map (fun x => x.acc.length) := by
      rw [hacc2]
      have := congrArg (List.map (fun t : Nat × Nat × Nat × Nat × Nat => t.2.2.2.2)) hdg1
      simpa [List.map_map, Function.comp_def, ORec.dgO] using this
    have hacc2' : ∀ x ∈ o2 :: os2, 2 ≤ x.acc.length := by
      intro x hx
      have h1 : x.acc.length ∈ (o2 :: os2).map (fun x => x.acc.length) := List.mem_map_of_mem hx
      rw [hm] at h1
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h1
      rw [← hyx]; exact hacc y hy
    have hnext := nextEntry X R'' v hNoB hrv o2 os2 hok2 hacc2' e
    rw [hvE', hs1] at hnext
    obtain ⟨D', hit, hout⟩ := ih _ (by omega) (s1 + 1) o2 os2 rfl (by omega) hlen2 hok2 hacc2'
    refine ⟨D', DIter.step ⟨o1, os1, o2, os2, hok1, hdg1, hst1, rfl⟩ hit, ?_⟩
    exact LpOut.pre (hr.trans hnext) hout
  · exact ⟨_, DIter.refl _, Or.inl hbeep⟩
  · exact ⟨_, DIter.refl _, Or.inr hsucc⟩


theorem incK_val (w k : Nat) (hk : 1 ≤ k) (hkw : k ≤ w) : incK w k - 1 = (k - 1 + 1) % w := by
  unfold incK
  split
  · subst_vars; have : k - 1 + 1 = k := by omega
    rw [this, Nat.mod_self]
  · have : k - 1 + 1 = k := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega

theorem incKn_val (w : Nat) : ∀ (n k : Nat), 1 ≤ k → k ≤ w → 1 ≤ incKn w n k ∧ incKn w n k ≤ w ∧
    incKn w n k - 1 = (k - 1 + n) % w
  | 0, k, hk, hkw => by
    refine ⟨hk, hkw, ?_⟩
    simp [incKn]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, k, hk, hkw => by
    have h1 := incK_bounds w k hk hkw
    obtain ⟨a, b, c⟩ := incKn_val w n (incK w k) h1.1 h1.2
    refine ⟨a, b, ?_⟩
    simp only [incKn]
    rw [c, incK_val w k hk hkw, Nat.mod_add_mod]
    congr 1; omega

/-- Every record carries the invariants `Ok` and `m = 0`. -/
def VI (v : VR) : Prop := v.Ok ∧ v.m = 0

theorem vis_fields (v : VR) (h : VI v) :
    VI v.vis ∧ v.vis.w = v.w ∧ v.vis.c = v.c ∧ v.vis.n = v.n ∧ v.vis.a = v.a ∧ v.vis.t = v.t ∧ v.vis.O = v.O ∧
    v.vis.E = v.E ∧ v.vis.P = v.P ∧
    v.vis.k - 1 = (v.k - 1 + (if v.c = 1 then v.n else 0)) % v.w := by
  obtain ⟨ho, hm⟩ := h
  by_cases hc : v.c = 1
  · have hb := incKn_val v.w v.n v.k ho.k1 ho.kw
    have e : v.vis = { v with k := incKn v.w v.n v.k, m := 0, n := v.n } := by
      unfold VR.vis; rw [if_pos hc, hm, Nat.zero_add]
    rw [e, if_pos hc]
    exact ⟨⟨{ F := ho.F, O := ho.O, P := ho.P, k1 := hb.1, kw := hb.2.1, E := ho.E, Elen := ho.Elen }, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hb.2.2⟩
  · have e : v.vis = v := by unfold VR.vis; rw [if_neg hc]
    rw [e, if_neg hc]
    refine ⟨⟨ho, hm⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by have := ho.kw; have := ho.k1; omega)]

theorem inc_fields (v : VR) (h : VI v) :
    VI v.inc ∧ v.inc.w = v.w ∧ v.inc.c = v.c ∧ v.inc.n = v.n ∧ v.inc.a = v.a ∧ v.inc.t = v.t ∧ v.inc.O = v.O ∧
    v.inc.E = v.E ∧ v.inc.P = v.P ∧ v.inc.k - 1 = (v.k - 1 + 1) % v.w := by
  obtain ⟨ho, hm⟩ := h
  exact ⟨⟨ho.inc, hm⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, incK_val v.w v.k ho.k1 ho.kw⟩

def visN : Nat → VR → VR
  | 0, v => v
  | r + 1, v => visN r v.vis

/-- Value `k - 1` of a record after `r` visits. -/
theorem visIter (r : Nat) : ∀ v : VR, VI v →
    VI (visN r v) ∧ (visN r v).w = v.w ∧ (visN r v).c = v.c ∧ (visN r v).n = v.n ∧
    (visN r v).a = v.a ∧ (visN r v).t = v.t ∧ (visN r v).O = v.O ∧ (visN r v).E = v.E ∧
    (visN r v).P = v.P ∧
    (visN r v).k - 1 = (v.k - 1 + r * (if v.c = 1 then v.n else 0)) % v.w := by
  induction r with
  | zero =>
    intro v h
    refine ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show v.k - 1 = (v.k - 1 + 0 * (if v.c = 1 then v.n else 0)) % v.w
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by have := h.1.kw; have := h.1.k1; omega)]
  | succ r ih =>
    intro v h
    simp only [visN]
    obtain ⟨h1, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := vis_fields v h
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := ih v.vis h1
    refine ⟨g1, by rw [g2, e1], by rw [g3, e2], by rw [g4, e3], by rw [g5, e4], by rw [g6, e5],
      by rw [g7, e6], by rw [g8, e7], by rw [g9, e8], ?_⟩
    rw [g10, e9, e2, e1, e3]
    rw [Nat.mod_add_mod, Nat.succ_mul]
    congr 1
    by_cases hc : v.c = 1
    · simp only [if_pos hc]
      generalize r * v.n = X
      omega
    · simp only [if_neg hc]
      simp

def incVisN : Nat → VR → VR
  | 0, v => v
  | r + 1, v => incVisN r v.inc.vis

theorem incVisN_val (r : Nat) : ∀ v : VR, VI v →
    VI (incVisN r v) ∧ (incVisN r v).w = v.w ∧ (incVisN r v).c = v.c ∧ (incVisN r v).n = v.n ∧
    (incVisN r v).a = v.a ∧ (incVisN r v).t = v.t ∧ (incVisN r v).O = v.O ∧ (incVisN r v).E = v.E ∧
    (incVisN r v).P = v.P ∧
    (incVisN r v).k - 1 = (v.k - 1 + r * (1 + (if v.c = 1 then v.n else 0))) % v.w := by
  induction r with
  | zero =>
    intro v h
    refine ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show v.k - 1 = (v.k - 1 + 0 * (1 + (if v.c = 1 then v.n else 0))) % v.w
    rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by have := h.1.kw; have := h.1.k1; omega)]
  | succ r ih =>
    intro v h
    simp only [incVisN]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := inc_fields v h
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := vis_fields v.inc a1
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := ih v.inc.vis b1
    refine ⟨g1, by rw [g2, b2, a2], by rw [g3, b3, a3], by rw [g4, b4, a4], by rw [g5, b5, a5],
      by rw [g6, b6, a6], by rw [g7, b7, a7], by rw [g8, b8, a8], by rw [g9, b9, a9], ?_⟩
    rw [g10, b10, a10, b3, b2, a3, a2, b4, a4, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]
    congr 1
    rw [Nat.succ_mul]
    generalize r * (1 + if v.c = 1 then v.n else 0) = X
    omega

theorem stepN_cons (r : Nat) : ∀ (w : VR) (ws : List VR), stepN r (w :: ws) = incVisN r w :: ws.map (visN r) := by
  induction r with
  | zero => intro w ws; simp [stepN, incVisN, visN]
  | succ r ih =>
    intro w ws
    simp only [stepN, stepList]
    rw [ih]
    simp [incVisN, visN, List.map_map, Function.comp_def]


theorem valsAux_prefix (t p : Nat) : ∀ (recs : List Rec) (j : Nat) (vs : List Nat),
    vs <+: valsAux t p j recs vs ∧ (valsAux t p j recs vs).length = vs.length + recs.length
  | [], j, vs => by simp [valsAux]
  | (u, b) :: rs, j, vs => by
    obtain ⟨h1, h2⟩ := valsAux_prefix t p rs (j + 1) (vs ++ [((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p])
    simp only [valsAux]
    refine ⟨(List.prefix_append _ _).trans h1, ?_⟩
    rw [h2]; simp; omega

theorem getD_prefix {l1 l2 : List Nat} (h : l1 <+: l2) {i : Nat} (hi : i < l1.length) : l2.getD i 0 = l1.getD i 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem valsAux_get (t p : Nat) : ∀ (recs : List Rec) (j : Nat) (vs : List Nat), vs.length = j →
    ∀ i, j ≤ i → i < j + recs.length →
    (valsAux t p j recs vs).getD i 0 =
      ((if i = t then 1 else 0) + (if i = 0 then 0 else (valsAux t p j recs vs).getD (i - 1) 0) +
        ptrVal (recs.getD (i - j) (none, 0)).1 i (recs.getD (i - j) (none, 0)).2 (valsAux t p j recs vs)) % p
  | [], j, vs, hl, i, h1, h2 => by simp at h2; omega
  | (u, b) :: rs, j, vs, hl, i, h1, h2 => by
    obtain ⟨v, hv⟩ : ∃ v, v = ((if j = t then 1 else 0) + vs.getLastD 0 + ptrVal u j b vs) % p := ⟨_, rfl⟩
    have hlen : (vs ++ [v]).length = j + 1 := by simp [hl]
    have pre := (valsAux_prefix t p rs (j + 1) (vs ++ [v])).1
    simp only [valsAux]
    rw [← hv]
    by_cases hij : i = j
    · subst hij
      have e1 : (valsAux t p (i + 1) rs (vs ++ [v])).getD i 0 = v := by
        rw [getD_prefix pre (by omega)]
        simp [hl]
      rw [e1]
      simp only [Nat.sub_self, List.getD_cons_zero]
      have e2 : vs.getLastD 0 = (if i = 0 then 0 else (valsAux t p (i + 1) rs (vs ++ [v])).getD (i - 1) 0) := by
        by_cases h0 : i = 0
        · subst h0; have : vs = [] := List.length_eq_zero_iff.1 hl
          subst this; simp
        · rw [if_neg h0, getD_prefix pre (by simp [hl]; omega)]
          have : vs ≠ [] := by intro h; subst h; simp at hl; omega
          rw [List.getLastD_eq_getLast?, List.getD_eq_getElem?_getD, List.getLast?_eq_getElem?]
          rw [List.getElem?_append_left (by omega)]
          simp [hl]
      have e3 : ptrVal u i b vs = ptrVal u i b (valsAux t p (i + 1) rs (vs ++ [v])) := by
        unfold ptrVal
        cases u with
        | none => rfl
        | some u =>
          simp only
          split
          · rename_i hu
            rw [getD_prefix pre (by simp [hl]; omega)]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
          · rfl
      conv => lhs; rw [hv, e2, e3]
    · have := valsAux_get t p rs (j + 1) (vs ++ [v]) hlen i (by omega) (by simp at h2 ⊢; omega)
      rw [this]
      have : i - j = (i - (j + 1)) + 1 := by omega
      rw [this]
      simp


def ptrOf (π : Nat) : Option Nat := if 2 ≤ π then some (π - 2) else none

/-- Per-record column invariant at column `j`. -/
def RecI (p T j π d : Nat) (vals : List Nat) (chain : Nat) (x : VR) : Prop :=
  VI x ∧ x.w = p ∧ x.n = d ∧ x.a + x.c = π ∧ x.a = min π (j + 1) ∧
    x.k - 1 = (T + chain + ptrVal (ptrOf π) j d vals) % p

theorem dec_fields' (v : VR) : v.dec.n = v.n ∧ v.dec.m = v.m ∧ v.dec.k = v.k ∧ v.dec.w = v.w ∧
    v.dec.a + v.dec.c = v.a + v.c ∧ (v.c = 0 → v.dec.a = v.a) ∧ (v.c ≠ 0 → v.dec.a = v.a + 1 ∧ v.dec.c = v.c - 1) := by
  unfold VR.dec
  by_cases h : v.c = 0
  · simp [h]
  · simp [h]; omega

theorem curG_f (v : VR) (h : VI v) : VI v.curG ∧ v.curG.n = v.dec.n ∧ v.curG.k = v.dec.k ∧ v.curG.w = v.dec.w ∧
    v.curG.a = v.dec.a ∧ v.curG.c = v.dec.c := by
  have hI : VI v.dec := ⟨v.dec_ok h.1, by rw [(dec_fields' v).2.1]; exact h.2⟩
  have hm : v.O = 3 → v.m = 0 := fun _ => h.2
  have hc := (curG_inv v h.1 hm).1
  have hmm := (dg_curG v).2
  refine ⟨⟨hc, by rw [hmm]; exact h.2⟩, ?_⟩
  unfold VR.curG
  split <;> simp [VR.cur]

theorem ptrVal_succ (π d j : Nat) (vals : List Nat) :
    ptrVal (ptrOf π) (j + 1) d vals = ptrVal (ptrOf π) j d vals + (if π = j + 2 then d * vals.getD j 0 else 0) := by
  unfold ptrVal ptrOf
  by_cases h : 2 ≤ π
  · simp only [h, if_true]
    by_cases h1 : π - 2 < j
    · have : π ≠ j + 2 := by omega
      simp [h1, this]; omega
    · by_cases h2 : π = j + 2
      · have e : π - 2 = j := by omega
        simp [e, h2]
      · have : ¬ (π - 2 < j + 1) := by omega
        simp [h1, this, h2]
  · simp only [h, if_false]
    have : π ≠ j + 2 := by omega
    simp [this]

theorem c1_iff (π j : Nat) (x : VR) (hac : x.a + x.c = π) (ha : x.a = min π (j + 1)) :
    (x.c = 1 ↔ π = j + 2) := by omega

theorem dec_a_min (π j : Nat) (y : VR) (hac : y.a + y.c = π) (ha : y.a = min π (j + 1)) :
    y.dec.a = min π (j + 1 + 1) := by
  have df := dec_fields' y
  by_cases h : y.c = 0
  · rw [df.2.2.2.2.2.1 h]; omega
  · rw [(df.2.2.2.2.2.2 h).1]; omega

theorem recI_tail (p T j π d : Nat) (vals : List Nat) (x : VR) (r : Nat) (hp : 0 < p)
    (h : RecI p T j π d vals 0 x) (hr : r = vals.getD j 0) :
    RecI p T (j + 1) π d vals 0 (VR.dec (visN r x)) := by
  obtain ⟨hI, hw, hn, hac, ha, hk⟩ := h
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := visIter r x hI
  have df := dec_fields' (visN r x)
  have hI' : VI (VR.dec (visN r x)) := ⟨(visN r x).dec_ok v1.1, by rw [df.2.1]; exact v1.2⟩
  have hac' : (visN r x).a + (visN r x).c = π := by rw [v3, v5]; exact hac
  have ha' : (visN r x).a = min π (j + 1) := by rw [v5]; exact ha
  refine ⟨hI', by rw [df.2.2.2.1, v2, hw], by rw [df.1, v4, hn], by rw [df.2.2.2.2.1]; exact hac',
    dec_a_min π j _ hac' ha', ?_⟩
  rw [df.2.2.1]
  rw [v10, hw, hk, Nat.mod_add_mod, ptrVal_succ]
  have := c1_iff π j x hac ha
  by_cases hc : x.c = 1
  · have h2 : π = j + 2 := this.1 hc
    simp only [if_pos hc, if_pos h2, hn]
    have e : r * d = d * vals.getD j 0 := by rw [hr, Nat.mul_comm]
    rw [e, Nat.add_assoc]
  · have h2 : ¬ π = j + 2 := fun e => hc (this.2 e)
    simp only [if_neg hc, if_neg h2, Nat.mul_zero, Nat.add_zero]

theorem recI_head (p T j π d : Nat) (vals : List Nat) (x : VR) (r : Nat) (hp : 0 < p)
    (h : RecI p T j π d vals 0 x) (hr : r = vals.getD j 0) :
    RecI p T (j + 1) π d vals r (VR.curG (incVisN r x)) := by
  obtain ⟨hI, hw, hn, hac, ha, hk⟩ := h
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := incVisN_val r x hI
  have df := dec_fields' (incVisN r x)
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f _ v1
  have hac' : (incVisN r x).a + (incVisN r x).c = π := by rw [v3, v5]; exact hac
  have ha' : (incVisN r x).a = min π (j + 1) := by rw [v5]; exact ha
  refine ⟨g1, by rw [g4, df.2.2.2.1, v2, hw], by rw [g2, df.1, v4, hn], ?_, ?_, ?_⟩
  · rw [g5, g6, df.2.2.2.2.1]; exact hac'
  · rw [g5]; exact dec_a_min π j _ hac' ha'
  · rw [g3, df.2.2.1, v10, hw, hk, Nat.mod_add_mod, ptrVal_succ]
    have := c1_iff π j x hac ha
    by_cases hc : x.c = 1
    · have h2 : π = j + 2 := this.1 hc
      simp only [if_pos hc, if_pos h2, hn]
      have e : r * (1 + d) = r + d * r := by rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm r d]
      rw [e, ← hr]
      congr 1; omega
    · have h2 : ¬ π = j + 2 := fun e => hc (this.2 e)
      simp only [if_neg hc, if_neg h2, Nat.add_zero, Nat.mul_zero]
      congr 1; omega

def ColInv (p t j : Nat) (πs ds vals : List Nat) (xs : List VR) : Prop :=
  ∀ idx x, xs[idx]? = some x →
    RecI p (if j + idx = t then 1 else 0) j (πs.getD (j + idx) 0) (ds.getD (j + idx) 0) vals
      (if idx = 0 then (if j = 0 then 0 else vals.getD (j - 1) 0) else 0) x

def ValsOk (p t N : Nat) (πs ds vals : List Nat) : Prop :=
  ∀ i, i < N → vals.getD i 0 =
    ((if i = t then 1 else 0) + (if i = 0 then 0 else vals.getD (i - 1) 0) +
      ptrVal (ptrOf (πs.getD i 0)) i (ds.getD i 0) vals) % p

theorem cursor_val (p t N : Nat) (πs ds vals : List Nat) (hV : ValsOk p t N πs ds vals) (j : Nat) (c : VR)
    (vs : List VR) (hj : j < N) (hI : ColInv p t j πs ds vals (c :: vs)) : c.k - 1 = vals.getD j 0 := by
  obtain ⟨_, _, _, _, _, hk⟩ := hI 0 c (by simp)
  rw [hk, hV j hj]
  simp

theorem loopVals (p t N : Nat) (πs ds vals : List Nat) (hp : 0 < p) (hV : ValsOk p t N πs ds vals) :
    ∀ (n j : Nat) (c : VR) (vs : List VR) (r s : Nat) (pp : Nat × Nat), vs.length = n → j + n + 1 = N →
      ColInv p t j πs ds vals (c :: vs) → r = c.k - 1 →
      (loopRun n c vs r s pp).cs.map (fun x => x.1.k - 1) = (List.range n).map (fun i => vals.getD (j + i) 0) ∧
      (loopRun n c vs r s pp).c'.k - 1 = vals.getD (j + n) 0 := by
  intro n
  induction n with
  | zero =>
    intro j c vs r s pp hl hN hI hr
    have hvs : vs = [] := List.length_eq_zero_iff.1 hl
    subst hvs
    simp only [loopRun, List.range_zero, List.map_nil, true_and]
    exact cursor_val p t N πs ds vals hV j c [] (by omega) hI
  | succ n ih =>
    intro j c vs r s pp hl hN hI hr
    obtain ⟨v0, vs', rfl⟩ : ∃ v0 vs', vs = v0 :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons a b => exact ⟨a, b, rfl⟩
    have hrj : r = vals.getD j 0 := by
      rw [hr]; exact cursor_val p t N πs ds vals hV j c _ (by omega) hI
    have h0 := hI 1 v0 (by simp)
    simp only [show ¬ ((1:Nat) = 0) from by decide, if_false] at h0
    have hhead := recI_head p _ j _ _ vals v0 r hp h0 hrj
    have hI' : ColInv p t (j + 1) πs ds vals
        (VR.curG (incVisN r v0) :: (vs'.map (visN r)).map VR.dec) := by
      intro idx x hx
      cases idx with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have e : (if (0:Nat) = 0 then (if j + 1 = 0 then 0 else vals.getD (j + 1 - 1) 0) else 0) = r := by
          simp [hrj]
        rw [e]; exact hhead
      | succ idx =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
        obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
        have hz' : (c :: v0 :: vs')[idx + 2]? = some z := by simpa using hz
        have h1 := hI (idx + 2) z hz'
        have e : j + 1 + (idx + 1) = j + (idx + 2) := by omega
        rw [e]
        simp only [show ¬ (idx + 2 = 0) from by omega, if_false] at h1
        simp only [show ¬ (idx + 1 = 0) from by omega, if_false]
        exact recI_tail p _ j _ _ vals z r hp h1 hrj
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f (incVisN r v0) (incVisN_val r v0 h0.1).1
    have df := dec_fields' (incVisN r v0)
    have hr' : (incVisN r v0).k - 1 = (VR.curG (incVisN r v0)).k - 1 := by rw [g3, df.2.2.1]
    have hl' : ((vs'.map (visN r)).map VR.dec).length = n := by simp at hl ⊢; omega
    have IH := ih (j + 1) (VR.curG (incVisN r v0)) _ ((incVisN r v0).k - 1) ((incVisN r v0).w - (incVisN r v0).k)
      (outP c r pp) hl' (by omega) hI' hr'
    have hk : (outRec c r).k = c.k := by unfold outRec; split <;> rfl
    simp only [loopRun, stepN_cons]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map, List.map_cons, List.map_cons]
      refine List.cons_eq_cons.2 ⟨?_, ?_⟩
      · simp only [hk, Nat.add_zero]; rw [← hr]; exact hrj.symm ▸ rfl
      · rw [IH.1, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1; omega
    · have := IH.2
      rw [this]; congr 1; omega


theorem eAdv_val (w : Nat) : ∀ (n e : Nat), 1 ≤ e → e ≤ w → 1 ≤ eAdv w n e ∧ eAdv w n e ≤ w ∧
    eAdv w n e - 1 = (e - 1 + n) % w
  | 0, e, h1, h2 => by
    refine ⟨h1, h2, ?_⟩
    simp [eAdv]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, e, h1, h2 => by
    have hb := incK_bounds w e h1 h2
    obtain ⟨a, b, c⟩ := eAdv_val w n (incK w e) hb.1 hb.2
    refine ⟨a, b, ?_⟩
    simp only [eAdv]
    rw [c, incK_val w e h1 h2, Nat.mod_add_mod]
    congr 1; omega

theorem sAdv_val : ∀ (n : Nat) (p : Nat × Nat), 1 ≤ p.2 →
    (sAdv n p).1 + (sAdv n p).2 = p.1 + p.2 ∧ 1 ≤ (sAdv n p).2 ∧
    (sAdv n p).1 = (p.1 + n) % (p.1 + p.2)
  | 0, p, h => by
    refine ⟨rfl, h, ?_⟩
    simp [sAdv]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1, p, h => by
    have hn : 1 ≤ (sNext p).2 ∧ (sNext p).1 + (sNext p).2 = p.1 + p.2 := by
      unfold sNext; split <;> simp <;> omega
    obtain ⟨a, b, c⟩ := sAdv_val n (sNext p) hn.1
    simp only [sAdv]
    refine ⟨by rw [a]; exact hn.2, b, ?_⟩
    rw [c, hn.2]
    have : (sNext p).1 = (p.1 + 1) % (p.1 + p.2) := by
      unfold sNext
      split
      · rename_i h2
        have : p.1 + 1 = p.1 + p.2 := by omega
        rw [this, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega)]
    rw [this, Nat.mod_add_mod]
    congr 1; omega

theorem count3_fld' (len e : Nat) (h : e ≤ len) : (fld len e).count 3 = e := by
  simp [fld, List.count_replicate]

/-- The `E` register of a finished output cursor: value `z * acc` (it was reset to value 0 by `curG`). -/
theorem outRec_E (c : VR) (r : Nat) (hO : c.O = 3) (hE : c.E = fld c.E.length 1) (hl : 1 ≤ c.E.length) :
    ∃ e, 1 ≤ e ∧ e ≤ c.E.length ∧ (outRec c r).E = fld c.E.length e ∧ e - 1 = (r * c.n) % c.E.length := by
  unfold outRec
  rw [if_neg (by omega)]
  have hc : c.E.count 3 = 1 := by rw [hE]; exact count3_fld' _ _ hl |>.trans rfl
  have := eAdv_val c.E.length (r * c.n) 1 (by omega) hl
  refine ⟨eAdv c.E.length (r * c.n) (c.E.count 3), ?_⟩
  rw [hc]
  refine ⟨this.1, this.2.1, rfl, ?_⟩
  rw [this.2.2]; simp


/-- A record at the start of pass `t` (before the first decrement). -/
def StartRec (p T π d : Nat) (y : VR) : Prop :=
  VI y ∧ y.w = p ∧ y.n = d ∧ y.a = 0 ∧ y.a + y.c = π ∧ y.k = T + 1

theorem recI_start_dec (p T π d : Nat) (vals : List Nat) (y : VR) (hp : 2 ≤ p) (hT : T ≤ 1)
    (h : StartRec p T π d y) : RecI p T 0 π d vals 0 y.dec := by
  obtain ⟨hI, hw, hn, ha, hac, hk⟩ := h
  have df := dec_fields' y
  have hdI : VI y.dec := ⟨y.dec_ok hI.1, by rw [df.2.1]; exact hI.2⟩
  refine ⟨hdI, by rw [df.2.2.2.1, hw], by rw [df.1, hn], by rw [df.2.2.2.2.1]; exact hac, ?_, ?_⟩
  · by_cases hc : y.c = 0
    · rw [df.2.2.2.2.2.1 hc]; omega
    · rw [(df.2.2.2.2.2.2 hc).1]; omega
  · rw [df.2.2.1, hk]
    have : ptrVal (ptrOf π) 0 d vals = 0 := by
      unfold ptrVal; cases ptrOf π <;> simp
    rw [this, Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; rfl

theorem recI_start_cur (p T π d : Nat) (vals : List Nat) (y : VR) (hp : 2 ≤ p) (hT : T ≤ 1)
    (h : StartRec p T π d y) : RecI p T 0 π d vals 0 y.curG := by
  have hd := recI_start_dec p T π d vals y hp hT h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := curG_f y h.1
  obtain ⟨_, hw, hn, hac, ha, hk⟩ := hd
  refine ⟨g1, by rw [g4]; exact hw, by rw [g2]; exact hn, by rw [g5, g6]; exact hac, by rw [g5]; exact ha, ?_⟩
  rw [g3]; exact hk

theorem startColInv (p t : Nat) (πs ds vals : List Nat) (hp : 2 ≤ p) (y0 : VR) (ys : List VR)
    (hy : ∀ idx y, (y0 :: ys)[idx]? = some y →
      StartRec p (if idx = t then 1 else 0) (πs.getD idx 0) (ds.getD idx 0) y) :
    ColInv p t 0 πs ds vals (y0.curG :: ys.map VR.dec) := by
  intro idx x hx
  cases idx with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    have := recI_start_cur p _ (πs.getD 0 0) (ds.getD 0 0) vals y0 hp (by split <;> omega) (hy 0 y0 (by simp))
    simpa using this
  | succ idx =>
    simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have := recI_start_dec p _ (πs.getD (idx + 1) 0) (ds.getD (idx + 1) 0) vals z hp (by split <;> omega)
      (hy (idx + 1) z (by simpa using hz))
    simpa using this

end ZP.NTT

