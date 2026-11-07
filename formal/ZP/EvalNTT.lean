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

end ZP.NTT

