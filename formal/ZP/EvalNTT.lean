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
            kw := (incKn_bounds v.w v.n v.k hv.k1 hv.kw).2, E := hv.E }
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
theorem visitAll : ∀ (vs : List VR) (v : VR), v.Ok → (∀ w ∈ vs, w.Ok) → ∀ (A0 : List Nat), Sym4 A0 →
    znttLogic.Reach (hdR QNTT.LA (A0 ++ [1]) (v.tl ++ tailVR vs))
      (hd QNTT.RFL (A0 ++ [1] ++ v.vis.tl ++ tailVR (vs.map VR.vis)) [])
  | [], v, hv, _, A0, hA => by
    have := visitEnd v hv A0 hA _ (visitPre v hv (A0 ++ [1]) [] (hA.app (sym4_cell 1 (by simp))) Sym4.nil)
    simpa [tailVR] using this
  | w :: vs, v, hv, hvs, A0, hA => by
    have hw : w.Ok := hvs w (by simp)
    have hvs' : ∀ x ∈ vs, x.Ok := fun x hx => hvs x (by simp [hx])
    have hf : BitsD [w.F, w.O, w.P] := hw.hdr3
    have h1 := visitNext v hv A0 [w.F, w.O, w.P] (w.tl ++ tailVR vs) hA hf
      (hw.tl_sym4.app (tailVR_sym4 vs hvs')) _
      (visitPre v hv (A0 ++ [1]) (1 :: 1 :: ([w.F, w.O, w.P] ++ 1 :: (w.tl ++ tailVR vs))) (hA.app (sym4_cell 1 (by simp)))
        (sym4_M (sym4_M ((hf.sym4).app (sym4_M (hw.tl_sym4.app (tailVR_sym4 vs hvs')))))))
    have h2 := visitAll vs w hw hvs' (A0 ++ [1] ++ v.vis.tl ++ [1, 1] ++ [w.F, w.O, w.P])
      ((((hA.app (sym4_cell 1 (by simp))).app (vis_Ok v hv).tl_sym4).app (sym4_M (sym4_M Sym4.nil))).app hf.sym4)
    obtain ⟨e1, e2, e3⟩ := vis_hdr w
    simp only [tailVR, VR.recd, List.map_cons, List.flatten_cons, e1, e2, e3, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact h1.trans h2

end ZP.NTT

