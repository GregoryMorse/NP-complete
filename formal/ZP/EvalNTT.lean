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

end ZP.NTT

