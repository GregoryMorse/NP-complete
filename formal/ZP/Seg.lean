module

public import ZP.Zip
public import ZP.Logic

@[expose] public section

/-!
# Segment lemmas: tools

`Reach c c'`: `zpLogic` runs from `c` to `c'` without taking a step from the beep
state. Layouts are written `cfg q l r`: state `q`, the cells `l` left of the head (in
tape order), the head on the first cell of `r`, blanks beyond both ends.

The sweep lemmas cover every state that walks over a block of symbols, rewriting each
symbol by a fixed map. Their side conditions are checked by `decide +kernel`.
-/

namespace ZP

/-- `zpLogic` runs from `c` to `c'`, never stepping from the beep state. -/
def Reach (c c' : ZC) : Prop := ∃ n, zpLogic.zrun n c = some c'

theorem Reach.refl (c : ZC) : Reach c c := ⟨0, rfl⟩

theorem Reach.trans {c c' c'' : ZC} (h1 : Reach c c') (h2 : Reach c' c'') : Reach c c'' := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a + b, ?_⟩
  rw [LTM.zrun_add, ha]
  exact hb

theorem zrun_step {M : LTM} {c c' : ZC} {n : Nat} (hb : c.q ≠ M.beep)
    (h : M.zstep c = some c') : M.zrun (n + 1) c = M.zrun n c' := by
  show (if c.q = M.beep then none else (M.zstep c).bind (M.zrun n)) = M.zrun n c'
  rw [ite_eq_right hb, h] <;> rfl

theorem Reach.step {c c' c'' : ZC} (hb : c.q ≠ zpLogic.beep) (h : zpLogic.zstep c = some c')
    (h2 : Reach c' c'') : Reach c c'' := by
  obtain ⟨n, hn⟩ := h2
  exact ⟨n + 1, by rw [zrun_step hb h]; exact hn⟩

theorem zstep_R {M : LTM} {q w q' : Nat} {L R : Strm} (h : M.act q (R 0) = some (w, 1, q')) :
    M.zstep ⟨q, L, R⟩ = some ⟨q', scons w L, stail R⟩ := by
  show (match M.act q (R 0) with
    | none => none
    | some (w, r, q') =>
      if r = 1 then some (⟨q', scons w L, stail R⟩ : ZC)
      else some (⟨q', stail L, scons (L 0) (scons w (stail R))⟩ : ZC)) = _
  rw [h] <;> rfl

theorem zstep_L {M : LTM} {q w q' : Nat} {L R : Strm} (h : M.act q (R 0) = some (w, 0, q')) :
    M.zstep ⟨q, L, R⟩ = some ⟨q', stail L, scons (L 0) (scons w (stail R))⟩ := by
  show (match M.act q (R 0) with
    | none => none
    | some (w, r, q') =>
      if r = 1 then some (⟨q', scons w L, stail R⟩ : ZC)
      else some (⟨q', stail L, scons (L 0) (scons w (stail R))⟩ : ZC)) = _
  rw [h] <;> rfl

theorem sapp_rev_cons (a : Nat) (l : List Nat) (s : Strm) :
    sapp (a :: l).reverse s = sapp l.reverse (scons a s) := by
  rw [List.reverse_cons, sapp_append] <;> rfl

/-! ## Sweeps on streams -/

theorem sweepR {M : LTM} {q : Nat} {S : List Nat} {f : Nat → Nat} (hq : q ≠ M.beep)
    (hact : ∀ a ∈ S, M.act q a = some (f a, 1, q)) :
    ∀ (w : List Nat) (Lt s : Strm), (∀ a ∈ w, a ∈ S) →
      M.zrun w.length ⟨q, Lt, sapp w s⟩ = some ⟨q, sapp (w.map f).reverse Lt, s⟩ := by
  intro w
  induction w with
  | nil => intro Lt s _; rfl
  | cons a w ih =>
    intro Lt s hw
    have ha : a ∈ S := hw a (by simp)
    have hw' : ∀ b ∈ w, b ∈ S := fun b hb => hw b (by simp [hb])
    have hs : M.zstep ⟨q, Lt, sapp (a :: w) s⟩ = some ⟨q, scons (f a) Lt, sapp w s⟩ :=
      zstep_R (hact a ha)
    rw [show (a :: w).length = w.length + 1 from rfl, zrun_step hq hs, ih _ s hw']
    show _ = some (⟨q, sapp (f a :: w.map f).reverse Lt, s⟩ : ZC)
    rw [sapp_rev_cons (f a)]

theorem sweepL {M : LTM} {q : Nat} {S : List Nat} {f : Nat → Nat} (hq : q ≠ M.beep)
    (hact : ∀ a ∈ S, M.act q a = some (f a, 0, q)) :
    ∀ (w : List Nat) (x : Nat) (Lt Rt : Strm), x ∈ S → (∀ a ∈ w, a ∈ S) →
      M.zrun (w.length + 1) ⟨q, sapp w Lt, scons x Rt⟩ =
        some ⟨q, stail Lt, scons (Lt 0) (sapp ((x :: w).map f).reverse Rt)⟩ := by
  intro w
  induction w with
  | nil =>
    intro x Lt Rt hx _
    have hs : M.zstep ⟨q, sapp [] Lt, scons x Rt⟩ =
        some ⟨q, stail Lt, scons (Lt 0) (scons (f x) Rt)⟩ := zstep_L (hact x hx)
    rw [show ([] : List Nat).length + 1 = 0 + 1 from rfl, zrun_step hq hs]
    rfl
  | cons y w ih =>
    intro x Lt Rt hx hw
    have hy : y ∈ S := hw y (by simp)
    have hw' : ∀ b ∈ w, b ∈ S := fun b hb => hw b (by simp [hb])
    have hs : M.zstep ⟨q, sapp (y :: w) Lt, scons x Rt⟩ =
        some ⟨q, sapp w Lt, scons y (scons (f x) Rt)⟩ := zstep_L (hact x hx)
    rw [show (y :: w).length + 1 = (w.length + 1) + 1 from rfl, zrun_step hq hs,
      ih y Lt (scons (f x) Rt) hy hw']
    show _ = some (⟨q, stail Lt, scons (Lt 0) (sapp (f x :: (y :: w).map f).reverse Rt)⟩ : ZC)
    rw [sapp_rev_cons (f x)]

/-! ## List layouts -/

/-- State `q`, cells `l` left of the head, head on the first cell of `r`. -/
def cfg (q : Nat) (l r : List Nat) : ZC := ⟨q, sapp l.reverse blank, sapp r blank⟩

theorem map_rev (f : Nat → Nat) (l : List Nat) : l.reverse.map f = (l.map f).reverse := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.reverse_cons, List.map_append, ih]

theorem sapp_left (l w : List Nat) : sapp (l ++ w).reverse blank = sapp w.reverse (sapp l.reverse blank) := by
  rw [List.reverse_append, sapp_append]

/-- Leading blanks on the left can be dropped. -/
theorem cfg_padL (q : Nat) (l r : List Nat) : cfg q (0 :: l) r = cfg q l r := by
  show (⟨q, sapp (0 :: l).reverse blank, sapp r blank⟩ : ZC) = ⟨q, sapp l.reverse blank, sapp r blank⟩
  rw [sapp_rev_cons, scons_blank]

/-- Trailing blanks on the right can be dropped. -/
theorem cfg_padR (q : Nat) (l r : List Nat) : cfg q l (r ++ [0]) = cfg q l r := by
  show (⟨q, sapp l.reverse blank, sapp (r ++ [0]) blank⟩ : ZC) = ⟨q, sapp l.reverse blank, sapp r blank⟩
  rw [sapp_append]
  show (⟨q, sapp l.reverse blank, sapp r (scons 0 blank)⟩ : ZC) = _
  rw [scons_blank]

/-- Right sweep in layout form. -/
theorem sweepR_cfg {q : Nat} {S : List Nat} {f : Nat → Nat} (hq : q ≠ zpLogic.beep)
    (hact : ∀ a ∈ S, zpLogic.act q a = some (f a, 1, q)) (l w r : List Nat)
    (hw : ∀ a ∈ w, a ∈ S) : Reach (cfg q l (w ++ r)) (cfg q (l ++ w.map f) r) := by
  refine ⟨w.length, ?_⟩
  show zpLogic.zrun w.length ⟨q, sapp l.reverse blank, sapp (w ++ r) blank⟩ =
    some ⟨q, sapp (l ++ w.map f).reverse blank, sapp r blank⟩
  rw [sapp_append, sweepR hq hact w _ _ hw, sapp_left]

/-- Left sweep in layout form: the head walks left over `w` and stops on `y`. -/
theorem sweepL_cfg {q : Nat} {S : List Nat} {f : Nat → Nat} (hq : q ≠ zpLogic.beep)
    (hact : ∀ a ∈ S, zpLogic.act q a = some (f a, 0, q)) (l0 : List Nat) (y : Nat)
    (w : List Nat) (x : Nat) (r : List Nat) (hx : x ∈ S) (hw : ∀ a ∈ w, a ∈ S) :
    Reach (cfg q (l0 ++ y :: w) (x :: r)) (cfg q l0 (y :: (w ++ [x]).map f ++ r)) := by
  refine ⟨w.reverse.length + 1, ?_⟩
  have hw' : ∀ a ∈ w.reverse, a ∈ S := fun a ha => hw a (List.mem_reverse.mp ha)
  show zpLogic.zrun (w.reverse.length + 1)
      ⟨q, sapp (l0 ++ y :: w).reverse blank, sapp (x :: r) blank⟩ =
    some ⟨q, sapp l0.reverse blank, sapp (y :: (w ++ [x]).map f ++ r) blank⟩
  have e1 : sapp (l0 ++ y :: w).reverse blank = sapp w.reverse (scons y (sapp l0.reverse blank)) := by
    rw [sapp_left, sapp_rev_cons]
  rw [e1]
  rw [show sapp (x :: r) blank = scons x (sapp r blank) from rfl]
  rw [sweepL hq hact w.reverse x _ _ hx hw']
  show some (⟨q, sapp l0.reverse blank, scons y (sapp ((x :: w.reverse).map f).reverse (sapp r blank))⟩ : ZC) =
    some ⟨q, sapp l0.reverse blank, scons y (sapp ((w ++ [x]).map f ++ r) blank)⟩
  have e2 : ((x :: w.reverse).map f).reverse = (w ++ [x]).map f := by
    simp [List.map_append, List.reverse_cons]
  rw [sapp_append, e2]

end ZP
