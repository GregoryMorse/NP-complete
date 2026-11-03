module

public import ZP.Zip

@[expose] public section

/-!
# A verified symbolic executor for logical machines

Segment lemmas of layer N3 are about tapes that hold words of unknown length: `J`,
`s`, counters, blocks of `1`s. A *symbolic configuration* `SC` lists the tape as
*items*: a concrete symbol `sym a`, or a block `blk i f`, which stands for the word
`env[i]` with every symbol mapped by `f` (the identity or a constant). The executor
`mstep` takes a concrete step when the head is on a concrete symbol, and jumps over a
whole block when the machine sweeps it (same state, same direction, rewriting by a
map that is again the identity or a constant). It knows only, for every word
variable, a list of the symbols it may contain.

`mreach_sound`: if `mreach` says that `c` reaches `t`, then the denotation of `c`
reaches that of `t` under every environment that respects the symbol lists. The
check `mreach … = true` is closed by `decide +kernel`.

`substCons` and `substSnoc` express `env[i] := b :: env[i]` and
`env[i] := env[i] ++ [b]` on the configuration side, so a loop body over a word is
also a single `mreach` check.
-/

namespace ZP

/-! ## Reachability -/

/-- `M` runs from `c` to `c'`, never stepping from the beep state. -/
def LTM.Reach (M : LTM) (c c' : ZC) : Prop := ∃ n, M.zrun n c = some c'

theorem LTM.Reach.refl (M : LTM) (c : ZC) : M.Reach c c := ⟨0, rfl⟩

theorem LTM.Reach.trans {M : LTM} {c c' c'' : ZC} (h1 : M.Reach c c') (h2 : M.Reach c' c'') :
    M.Reach c c'' := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨a + b, ?_⟩
  rw [LTM.zrun_add, ha]
  exact hb

theorem LTM.zrun_succ {M : LTM} {c c' : ZC} {n : Nat} (hb : c.q ≠ M.beep)
    (h : M.zstep c = some c') : M.zrun (n + 1) c = M.zrun n c' := by
  show (if c.q = M.beep then none else (M.zstep c).bind (M.zrun n)) = M.zrun n c'
  rw [ite_eq_right hb, h] <;> rfl

theorem LTM.Reach.step {M : LTM} {c c' c'' : ZC} (hb : c.q ≠ M.beep)
    (h : M.zstep c = some c') (h2 : M.Reach c' c'') : M.Reach c c'' := by
  obtain ⟨n, hn⟩ := h2
  exact ⟨n + 1, by rw [LTM.zrun_succ hb h]; exact hn⟩

theorem LTM.zstep_R {M : LTM} {q w q' : Nat} {L R : Strm} (h : M.act q (R 0) = some (w, 1, q')) :
    M.zstep ⟨q, L, R⟩ = some ⟨q', scons w L, stail R⟩ := by
  show (match M.act q (R 0) with
    | none => none
    | some (w, r, q') =>
      if r = 1 then some (⟨q', scons w L, stail R⟩ : ZC)
      else some (⟨q', stail L, scons (L 0) (scons w (stail R))⟩ : ZC)) = _
  rw [h] <;> rfl

theorem LTM.zstep_L {M : LTM} {q w d q' : Nat} {L R : Strm} (h : M.act q (R 0) = some (w, d, q'))
    (hd : d ≠ 1) : M.zstep ⟨q, L, R⟩ = some ⟨q', stail L, scons (L 0) (scons w (stail R))⟩ := by
  show (match M.act q (R 0) with
    | none => none
    | some (w, r, q') =>
      if r = 1 then some (⟨q', scons w L, stail R⟩ : ZC)
      else some (⟨q', stail L, scons (L 0) (scons w (stail R))⟩ : ZC)) = _
  rw [h]
  exact ite_eq_right hd

theorem sapp_rev_cons (a : Nat) (l : List Nat) (s : Strm) :
    sapp (a :: l).reverse s = sapp l.reverse (scons a s) := by
  rw [List.reverse_cons, sapp_append] <;> rfl

theorem map_rev (f : Nat → Nat) (l : List Nat) : l.reverse.map f = (l.map f).reverse := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.reverse_cons, List.map_append, ih]

/-! ## Symbolic configurations -/

/-- A symbol map: the identity or a constant. -/
inductive Fn where
  | id
  | const (c : Nat)
deriving DecidableEq, Repr

def Fn.app : Fn → Nat → Nat
  | .id, a => a
  | .const c, _ => c

inductive Item where
  | sym (a : Nat)
  | blk (i : Nat) (f : Fn)
deriving DecidableEq, Repr

/-- Values of the word variables. -/
abbrev Env := List (List Nat)

def Item.den (env : Env) : Item → List Nat
  | .sym a => [a]
  | .blk i f => (env.getD i []).map f.app

/-- Items in tape order. -/
def dR (env : Env) : List Item → List Nat
  | [] => []
  | it :: r => it.den env ++ dR env r

/-- Items nearest first, as the left stream reads them. -/
def dL (env : Env) : List Item → List Nat
  | [] => []
  | it :: l => (it.den env).reverse ++ dL env l

/-- State, items left of the boundary (nearest first), items right of it. The head is
on the first cell right of the boundary (`dirL = false`) or on the first cell left of
it (`dirL = true`). -/
structure SC where
  q : Nat
  l : List Item
  r : List Item
  dirL : Bool
deriving DecidableEq, Repr

def SC.den (env : Env) (c : SC) : ZC :=
  match c.dirL with
  | false => ⟨c.q, sapp (dL env c.l) blank, sapp (dR env c.r) blank⟩
  | true => ⟨c.q, stail (sapp (dL env c.l) blank),
      scons (sapp (dL env c.l) blank 0) (sapp (dR env c.r) blank)⟩

/-- Every word `env[i]` uses only symbols of `sets[i]`. -/
def Valid (sets env : Env) : Prop := ∀ i, ∀ a ∈ env.getD i [], a ∈ sets.getD i []

theorem Valid.nil (sets : Env) : Valid sets [] := by
  intro i a ha
  have : ([] : Env).getD i [] = [] := by cases i <;> rfl
  rw [this] at ha
  cases ha

theorem Valid.cons {S w : List Nat} {sets env : Env} (h : ∀ a ∈ w, a ∈ S) (h2 : Valid sets env) :
    Valid (S :: sets) (w :: env) := by
  intro i a ha
  cases i with
  | zero => exact h a ha
  | succ i => exact h2 i a ha

/-! ## The executor -/

inductive View where
  | cell (a : Nat) (rest : List Item)
  | block (i : Nat) (f : Fn) (rest : List Item)

/-- What the head meets first; the blank beyond the last item is a cell. -/
def view : List Item → View
  | [] => .cell 0 []
  | .sym a :: r => .cell a r
  | .blk i f :: r => .block i f r

def stepR (M : LTM) (q a : Nat) (l rest : List Item) : Option SC :=
  match M.act q a with
  | none => none
  | some (w, d, q') =>
    if d = 1 then some ⟨q', .sym w :: l, rest, false⟩ else some ⟨q', l, .sym w :: rest, true⟩

def stepL (M : LTM) (q a : Nat) (rest r : List Item) : Option SC :=
  match M.act q a with
  | none => none
  | some (w, d, q') =>
    if d = 1 then some ⟨q', .sym w :: rest, r, false⟩ else some ⟨q', rest, .sym w :: r, true⟩

/-- State `q` rewrites every symbol `f a` (`a ∈ S`) to `f' a`, moves in direction
`dir` and stays in `q`. -/
def sweepOK (M : LTM) (q dir : Nat) (S : List Nat) (f f' : Fn) : Bool :=
  S.all fun a => decide (M.act q (f.app a) = some (f'.app a, dir, q))

def sweepFn (M : LTM) (q dir : Nat) (S : List Nat) (f : Fn) : Option Fn :=
  if sweepOK M q dir S f f then some f
  else
    match M.act q (f.app (S.headD 0)) with
    | some (w, _, _) => if sweepOK M q dir S f (.const w) then some (.const w) else none
    | none => none

def mstepR (M : LTM) (sets : Env) (q : Nat) (l r : List Item) : Option SC :=
  match view r with
  | .cell a rest => stepR M q a l rest
  | .block i f rest =>
    (sweepFn M q 1 (sets.getD i []) f).map fun f' => ⟨q, .blk i f' :: l, rest, false⟩

def mstepL (M : LTM) (sets : Env) (q : Nat) (l r : List Item) : Option SC :=
  match view l with
  | .cell a rest => stepL M q a rest r
  | .block i f rest =>
    (sweepFn M q 0 (sets.getD i []) f).map fun f' => ⟨q, rest, .blk i f' :: r, true⟩

/-- One executor step; `none` in the beep state and wherever the executor is stuck. -/
def mstep (M : LTM) (sets : Env) (c : SC) : Option SC :=
  if c.q = M.beep then none
  else bif c.dirL then mstepL M sets c.q c.l c.r else mstepR M sets c.q c.l c.r

/-- `c` reaches `t` within `k` executor steps. -/
def mreach (M : LTM) (sets : Env) : Nat → SC → SC → Bool
  | 0, c, t => decide (c = t)
  | k + 1, c, t =>
    decide (c = t) || ((mstep M sets c).map fun c' => mreach M sets k c' t).getD false

/-! ## Soundness -/

theorem view_cellR {env : Env} {l rest : List Item} {a : Nat} (h : view l = .cell a rest) :
    sapp (dR env l) blank = scons a (sapp (dR env rest) blank) := by
  match l, h with
  | [], h =>
    cases h
    exact scons_blank.symm
  | .sym b :: r, h =>
    cases h
    rfl
  | .blk i f :: r, h => cases h

theorem view_cellL {env : Env} {l rest : List Item} {a : Nat} (h : view l = .cell a rest) :
    sapp (dL env l) blank = scons a (sapp (dL env rest) blank) := by
  match l, h with
  | [], h =>
    cases h
    exact scons_blank.symm
  | .sym b :: r, h =>
    cases h
    rfl
  | .blk i f :: r, h => cases h

theorem view_block {l rest : List Item} {i : Nat} {f : Fn} (h : view l = .block i f rest) :
    l = .blk i f :: rest := by
  match l, h with
  | [], h => cases h
  | .sym b :: r, h => cases h
  | .blk j g :: r, h =>
    cases h
    rfl

theorem stepR_sound {M : LTM} {env : Env} {q a : Nat} {l rest : List Item} {c' : SC}
    (hq : q ≠ M.beep) (h : stepR M q a l rest = some c') :
    M.Reach ⟨q, sapp (dL env l) blank, scons a (sapp (dR env rest) blank)⟩ (c'.den env) := by
  unfold stepR at h
  cases ha : M.act q a with
  | none =>
    rw [ha] at h
    have h' : (none : Option SC) = some c' := h
    cases h'
  | some x =>
    obtain ⟨w, d, q'⟩ := x
    rw [ha] at h
    have h' : (if d = 1 then some (⟨q', .sym w :: l, rest, false⟩ : SC)
        else some (⟨q', l, .sym w :: rest, true⟩ : SC)) = some c' := h
    by_cases hd : d = 1
    · subst hd
      rw [ite_eq_left rfl] at h'
      cases h'
      exact LTM.Reach.step hq (LTM.zstep_R ha) (LTM.Reach.refl M _)
    · rw [ite_eq_right hd] at h'
      cases h'
      exact LTM.Reach.step hq (LTM.zstep_L ha hd) (LTM.Reach.refl M _)

theorem stepL_sound {M : LTM} {env : Env} {q a : Nat} {rest r : List Item} {c' : SC}
    (hq : q ≠ M.beep) (h : stepL M q a rest r = some c') :
    M.Reach ⟨q, sapp (dL env rest) blank, scons a (sapp (dR env r) blank)⟩ (c'.den env) := by
  unfold stepL at h
  cases ha : M.act q a with
  | none =>
    rw [ha] at h
    have h' : (none : Option SC) = some c' := h
    cases h'
  | some x =>
    obtain ⟨w, d, q'⟩ := x
    rw [ha] at h
    have h' : (if d = 1 then some (⟨q', .sym w :: rest, r, false⟩ : SC)
        else some (⟨q', rest, .sym w :: r, true⟩ : SC)) = some c' := h
    by_cases hd : d = 1
    · subst hd
      rw [ite_eq_left rfl] at h'
      cases h'
      exact LTM.Reach.step hq (LTM.zstep_R ha) (LTM.Reach.refl M _)
    · rw [ite_eq_right hd] at h'
      cases h'
      exact LTM.Reach.step hq (LTM.zstep_L ha hd) (LTM.Reach.refl M _)

theorem sweepOK_spec {M : LTM} {q dir : Nat} {S : List Nat} {f f' : Fn}
    (h : sweepOK M q dir S f f' = true) :
    ∀ a ∈ S, M.act q (f.app a) = some (f'.app a, dir, q) := by
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp h a ha)

theorem sweepFn_spec {M : LTM} {q dir : Nat} {S : List Nat} {f f' : Fn}
    (h : sweepFn M q dir S f = some f') : sweepOK M q dir S f f' = true := by
  unfold sweepFn at h
  by_cases h1 : sweepOK M q dir S f f = true
  · rw [ite_eq_left h1] at h
    cases h
    exact h1
  · rw [ite_eq_right h1] at h
    cases hm : M.act q (f.app (S.headD 0)) with
    | none =>
      rw [hm] at h
      have h' : (none : Option Fn) = some f' := h
      cases h'
    | some x =>
      obtain ⟨w, d, q'⟩ := x
      rw [hm] at h
      have h2 : (if sweepOK M q dir S f (.const w) = true then some (Fn.const w) else none) =
          some f' := h
      by_cases h3 : sweepOK M q dir S f (.const w) = true
      · rw [ite_eq_left h3] at h2
        cases h2
        exact h3
      · rw [ite_eq_right h3] at h2
        cases h2

/-- Sweeping right over the symbols `as.map f`. -/
theorem sweepR_strm {M : LTM} {q : Nat} {f f' : Nat → Nat} (hq : q ≠ M.beep) :
    ∀ (as : List Nat) (Lt Rt : Strm), (∀ a ∈ as, M.act q (f a) = some (f' a, 1, q)) →
      M.zrun as.length ⟨q, Lt, sapp (as.map f) Rt⟩ = some ⟨q, sapp (as.map f').reverse Lt, Rt⟩ := by
  intro as
  induction as with
  | nil => intro Lt Rt _; rfl
  | cons a as ih =>
    intro Lt Rt h
    have ha : M.act q (f a) = some (f' a, 1, q) := h a (by simp)
    have h' : ∀ b ∈ as, M.act q (f b) = some (f' b, 1, q) := fun b hb => h b (by simp [hb])
    have hs : M.zstep ⟨q, Lt, sapp ((a :: as).map f) Rt⟩ =
        some ⟨q, scons (f' a) Lt, sapp (as.map f) Rt⟩ := LTM.zstep_R ha
    rw [show (a :: as).length = as.length + 1 from rfl, LTM.zrun_succ hq hs, ih _ _ h']
    show _ = some (⟨q, sapp (f' a :: as.map f').reverse Lt, Rt⟩ : ZC)
    rw [sapp_rev_cons]

/-- Sweeping left over the symbols `as.map f`, nearest first. -/
theorem sweepL_strm {M : LTM} {q : Nat} {f f' : Nat → Nat} (hq : q ≠ M.beep) :
    ∀ (as : List Nat) (Lt Rs : Strm), (∀ a ∈ as, M.act q (f a) = some (f' a, 0, q)) →
      M.zrun as.length ⟨q, stail (sapp (as.map f) Lt), scons (sapp (as.map f) Lt 0) Rs⟩ =
        some ⟨q, stail Lt, scons (Lt 0) (sapp (as.map f').reverse Rs)⟩ := by
  intro as
  induction as with
  | nil => intro Lt Rs _; rfl
  | cons a as ih =>
    intro Lt Rs h
    have ha : M.act q (f a) = some (f' a, 0, q) := h a (by simp)
    have h' : ∀ b ∈ as, M.act q (f b) = some (f' b, 0, q) := fun b hb => h b (by simp [hb])
    have hs : M.zstep ⟨q, stail (sapp ((a :: as).map f) Lt), scons (sapp ((a :: as).map f) Lt 0) Rs⟩ =
        some ⟨q, stail (sapp (as.map f) Lt), scons (sapp (as.map f) Lt 0) (scons (f' a) Rs)⟩ :=
      LTM.zstep_L ha (by decide)
    rw [show (a :: as).length = as.length + 1 from rfl, LTM.zrun_succ hq hs, ih Lt _ h']
    show _ = some (⟨q, stail Lt, scons (Lt 0) (sapp (f' a :: as.map f').reverse Rs)⟩ : ZC)
    rw [sapp_rev_cons]

theorem sweepR_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {q i : Nat} {f f' : Fn}
    {l rest : List Item} (hq : q ≠ M.beep) (hok : sweepOK M q 1 (sets.getD i []) f f' = true) :
    M.Reach (SC.den env ⟨q, l, .blk i f :: rest, false⟩)
      (SC.den env ⟨q, .blk i f' :: l, rest, false⟩) := by
  have hact : ∀ a ∈ env.getD i [], M.act q (f.app a) = some (f'.app a, 1, q) :=
    fun a ha => sweepOK_spec hok a (hv i a ha)
  refine ⟨(env.getD i []).length, ?_⟩
  show M.zrun _ ⟨q, sapp (dL env l) blank, sapp ((env.getD i []).map f.app ++ dR env rest) blank⟩ =
    some ⟨q, sapp (((env.getD i []).map f'.app).reverse ++ dL env l) blank, sapp (dR env rest) blank⟩
  rw [sapp_append, sapp_append]
  exact sweepR_strm hq _ _ _ hact

theorem sweepL_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {q i : Nat} {f f' : Fn}
    {rest r : List Item} (hq : q ≠ M.beep) (hok : sweepOK M q 0 (sets.getD i []) f f' = true) :
    M.Reach (SC.den env ⟨q, .blk i f :: rest, r, true⟩)
      (SC.den env ⟨q, rest, .blk i f' :: r, true⟩) := by
  have hact : ∀ a ∈ (env.getD i []).reverse, M.act q (f.app a) = some (f'.app a, 0, q) :=
    fun a ha => sweepOK_spec hok a (hv i a (List.mem_reverse.mp ha))
  have e1 : sapp (dL env (.blk i f :: rest)) blank =
      sapp ((env.getD i []).reverse.map f.app) (sapp (dL env rest) blank) := by
    show sapp (((env.getD i []).map f.app).reverse ++ dL env rest) blank = _
    rw [sapp_append, ← map_rev]
  have e2 : sapp (dR env (.blk i f' :: r)) blank =
      sapp ((env.getD i []).reverse.map f'.app).reverse (sapp (dR env r) blank) := by
    show sapp ((env.getD i []).map f'.app ++ dR env r) blank = _
    rw [sapp_append, map_rev, List.reverse_reverse]
  refine ⟨(env.getD i []).reverse.length, ?_⟩
  show M.zrun _ ⟨q, stail (sapp (dL env (.blk i f :: rest)) blank),
      scons (sapp (dL env (.blk i f :: rest)) blank 0) (sapp (dR env r) blank)⟩ =
    some ⟨q, stail (sapp (dL env rest) blank),
      scons (sapp (dL env rest) blank 0) (sapp (dR env (.blk i f' :: r)) blank)⟩
  rw [e1, e2]
  exact sweepL_strm hq _ _ _ hact

theorem view_cellR {env : Env} {l rest : List Item} {a : Nat} (h : view l = .cell a rest) :
    sapp (dR env l) blank = scons a (sapp (dR env rest) blank) := by
  match l, h with
  | [], h =>
    cases h
    exact scons_blank.symm
  | .sym b :: r, h =>
    cases h
    rfl
  | .blk i f :: r, h => cases h

theorem view_cellL {env : Env} {l rest : List Item} {a : Nat} (h : view l = .cell a rest) :
    sapp (dL env l) blank = scons a (sapp (dL env rest) blank) := by
  match l, h with
  | [], h =>
    cases h
    exact scons_blank.symm
  | .sym b :: r, h =>
    cases h
    rfl
  | .blk i f :: r, h => cases h

theorem view_block {l rest : List Item} {i : Nat} {f : Fn} (h : view l = .block i f rest) :
    l = .blk i f :: rest := by
  match l, h with
  | [], h => cases h
  | .sym b :: r, h => cases h
  | .blk j g :: r, h =>
    cases h
    rfl

theorem mstepR_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {q : Nat}
    {l r : List Item} {c' : SC} (hq : q ≠ M.beep) (h : mstepR M sets q l r = some c') :
    M.Reach (SC.den env ⟨q, l, r, false⟩) (c'.den env) := by
  unfold mstepR at h
  cases hw : view r with
  | cell a rest =>
    rw [hw] at h
    have h2 : stepR M q a l rest = some c' := h
    show M.Reach ⟨q, sapp (dL env l) blank, sapp (dR env r) blank⟩ _
    rw [view_cellR hw]
    exact stepR_sound hq h2
  | block i f rest =>
    rw [hw] at h
    have h2 : (sweepFn M q 1 (sets.getD i []) f).map
        (fun f' => (⟨q, .blk i f' :: l, rest, false⟩ : SC)) = some c' := h
    cases hs : sweepFn M q 1 (sets.getD i []) f with
    | none =>
      rw [hs] at h2
      have h3 : (none : Option SC) = some c' := h2
      cases h3
    | some f' =>
      rw [hs] at h2
      have h3 : some (⟨q, .blk i f' :: l, rest, false⟩ : SC) = some c' := h2
      cases h3
      obtain rfl := view_block hw
      exact sweepR_sound hv hq (sweepFn_spec hs)

theorem mstepL_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {q : Nat}
    {l r : List Item} {c' : SC} (hq : q ≠ M.beep) (h : mstepL M sets q l r = some c') :
    M.Reach (SC.den env ⟨q, l, r, true⟩) (c'.den env) := by
  unfold mstepL at h
  cases hw : view l with
  | cell a rest =>
    rw [hw] at h
    have h2 : stepL M q a rest r = some c' := h
    show M.Reach ⟨q, stail (sapp (dL env l) blank),
      scons (sapp (dL env l) blank 0) (sapp (dR env r) blank)⟩ _
    rw [view_cellL hw]
    exact stepL_sound hq h2
  | block i f rest =>
    rw [hw] at h
    have h2 : (sweepFn M q 0 (sets.getD i []) f).map
        (fun f' => (⟨q, rest, .blk i f' :: r, true⟩ : SC)) = some c' := h
    cases hs : sweepFn M q 0 (sets.getD i []) f with
    | none =>
      rw [hs] at h2
      have h3 : (none : Option SC) = some c' := h2
      cases h3
    | some f' =>
      rw [hs] at h2
      have h3 : some (⟨q, rest, .blk i f' :: r, true⟩ : SC) = some c' := h2
      cases h3
      obtain rfl := view_block hw
      exact sweepL_sound hv hq (sweepFn_spec hs)

theorem mstep_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {c c' : SC}
    (h : mstep M sets c = some c') : M.Reach (c.den env) (c'.den env) := by
  obtain ⟨q, l, r, dl⟩ := c
  have h0 : (if q = M.beep then none
      else bif dl then mstepL M sets q l r else mstepR M sets q l r) = some c' := h
  by_cases hq : q = M.beep
  · rw [ite_eq_left hq] at h0
    cases h0
  · rw [ite_eq_right hq] at h0
    cases dl with
    | false => exact mstepR_sound hv hq h0
    | true => exact mstepL_sound hv hq h0

theorem mreach_sound {M : LTM} {sets env : Env} (hv : Valid sets env) :
    ∀ (k : Nat) (c t : SC), mreach M sets k c t = true → M.Reach (c.den env) (t.den env) := by
  intro k
  induction k with
  | zero =>
    intro c t h
    have e : c = t := of_decide_eq_true h
    subst e
    exact LTM.Reach.refl M _
  | succ k ih =>
    intro c t h
    by_cases hct : c = t
    · subst hct
      exact LTM.Reach.refl M _
    · have h0 : (decide (c = t) ||
          ((mstep M sets c).map fun c' => mreach M sets k c' t).getD false) = true := h
      rw [decide_eq_false hct, Bool.false_or] at h0
      cases hm : mstep M sets c with
      | none =>
        rw [hm] at h0
        have h1 : false = true := h0
        cases h1
      | some c' =>
        rw [hm] at h0
        exact (mstep_sound hv hm).trans (ih c' t h0)

/-! ## Changing one word: `env[i] := b :: env[i]` and `env[i] := env[i] ++ [b]` -/

/-- `env` with word `i` replaced by `g` of it. -/
def Env.upd : Env → Nat → (List Nat → List Nat) → Env
  | [], _, _ => []
  | w :: env, 0, g => g w :: env
  | w :: env, i + 1, g => w :: Env.upd env i g

theorem Env.upd_getD_self : ∀ (env : Env) (i : Nat) (g : List Nat → List Nat),
    i < env.length → (env.upd i g).getD i [] = g (env.getD i [])
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: env, i + 1, g, h => Env.upd_getD_self env i g (Nat.lt_of_succ_lt_succ h)

theorem Env.upd_getD_ne : ∀ (env : Env) (i j : Nat) (g : List Nat → List Nat),
    j ≠ i → (env.upd i g).getD j [] = env.getD j []
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: env, i + 1, j + 1, g, h => Env.upd_getD_ne env i j g (fun e => h (by rw [e]))

theorem Env.upd_valid {sets env : Env} (hv : Valid sets env) {i : Nat} {g : List Nat → List Nat}
    (hg : ∀ a ∈ g (env.getD i []), a ∈ sets.getD i []) : Valid sets (env.upd i g) := by
  intro j a ha
  by_cases hj : j = i
  · subst hj
    by_cases hi : j < env.length
    · rw [Env.upd_getD_self env j g hi] at ha
      exact hg a ha
    · have e : env.upd j g = env := by
        clear ha hg hv
        induction env generalizing j with
        | nil => rfl
        | cons w env ih =>
          cases j with
          | zero => exact absurd (Nat.zero_lt_succ _) hi
          | succ j =>
            show w :: env.upd j g = w :: env
            rw [ih j (fun h => hi (Nat.succ_lt_succ h))]
      rw [e] at ha
      exact hv j a ha
  · rw [Env.upd_getD_ne env i j g hj] at ha
    exact hv j a ha

/-- Substitute an item by items (in tape order). -/
def substR (s : Item → List Item) : List Item → List Item
  | [] => []
  | it :: r => s it ++ substR s r

/-- The same for a list read nearest first. -/
def substL (s : Item → List Item) : List Item → List Item
  | [] => []
  | it :: l => (s it).reverse ++ substL s l

def SC.subst (s : Item → List Item) (c : SC) : SC := ⟨c.q, substL s c.l, substR s c.r, c.dirL⟩

def Item.cons (i b : Nat) : Item → List Item
  | .sym a => [.sym a]
  | .blk j f => if j = i then [.sym (f.app b), .blk j f] else [.blk j f]

def Item.snoc (i b : Nat) : Item → List Item
  | .sym a => [.sym a]
  | .blk j f => if j = i then [.blk j f, .sym (f.app b)] else [.blk j f]

theorem dR_append (env : Env) (u v : List Item) : dR env (u ++ v) = dR env u ++ dR env v := by
  induction u with
  | nil => rfl
  | cons it u ih =>
    show it.den env ++ dR env (u ++ v) = (it.den env ++ dR env u) ++ dR env v
    rw [ih, List.append_assoc]

theorem dL_append (env : Env) (u v : List Item) : dL env (u ++ v) = dL env u ++ dL env v := by
  induction u with
  | nil => rfl
  | cons it u ih =>
    show (it.den env).reverse ++ dL env (u ++ v) = ((it.den env).reverse ++ dL env u) ++ dL env v
    rw [ih, List.append_assoc]

theorem dL_reverse (env : Env) (u : List Item) : dL env u.reverse = (dR env u).reverse := by
  induction u with
  | nil => rfl
  | cons it u ih =>
    rw [List.reverse_cons, dL_append, ih]
    show (dR env u).reverse ++ ((it.den env).reverse ++ []) = (it.den env ++ dR env u).reverse
    rw [List.append_nil, List.reverse_append]

theorem den_subst {env env' : Env} {s : Item → List Item}
    (hs : ∀ it, it.den env' = dR env (s it)) (c : SC) : c.den env' = (c.subst s).den env := by
  have hR : ∀ r, dR env' r = dR env (substR s r) := by
    intro r
    induction r with
    | nil => rfl
    | cons it r ih =>
      show it.den env' ++ dR env' r = dR env (s it ++ substR s r)
      rw [dR_append, ih, hs]
  have hL : ∀ l, dL env' l = dL env (substL s l) := by
    intro l
    induction l with
    | nil => rfl
    | cons it l ih =>
      show (it.den env').reverse ++ dL env' l = dL env ((s it).reverse ++ substL s l)
      rw [dL_append, ih, hs, dL_reverse]
  obtain ⟨q, l, r, dl⟩ := c
  cases dl with
  | false =>
    show (⟨q, sapp (dL env' l) blank, sapp (dR env' r) blank⟩ : ZC) =
      ⟨q, sapp (dL env (substL s l)) blank, sapp (dR env (substR s r)) blank⟩
    rw [hL, hR]
  | true =>
    show (⟨q, stail (sapp (dL env' l) blank), scons (sapp (dL env' l) blank 0)
        (sapp (dR env' r) blank)⟩ : ZC) =
      ⟨q, stail (sapp (dL env (substL s l)) blank), scons (sapp (dL env (substL s l)) blank 0)
        (sapp (dR env (substR s r)) blank)⟩
    rw [hL, hR]

theorem item_cons {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (it : Item) :
    it.den (env.upd i (b :: ·)) = dR env (it.cons i b) := by
  cases it with
  | sym a => rfl
  | blk j f =>
    by_cases hj : j = i
    · subst hj
      show ((env.upd j (b :: ·)).getD j []).map f.app =
        dR env (if j = j then [.sym (f.app b), .blk j f] else [.blk j f])
      rw [ite_eq_left rfl, Env.upd_getD_self env j _ hi]
      show f.app b :: (env.getD j []).map f.app = [f.app b] ++ ((env.getD j []).map f.app ++ [])
      rw [List.append_nil]
      rfl
    · show ((env.upd i (b :: ·)).getD j []).map f.app =
        dR env (if j = i then [.sym (f.app b), .blk j f] else [.blk j f])
      rw [ite_eq_right hj, Env.upd_getD_ne env i j _ hj]
      show _ = (env.getD j []).map f.app ++ []
      rw [List.append_nil]

theorem item_snoc {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (it : Item) :
    it.den (env.upd i (· ++ [b])) = dR env (it.snoc i b) := by
  cases it with
  | sym a => rfl
  | blk j f =>
    by_cases hj : j = i
    · subst hj
      show ((env.upd j (· ++ [b])).getD j []).map f.app =
        dR env (if j = j then [.blk j f, .sym (f.app b)] else [.blk j f])
      rw [ite_eq_left rfl, Env.upd_getD_self env j _ hi]
      show (env.getD j [] ++ [b]).map f.app = (env.getD j []).map f.app ++ ([f.app b] ++ [])
      rw [List.map_append]
      rfl
    · show ((env.upd i (· ++ [b])).getD j []).map f.app =
        dR env (if j = i then [.blk j f, .sym (f.app b)] else [.blk j f])
      rw [ite_eq_right hj, Env.upd_getD_ne env i j _ hj]
      show _ = (env.getD j []).map f.app ++ []
      rw [List.append_nil]

theorem den_cons {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (c : SC) :
    c.den (env.upd i (b :: ·)) = (c.subst (Item.cons i b)).den env :=
  den_subst (item_cons hi b) c

theorem den_snoc {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (c : SC) :
    c.den (env.upd i (· ++ [b])) = (c.subst (Item.snoc i b)).den env :=
  den_subst (item_snoc hi b) c

/-- A loop body as one check: from `c` with `env[i] = b :: _` to `c` with
`env[i'] = _ ++ [b]`. -/
theorem body_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {i i' : Nat}
    (hi : i < env.length) (hi' : i' < env.length) {b k : Nat} {c : SC}
    (h : mreach M sets k (c.subst (Item.cons i b)) (c.subst (Item.snoc i' b)) = true) :
    M.Reach (c.den (env.upd i (b :: ·))) (c.den (env.upd i' (· ++ [b]))) := by
  rw [den_cons hi, den_snoc hi']
  exact mreach_sound hv _ _ _ h

/-- Moving a word from one variable to another, one symbol per iteration. -/
theorem LTM.Reach.fold {M : LTM} {S : List Nat} (F : List Nat → List Nat → ZC)
    (h : ∀ u b v, b ∈ S → M.Reach (F u (b :: v)) (F (u ++ [b]) v)) :
    ∀ v u, (∀ x ∈ v, x ∈ S) → M.Reach (F u v) (F (u ++ v) []) := by
  intro v
  induction v with
  | nil =>
    intro u _
    rw [List.append_nil]
    exact LTM.Reach.refl M _
  | cons b v ih =>
    intro u hv
    refine (h u b v (hv b (by simp))).trans ?_
    have := ih (u ++ [b]) (fun x hx => hv x (by simp [hx]))
    rw [List.append_assoc] at this
    exact this

end ZP
