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

theorem SC.den_q (env : Env) (c : SC) : (c.den env).q = c.q := by
  obtain ⟨q, l, r, dl⟩ := c
  cases dl <;> rfl

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

/-- `1^n 1 = 1 1^n`: a constant block and the same symbol after it commute. -/
def swapB (i : Nat) (f : Fn) : List Item → Option (List Item)
  | .sym a :: rest => if f = .const a then some (.sym a :: .blk i f :: rest) else none
  | _ => none

def blockR (M : LTM) (sets : Env) (q : Nat) (l : List Item) (i : Nat) (f : Fn)
    (rest : List Item) : Option SC :=
  match sweepFn M q 1 (sets.getD i []) f with
  | some f' => some ⟨q, .blk i f' :: l, rest, false⟩
  | none => (swapB i f rest).map fun r' => ⟨q, l, r', false⟩

def blockL (M : LTM) (sets : Env) (q : Nat) (r : List Item) (i : Nat) (f : Fn)
    (rest : List Item) : Option SC :=
  match sweepFn M q 0 (sets.getD i []) f with
  | some f' => some ⟨q, rest, .blk i f' :: r, true⟩
  | none => (swapB i f rest).map fun l' => ⟨q, l', r, true⟩

def mstepR (M : LTM) (sets : Env) (q : Nat) (l r : List Item) : Option SC :=
  match view r with
  | .cell a rest => stepR M q a l rest
  | .block i f rest => blockR M sets q l i f rest

def mstepL (M : LTM) (sets : Env) (q : Nat) (l r : List Item) : Option SC :=
  match view l with
  | .cell a rest => stepL M q a rest r
  | .block i f rest => blockL M sets q r i f rest

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

theorem const_comm (c : Nat) :
    ∀ w : List Nat, w.map (Fn.const c).app ++ [c] = c :: w.map (Fn.const c).app
  | [] => rfl
  | _ :: w => by
    show c :: (w.map (Fn.const c).app ++ [c]) = c :: c :: w.map (Fn.const c).app
    rw [const_comm c w]

theorem const_rev (c : Nat) : ∀ w : List Nat, (w.map (Fn.const c).app).reverse = w.map (Fn.const c).app
  | [] => rfl
  | _ :: w => by
    show (c :: w.map (Fn.const c).app).reverse = c :: w.map (Fn.const c).app
    rw [List.reverse_cons, const_rev c w, const_comm]

theorem swapB_dR {env : Env} {i : Nat} {f : Fn} {rest r' : List Item}
    (h : swapB i f rest = some r') : dR env (.blk i f :: rest) = dR env r' := by
  match rest, h with
  | .sym a :: rest, h =>
    have h' : (if f = .const a then some (.sym a :: .blk i f :: rest) else none) = some r' := h
    by_cases hf : f = .const a
    · subst hf
      rw [ite_eq_left rfl] at h'
      cases h'
      have e := const_comm a (env.getD i [])
      show (env.getD i []).map (Fn.const a).app ++ ([a] ++ dR env rest) =
        a :: ((env.getD i []).map (Fn.const a).app ++ dR env rest)
      rw [← List.append_assoc, e, List.cons_append]
    · rw [ite_eq_right hf] at h'
      cases h'
  | .blk _ _ :: _, h => cases h
  | [], h => cases h

theorem swapB_dL {env : Env} {i : Nat} {f : Fn} {rest l' : List Item}
    (h : swapB i f rest = some l') : dL env (.blk i f :: rest) = dL env l' := by
  match rest, h with
  | .sym a :: rest, h =>
    have h' : (if f = .const a then some (.sym a :: .blk i f :: rest) else none) = some l' := h
    by_cases hf : f = .const a
    · subst hf
      rw [ite_eq_left rfl] at h'
      cases h'
      have e := const_comm a (env.getD i [])
      show ((env.getD i []).map (Fn.const a).app).reverse ++ ([a] ++ dL env rest) =
        a :: (((env.getD i []).map (Fn.const a).app).reverse ++ dL env rest)
      rw [const_rev, ← List.append_assoc, e, List.cons_append]
    · rw [ite_eq_right hf] at h'
      cases h'
  | .blk _ _ :: _, h => cases h
  | [], h => cases h

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
    have h2 : blockR M sets q l i f rest = some c' := h
    unfold blockR at h2
    obtain rfl := view_block hw
    cases hs : sweepFn M q 1 (sets.getD i []) f with
    | some f' =>
      rw [hs] at h2
      have h3 : some (⟨q, .blk i f' :: l, rest, false⟩ : SC) = some c' := h2
      cases h3
      exact sweepR_sound hv hq (sweepFn_spec hs)
    | none =>
      rw [hs] at h2
      have h3 : (swapB i f rest).map (fun r' => (⟨q, l, r', false⟩ : SC)) = some c' := h2
      cases hb : swapB i f rest with
      | none =>
        rw [hb] at h3
        have h4 : (none : Option SC) = some c' := h3
        cases h4
      | some r' =>
        rw [hb] at h3
        have h4 : some (⟨q, l, r', false⟩ : SC) = some c' := h3
        cases h4
        show M.Reach ⟨q, sapp (dL env l) blank, sapp (dR env (.blk i f :: rest)) blank⟩
          ⟨q, sapp (dL env l) blank, sapp (dR env r') blank⟩
        rw [swapB_dR hb]
        exact LTM.Reach.refl M _

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
    have h2 : blockL M sets q r i f rest = some c' := h
    unfold blockL at h2
    obtain rfl := view_block hw
    cases hs : sweepFn M q 0 (sets.getD i []) f with
    | some f' =>
      rw [hs] at h2
      have h3 : some (⟨q, rest, .blk i f' :: r, true⟩ : SC) = some c' := h2
      cases h3
      exact sweepL_sound hv hq (sweepFn_spec hs)
    | none =>
      rw [hs] at h2
      have h3 : (swapB i f rest).map (fun l' => (⟨q, l', r, true⟩ : SC)) = some c' := h2
      cases hb : swapB i f rest with
      | none =>
        rw [hb] at h3
        have h4 : (none : Option SC) = some c' := h3
        cases h4
      | some l' =>
        rw [hb] at h3
        have h4 : some (⟨q, l', r, true⟩ : SC) = some c' := h3
        cases h4
        show M.Reach ⟨q, stail (sapp (dL env (.blk i f :: rest)) blank),
            scons (sapp (dL env (.blk i f :: rest)) blank 0) (sapp (dR env r) blank)⟩
          ⟨q, stail (sapp (dL env l') blank), scons (sapp (dL env l') blank 0) (sapp (dR env r) blank)⟩
        rw [swapB_dL hb]
        exact LTM.Reach.refl M _

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
    i < env.length → (Env.upd env i g).getD i [] = g (env.getD i [])
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: env, i + 1, g, h => Env.upd_getD_self env i g (Nat.lt_of_succ_lt_succ h)

theorem Env.upd_getD_ne : ∀ (env : Env) (i j : Nat) (g : List Nat → List Nat),
    j ≠ i → (Env.upd env i g).getD j [] = env.getD j []
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: env, i + 1, j + 1, g, h => Env.upd_getD_ne env i j g (fun e => h (by rw [e]))

theorem Env.upd_valid {sets env : Env} (hv : Valid sets env) {i : Nat} {g : List Nat → List Nat}
    (hg : ∀ a ∈ g (env.getD i []), a ∈ sets.getD i []) : Valid sets (Env.upd env i g) := by
  intro j a ha
  by_cases hj : j = i
  · subst hj
    by_cases hi : j < env.length
    · rw [Env.upd_getD_self env j g hi] at ha
      exact hg a ha
    · have e : Env.upd env j g = env := by
        clear ha hg hv
        induction env generalizing j with
        | nil => rfl
        | cons w env ih =>
          cases j with
          | zero => exact absurd (Nat.zero_lt_succ _) hi
          | succ j =>
            show w :: Env.upd env j g = w :: env
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
    it.den (Env.upd env i (b :: ·)) = dR env (it.cons i b) := by
  cases it with
  | sym a => rfl
  | blk j f =>
    by_cases hj : j = i
    · subst hj
      show ((Env.upd env j (b :: ·)).getD j []).map f.app =
        dR env (if j = j then [.sym (f.app b), .blk j f] else [.blk j f])
      rw [ite_eq_left rfl, Env.upd_getD_self env j _ hi]
      show f.app b :: (env.getD j []).map f.app = [f.app b] ++ ((env.getD j []).map f.app ++ [])
      rw [List.append_nil]
      rfl
    · show ((Env.upd env i (b :: ·)).getD j []).map f.app =
        dR env (if j = i then [.sym (f.app b), .blk j f] else [.blk j f])
      rw [ite_eq_right hj, Env.upd_getD_ne env i j _ hj]
      show _ = (env.getD j []).map f.app ++ []
      rw [List.append_nil]

theorem item_snoc {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (it : Item) :
    it.den (Env.upd env i (· ++ [b])) = dR env (it.snoc i b) := by
  cases it with
  | sym a => rfl
  | blk j f =>
    by_cases hj : j = i
    · subst hj
      show ((Env.upd env j (· ++ [b])).getD j []).map f.app =
        dR env (if j = j then [.blk j f, .sym (f.app b)] else [.blk j f])
      rw [ite_eq_left rfl, Env.upd_getD_self env j _ hi]
      show (env.getD j [] ++ [b]).map f.app = (env.getD j []).map f.app ++ ([f.app b] ++ [])
      rw [List.map_append]
      rfl
    · show ((Env.upd env i (· ++ [b])).getD j []).map f.app =
        dR env (if j = i then [.blk j f, .sym (f.app b)] else [.blk j f])
      rw [ite_eq_right hj, Env.upd_getD_ne env i j _ hj]
      show _ = (env.getD j []).map f.app ++ []
      rw [List.append_nil]

theorem den_cons {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (c : SC) :
    c.den (Env.upd env i (b :: ·)) = (c.subst (Item.cons i b)).den env :=
  den_subst (item_cons hi b) c

theorem den_snoc {env : Env} {i : Nat} (hi : i < env.length) (b : Nat) (c : SC) :
    c.den (Env.upd env i (· ++ [b])) = (c.subst (Item.snoc i b)).den env :=
  den_subst (item_snoc hi b) c

/-- A loop body as one check: from `c` with `env[i] = b :: _` to `c` with
`env[i'] = _ ++ [b]`. -/
theorem body_sound {M : LTM} {sets env : Env} (hv : Valid sets env) {i i' : Nat}
    (hi : i < env.length) (hi' : i' < env.length) {b k : Nat} {c : SC}
    (h : mreach M sets k (c.subst (Item.cons i b)) (c.subst (Item.snoc i' b)) = true) :
    M.Reach (c.den (Env.upd env i (b :: ·))) (c.den (Env.upd env i' (· ++ [b]))) := by
  rw [den_cons hi, den_snoc hi']
  exact mreach_sound hv _ _ _ h

/-- Moving a word from one variable to another, one symbol per iteration. -/
theorem LTM.Reach.fold {M : LTM} {S : List Nat} (F : List Nat → List Nat → ZC)
    (h : ∀ u b v, b ∈ S → (∀ x ∈ u, x ∈ S) → (∀ x ∈ v, x ∈ S) →
      M.Reach (F u (b :: v)) (F (u ++ [b]) v)) :
    ∀ v u, (∀ x ∈ u, x ∈ S) → (∀ x ∈ v, x ∈ S) → M.Reach (F u v) (F (u ++ v) []) := by
  intro v
  induction v with
  | nil =>
    intro u _ _
    rw [List.append_nil]
    exact LTM.Reach.refl M _
  | cons b v ih =>
    intro u hu hv
    have hb : b ∈ S := hv b (by simp)
    have hv' : ∀ x ∈ v, x ∈ S := fun x hx => hv x (by simp [hx])
    refine (h u b v hb hu hv').trans ?_
    have hu' : ∀ x ∈ u ++ [b], x ∈ S := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hu x hx
      · rw [List.mem_singleton.mp hx]
        exact hb
    have := ih (u ++ [b]) hu' hv'
    rw [List.append_assoc] at this
    exact this

/-! ## Single steps, also from the beep state -/

/-- Runs of at least one step. -/
def LTM.Reach1 (M : LTM) (c c' : ZC) : Prop := ∃ n, M.zrun (n + 1) c = some c'

theorem LTM.Reach1.reach {M : LTM} {c c' : ZC} (h : M.Reach1 c c') : M.Reach c c' :=
  let ⟨n, hn⟩ := h
  ⟨n + 1, hn⟩

theorem LTM.Reach1.trans {M : LTM} {a b c : ZC} (h1 : M.Reach1 a b) (h2 : M.Reach b c) :
    M.Reach1 a c := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  refine ⟨n + m, ?_⟩
  rw [show n + m + 1 = (n + 1) + m by omega, LTM.zrun_add, hn]
  exact hm

theorem stepR_zstep {M : LTM} {env : Env} {q a : Nat} {l rest : List Item} {c' : SC}
    (h : stepR M q a l rest = some c') :
    M.zstep ⟨q, sapp (dL env l) blank, scons a (sapp (dR env rest) blank)⟩ = some (c'.den env) := by
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
      exact LTM.zstep_R ha
    · rw [ite_eq_right hd] at h'
      cases h'
      exact LTM.zstep_L ha hd

theorem stepL_zstep {M : LTM} {env : Env} {q a : Nat} {rest r : List Item} {c' : SC}
    (h : stepL M q a rest r = some c') :
    M.zstep ⟨q, sapp (dL env rest) blank, scons a (sapp (dR env r) blank)⟩ = some (c'.den env) := by
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
      exact LTM.zstep_R ha
    · rw [ite_eq_right hd] at h'
      cases h'
      exact LTM.zstep_L ha hd

def cstepR (M : LTM) (q : Nat) (l r : List Item) : Option SC :=
  match view r with
  | .cell a rest => stepR M q a l rest
  | .block _ _ _ => none

def cstepL (M : LTM) (q : Nat) (l r : List Item) : Option SC :=
  match view l with
  | .cell a rest => stepL M q a rest r
  | .block _ _ _ => none

/-- One concrete step (the head is on a concrete cell); taken also from the beep state. -/
def cstep (M : LTM) (c : SC) : Option SC :=
  bif c.dirL then cstepL M c.q c.l c.r else cstepR M c.q c.l c.r

theorem cstep_zstep {M : LTM} {env : Env} {c c' : SC} (h : cstep M c = some c') :
    M.zstep (c.den env) = some (c'.den env) := by
  obtain ⟨q, l, r, dl⟩ := c
  cases dl with
  | false =>
    have h0 : cstepR M q l r = some c' := h
    unfold cstepR at h0
    cases hw : view r with
    | cell a rest =>
      rw [hw] at h0
      have h2 : stepR M q a l rest = some c' := h0
      show M.zstep ⟨q, sapp (dL env l) blank, sapp (dR env r) blank⟩ = _
      rw [view_cellR hw]
      exact stepR_zstep h2
    | block i f rest =>
      rw [hw] at h0
      have h3 : (none : Option SC) = some c' := h0
      cases h3
  | true =>
    have h0 : cstepL M q l r = some c' := h
    unfold cstepL at h0
    cases hw : view l with
    | cell a rest =>
      rw [hw] at h0
      have h2 : stepL M q a rest r = some c' := h0
      show M.zstep ⟨q, stail (sapp (dL env l) blank),
        scons (sapp (dL env l) blank 0) (sapp (dR env r) blank)⟩ = _
      rw [view_cellL hw]
      exact stepL_zstep h2
    | block i f rest =>
      rw [hw] at h0
      have h3 : (none : Option SC) = some c' := h0
      cases h3

/-! ## Renaming variables and dropping empty ones -/

/-- Concatenation of the words `env[k]`, `k ∈ ks`. -/
def cat (env : Env) : List Nat → List Nat
  | [] => []
  | [k] => env.getD k []
  | k :: ks => env.getD k [] ++ cat env ks

theorem cat_cons (env : Env) (k : Nat) (ks : List Nat) :
    cat env (k :: ks) = env.getD k [] ++ cat env ks := by
  cases ks with
  | nil => exact (List.append_nil _).symm
  | cons k2 ks2 => rfl

/-- Variable `i` becomes the concatenation of the variables `ρ[i]`. -/
def Item.ren (ρ : List (List Nat)) : Item → List Item
  | .sym a => [.sym a]
  | .blk i f => (ρ.getD i []).map fun k => .blk k f

theorem dR_blks (env : Env) (f : Fn) :
    ∀ ks : List Nat, dR env (ks.map fun k => Item.blk k f) = (cat env ks).map f.app
  | [] => rfl
  | k :: ks => by
    rw [List.map_cons]
    show (env.getD k []).map f.app ++ dR env (ks.map fun k => Item.blk k f) = _
    rw [dR_blks env f ks, cat_cons, List.map_append]

theorem getD_map_cat (env : Env) :
    ∀ (ρ : List (List Nat)) (i : Nat), (ρ.map (cat env)).getD i [] = cat env (ρ.getD i [])
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | _ :: ρ, i + 1 => getD_map_cat env ρ i

theorem item_ren (env : Env) (ρ : List (List Nat)) (it : Item) :
    it.den (ρ.map (cat env)) = dR env (it.ren ρ) := by
  cases it with
  | sym a => rfl
  | blk i f =>
    show ((ρ.map (cat env)).getD i []).map f.app = dR env ((ρ.getD i []).map fun k => Item.blk k f)
    rw [getD_map_cat, dR_blks]

theorem den_ren (env : Env) (ρ : List (List Nat)) (c : SC) :
    c.den (ρ.map (cat env)) = (c.subst (Item.ren ρ)).den env :=
  den_subst (item_ren env ρ) c

def memB : List Nat → Nat → Bool
  | [], _ => false
  | k :: E, i => decide (i = k) || memB E i

/-- The variables in `E` are empty. -/
def AllEmpty (env : Env) : List Nat → Prop
  | [] => True
  | i :: E => env.getD i [] = [] ∧ AllEmpty env E

theorem AllEmpty.get {env : Env} : ∀ (E : List Nat) (i : Nat), AllEmpty env E →
    memB E i = true → env.getD i [] = []
  | [], _, _, h => by cases h
  | k :: E, i, ⟨h1, h2⟩, h => by
    by_cases hik : i = k
    · subst hik
      exact h1
    · have h0 : (decide (i = k) || memB E i) = true := h
      rw [decide_eq_false hik, Bool.false_or] at h0
      exact AllEmpty.get E i h2 h0

def dropE (E : List Nat) : List Item → List Item
  | [] => []
  | .sym a :: r => .sym a :: dropE E r
  | .blk i f :: r => if memB E i then dropE E r else .blk i f :: dropE E r

theorem dR_dropE {env : Env} {E : List Nat} (hE : AllEmpty env E) :
    ∀ r, dR env (dropE E r) = dR env r
  | [] => rfl
  | .sym a :: r => by
    show [a] ++ dR env (dropE E r) = [a] ++ dR env r
    rw [dR_dropE hE r]
  | .blk i f :: r => by
    show dR env (if memB E i then dropE E r else .blk i f :: dropE E r) =
      (env.getD i []).map f.app ++ dR env r
    by_cases hm : memB E i = true
    · rw [ite_eq_left hm, AllEmpty.get E i hE hm, dR_dropE hE r] <;> rfl
    · rw [ite_eq_right hm]
      show (env.getD i []).map f.app ++ dR env (dropE E r) = _
      rw [dR_dropE hE r]

theorem dL_dropE {env : Env} {E : List Nat} (hE : AllEmpty env E) :
    ∀ l, dL env (dropE E l) = dL env l
  | [] => rfl
  | .sym a :: l => by
    show [a].reverse ++ dL env (dropE E l) = [a].reverse ++ dL env l
    rw [dL_dropE hE l]
  | .blk i f :: l => by
    show dL env (if memB E i then dropE E l else .blk i f :: dropE E l) =
      ((env.getD i []).map f.app).reverse ++ dL env l
    by_cases hm : memB E i = true
    · rw [ite_eq_left hm, AllEmpty.get E i hE hm, dL_dropE hE l] <;> rfl
    · rw [ite_eq_right hm]
      show ((env.getD i []).map f.app).reverse ++ dL env (dropE E l) = _
      rw [dL_dropE hE l]

def trimAux : Item → List Item → List Item
  | .sym 0, [] => []
  | .blk _ (.const 0), [] => []
  | it, r => it :: r

/-- Drop blank cells at the far end. -/
def trim : List Item → List Item
  | [] => []
  | it :: r => trimAux it (trim r)

theorem sapp_zeros (s : Strm) (h : s = blank) : ∀ w : List Nat, sapp (w.map (Fn.const 0).app) s = blank
  | [] => h
  | _ :: w => by
    show scons 0 (sapp (w.map (Fn.const 0).app) s) = blank
    rw [sapp_zeros s h w, scons_blank]

theorem trimAux_dR (env : Env) (it : Item) (r : List Item) :
    sapp (dR env (trimAux it r)) blank = sapp (dR env (it :: r)) blank := by
  match it, r with
  | .sym 0, [] => exact scons_blank.symm
  | .blk i (.const 0), [] =>
    show blank = sapp ((env.getD i []).map (Fn.const 0).app ++ []) blank
    rw [List.append_nil, sapp_zeros blank rfl]
  | .sym 0, _ :: _ => rfl
  | .sym (_ + 1), _ => rfl
  | .blk _ .id, _ => rfl
  | .blk _ (.const (_ + 1)), _ => rfl
  | .blk _ (.const 0), _ :: _ => rfl

theorem trimAux_dL (env : Env) (it : Item) (l : List Item) :
    sapp (dL env (trimAux it l)) blank = sapp (dL env (it :: l)) blank := by
  match it, l with
  | .sym 0, [] => exact scons_blank.symm
  | .blk i (.const 0), [] =>
    show blank = sapp (((env.getD i []).map (Fn.const 0).app).reverse ++ []) blank
    rw [List.append_nil, const_rev, sapp_zeros blank rfl]
  | .sym 0, _ :: _ => rfl
  | .sym (_ + 1), _ => rfl
  | .blk _ .id, _ => rfl
  | .blk _ (.const (_ + 1)), _ => rfl
  | .blk _ (.const 0), _ :: _ => rfl

theorem trim_dR (env : Env) : ∀ r, sapp (dR env (trim r)) blank = sapp (dR env r) blank
  | [] => rfl
  | it :: r => by
    show sapp (dR env (trimAux it (trim r))) blank = _
    rw [trimAux_dR]
    show sapp (it.den env ++ dR env (trim r)) blank = sapp (it.den env ++ dR env r) blank
    rw [sapp_append, sapp_append, trim_dR env r]

theorem trim_dL (env : Env) : ∀ l, sapp (dL env (trim l)) blank = sapp (dL env l) blank
  | [] => rfl
  | it :: l => by
    show sapp (dL env (trimAux it (trim l))) blank = _
    rw [trimAux_dL]
    show sapp ((it.den env).reverse ++ dL env (trim l)) blank =
      sapp ((it.den env).reverse ++ dL env l) blank
    rw [sapp_append, sapp_append, trim_dL env l]

/-- Move a constant block past the equal symbols after it. -/
def ins : Item → List Item → List Item
  | .blk i (.const c), .sym a :: rest =>
    if a = c then .sym a :: ins (.blk i (.const c)) rest else .blk i (.const c) :: .sym a :: rest
  | it, r => it :: r

/-- In every run of one constant, symbols before blocks. -/
def canon : List Item → List Item
  | [] => []
  | it :: r => ins it (canon r)

theorem ins_dR (env : Env) : ∀ (it : Item) (r : List Item), dR env (ins it r) = dR env (it :: r)
  | .blk i (.const c), .sym a :: rest => by
    by_cases h : a = c
    · subst h
      show dR env (if a = a then .sym a :: ins (.blk i (.const a)) rest
        else .blk i (.const a) :: .sym a :: rest) = _
      rw [ite_eq_left rfl]
      show [a] ++ dR env (ins (.blk i (.const a)) rest) = _
      rw [ins_dR env (.blk i (.const a)) rest]
      show [a] ++ ((env.getD i []).map (Fn.const a).app ++ dR env rest) =
        (env.getD i []).map (Fn.const a).app ++ ([a] ++ dR env rest)
      rw [← List.append_assoc ((env.getD i []).map (Fn.const a).app), const_comm]
      rfl
    · show dR env (if a = c then .sym a :: ins (.blk i (.const c)) rest
        else .blk i (.const c) :: .sym a :: rest) = _
      rw [ite_eq_right h]
  | .blk _ .id, [] => rfl
  | .blk _ .id, .sym _ :: _ => rfl
  | .blk _ .id, .blk _ _ :: _ => rfl
  | .blk _ (.const _), [] => rfl
  | .blk _ (.const _), .blk _ _ :: _ => rfl
  | .sym _, [] => rfl
  | .sym _, .sym _ :: _ => rfl
  | .sym _, .blk _ _ :: _ => rfl

theorem ins_dL (env : Env) : ∀ (it : Item) (l : List Item), dL env (ins it l) = dL env (it :: l)
  | .blk i (.const c), .sym a :: rest => by
    by_cases h : a = c
    · subst h
      show dL env (if a = a then .sym a :: ins (.blk i (.const a)) rest
        else .blk i (.const a) :: .sym a :: rest) = _
      rw [ite_eq_left rfl]
      show [a].reverse ++ dL env (ins (.blk i (.const a)) rest) = _
      rw [ins_dL env (.blk i (.const a)) rest]
      show [a] ++ (((env.getD i []).map (Fn.const a).app).reverse ++ dL env rest) =
        ((env.getD i []).map (Fn.const a).app).reverse ++ ([a] ++ dL env rest)
      rw [const_rev, ← List.append_assoc ((env.getD i []).map (Fn.const a).app), const_comm]
      rfl
    · show dL env (if a = c then .sym a :: ins (.blk i (.const c)) rest
        else .blk i (.const c) :: .sym a :: rest) = _
      rw [ite_eq_right h]
  | .blk _ .id, [] => rfl
  | .blk _ .id, .sym _ :: _ => rfl
  | .blk _ .id, .blk _ _ :: _ => rfl
  | .blk _ (.const _), [] => rfl
  | .blk _ (.const _), .blk _ _ :: _ => rfl
  | .sym _, [] => rfl
  | .sym _, .sym _ :: _ => rfl
  | .sym _, .blk _ _ :: _ => rfl

theorem canon_dR (env : Env) : ∀ r, dR env (canon r) = dR env r
  | [] => rfl
  | it :: r => by
    show dR env (ins it (canon r)) = _
    rw [ins_dR]
    show it.den env ++ dR env (canon r) = it.den env ++ dR env r
    rw [canon_dR env r]

theorem canon_dL (env : Env) : ∀ l, dL env (canon l) = dL env l
  | [] => rfl
  | it :: l => by
    show dL env (ins it (canon l)) = _
    rw [ins_dL]
    show (it.den env).reverse ++ dL env (canon l) = (it.den env).reverse ++ dL env l
    rw [canon_dL env l]

/-- Drop the variables of `E`, order constant runs, drop blanks at both far ends. -/
def SC.norm (E : List Nat) (c : SC) : SC :=
  ⟨c.q, trim (canon (dropE E c.l)), trim (canon (dropE E c.r)), c.dirL⟩

theorem den_norm {env : Env} {E : List Nat} (hE : AllEmpty env E) (c : SC) :
    (c.norm E).den env = c.den env := by
  obtain ⟨q, l, r, dl⟩ := c
  cases dl with
  | false =>
    show (⟨q, sapp (dL env (trim (canon (dropE E l)))) blank,
        sapp (dR env (trim (canon (dropE E r)))) blank⟩ : ZC) =
      ⟨q, sapp (dL env l) blank, sapp (dR env r) blank⟩
    rw [trim_dL, canon_dL, dL_dropE hE, trim_dR, canon_dR, dR_dropE hE]
  | true =>
    show (⟨q, stail (sapp (dL env (trim (canon (dropE E l)))) blank),
        scons (sapp (dL env (trim (canon (dropE E l)))) blank 0)
          (sapp (dR env (trim (canon (dropE E r)))) blank)⟩ : ZC) =
      ⟨q, stail (sapp (dL env l) blank), scons (sapp (dL env l) blank 0) (sapp (dR env r) blank)⟩
    rw [trim_dL, canon_dL, dL_dropE hE, trim_dR, canon_dR, dR_dropE hE]

/-- `mreach`, comparing configurations with the variables of `E` dropped. -/
def mreachN (M : LTM) (sets : Env) (E : List Nat) : Nat → SC → SC → Bool
  | 0, c, t => decide (c.norm E = t.norm E)
  | k + 1, c, t =>
    decide (c.norm E = t.norm E) || ((mstep M sets c).map fun c' => mreachN M sets E k c' t).getD false

/-- The same with a first concrete step. -/
def mreach1N (M : LTM) (sets : Env) (E : List Nat) : Nat → SC → SC → Bool
  | 0, _, _ => false
  | k + 1, c, t =>
    if c.q = M.beep then false else ((cstep M c).map fun c' => mreachN M sets E k c' t).getD false

theorem mreachN_sound {M : LTM} {sets env : Env} {E : List Nat} (hv : Valid sets env)
    (hE : AllEmpty env E) :
    ∀ (k : Nat) (c t : SC), mreachN M sets E k c t = true → M.Reach (c.den env) (t.den env) := by
  intro k
  induction k with
  | zero =>
    intro c t h
    have e : c.norm E = t.norm E := of_decide_eq_true h
    rw [← den_norm hE c, e, den_norm hE t]
    exact LTM.Reach.refl M _
  | succ k ih =>
    intro c t h
    by_cases hct : c.norm E = t.norm E
    · rw [← den_norm hE c, hct, den_norm hE t]
      exact LTM.Reach.refl M _
    · have h0 : (decide (c.norm E = t.norm E) ||
          ((mstep M sets c).map fun c' => mreachN M sets E k c' t).getD false) = true := h
      rw [decide_eq_false hct, Bool.false_or] at h0
      cases hm : mstep M sets c with
      | none =>
        rw [hm] at h0
        have h1 : false = true := h0
        cases h1
      | some c' =>
        rw [hm] at h0
        exact (mstep_sound hv hm).trans (ih c' t h0)

theorem mreach1N_sound {M : LTM} {sets env : Env} {E : List Nat} (hv : Valid sets env)
    (hE : AllEmpty env E) :
    ∀ (k : Nat) (c t : SC), mreach1N M sets E k c t = true → M.Reach1 (c.den env) (t.den env)
  | 0, _, _, h => by cases h
  | k + 1, c, t, h => by
    have h0 : (if c.q = M.beep then false
        else ((cstep M c).map fun c' => mreachN M sets E k c' t).getD false) = true := h
    by_cases hq : c.q = M.beep
    · rw [ite_eq_left hq] at h0
      cases h0
    · rw [ite_eq_right hq] at h0
      cases hm : cstep M c with
      | none =>
        rw [hm] at h0
        have h1 : false = true := h0
        cases h1
      | some c' =>
        rw [hm] at h0
        obtain ⟨n, hn⟩ := mreachN_sound hv hE k c' t h0
        have hq' : (c.den env).q ≠ M.beep := by rw [SC.den_q]; exact hq
        exact ⟨n, by rw [LTM.zrun_succ hq' (cstep_zstep hm)]; exact hn⟩

/-- A segment check: from `c` (variables `env`, those of `E` empty) to `t` (variables
`ρ` over `env`). -/
theorem check {M : LTM} {sets env : Env} {E : List Nat} {ρ : List (List Nat)} {k : Nat}
    {c t : SC} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k (c.norm E) (t.subst (Item.ren ρ)) = true) :
    M.Reach (c.den env) (t.den (ρ.map (cat env))) := by
  rw [den_ren, ← den_norm hE c]
  exact mreachN_sound hv hE k _ _ h

theorem check1 {M : LTM} {sets env : Env} {E : List Nat} {ρ : List (List Nat)} {k : Nat}
    {c t : SC} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreach1N M sets E k (c.norm E) (t.subst (Item.ren ρ)) = true) :
    M.Reach1 (c.den env) (t.den (ρ.map (cat env))) := by
  rw [den_ren, ← den_norm hE c]
  exact mreach1N_sound hv hE k _ _ h

/-- A loop body: from `c` with `env[i] = b :: _` to `c` with `env[i'] = _ ++ [b]`. -/
theorem body {M : LTM} {sets env : Env} {E : List Nat} (hv : Valid sets env) (hE : AllEmpty env E)
    {i i' : Nat} (hi : i < env.length) (hi' : i' < env.length) {b k : Nat} {c : SC}
    (h : mreachN M sets E k (c.subst (Item.cons i b)) (c.subst (Item.snoc i' b)) = true) :
    M.Reach (c.den (Env.upd env i (b :: ·))) (c.den (Env.upd env i' (· ++ [b]))) := by
  rw [den_cons hi, den_snoc hi']
  exact mreachN_sound hv hE _ _ _ h

/-! ## Instantiating variables by item lists -/

def Fn.comp : Fn → Fn → Fn
  | .id, f => f
  | .const c, _ => .const c

theorem Fn.comp_fun (g f : Fn) : (g.comp f).app = g.app ∘ f.app := by
  funext a
  cases g <;> rfl

def Item.mapF (g : Fn) : Item → Item
  | .sym a => .sym (g.app a)
  | .blk k f => .blk k (g.comp f)

theorem dR_mapF (env : Env) (g : Fn) :
    ∀ its : List Item, dR env (its.map (Item.mapF g)) = (dR env its).map g.app
  | [] => rfl
  | .sym a :: r => by
    show [g.app a] ++ dR env (r.map (Item.mapF g)) = ([a] ++ dR env r).map g.app
    rw [dR_mapF env g r] <;> rfl
  | .blk k f :: r => by
    show (env.getD k []).map (g.comp f).app ++ dR env (r.map (Item.mapF g)) =
      ((env.getD k []).map f.app ++ dR env r).map g.app
    rw [dR_mapF env g r, List.map_append, List.map_map, Fn.comp_fun]

theorem map_id_app : ∀ w : List Nat, w.map Fn.id.app = w
  | [] => rfl
  | a :: w => by
    show a :: w.map Fn.id.app = a :: w
    rw [map_id_app w]

/-- The word of one item, with `blk k .id` read as `env[k]` itself. -/
def den1 (env : Env) : Item → List Nat
  | .sym a => [a]
  | .blk k .id => env.getD k []
  | .blk k (.const c) => (env.getD k []).map (Fn.const c).app

/-- The word of a list of items, in a form that reduces well on literals. -/
def dW (env : Env) : List Item → List Nat
  | [] => []
  | [it] => den1 env it
  | it :: r => den1 env it ++ dW env r

theorem den1_eq (env : Env) (it : Item) : den1 env it = it.den env := by
  cases it with
  | sym a => rfl
  | blk k f =>
    cases f with
    | id => exact (map_id_app _).symm
    | const c => rfl

theorem dW_eq (env : Env) : ∀ its : List Item, dW env its = dR env its
  | [] => rfl
  | [it] => by
    show den1 env it = it.den env ++ []
    rw [den1_eq, List.append_nil]
  | it :: it2 :: r => by
    show den1 env it ++ dW env (it2 :: r) = it.den env ++ dR env (it2 :: r)
    rw [den1_eq, dW_eq env (it2 :: r)]

theorem getD_map_nil {α β : Type} (g : List α → List β) (hg : g [] = []) :
    ∀ (σ : List (List α)) (i : Nat), (σ.map g).getD i [] = g (σ.getD i [])
  | [], i => by cases i <;> exact hg.symm
  | _ :: _, 0 => rfl
  | _ :: σ, i + 1 => getD_map_nil g hg σ i

/-- Variable `i` becomes the items `σ[i]`. -/
def Item.inst (σ : List (List Item)) : Item → List Item
  | .sym a => [.sym a]
  | .blk i f => (σ.getD i []).map (Item.mapF f)

theorem item_inst (env : Env) (σ : List (List Item)) (it : Item) :
    it.den (σ.map (dW env)) = dR env (it.inst σ) := by
  cases it with
  | sym a => rfl
  | blk i f =>
    show ((σ.map (dW env)).getD i []).map f.app = dR env ((σ.getD i []).map (Item.mapF f))
    rw [getD_map_nil (dW env) rfl, dW_eq, dR_mapF]

theorem den_inst (env : Env) (σ : List (List Item)) (c : SC) :
    c.den (σ.map (dW env)) = (c.subst (Item.inst σ)).den env :=
  den_subst (item_inst env σ) c

theorem den_of_norm {env : Env} {E : List Nat} (hE : AllEmpty env E) {c c' : SC}
    (h : c.norm E = c'.norm E) : c.den env = c'.den env := by
  rw [← den_norm hE c, h, den_norm hE c']

/-- A segment check: from `c` (variables `env`, those of `E` empty) to `t` with its
variables instantiated by `σ`. -/
theorem checkI {M : LTM} {sets env : Env} {E : List Nat} {σ : List (List Item)} {k : Nat}
    {c t : SC} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k (c.norm E) (t.subst (Item.inst σ)) = true) :
    M.Reach (c.den env) (t.den (σ.map (dW env))) := by
  rw [den_inst, ← den_norm hE c]
  exact mreachN_sound hv hE k _ _ h

theorem check1I {M : LTM} {sets env : Env} {E : List Nat} {σ : List (List Item)} {k : Nat}
    {c t : SC} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreach1N M sets E k (c.norm E) (t.subst (Item.inst σ)) = true) :
    M.Reach1 (c.den env) (t.den (σ.map (dW env))) := by
  rw [den_inst, ← den_norm hE c]
  exact mreach1N_sound hv hE k _ _ h

/-- Using a symbolic lemma `A ⇝ B` at an instance: `c` matches `A` under `σ`, and the
run continues from `B` under `σ`. -/
theorem LTM.Reach.inst {M : LTM} {env : Env} {E : List Nat} {σ : List (List Item)}
    {A B c : SC} (hAB : M.Reach (A.den (σ.map (dW env))) (B.den (σ.map (dW env))))
    (hE : AllEmpty env E) (h : c.norm E = (A.subst (Item.inst σ)).norm E) :
    M.Reach (c.den env) ((B.subst (Item.inst σ)).den env) := by
  rw [den_of_norm hE h, ← den_inst, ← den_inst]
  exact hAB

/-! ## Plain checks, and configurations given by two words -/

/-- A segment check with the same variables at both ends. -/
theorem checkE {M : LTM} {sets env : Env} {E : List Nat} {k : Nat} {c t : SC}
    (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k (c.norm E) t = true) : M.Reach (c.den env) (t.den env) := by
  rw [← den_norm hE c]
  exact mreachN_sound hv hE k _ _ h

/-- State `q`, head on the last cell of `A`, then `R`. -/
def atL (q : Nat) : SC := ⟨q, [.blk 0 .id], [.blk 1 .id], true⟩

def hd (q : Nat) (A R : List Nat) : ZC := (atL q).den [A, R]

/-- State `q`, `A`, head on the first cell of `R`. -/
def atR (q : Nat) : SC := ⟨q, [.blk 0 .id], [.blk 1 .id], false⟩

def hdR (q : Nat) (A R : List Nat) : ZC := (atR q).den [A, R]

theorem dW_blk0 (A R : List Nat) : dL [A, R] [.blk 0 .id] = A.reverse := by
  show (A.map Fn.id.app).reverse ++ [] = A.reverse
  rw [map_id_app, List.append_nil]

theorem dW_blk1 (A R : List Nat) : dR [A, R] [.blk 1 .id] = R := by
  show R.map Fn.id.app ++ [] = R
  rw [map_id_app, List.append_nil]

/-- A symbolic configuration (left items in tape order) as `hd`. -/
theorem den_tape {q : Nat} {env : Env} {ls rs : List Item} {A R : List Nat}
    (hl : dR env ls = A) (hr : dR env rs = R) :
    (⟨q, ls.reverse, rs, true⟩ : SC).den env = hd q A R := by
  show (⟨q, stail (sapp (dL env ls.reverse) blank),
      scons (sapp (dL env ls.reverse) blank 0) (sapp (dR env rs) blank)⟩ : ZC) =
    ⟨q, stail (sapp (dL [A, R] [.blk 0 .id]) blank),
      scons (sapp (dL [A, R] [.blk 0 .id]) blank 0) (sapp (dR [A, R] [.blk 1 .id]) blank)⟩
  rw [dL_reverse, hl, hr, dW_blk0, dW_blk1]

theorem den_tapeR {q : Nat} {env : Env} {ls rs : List Item} {A R : List Nat}
    (hl : dR env ls = A) (hr : dR env rs = R) :
    (⟨q, ls.reverse, rs, false⟩ : SC).den env = hdR q A R := by
  show (⟨q, sapp (dL env ls.reverse) blank, sapp (dR env rs) blank⟩ : ZC) =
    ⟨q, sapp (dL [A, R] [.blk 0 .id]) blank, sapp (dR [A, R] [.blk 1 .id]) blank⟩
  rw [dL_reverse, hl, hr, dW_blk0, dW_blk1]

/-- Segment checks between configurations given by words (`hd`: head left of the
boundary, `hdR`: right of it). -/
theorem checkTT {M : LTM} {sets env : Env} {E : List Nat} {k q q' : Nat}
    {ls rs ls' rs' : List Item} {A R A' R' : List Nat} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k ((⟨q, ls.reverse, rs, true⟩ : SC).norm E) ⟨q', ls'.reverse, rs', true⟩ = true)
    (hl : dR env ls = A) (hr : dR env rs = R) (hl' : dR env ls' = A') (hr' : dR env rs' = R') :
    M.Reach (hd q A R) (hd q' A' R') := by
  have := checkE hv hE h
  rw [den_tape hl hr, den_tape hl' hr'] at this
  exact this

theorem checkTF {M : LTM} {sets env : Env} {E : List Nat} {k q q' : Nat}
    {ls rs ls' rs' : List Item} {A R A' R' : List Nat} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k ((⟨q, ls.reverse, rs, true⟩ : SC).norm E) ⟨q', ls'.reverse, rs', false⟩ = true)
    (hl : dR env ls = A) (hr : dR env rs = R) (hl' : dR env ls' = A') (hr' : dR env rs' = R') :
    M.Reach (hd q A R) (hdR q' A' R') := by
  have := checkE hv hE h
  rw [den_tape hl hr, den_tapeR hl' hr'] at this
  exact this

theorem checkFT {M : LTM} {sets env : Env} {E : List Nat} {k q q' : Nat}
    {ls rs ls' rs' : List Item} {A R A' R' : List Nat} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k ((⟨q, ls.reverse, rs, false⟩ : SC).norm E) ⟨q', ls'.reverse, rs', true⟩ = true)
    (hl : dR env ls = A) (hr : dR env rs = R) (hl' : dR env ls' = A') (hr' : dR env rs' = R') :
    M.Reach (hdR q A R) (hd q' A' R') := by
  have := checkE hv hE h
  rw [den_tapeR hl hr, den_tape hl' hr'] at this
  exact this

theorem checkFF {M : LTM} {sets env : Env} {E : List Nat} {k q q' : Nat}
    {ls rs ls' rs' : List Item} {A R A' R' : List Nat} (hv : Valid sets env) (hE : AllEmpty env E)
    (h : mreachN M sets E k ((⟨q, ls.reverse, rs, false⟩ : SC).norm E) ⟨q', ls'.reverse, rs', false⟩ = true)
    (hl : dR env ls = A) (hr : dR env rs = R) (hl' : dR env ls' = A') (hr' : dR env rs' = R') :
    M.Reach (hdR q A R) (hdR q' A' R') := by
  have := checkE hv hE h
  rw [den_tapeR hl hr, den_tapeR hl' hr'] at this
  exact this

theorem map_const_rep (u a c : Nat) : (List.replicate u a).map (Fn.const c).app = List.replicate u c := by
  rw [List.map_replicate]
  rfl

theorem rep_cons_comm {α : Type} (a : α) (X : List α) :
    ∀ u : Nat, List.replicate u a ++ a :: X = a :: (List.replicate u a ++ X)
  | 0 => rfl
  | u + 1 => by
    show a :: (List.replicate u a ++ a :: X) = a :: (a :: List.replicate u a ++ X)
    exact congrArg (a :: ·) (rep_cons_comm a X u)

end ZP
