module

public import ZP.LTM

@[expose] public section

/-!
# Logical machines on stream tapes

For the segment lemmas of layer N3 a configuration is a state and two infinite
streams: `R` starts at the scanned cell and runs right, `L` starts at the cell left of
it and runs left. There are no absolute positions and no tape ends, and moving onto
`scons a s` reads `a` by definition.

`zrun_sound` transfers a stream run to `LTM.conf`. `zrun` refuses to take a step from
the beep state, so `zrun n z = some z'` also says that none of the first `n`
configurations is in the beep state.
-/

namespace ZP

abbrev Strm := Nat → Nat

def scons (a : Nat) (s : Strm) : Strm := fun i =>
  match i with
  | 0 => a
  | i + 1 => s i

def stail (s : Strm) : Strm := fun i => s (i + 1)

def sapp : List Nat → Strm → Strm
  | [], s => s
  | a :: w, s => scons a (sapp w s)

def blank : Strm := fun _ => 0

theorem sapp_append (u v : List Nat) (s : Strm) : sapp (u ++ v) s = sapp u (sapp v s) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    show scons a (sapp (u ++ v) s) = scons a (sapp u (sapp v s))
    rw [ih]

theorem scons_blank : scons 0 blank = blank := by
  funext i
  cases i <;> rfl

/-- Configuration: state, the stream left of the head, the stream from the head on. -/
structure ZC where
  q : Nat
  L : Strm
  R : Strm

/-- What state `q` does on symbol `a`: written symbol, direction (1 = right), next state. -/
def LTM.act (M : LTM) (q a : Nat) : Option (Nat × Nat × Nat) :=
  match M.table[q]? with
  | none => none
  | some row =>
    let code := row.getD a 0
    if code = 0 then none else some ((code - 1) % 4, (code - 1) / 4 % 2, (code - 1) / 8)

def LTM.zstep (M : LTM) (c : ZC) : Option ZC :=
  match M.act c.q (c.R 0) with
  | none => none
  | some (w, r, q') =>
    if r = 1 then some ⟨q', scons w c.L, stail c.R⟩
    else some ⟨q', stail c.L, scons (c.L 0) (scons w (stail c.R))⟩

/-- `n` steps, none of them taken from the beep state. -/
def LTM.zrun (M : LTM) : Nat → ZC → Option ZC
  | 0, c => some c
  | n + 1, c => if c.q = M.beep then none else (M.zstep c).bind (M.zrun n)

theorem LTM.zrun_add (M : LTM) (a b : Nat) (c : ZC) :
    M.zrun (a + b) c = (M.zrun a c).bind (M.zrun b) := by
  induction a generalizing c with
  | zero => rw [Nat.zero_add] <;> rfl
  | succ a ih =>
    rw [Nat.add_right_comm]
    show (if c.q = M.beep then none else (M.zstep c).bind (M.zrun (a + b))) =
      (if c.q = M.beep then none else (M.zstep c).bind (M.zrun a)).bind (M.zrun b)
    by_cases hb : c.q = M.beep
    · rw [ite_eq_left hb, ite_eq_left hb] <;> rfl
    · rw [ite_eq_right hb, ite_eq_right hb]
      cases M.zstep c with
      | none => rfl
      | some d => exact ih d

theorem LTM.zrun_one {M : LTM} {c c' : ZC} (hb : c.q ≠ M.beep) (h : M.zstep c = some c') :
    M.zrun 1 c = some c' := by
  show (if c.q = M.beep then none else (M.zstep c).bind (M.zrun 0)) = some c'
  rw [ite_eq_right hb, h] <;> rfl

/-! ## Link with `LTM.conf` -/

/-- `k` steps of the `Int`-tape semantics from `c`. -/
def LTM.lrun (M : LTM) : Nat → LConf → Option LConf
  | 0, c => some c
  | k + 1, c => (M.step c).bind (M.lrun k)

theorem LTM.lrun_succ_last (M : LTM) (k : Nat) (c : LConf) :
    M.lrun (k + 1) c = (M.lrun k c).bind M.step := by
  induction k generalizing c with
  | zero =>
    show (M.step c).bind (M.lrun 0) = M.step c
    cases M.step c <;> rfl
  | succ k ih =>
    show (M.step c).bind (M.lrun (k + 1)) = ((M.step c).bind (M.lrun k)).bind M.step
    cases M.step c with
    | none => rfl
    | some d => exact ih d

theorem LTM.conf_add (M : LTM) (a b : Nat) : M.conf (a + b) = (M.conf a).bind (M.lrun b) := by
  induction b with
  | zero =>
    show M.conf a = (M.conf a).bind (M.lrun 0)
    cases M.conf a <;> rfl
  | succ b ih =>
    show (M.conf (a + b)).bind M.step = (M.conf a).bind (M.lrun (b + 1))
    rw [ih]
    cases M.conf a with
    | none => rfl
    | some c => exact (LTM.lrun_succ_last M b c).symm

theorem LTM.step_eq (M : LTM) (c : LConf) :
    M.step c = (M.act c.q (c.tape c.head)).map (fun a =>
      ({ q := a.2.2, tape := fun i => if i = c.head then a.1 else c.tape i,
         head := if a.2.1 = 1 then c.head + 1 else c.head - 1 } : LConf)) := by
  unfold LTM.step LTM.act
  cases M.table[c.q]? with
  | none => rfl
  | some row =>
    dsimp only
    by_cases hc : row.getD (c.tape c.head) 0 = 0
    · rw [ite_eq_left hc, ite_eq_left hc] <;> rfl
    · rw [ite_eq_right hc, ite_eq_right hc] <;> rfl

/-- The `Int` tape of `c` reads `z.R` from the head rightwards and `z.L` leftwards. -/
structure ZRel (c : LConf) (z : ZC) : Prop where
  q : c.q = z.q
  R : ∀ i : Nat, c.tape (c.head + (i : Int)) = z.R i
  L : ∀ i : Nat, c.tape (c.head - 1 - (i : Int)) = z.L i

theorem zstep_sound {M : LTM} {c : LConf} {z z' : ZC} (h : ZRel c z)
    (hz : M.zstep z = some z') : ∃ c', M.step c = some c' ∧ ZRel c' z' := by
  obtain ⟨hq, hR, hL⟩ := h
  have h0 : c.tape c.head = z.R 0 := by
    have := hR 0
    rw [show c.head + ((0 : Nat) : Int) = c.head by omega] at this
    exact this
  rw [LTM.step_eq, hq, h0]
  unfold LTM.zstep at hz
  cases ha : M.act z.q (z.R 0) with
  | none =>
    rw [ha] at hz
    have h' : (none : Option ZC) = some z' := hz
    cases h'
  | some a =>
    obtain ⟨w, r, q'⟩ := a
    rw [ha] at hz
    have hz' : (if r = 1 then some (⟨q', scons w z.L, stail z.R⟩ : ZC)
        else some ⟨q', stail z.L, scons (z.L 0) (scons w (stail z.R))⟩) = some z' := hz
    refine ⟨_, rfl, ?_⟩
    by_cases hr : r = 1
    · rw [ite_eq_left hr] at hz'
      cases hz'
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        show (if (if r = 1 then c.head + 1 else c.head - 1) + (i : Int) = c.head then w
          else c.tape ((if r = 1 then c.head + 1 else c.head - 1) + (i : Int))) = z.R (i + 1)
        rw [ite_eq_left hr, ite_eq_right (by omega),
          show c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
        exact hR (i + 1)
      · intro i
        cases i with
        | zero =>
          show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - ((0 : Nat) : Int) = c.head
            then w else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 -
              ((0 : Nat) : Int))) = w
          rw [ite_eq_left hr, ite_eq_left (by omega)]
        | succ k =>
          show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - ((k + 1 : Nat) : Int) =
            c.head then w else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 -
              ((k + 1 : Nat) : Int))) = z.L k
          rw [ite_eq_left hr, ite_eq_right (by omega),
            show c.head + 1 - 1 - ((k + 1 : Nat) : Int) = c.head - 1 - (k : Int) by omega]
          exact hL k
    · rw [ite_eq_right hr] at hz'
      cases hz'
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        rcases i with _ | _ | i
        · show (if (if r = 1 then c.head + 1 else c.head - 1) + ((0 : Nat) : Int) = c.head
            then w else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((0 : Nat) : Int))) = z.L 0
          rw [ite_eq_right hr, ite_eq_right (by omega),
            show c.head - 1 + ((0 : Nat) : Int) = c.head - 1 - ((0 : Nat) : Int) by omega]
          exact hL 0
        · show (if (if r = 1 then c.head + 1 else c.head - 1) + ((0 + 1 : Nat) : Int) = c.head
            then w else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((0 + 1 : Nat) : Int))) = w
          rw [ite_eq_right hr, ite_eq_left (by omega)]
        · show (if (if r = 1 then c.head + 1 else c.head - 1) + ((i + 1 + 1 : Nat) : Int) =
            c.head then w else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((i + 1 + 1 : Nat) : Int))) = z.R (i + 1)
          rw [ite_eq_right hr, ite_eq_right (by omega),
            show c.head - 1 + ((i + 1 + 1 : Nat) : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
          exact hR (i + 1)
      · intro i
        show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - (i : Int) = c.head then w
          else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 - (i : Int))) = z.L (i + 1)
        rw [ite_eq_right hr, ite_eq_right (by omega),
          show c.head - 1 - 1 - (i : Int) = c.head - 1 - ((i + 1 : Nat) : Int) by omega]
        exact hL (i + 1)

theorem zrun_sound (M : LTM) : ∀ (n : Nat) (c : LConf) (z z' : ZC), ZRel c z →
    M.zrun n z = some z' →
      (∃ c', M.lrun n c = some c' ∧ ZRel c' z') ∧
      ∀ j, j < n → ∃ d, M.lrun j c = some d ∧ d.q ≠ M.beep := by
  intro n
  induction n with
  | zero =>
    intro c z z' h hz
    have h' : some z = some z' := hz
    cases h'
    exact ⟨⟨c, rfl, h⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    intro c z z' h hz
    have hz1 : (if z.q = M.beep then none else (M.zstep z).bind (M.zrun n)) = some z' := hz
    by_cases hb : z.q = M.beep
    · rw [ite_eq_left hb] at hz1
      cases hz1
    · rw [ite_eq_right hb] at hz1
      cases hs : M.zstep z with
      | none =>
        rw [hs] at hz1
        have h' : (none : Option ZC) = some z' := hz1
        cases h'
      | some z1 =>
        rw [hs] at hz1
        have hz2 : M.zrun n z1 = some z' := hz1
        obtain ⟨c1, hc1, h1⟩ := zstep_sound h hs
        obtain ⟨⟨c', hc', h'⟩, hmid⟩ := ih c1 z1 z' h1 hz2
        refine ⟨⟨c', ?_, h'⟩, ?_⟩
        · show (M.step c).bind (M.lrun n) = some c'
          rw [hc1]
          exact hc'
        · intro j hj
          cases j with
          | zero =>
            refine ⟨c, rfl, ?_⟩
            rw [h.q]
            exact hb
          | succ j =>
            obtain ⟨d, hd, hdq⟩ := hmid j (by omega)
            refine ⟨d, ?_, hdq⟩
            show (M.step c).bind (M.lrun j) = some d
            rw [hc1]
            exact hd

/-! ## The stream run from the blank tape -/

/-- Configuration after `k` steps from the blank tape (no beep check). -/
def LTM.zconf (M : LTM) : Nat → Option ZC
  | 0 => some ⟨0, blank, blank⟩
  | k + 1 => (M.zconf k).bind M.zstep

theorem zconf_rel (M : LTM) : ∀ k z, M.zconf k = some z → ∃ c, M.conf k = some c ∧ ZRel c z := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have h' : some (⟨0, blank, blank⟩ : ZC) = some z := hz
    cases h'
    exact ⟨_, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  | succ k ih =>
    intro z hz
    cases hk : M.zconf k with
    | none =>
      have h : (M.zconf k).bind M.zstep = some z := hz
      rw [hk] at h
      have h' : (none : Option ZC) = some z := h
      cases h'
    | some y =>
      have h : (M.zconf k).bind M.zstep = some z := hz
      rw [hk] at h
      have hs : M.zstep y = some z := h
      obtain ⟨c, hc, hr⟩ := ih y hk
      obtain ⟨c', hc', hr'⟩ := zstep_sound hr hs
      refine ⟨c', ?_, hr'⟩
      show (M.conf k).bind M.step = some c'
      rw [hc]
      exact hc'

theorem zconf_add (M : LTM) (k n : Nat) {z z' : ZC} (hk : M.zconf k = some z)
    (hn : M.zrun n z = some z') :
    M.zconf (k + n) = some z' ∧ ∀ j, j < n → ∃ y, M.zconf (k + j) = some y ∧ y.q ≠ M.beep := by
  induction n generalizing k z with
  | zero =>
    have h' : some z = some z' := hn
    cases h'
    exact ⟨hk, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    have hz1 : (if z.q = M.beep then none else (M.zstep z).bind (M.zrun n)) = some z' := hn
    by_cases hb : z.q = M.beep
    · rw [ite_eq_left hb] at hz1
      cases hz1
    · rw [ite_eq_right hb] at hz1
      cases hs : M.zstep z with
      | none =>
        rw [hs] at hz1
        have h' : (none : Option ZC) = some z' := hz1
        cases h'
      | some z1 =>
        rw [hs] at hz1
        have hz2 : M.zrun n z1 = some z' := hz1
        have hk1 : M.zconf (k + 1) = some z1 := by
          show (M.zconf k).bind M.zstep = some z1
          rw [hk]
          exact hs
        obtain ⟨h1, h2⟩ := ih (k := k + 1) (z := z1) hk1 hz2
        refine ⟨?_, ?_⟩
        · rw [show k + (n + 1) = k + 1 + n by omega]
          exact h1
        · intro j hj
          cases j with
          | zero => exact ⟨z, hk, hb⟩
          | succ j =>
            obtain ⟨y, hy, hyq⟩ := h2 j (by omega)
            refine ⟨y, ?_, hyq⟩
            rw [show k + (j + 1) = k + 1 + j by omega]
            exact hy

theorem zconf_step (M : LTM) {k : Nat} {z z' : ZC} (hk : M.zconf k = some z)
    (hs : M.zstep z = some z') : M.zconf (k + 1) = some z' := by
  show (M.zconf k).bind M.zstep = some z'
  rw [hk]
  exact hs

end ZP
