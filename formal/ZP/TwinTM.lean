module

public import ZP.Compile

@[expose] public section

/-!
# Two-symbol machines on stream tapes

The binary counterpart of `ZP/Zip.lean`: a configuration is a state and two streams, `R` from the
scanned cell rightwards and `L` from the cell left of it leftwards. `TM.zrun` refuses to step from
the beep state, so `zrun n z = some z'` also says that none of the first `n` configurations is a
beep.
-/

namespace ZP

abbrev BS := Nat → Bool

def bcons (a : Bool) (s : BS) : BS := fun i =>
  match i with
  | 0 => a
  | i + 1 => s i

def bblank : BS := fun _ => false

def bapp : List Bool → BS → BS
  | [], s => s
  | a :: w, s => bcons a (bapp w s)

/-- `n` bo, then `s`. -/
def bo (n : Nat) (s : BS) : BS := bapp (List.replicate n true) s

theorem bo_zero (s : BS) : bo 0 s = s := rfl
theorem bo_succ (n : Nat) (s : BS) : bo (n + 1) s = bcons true (bo n s) := rfl

theorem bo_succ' (n : Nat) (s : BS) : bo n (bcons true s) = bo (n + 1) s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bo_succ, bo_succ, ih]

theorem bblank_cons : bcons false bblank = bblank := by
  funext i
  cases i <;> rfl

structure BZ where
  q : Nat
  L : BS
  R : BS

def BZ.tl (s : BS) : BS := fun i => s (i + 1)

def TM.zstep (M : TM) (c : BZ) : Option BZ :=
  match M.act c.q (c.R 0) with
  | none => none
  | some (q', w, r) =>
    if r = 1 then some ⟨q', bcons (decide (w = 1)) c.L, BZ.tl c.R⟩
    else some ⟨q', BZ.tl c.L, bcons (c.L 0) (bcons (decide (w = 1)) (BZ.tl c.R))⟩

/-- `n` steps, none of them taken from the beep state. -/
def TM.zrun (M : TM) : Nat → BZ → Option BZ
  | 0, c => some c
  | n + 1, c => if c.q = M.beep then none else (M.zstep c).bind (M.zrun n)

theorem TM.zrun_add (M : TM) (a b : Nat) (c : BZ) :
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

/-! ## Link with `TM.conf` -/

structure BRel (c : Conf) (z : BZ) : Prop where
  q : c.q = z.q
  R : ∀ i : Nat, c.tape (c.head + (i : Int)) = z.R i
  L : ∀ i : Nat, c.tape (c.head - 1 - (i : Int)) = z.L i

theorem bstep_sound {M : TM} {c : Conf} {z z' : BZ} (h : BRel c z)
    (hz : M.zstep z = some z') : ∃ c', M.step c = some c' ∧ BRel c' z' := by
  obtain ⟨hq, hR, hL⟩ := h
  have h0 : c.tape c.head = z.R 0 := by
    have := hR 0
    rw [show c.head + ((0 : Nat) : Int) = c.head by omega] at this
    exact this
  rw [TM.step_eq, hq, h0]
  unfold TM.zstep at hz
  cases ha : M.act z.q (z.R 0) with
  | none =>
    rw [ha] at hz
    have h' : (none : Option BZ) = some z' := hz
    cases h'
  | some a =>
    obtain ⟨q', w, r⟩ := a
    rw [ha] at hz
    have hz' : (if r = 1 then some (⟨q', bcons (decide (w = 1)) z.L, BZ.tl z.R⟩ : BZ)
        else some ⟨q', BZ.tl z.L, bcons (z.L 0) (bcons (decide (w = 1)) (BZ.tl z.R))⟩) = some z' := hz
    refine ⟨_, rfl, ?_⟩
    by_cases hr : r = 1
    · rw [ite_eq_left hr] at hz'
      cases hz'
      refine ⟨rfl, ?_, ?_⟩
      · intro i
        show (if (if r = 1 then c.head + 1 else c.head - 1) + (i : Int) = c.head then decide (w = 1)
          else c.tape ((if r = 1 then c.head + 1 else c.head - 1) + (i : Int))) = z.R (i + 1)
        rw [ite_eq_left hr, ite_eq_right (by omega),
          show c.head + 1 + (i : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
        exact hR (i + 1)
      · intro i
        cases i with
        | zero =>
          show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - ((0 : Nat) : Int) = c.head
            then decide (w = 1) else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 -
              ((0 : Nat) : Int))) = decide (w = 1)
          rw [ite_eq_left hr, ite_eq_left (by omega)]
        | succ k =>
          show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - ((k + 1 : Nat) : Int) =
            c.head then decide (w = 1) else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 -
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
            then decide (w = 1) else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((0 : Nat) : Int))) = z.L 0
          rw [ite_eq_right hr, ite_eq_right (by omega),
            show c.head - 1 + ((0 : Nat) : Int) = c.head - 1 - ((0 : Nat) : Int) by omega]
          exact hL 0
        · show (if (if r = 1 then c.head + 1 else c.head - 1) + ((0 + 1 : Nat) : Int) = c.head
            then decide (w = 1) else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((0 + 1 : Nat) : Int))) = decide (w = 1)
          rw [ite_eq_right hr, ite_eq_left (by omega)]
        · show (if (if r = 1 then c.head + 1 else c.head - 1) + ((i + 1 + 1 : Nat) : Int) =
            c.head then decide (w = 1) else c.tape ((if r = 1 then c.head + 1 else c.head - 1) +
              ((i + 1 + 1 : Nat) : Int))) = z.R (i + 1)
          rw [ite_eq_right hr, ite_eq_right (by omega),
            show c.head - 1 + ((i + 1 + 1 : Nat) : Int) = c.head + ((i + 1 : Nat) : Int) by omega]
          exact hR (i + 1)
      · intro i
        show (if (if r = 1 then c.head + 1 else c.head - 1) - 1 - (i : Int) = c.head then decide (w = 1)
          else c.tape ((if r = 1 then c.head + 1 else c.head - 1) - 1 - (i : Int))) = z.L (i + 1)
        rw [ite_eq_right hr, ite_eq_right (by omega),
          show c.head - 1 - 1 - (i : Int) = c.head - 1 - ((i + 1 : Nat) : Int) by omega]
        exact hL (i + 1)

/-- The stream run from the blank tape (no beep check). -/
def TM.zconf (M : TM) : Nat → Option BZ
  | 0 => some ⟨0, bblank, bblank⟩
  | k + 1 => (M.zconf k).bind M.zstep

theorem bzconf_rel (M : TM) : ∀ k z, M.zconf k = some z → ∃ c, M.conf k = some c ∧ BRel c z := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have h' : some (⟨0, bblank, bblank⟩ : BZ) = some z := hz
    cases h'
    exact ⟨_, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  | succ k ih =>
    intro z hz
    cases hk : M.zconf k with
    | none =>
      have h : (M.zconf k).bind M.zstep = some z := hz
      rw [hk] at h
      have h' : (none : Option BZ) = some z := h
      cases h'
    | some y =>
      have h : (M.zconf k).bind M.zstep = some z := hz
      rw [hk] at h
      have hs : M.zstep y = some z := h
      obtain ⟨c, hc, hr⟩ := ih y hk
      obtain ⟨c', hc', hr'⟩ := bstep_sound hr hs
      refine ⟨c', ?_, hr'⟩
      show (M.conf k).bind M.step = some c'
      rw [hc]
      exact hc'

theorem bzconf_add (M : TM) (k n : Nat) {z z' : BZ} (hk : M.zconf k = some z)
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
        have h' : (none : Option BZ) = some z' := hz1
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

theorem bzconf_step (M : TM) {k : Nat} {z z' : BZ} (hk : M.zconf k = some z)
    (hs : M.zstep z = some z') : M.zconf (k + 1) = some z' := by
  show (M.zconf k).bind M.zstep = some z'
  rw [hk]
  exact hs

end ZP
