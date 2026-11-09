module

public import ZP.TwinTM
public import ZP.TableTwin
public import ZP.DefsTwin

@[expose] public section

namespace ZP

/-- Reachability by a run that never steps from the beep state. -/
def Rn (z z' : BZ) : Prop := ∃ n, twinMachine.zrun n z = some z'
def Rp (z z' : BZ) : Prop := ∃ n, 0 < n ∧ twinMachine.zrun n z = some z'

theorem Rn.refl (z : BZ) : Rn z z := ⟨0, rfl⟩

theorem Rn.trans {a b c : BZ} (h1 : Rn a b) (h2 : Rn b c) : Rn a c := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by rw [TM.zrun_add, hn]; exact hm⟩

theorem Rp.trans {a b c : BZ} (h1 : Rp a b) (h2 : Rn b c) : Rp a c := by
  obtain ⟨n, hn0, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [TM.zrun_add, hn]; exact hm⟩

theorem Rn.trans_p {a b c : BZ} (h1 : Rn a b) (h2 : Rp b c) : Rp a c := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm0, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [TM.zrun_add, hn]; exact hm⟩

theorem Rp.rn {a b : BZ} (h : Rp a b) : Rn a b := by
  obtain ⟨n, -, hn⟩ := h
  exact ⟨n, hn⟩

theorem tR {q q' : Nat} {b w : Bool} (L R : BS) (hq : q ≠ 5)
    (h : twinMachine.act q b = some (q', w.toNat, 1)) :
    Rp ⟨q, L, bcons b R⟩ ⟨q', bcons w L, R⟩ := by
  refine ⟨1, by omega, ?_⟩
  show (if q = twinMachine.beep then none else (twinMachine.zstep ⟨q, L, bcons b R⟩).bind
    (twinMachine.zrun 0)) = _
  have hq' : q ≠ twinMachine.beep := hq
  rw [ite_eq_right hq']
  unfold TM.zstep
  show (match twinMachine.act q b with | none => none | some (q', w, r) => if r = 1 then _ else _).bind _ = _
  rw [h]
  cases w <;> rfl

theorem tL {q q' : Nat} {b w : Bool} (a : Bool) (L R : BS) (hq : q ≠ 5)
    (h : twinMachine.act q b = some (q', w.toNat, 0)) :
    Rp ⟨q, bcons a L, bcons b R⟩ ⟨q', L, bcons a (bcons w R)⟩ := by
  refine ⟨1, by omega, ?_⟩
  show (if q = twinMachine.beep then none else (twinMachine.zstep ⟨q, bcons a L, bcons b R⟩).bind
    (twinMachine.zrun 0)) = _
  have hq' : q ≠ twinMachine.beep := hq
  rw [ite_eq_right hq']
  unfold TM.zstep
  show (match twinMachine.act q b with | none => none | some (q', w, r) => if r = 1 then _ else _).bind _ = _
  rw [h]
  cases w <;> simp <;> rfl

theorem scanR {q : Nat} (hq : q ≠ 5) (h : twinMachine.act q true = some (q, 1, 1)) :
    ∀ (n : Nat) (L R : BS), Rn ⟨q, L, bo n R⟩ ⟨q, bo n L, R⟩ := by
  intro n
  induction n with
  | zero => intro L R; exact Rn.refl _
  | succ n ih =>
    intro L R
    have h1 := tR (b := true) (w := true) L (bo n R) hq h
    have h2 := ih (bcons true L) R
    rw [bo_succ'] at h2
    exact (Rp.trans h1 h2).rn

theorem scanL {q : Nat} (hq : q ≠ 5) (h : twinMachine.act q true = some (q, 1, 0)) :
    ∀ (n : Nat) (L R : BS), Rn ⟨q, bo n L, bcons true R⟩ ⟨q, L, bcons true (bo n R)⟩ := by
  intro n
  induction n with
  | zero => intro L R; exact Rn.refl _
  | succ n ih =>
    intro L R
    have h1 := tL (b := true) (w := true) true (bo n L) R hq h
    have h2 := ih L (bcons true R)
    rw [bo_succ'] at h2
    exact (Rp.trans h1 h2).rn


theorem bo_add (a b : Nat) (s : BS) : bo a (bo b s) = bo (a + b) s := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => rw [bo_succ, ih, show a + 1 + b = (a + b) + 1 by omega, bo_succ]

theorem Rn.tr {a b c : BZ} (h1 : Rn a b) (h2 : Rn b c) : Rn a c := Rn.trans h1 h2
theorem Rp.tr {a b c : BZ} (h1 : Rp a b) (h2 : Rp b c) : Rp a c := Rp.trans h1 h2.rn
theorem Rp.tr' {a b c : BZ} (h1 : Rp a b) (h2 : Rn b c) : Rn a c := (Rp.trans h1 h2).rn

/-- The left part of the tape: `e` ones, the hole, `c` ones, then the blank. -/
def Dl (e c : Nat) : BS := bo e (bcons false (bo c bblank))

/-- Y2 sweeps left over `k` ones plus the one it stands on, then fills the hole. -/
theorem y2sweep (k : Nat) (X R : BS) :
    Rn ⟨8, bo k (bcons false X), bcons true R⟩ ⟨9, bcons true X, bo (k + 1) R⟩ := by
  have h1 := scanL (q := 8) (by decide) (by decide) k (bcons false X) R
  have h2 := tL (q := 8) (q' := 8) (b := true) (w := true) false X (bo k R) (by decide) (by decide)
  have h3 := tR (q := 8) (q' := 9) (b := false) (w := true) X (bcons true (bo k R)) (by decide) (by decide)
  exact (h1.tr (h2.tr' h3.rn))

theorem y1A (e c : Nat) (Rr : BS) :
    Rn ⟨7, Dl e c, bcons false Rr⟩ ⟨9, bo (c + 1) bblank, bo e (bcons false Rr)⟩ := by
  cases e with
  | zero =>
    have h1 := tL (q := 7) (q' := 8) (b := false) (w := false) false (bo c bblank) Rr
      (by decide) (by decide)
    have h2 := tR (q := 8) (q' := 9) (b := false) (w := true) (bo c bblank) (bcons false Rr)
      (by decide) (by decide)
    exact h1.tr' h2.rn
  | succ k =>
    have h1 := tL (q := 7) (q' := 8) (b := false) (w := false) true
      (bo k (bcons false (bo c bblank))) Rr (by decide) (by decide)
    have h2 := y2sweep k (bo c bblank) (bcons false Rr)
    exact h1.tr' h2


theorem zt (k : Nat) (X : BS) (j : Nat) (rest : BS) :
    Rn ⟨11, bcons false X, bo k (bcons false (bo j (bcons false rest)))⟩
      ⟨6, bo (j + 1) (bcons false (bo k (bcons false X))), rest⟩ := by
  have h1 := scanR (q := 11) (by decide) (by decide) k (bcons false X) (bcons false (bo j (bcons false rest)))
  have h2 := tR (q := 11) (q' := 12) (b := false) (w := false) (bo k (bcons false X))
    (bo j (bcons false rest)) (by decide) (by decide)
  have h3 := scanR (q := 12) (by decide) (by decide) j (bcons false (bo k (bcons false X))) (bcons false rest)
  have h4 := tR (q := 12) (q' := 6) (b := false) (w := true) (bo j (bcons false (bo k (bcons false X))))
    rest (by decide) (by decide)
  exact h1.tr (h2.tr' (h3.tr h4.rn))

theorem wA (k c j : Nat) (rest : BS) :
    Rn ⟨9, bo (c + 1) bblank, bo (k + 1) (bcons false (bo j (bcons false rest)))⟩
      ⟨6, bo (j + 1) (bcons false (Dl k (c + 1))), rest⟩ := by
  have h1 := tR (q := 9) (q' := 11) (b := true) (w := false) (bo (c + 1) bblank)
    (bo k (bcons false (bo j (bcons false rest)))) (by decide) (by decide)
  exact h1.tr' (zt k (bo (c + 1) bblank) j rest)

theorem wW (c j : Nat) (rest : BS) :
    Rn ⟨9, bo (c + 1) bblank, bcons false (bo j (bcons false rest))⟩
      ⟨6, bo (j + 1) (bcons false (Dl c 0)), rest⟩ := by
  have e : bo c bblank = bo c (bcons false bblank) := by rw [bblank_cons]
  have h1 := tL (q := 9) (q' := 10) (b := false) (w := false) true (bo c bblank)
    (bo j (bcons false rest)) (by decide) (by decide)
  rw [e] at h1
  have h2 := scanL (q := 10) (by decide) (by decide) c (bcons false bblank)
    (bcons false (bo j (bcons false rest)))
  have h3 := tL (q := 10) (q' := 10) (b := true) (w := true) false bblank
    (bo c (bcons false (bo j (bcons false rest)))) (by decide) (by decide)
  have h4 := tR (q := 10) (q' := 9) (b := false) (w := false) bblank
    (bcons true (bo c (bcons false (bo j (bcons false rest))))) (by decide) (by decide)
  have h5 := tR (q := 9) (q' := 11) (b := true) (w := false) (bcons false bblank)
    (bo c (bcons false (bo j (bcons false rest)))) (by decide) (by decide)
  have h6 := zt c (bcons false bblank) j rest
  have hh := h1.tr' (h2.tr (h3.tr' (h4.tr' (h5.tr' h6))))
  have e2 : bcons false (bcons false bblank) = bcons false bblank := congrArg (bcons false) bblank_cons
  rw [e2] at hh
  have e3 : bo (c + 1) bblank = bcons true (bo c (bcons false bblank)) := by rw [← e]; rfl
  rw [e3]
  exact hh

theorem bw (j : Nat) (D' R : BS) :
    Rn ⟨6, bo (j + 1) (bcons false D'), bcons true R⟩
      ⟨7, D', bcons false (bo (j + 1) (bcons false R))⟩ := by
  have h1 := tL (q := 6) (q' := 7) (b := true) (w := false) true (bo j (bcons false D')) R
    (by decide) (by decide)
  have h2 := scanL (q := 7) (by decide) (by decide) j (bcons false D') (bcons false R)
  have h3 := tL (q := 7) (q' := 7) (b := true) (w := true) false D'
    (bo j (bcons false R)) (by decide) (by decide)
  exact h1.tr' (h2.tr h3.rn)


/-- One walk step: hole of `D` (`d` cells) at `c` moves to `(c+1) % d`; R's hole moves right. -/
theorem wstepB (d c j : Nat) (rest : BS) (hc : c < d) :
    Rn ⟨7, Dl (d - 1 - c) c, bcons false (bo j (bcons false rest))⟩
      ⟨6, bo (j + 1) (bcons false (Dl (d - 1 - (c + 1) % d) ((c + 1) % d))), rest⟩ := by
  have h1 := y1A (d - 1 - c) c (bo j (bcons false rest))
  by_cases hlt : c + 1 < d
  · obtain ⟨k, hk⟩ : ∃ k, d - 1 - c = k + 1 := ⟨d - 2 - c, by omega⟩
    rw [hk] at h1 ⊢
    rw [Nat.mod_eq_of_lt hlt, show d - 1 - (c + 1) = k by omega]
    exact h1.tr (wA k c j rest)
  · have hd : c + 1 = d := by omega
    have hk : d - 1 - c = 0 := by omega
    rw [hk] at h1 ⊢
    rw [hd, Nat.mod_self, show d - 1 - 0 = c by omega]
    exact h1.tr (wW c j rest)

theorem walkN (d : Nat) :
    ∀ (s c j : Nat), c < d →
    Rn ⟨7, Dl (d - 1 - c) c, bcons false (bo j (bcons false (bo s bblank)))⟩
      ⟨7, Dl (d - 1 - (c + s) % d) ((c + s) % d), bcons false (bo (j + s) (bcons false bblank))⟩ := by
  intro s
  induction s with
  | zero =>
    intro c j hc
    rw [Nat.add_zero, Nat.mod_eq_of_lt hc]
    exact Rn.refl _
  | succ s ih =>
    intro c j hc
    have h1 := wstepB d c j (bo (s + 1) bblank) hc
    have h2 := bw j (Dl (d - 1 - (c + 1) % d) ((c + 1) % d)) (bo s bblank)
    have h3 := ih ((c + 1) % d) (j + 1) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show j + 1 + s = j + (s + 1) by omega,
      show c + 1 + s = c + (s + 1) by omega] at h3
    exact h1.tr (h2.tr h3)

theorem vph (r' : Nat) (D : BS) :
    Rn ⟨6, bo (r' + 1) (bcons false D), bblank⟩ ⟨13, D, bcons false (bo (r' + 1) bblank)⟩ := by
  have h1 := tL (q := 6) (q' := 13) (b := false) (w := false) true (bo r' (bcons false D)) bblank
    (by decide) (by decide)
  rw [bblank_cons] at h1
  have h2 := scanL (q := 13) (by decide) (by decide) r' (bcons false D) bblank
  have h3 := tL (q := 13) (q' := 13) (b := true) (w := true) false D (bo r' bblank)
    (by decide) (by decide)
  exact h1.tr' (h2.tr h3.rn)

theorem ck0 (c r : Nat) :
    Rn ⟨13, Dl 0 c, bcons false (bo r bblank)⟩ ⟨2, bo (c + 1) bblank, bcons false (bo r bblank)⟩ := by
  have h1 := tL (q := 13) (q' := 14) (b := false) (w := false) false (bo c bblank) (bo r bblank)
    (by decide) (by decide)
  have h2 := tR (q := 14) (q' := 2) (b := false) (w := true) (bo c bblank)
    (bcons false (bo r bblank)) (by decide) (by decide)
  exact h1.tr' h2.rn

theorem ck1 (c r : Nat) :
    Rn ⟨13, Dl 1 c, bcons false (bo r bblank)⟩
      ⟨18, bo (c + 1) bblank, bo 1 (bcons false (bo r bblank))⟩ := by
  have h1 := tL (q := 13) (q' := 14) (b := false) (w := false) true
    (bcons false (bo c bblank)) (bo r bblank) (by decide) (by decide)
  have h2 := tL (q := 14) (q' := 15) (b := true) (w := true) false (bo c bblank)
    (bcons false (bo r bblank)) (by decide) (by decide)
  have h3 := tR (q := 15) (q' := 18) (b := false) (w := true) (bo c bblank)
    (bcons true (bcons false (bo r bblank))) (by decide) (by decide)
  exact h1.tr' (h2.tr' h3.rn)

theorem ck2 (c r : Nat) :
    Rn ⟨13, Dl 2 c, bcons false (bo r bblank)⟩
      ⟨2, bo (c + 3) bblank, bcons false (bo r bblank)⟩ := by
  have h1 := tL (q := 13) (q' := 14) (b := false) (w := false) true
    (bcons true (bcons false (bo c bblank))) (bo r bblank) (by decide) (by decide)
  have h2 := tL (q := 14) (q' := 15) (b := true) (w := true) true
    (bcons false (bo c bblank)) (bcons false (bo r bblank)) (by decide) (by decide)
  have h3 := tL (q := 15) (q' := 16) (b := true) (w := true) false (bo c bblank)
    (bcons true (bcons false (bo r bblank))) (by decide) (by decide)
  have h4 := tR (q := 16) (q' := 2) (b := false) (w := true) (bo c bblank)
    (bcons true (bcons true (bcons false (bo r bblank)))) (by decide) (by decide)
  have h5 := scanR (q := 2) (by decide) (by decide) 2 (bcons true (bo c bblank))
    (bcons false (bo r bblank))
  have := h1.tr' (h2.tr' (h3.tr' (h4.tr' h5)))
  rw [show bo 2 (bcons true (bo c bblank)) = bo (c + 3) bblank by
    rw [show bcons true (bo c bblank) = bo (c + 1) bblank from rfl, bo_add, Nat.add_comm]] at this
  exact this

theorem ck3 (k c r : Nat) :
    Rn ⟨13, Dl (k + 3) c, bcons false (bo r bblank)⟩
      ⟨18, bo (c + 1) bblank, bo (k + 3) (bcons false (bo r bblank))⟩ := by
  have h1 := tL (q := 13) (q' := 14) (b := false) (w := false) true
    (bcons true (bcons true (bo k (bcons false (bo c bblank))))) (bo r bblank) (by decide) (by decide)
  have h2 := tL (q := 14) (q' := 15) (b := true) (w := true) true
    (bcons true (bo k (bcons false (bo c bblank)))) (bcons false (bo r bblank)) (by decide) (by decide)
  have h3 := tL (q := 15) (q' := 16) (b := true) (w := true) true
    (bo k (bcons false (bo c bblank))) (bcons true (bcons false (bo r bblank))) (by decide) (by decide)
  have hh := h1.tr' (h2.tr' h3.rn)
  cases k with
  | zero =>
    have h4 := tL (q := 16) (q' := 17) (b := true) (w := true) false (bo c bblank)
      (bcons true (bcons true (bcons false (bo r bblank)))) (by decide) (by decide)
    have h5 := tR (q := 17) (q' := 18) (b := false) (w := true) (bo c bblank)
      (bcons true (bcons true (bcons true (bcons false (bo r bblank))))) (by decide) (by decide)
    exact hh.tr (h4.tr' h5.rn)
  | succ k' =>
    have h4 := tL (q := 16) (q' := 17) (b := true) (w := true) true (bo k' (bcons false (bo c bblank)))
      (bcons true (bcons true (bcons false (bo r bblank)))) (by decide) (by decide)
    have h5 := scanL (q := 17) (by decide) (by decide) k' (bcons false (bo c bblank))
      (bcons true (bcons true (bcons true (bcons false (bo r bblank)))))
    have h6 := tL (q := 17) (q' := 17) (b := true) (w := true) false (bo c bblank)
      (bo k' (bcons true (bcons true (bcons true (bcons false (bo r bblank)))))) (by decide) (by decide)
    have h7 := tR (q := 17) (q' := 18) (b := false) (w := true) (bo c bblank)
      (bcons true (bo k' (bcons true (bcons true (bcons true (bcons false (bo r bblank))))))) (by decide) (by decide)
    have := hh.tr (h4.tr' (h5.tr (h6.tr' h7.rn)))
    have e : bo (k' + 1 + 3) (bcons false (bo r bblank)) =
        bcons true (bo k' (bo 3 (bcons false (bo r bblank)))) := by
      rw [show k' + 1 + 3 = (k' + 3) + 1 by omega, bo_succ, ← bo_add]
    rw [e]
    exact this


theorem ptail (a e r' : Nat) :
    Rn ⟨18, bo a bblank, bo e (bcons false (bo (r' + 1) bblank))⟩
      ⟨4, bcons false (bcons false (bo (e + a) bblank)), bo r' bblank⟩ := by
  have h1 := scanR (q := 18) (by decide) (by decide) e (bo a bblank) (bcons false (bo (r' + 1) bblank))
  have h2 := tR (q := 18) (q' := 3) (b := false) (w := false) (bo e (bo a bblank))
    (bo (r' + 1) bblank) (by decide) (by decide)
  have h3 := tR (q := 3) (q' := 4) (b := true) (w := false) (bcons false (bo e (bo a bblank)))
    (bo r' bblank) (by decide) (by decide)
  have := h1.tr (h2.tr' h3.rn)
  rw [bo_add] at this
  exact this

theorem rb (a' r : Nat) :
    Rn ⟨2, bo (a' + 1) bblank, bcons false (bo r bblank)⟩
      ⟨4, bcons false (bcons false (bo 1 bblank)), bo (a' + r) bblank⟩ := by
  have e : bo a' bblank = bo a' (bcons false bblank) := by rw [bblank_cons]
  have h1 := tL (q := 2) (q' := 0) (b := false) (w := true) true (bo a' bblank) (bo r bblank)
    (by decide) (by decide)
  rw [e] at h1
  have h2 : Rn ⟨0, bo a' (bcons false bblank), bo (r + 2) bblank⟩
      ⟨0, bcons false bblank, bcons true (bo a' (bo (r + 1) bblank))⟩ :=
    scanL (q := 0) (by decide) (by decide) a' (bcons false bblank) (bo (r + 1) bblank)
  have h3 := tL (q := 0) (q' := 0) (b := true) (w := true) false bblank
    (bo a' (bo (r + 1) bblank)) (by decide) (by decide)
  have h4 := tR (q := 0) (q' := 1) (b := false) (w := true) bblank
    (bcons true (bo a' (bo (r + 1) bblank))) (by decide) (by decide)
  rw [bo_add, show a' + (r + 1) = (a' + r) + 1 by omega] at h2 h3 h4
  have h5 := tR (q := 1) (q' := 3) (b := true) (w := false) (bcons true bblank)
    (bo (a' + r + 1) bblank) (by decide) (by decide)
  have h6 := tR (q := 3) (q' := 4) (b := true) (w := false) (bcons false (bcons true bblank))
    (bo (a' + r) bblank) (by decide) (by decide)
  have h1' : Rp ⟨2, bcons true (bo a' (bcons false bblank)), bcons false (bo r bblank)⟩
      ⟨0, bo a' (bcons false bblank), bo (r + 2) bblank⟩ := h1
  have hh := h1'.tr' (h2.tr (h3.tr' (h4.tr' (h5.tr' h6.rn))))
  have e3 : bo (a' + 1) bblank = bcons true (bo a' (bcons false bblank)) := by rw [← e]; rfl
  rw [e3]
  exact hh

theorem ckFail (e c r : Nat) (he : e = 0 ∨ e = 2) :
    Rn ⟨13, Dl e c, bcons false (bo r bblank)⟩
      ⟨4, bcons false (bcons false (bo 1 bblank)), bo (e + c + r) bblank⟩ := by
  rcases he with rfl | rfl
  · rw [Nat.zero_add]
    exact (ck0 c r).tr (rb c r)
  · rw [show 2 + c + r = c + 2 + r by omega]
    exact (ck2 c r).tr (rb (c + 2) r)

theorem ckPass (e c r' : Nat) (he : e = 1 ∨ 3 ≤ e) :
    Rn ⟨13, Dl e c, bcons false (bo (r' + 1) bblank)⟩
      ⟨4, bcons false (bcons false (bo (e + c + 1) bblank)), bo r' bblank⟩ := by
  rcases he with rfl | h3
  · exact (ck1 c (r' + 1)).tr (ptail (c + 1) 1 r')
  · obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
    have := (ck3 k c (r' + 1)).tr (ptail (c + 1) (k + 3) r')
    rw [show k + 3 + (c + 1) = k + 3 + c + 1 by omega] at this
    exact this


/-- Walk start: G2 on R's first cell, `D` has `d` cells with its hole on the last one,
and R has `r' + 1` cells. -/
def Kz (d r : Nat) : BZ := ⟨4, bcons false (bcons false (bo (d - 1) bblank)), bo r bblank⟩

theorem round_core (d r' : Nat) (hd : 2 ≤ d) :
    Rp (Kz d (r' + 1))
      ⟨13, Dl (d - 1 - (d + r') % d) ((d + r') % d), bcons false (bo (r' + 1) bblank)⟩ := by
  have h1 := tL (q := 4) (q' := 7) (b := true) (w := false) false
    (bcons false (bo (d - 1) bblank)) (bo r' bblank) (by decide) (by decide)
  have h2 := walkN d r' (d - 1) 0 (by omega)
  rw [show d - 1 - (d - 1) = 0 by omega, Nat.zero_add] at h2
  have h3 := wstepB d ((d - 1 + r') % d) r' bblank (Nat.mod_lt _ (by omega))
  rw [Nat.mod_add_mod, show d - 1 + r' + 1 = d + r' by omega] at h3
  have h4 := vph r' (Dl (d - 1 - (d + r') % d) ((d + r') % d))
  exact Rp.trans h1 (h2.tr (h3.tr h4))


theorem mod3 (cf d : Nat) (h : cf < d) (hd : 2 ≤ d) (h0 : (cf + 3) % d = 0) :
    cf + 3 = d ∨ cf + 1 = d := by
  by_cases hlt : cf + 3 < d
  · rw [Nat.mod_eq_of_lt hlt] at h0
    omega
  · rw [Nat.mod_eq_sub_mod (by omega)] at h0
    by_cases h2 : cf + 3 - d < d
    · rw [Nat.mod_eq_of_lt h2] at h0
      omega
    · omega

theorem mod1 (cf d : Nat) (h : cf < d) (h0 : (cf + 1) % d = 0) : cf + 1 = d := by
  by_cases hlt : cf + 1 < d
  · rw [Nat.mod_eq_of_lt hlt] at h0
    omega
  · omega

/-- The hole position decides failure: `d ∣ m` or `d ∣ m + 2`. -/
theorem fail_iff (d r' : Nat) (hd : 2 ≤ d) :
    ((d - 1 - (d + r') % d = 0 ∨ d - 1 - (d + r') % d = 2)) ↔
      ((d + r' + 1) % d = 0 ∨ (d + r' + 3) % d = 0) := by
  have hcf : (d + r') % d < d := Nat.mod_lt _ (by omega)
  have e1 : (d + r' + 1) % d = ((d + r') % d + 1) % d := by rw [Nat.mod_add_mod]
  have e3 : (d + r' + 3) % d = ((d + r') % d + 3) % d := by rw [Nat.mod_add_mod]
  rw [e1, e3]
  generalize (d + r') % d = cf at hcf ⊢
  constructor
  · rintro (h | h)
    · left
      rw [show cf + 1 = d by omega, Nat.mod_self]
    · right
      rw [show cf + 3 = d by omega, Nat.mod_self]
  · rintro (h | h)
    · left
      have := mod1 cf d hcf h
      omega
    · rcases mod3 cf d hcf hd h with h' | h'
      · right; omega
      · left; omega

theorem roundFail (d r' : Nat) (hd : 2 ≤ d)
    (hF : (d + r' + 1) % d = 0 ∨ (d + r' + 3) % d = 0) :
    Rp (Kz d (r' + 1)) (Kz 2 (d + r')) := by
  have hcf : (d + r') % d < d := Nat.mod_lt _ (by omega)
  have h := ckFail (d - 1 - (d + r') % d) ((d + r') % d) (r' + 1) ((fail_iff d r' hd).2 hF)
  have e : d - 1 - (d + r') % d + (d + r') % d + (r' + 1) = d + r' := by omega
  rw [e] at h
  exact Rp.trans (round_core d r' hd) h

theorem roundPass (d r' : Nat) (hd : 2 ≤ d)
    (hF : ¬ ((d + r' + 1) % d = 0 ∨ (d + r' + 3) % d = 0)) :
    Rp (Kz d (r' + 1)) (Kz (d + 1) r') := by
  have hcf : (d + r') % d < d := Nat.mod_lt _ (by omega)
  have hn : ¬ (d - 1 - (d + r') % d = 0 ∨ d - 1 - (d + r') % d = 2) := fun h => hF ((fail_iff d r' hd).1 h)
  have h := ckPass (d - 1 - (d + r') % d) ((d + r') % d) r' (by omega)
  have e : d - 1 - (d + r') % d + (d + r') % d + 1 = d + 1 - 1 := by omega
  rw [e] at h
  exact Rp.trans (round_core d r' hd) h


/-- Step from any state (also the beep state), moving left. -/
theorem zL {q q' : Nat} {b w : Bool} (a : Bool) (L R : BS)
    (h : twinMachine.act q b = some (q', w.toNat, 0)) :
    twinMachine.zstep ⟨q, bcons a L, bcons b R⟩ = some ⟨q', L, bcons a (bcons w R)⟩ := by
  unfold TM.zstep
  show (match twinMachine.act q b with | none => none | some (q', w, r) => if r = 1 then _ else _) = _
  rw [h]
  cases w <;> rfl

/-- A run of `n` steps from `z` to `z'`. It visits the beep state iff `b`, and then once. -/
def TSeg (z : BZ) (n : Nat) (z' : BZ) (b : Prop) : Prop :=
  (¬ b → twinMachine.zrun n z = some z') ∧
  (b → ∃ a c1 c2, a < n ∧ twinMachine.zrun a z = some c1 ∧ c1.q = 5 ∧
      twinMachine.zstep c1 = some c2 ∧ twinMachine.zrun (n - a - 1) c2 = some z')

theorem TSeg.congr {z z' : BZ} {n : Nat} {b b' : Prop} (h : TSeg z n z' b) (hb : b ↔ b') :
    TSeg z n z' b' := ⟨fun hn => h.1 (fun x => hn (hb.1 x)), fun x => h.2 (hb.2 x)⟩

theorem TSeg.pre {z z1 z' : BZ} {n0 n : Nat} {b : Prop} (h0 : twinMachine.zrun n0 z = some z1)
    (h : TSeg z1 n z' b) : TSeg z (n0 + n) z' b := by
  refine ⟨fun hn => ?_, fun hb => ?_⟩
  · rw [TM.zrun_add, h0]
    exact h.1 hn
  · obtain ⟨a, c1, c2, ha, h1, h2, h3, h4⟩ := h.2 hb
    refine ⟨n0 + a, c1, c2, by omega, ?_, h2, h3, ?_⟩
    · rw [TM.zrun_add, h0]
      exact h1
    · rw [show n0 + n - (n0 + a) - 1 = n - a - 1 by omega]
      exact h4

theorem TSeg.of_run {z z' : BZ} {n : Nat} (h : twinMachine.zrun n z = some z') :
    TSeg z n z' False := ⟨fun _ => h, fun hb => hb.elim⟩

/-- `d = m`: R is empty, G2 reads a blank and beeps, then the rebuild gives `K (m+1) 2`. -/
theorem beepPath (d' : Nat) :
    ∃ n, 0 < n ∧ TSeg (Kz (d' + 1) 0) n (Kz 2 d') True := by
  have hK : Kz (d' + 1) 0 =
      ⟨4, bcons false (bcons false (bo d' bblank)), bcons false bblank⟩ := by
    unfold Kz
    rw [show d' + 1 - 1 = d' by omega, bblank_cons]
    rfl
  rw [hK]
  -- G2 on a blank: write 0, move left, enter BP
  have h1 := tL (q := 4) (q' := 5) (b := false) (w := false) false (bcons false (bo d' bblank))
    bblank (by decide) (by decide)
  obtain ⟨n1, hn1, h1r⟩ := h1
  -- BP on 0: write 0, move left, enter X1
  have h2 := zL (q := 5) (q' := 14) (b := false) (w := false) false (bo d' bblank)
    (bcons false bblank) (by decide)
  have h3 := tR (q := 14) (q' := 2) (b := false) (w := true) (bo d' bblank)
    (bcons false (bcons false bblank)) (by decide) (by decide)
  have h4 : Rn ⟨2, bo (d' + 1) bblank, bcons false (bcons false bblank)⟩
      ⟨4, bcons false (bcons false (bo 1 bblank)), bo (d' + 0) bblank⟩ := by
    rw [bblank_cons]
    exact rb d' 0
  obtain ⟨n3, hn3, h3r⟩ := h3
  obtain ⟨n4, h4r⟩ := h4
  refine ⟨n1 + 1 + (n3 + n4), by omega, ?_, ?_⟩
  · intro hn
    exact (hn trivial).elim
  · intro _
    refine ⟨n1, ⟨5, bcons false (bo d' bblank), bcons false (bcons false bblank)⟩, _, by omega,
      h1r, rfl, h2, ?_⟩
    rw [show n1 + 1 + (n3 + n4) - n1 - 1 = n3 + n4 by omega, TM.zrun_add, h3r]
    exact h4r


/-- `d` divides `m` or `m + 2`. -/
def Fd (m d : Nat) : Prop := m % d = 0 ∨ (m + 2) % d = 0

/-- Trial division from divisor `d` on, starting at the walk start `K m d`. -/
theorem trial (m : Nat) : ∀ (t d : Nat), d + t = m → 2 ≤ d →
    ∃ n, 0 < n ∧ TSeg (Kz d t) n (Kz 2 (m - 1))
      (∀ d', d ≤ d' → d' < m → ¬ Fd m d') := by
  intro t
  induction t with
  | zero =>
    intro d hdm hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨n, hn, hs⟩ := beepPath d'
    rw [show m - 1 = d' by omega]
    exact ⟨n, hn, hs.congr ⟨fun _ d'' h1 h2 => absurd h2 (by omega), fun _ => trivial⟩⟩
  | succ r' ih =>
    intro d hdm hd
    by_cases hF : Fd m d
    · have hF' : (d + r' + 1) % d = 0 ∨ (d + r' + 3) % d = 0 := by
        rw [show d + r' + 1 = m by omega, show d + r' + 3 = m + 2 by omega]
        exact hF
      obtain ⟨n, hn, hr⟩ := roundFail d r' hd hF'
      rw [show m - 1 = d + r' by omega]
      refine ⟨n, hn, (TSeg.of_run hr).congr ⟨fun h => h.elim, fun h => ?_⟩⟩
      exact absurd hF (h d (Nat.le_refl _) (by omega))
    · have hF' : ¬ ((d + r' + 1) % d = 0 ∨ (d + r' + 3) % d = 0) := by
        rw [show d + r' + 1 = m by omega, show d + r' + 3 = m + 2 by omega]
        exact hF
      obtain ⟨n0, hn0, hr⟩ := roundPass d r' hd hF'
      obtain ⟨n1, hn1, hs⟩ := ih (d + 1) (by omega) (by omega)
      refine ⟨n0 + n1, by omega, (TSeg.pre hr hs).congr ⟨fun h d' h1 h2 => ?_, fun h d' h1 h2 => ?_⟩⟩
      · by_cases he : d' = d
        · subst he; exact hF
        · exact h d' (by omega) h2
      · exact h d' (by omega) h2


theorem twin_iff (m : Nat) (hm : 3 ≤ m) :
    (IsPrime m ∧ IsPrime (m + 2)) ↔ ∀ d', 2 ≤ d' → d' < m → ¬ Fd m d' := by
  constructor
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ d' hd hlt hF
    rcases hF with h | h
    · exact h1 d' hlt hd h
    · exact h2 d' (by omega) hd h
  · intro h
    refine ⟨⟨by omega, fun d' hlt hd h0 => h d' hd hlt (Or.inl h0)⟩, ⟨by omega, ?_⟩⟩
    intro d' hlt hd h0
    by_cases h1 : d' < m
    · exact h d' hd h1 (Or.inr h0)
    · by_cases h2 : d' = m
      · subst h2
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at h0
        omega
      · have h3 : d' = m + 1 := by omega
        subst h3
        rw [show m + 2 = (m + 1) + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at h0
        omega

theorem cand (m : Nat) (hm : 3 ≤ m) :
    ∃ n, 0 < n ∧ TSeg (Kz 2 (m - 2)) n (Kz 2 (m - 1)) (IsPrime m ∧ IsPrime (m + 2)) := by
  obtain ⟨n, hn, hs⟩ := trial m (m - 2) 2 (by omega) (Nat.le_refl _)
  exact ⟨n, hn, hs.congr (twin_iff m hm).symm⟩

/-- From the blank tape the machine reaches `K 3 2` (8 steps), without beeping. -/
theorem start : Rn ⟨0, bblank, bblank⟩ (Kz 2 1) := by
  have a1 : Rp (⟨0, bblank, bblank⟩ : BZ) ⟨1, bcons true bblank, bblank⟩ := by
    have := tR (q := 0) (q' := 1) (b := false) (w := true) bblank bblank (by decide) (by decide)
    rw [bblank_cons] at this
    exact this
  have a2 : Rp (⟨1, bcons true bblank, bblank⟩ : BZ) ⟨2, bcons true (bcons true bblank), bblank⟩ := by
    have := tR (q := 1) (q' := 2) (b := false) (w := true) (bcons true bblank) bblank
      (by decide) (by decide)
    rw [bblank_cons] at this
    exact this
  have a3 : Rp (⟨2, bcons true (bcons true bblank), bblank⟩ : BZ)
      ⟨0, bcons true bblank, bcons true (bcons true bblank)⟩ := by
    have := tL (q := 2) (q' := 0) (b := false) (w := true) true (bcons true bblank) bblank
      (by decide) (by decide)
    rw [bblank_cons] at this
    exact this
  have a4 := tL (q := 0) (q' := 0) (b := true) (w := true) true bblank (bcons true bblank)
    (by decide) (by decide)
  have a5 : Rp (⟨0, bblank, bcons true (bcons true (bcons true bblank))⟩ : BZ)
      ⟨0, bblank, bcons false (bcons true (bcons true (bcons true bblank)))⟩ := by
    have := tL (q := 0) (q' := 0) (b := true) (w := true) false bblank
      (bcons true (bcons true bblank)) (by decide) (by decide)
    rw [bblank_cons] at this
    exact this
  have a6 := tR (q := 0) (q' := 1) (b := false) (w := true) bblank
    (bcons true (bcons true (bcons true bblank))) (by decide) (by decide)
  have a7 := tR (q := 1) (q' := 3) (b := true) (w := false) (bcons true bblank)
    (bcons true (bcons true bblank)) (by decide) (by decide)
  have a8 := tR (q := 3) (q' := 4) (b := true) (w := false) (bcons false (bcons true bblank))
    (bcons true bblank) (by decide) (by decide)
  exact (a1.tr (a2.tr (a3.tr (a4.tr (a5.tr (a6.tr (a7.tr a8))))))).rn

end ZP
