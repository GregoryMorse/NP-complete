module

public import ZP.Defs
public import ZP.Logic
public import ZP.SymExec
public import ZP.Rot

@[expose] public section

/-!
# Layer N3: the fuel odometer

The fuel is a row of blocks `M 1^d 0^(n+1-d)`, one digit `d ≤ n+1` each, base `n+2`,
least significant block last. `DEC1` on the last cell decrements it; a borrow out of
the first block meets the `M` before it (the double `M`) and the machine enters `EXH`.
-/

namespace ZP

def Sym4 (w : List Nat) : Prop := ∀ a ∈ w, a ∈ ALL

/-- Symbols other than blank. -/
def NB : List Nat := [1, 2, 3]

def NoB (w : List Nat) : Prop := ∀ a ∈ w, a ∈ NB

theorem Sym4.app {u v : List Nat} (hu : Sym4 u) (hv : Sym4 v) : Sym4 (u ++ v) := by
  intro a ha
  rcases List.mem_append.mp ha with e | e
  · exact hu a e
  · exact hv a e

theorem Sym4.cons {b : Nat} {w : List Nat} (hb : b ∈ ALL) (hw : Sym4 w) : Sym4 (b :: w) := by
  intro a ha
  rcases List.mem_cons.mp ha with e | e
  · rw [e]; exact hb
  · exact hw a e

theorem Sym4.rep (u c : Nat) (h : c ∈ ALL) : Sym4 (List.replicate u c) := by
  intro a ha
  rw [List.eq_of_mem_replicate ha]
  exact h

theorem Sym4.nil : Sym4 [] := fun _ h => by cases h

theorem NoB.sym4 {w : List Nat} (h : NoB w) : Sym4 w := by
  intro a ha
  have := h a ha
  simp [NB] at this
  simp [ALL]
  omega

theorem NoB.app {u v : List Nat} (hu : NoB u) (hv : NoB v) : NoB (u ++ v) := by
  intro a ha
  rcases List.mem_append.mp ha with e | e
  · exact hu a e
  · exact hv a e

/-! ## Blocks -/

def blkW (n d : Nat) : List Nat := 1 :: (List.replicate d 3 ++ List.replicate (n + 1 - d) 2)

theorem blkW_noB (n d : Nat) : NoB (blkW n d) := by
  intro a ha
  simp only [blkW, List.mem_cons, List.mem_append] at ha
  rcases ha with e | e | e
  · rw [e]; simp [NB]
  · rw [List.eq_of_mem_replicate e]; simp [NB]
  · rw [List.eq_of_mem_replicate e]; simp [NB]

def fsets : Env := [ALL, ALL, ALL, ALL]

theorem fvalid {L U Z R : List Nat} (hL : Sym4 L) (hU : Sym4 U) (hZ : Sym4 Z) (hR : Sym4 R) :
    Valid fsets [L, U, Z, R] :=
  Valid.cons hL (Valid.cons hU (Valid.cons hZ (Valid.cons hR (Valid.nil _))))

/-- Decrementing a nonzero digit. -/
theorem dec_pos (n u : Nat) (hu : u ≤ n) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zpBase.Reach (hd Q.DEC1 (L ++ blkW n (u + 1)) R) (hd Q.FBACK L (blkW n u ++ R)) := by
  have e1 : n + 1 - (u + 1) = n - u := by omega
  have e2 : n + 1 - u = n - u + 1 := by omega
  unfold blkW
  rw [e1, e2]
  generalize n - u = z
  cases z with
  | zero =>
    exact checkTT (env := [L, List.replicate u 3, [], R]) (E := []) (k := 8)
      (fvalid hL (Sym4.rep _ _ (by simp [ALL])) Sym4.nil hR) trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 (.const 3), .sym 3]) (rs := [.blk 3 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 1 (.const 3), .sym 2, .blk 3 .id])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, rep_cons_comm, List.replicate_succ, Fn.app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, rep_cons_comm, List.replicate_succ, Fn.app])
  | succ z =>
    exact checkTT (env := [L, List.replicate u 3, List.replicate z 2, R]) (E := []) (k := 10)
      (fvalid hL (Sym4.rep _ _ (by simp [ALL])) (Sym4.rep _ _ (by simp [ALL])) hR) trivial
      (ls := [.blk 0 .id, .sym 1, .blk 1 (.const 3), .sym 3, .blk 2 (.const 2), .sym 2])
      (rs := [.blk 3 .id]) (ls' := [.blk 0 .id])
      (rs' := [.sym 1, .blk 1 (.const 3), .sym 2, .blk 2 (.const 2), .sym 2, .blk 3 .id])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, rep_cons_comm, List.replicate_succ, Fn.app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, rep_cons_comm, List.replicate_succ, Fn.app])

/-- A zero digit borrows: it is refilled and `DEC1` moves to the block before it. -/
theorem borrow (n : Nat) (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) (hR1 : R = [] ∨ ∃ R', R = 1 :: R') :
    zpBase.Reach (hd Q.DEC1 (L ++ blkW n 0) R) (hd Q.DEC1 L (blkW n (n + 1) ++ R)) := by
  have e : blkW n 0 = 1 :: (List.replicate n 2 ++ [2]) := by
    simp [blkW, rep_cons_comm, List.replicate_succ]
  have e' : blkW n (n + 1) = 1 :: (List.replicate n 3 ++ [3]) := by
    simp [blkW, rep_cons_comm, List.replicate_succ]
  rw [e, e']
  rcases hR1 with rfl | ⟨R', rfl⟩
  · exact checkTT (env := [L, [], List.replicate n 2, []]) (E := []) (k := 12)
      (fvalid hL Sym4.nil (Sym4.rep _ _ (by simp [ALL])) Sym4.nil) trivial
      (ls := [.blk 0 .id, .sym 1, .blk 2 (.const 2), .sym 2]) (rs := [])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app])
      (by simp [dR])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app])
  · have hR' : Sym4 R' := fun a ha => hR a (List.mem_cons_of_mem _ ha)
    exact checkTT (env := [L, [], List.replicate n 2, R']) (E := []) (k := 12)
      (fvalid hL Sym4.nil (Sym4.rep _ _ (by simp [ALL])) hR') trivial
      (ls := [.blk 0 .id, .sym 1, .blk 2 (.const 2), .sym 2]) (rs := [.sym 1, .blk 3 .id])
      (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 2 (.const 3), .sym 3, .sym 1, .blk 3 .id])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app, map_const_rep, Fn.app])

/-- The borrow meets the double `M`. -/
theorem exh (L R : List Nat) (hL : Sym4 L) (hR : Sym4 R) :
    zpBase.Reach (hd Q.DEC1 (L ++ [1]) R) (hd Q.EXH L (1 :: R)) :=
  checkTT (env := [L, [], [], R]) (E := []) (k := 3)
    (fvalid hL Sym4.nil Sym4.nil hR) trivial
    (ls := [.blk 0 .id, .sym 1]) (rs := [.blk 3 .id])
    (ls' := [.blk 0 .id]) (rs' := [.sym 1, .blk 3 .id])
    (by decide +kernel)
    (by simp [dR, Item.den, List.getD, map_id_app])
    (by simp [dR, Item.den, List.getD, map_id_app])
    (by simp [dR, Item.den, List.getD, map_id_app])
    (by simp [dR, Item.den, List.getD, map_id_app])

def wsets : Env := [ALL, NB, ALL]

/-- `FBACK` and `EXH` walk left over non-blank cells. -/
theorem walkL (q : Nat) (hq : q = Q.FBACK ∨ q = Q.EXH) (L W R : List Nat) (hL : Sym4 L) (hW : NoB W)
    (hR : Sym4 R) : zpBase.Reach (hd q (L ++ W) R) (hd q L (W ++ R)) := by
  have hv : Valid wsets [L, W, R] := Valid.cons hL (Valid.cons hW (Valid.cons hR (Valid.nil _)))
  rcases hq with rfl | rfl
  · exact checkTT (env := [L, W, R]) (E := []) (k := 3) hv trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
  · exact checkTT (env := [L, W, R]) (E := []) (k := 3) hv trivial
      (ls := [.blk 0 .id, .blk 1 .id]) (rs := [.blk 2 .id])
      (ls' := [.blk 0 .id]) (rs' := [.blk 1 .id, .blk 2 .id])
      (by decide +kernel)
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])
      (by simp [dR, Item.den, List.getD, map_id_app])

/-! ## The odometer -/

/-- Blocks, least significant first in the list, last on the tape. -/
def FWr (n : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => FWr n ds ++ blkW n d

def valr (n : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + (n + 2) * valr n ds

def Dig (n : Nat) (ds : List Nat) : Prop := ∀ d ∈ ds, d ≤ n + 1

theorem FWr_noB (n : Nat) : ∀ ds, NoB (FWr n ds)
  | [] => fun _ h => by cases h
  | d :: ds => (FWr_noB n ds).app (blkW_noB n d)

/-- One decrement of a fuel `M FWr ds` (the `M` is the one before the first block). -/
theorem fuel (n : Nat) : ∀ ds, Dig n ds → ∀ L R, Sym4 L → Sym4 R → (R = [] ∨ ∃ R', R = 1 :: R') →
    (0 < valr n ds → ∃ ds', Dig n ds' ∧ ds'.length = ds.length ∧ valr n ds' + 1 = valr n ds ∧
      zpBase.Reach (hd Q.DEC1 (L ++ [1] ++ FWr n ds) R) (hd Q.FBACK (L ++ [1]) (FWr n ds' ++ R))) ∧
    (valr n ds = 0 →
      zpBase.Reach (hd Q.DEC1 (L ++ [1] ++ FWr n ds) R)
        (hd Q.EXH L (1 :: (FWr n (ds.map fun _ => n + 1) ++ R))))
  | [], _, L, R, hL, hR, _ => by
    refine ⟨fun h => absurd h (Nat.lt_irrefl 0), fun _ => ?_⟩
    show zpBase.Reach (hd Q.DEC1 (L ++ [1] ++ []) R) (hd Q.EXH L (1 :: ([] ++ R)))
    rw [List.append_nil, List.nil_append]
    exact exh L R hL hR
  | d :: ds, hd0, L, R, hL, hR, hR1 => by
    have hds : Dig n ds := fun x hx => hd0 x (List.mem_cons_of_mem _ hx)
    have hdn : d ≤ n + 1 := hd0 d (List.mem_cons_self ..)
    have hL1 : Sym4 (L ++ [1] ++ FWr n ds) :=
      (hL.app (Sym4.cons (by simp [ALL]) Sym4.nil)).app (FWr_noB n ds).sym4
    have eA : L ++ [1] ++ FWr n (d :: ds) = (L ++ [1] ++ FWr n ds) ++ blkW n d :=
      (List.append_assoc _ _ _).symm
    rw [eA]
    cases d with
    | zero =>
      have hB := borrow n (L ++ [1] ++ FWr n ds) R hL1 hR hR1
      have hR2 : Sym4 (blkW n (n + 1) ++ R) := (blkW_noB n _).sym4.app hR
      have ih := fuel n ds hds L (blkW n (n + 1) ++ R) hL hR2 (Or.inr ⟨_, rfl⟩)
      have hv : valr n (0 :: ds) = (n + 2) * valr n ds := by simp [valr]
      refine ⟨fun hpos => ?_, fun hz => ?_⟩
      · have hpos' : 0 < valr n ds := by
          rw [hv] at hpos
          rcases Nat.eq_zero_or_pos (valr n ds) with h | h
          · rw [h, Nat.mul_zero] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
          · exact h
        obtain ⟨ds', hd', hl', hv', hr'⟩ := ih.1 hpos'
        refine ⟨(n + 1) :: ds', ?_, by simp [hl'], ?_, hB.trans ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with e | e
          · rw [e]; exact Nat.le_refl _
          · exact hd' x e
        · rw [hv, ← hv']
          simp only [valr]
          rw [Nat.mul_add, Nat.mul_one]
          omega
        · have e2 : FWr n ((n + 1) :: ds') ++ R = FWr n ds' ++ (blkW n (n + 1) ++ R) := by
            simp [FWr]
          rw [e2]
          exact hr'
      · have hz' : valr n ds = 0 := by
          rw [hv] at hz
          rcases Nat.mul_eq_zero.mp hz with h | h
          · omega
          · exact h
        refine hB.trans ?_
        have e2 : 1 :: (FWr n ((0 :: ds).map fun _ => n + 1) ++ R) =
            1 :: (FWr n (ds.map fun _ => n + 1) ++ (blkW n (n + 1) ++ R)) := by
          simp [FWr]
        rw [e2]
        exact ih.2 hz'
    | succ u =>
      have hD := dec_pos n u (by omega) (L ++ [1] ++ FWr n ds) R hL1 hR
      have hW := walkL Q.FBACK (Or.inl rfl) (L ++ [1]) (FWr n ds) (blkW n u ++ R)
        (hL.app (Sym4.cons (by simp [ALL]) Sym4.nil)) (FWr_noB n ds) ((blkW_noB n u).sym4.app hR)
      refine ⟨fun _ => ⟨u :: ds, ?_, rfl, ?_, hD.trans ?_⟩, fun hz => ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with e | e
        · rw [e]; omega
        · exact hds x e
      · simp only [valr]
        omega
      · have e2 : FWr n (u :: ds) ++ R = FWr n ds ++ (blkW n u ++ R) := by simp [FWr]
        rw [e2]
        exact hW
      · simp only [valr] at hz
        exact absurd hz (by omega)

end ZP
