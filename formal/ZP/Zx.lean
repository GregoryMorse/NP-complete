module

public import ZP.GuestTM

@[expose] public section

/-!
# Machines on zipper tapes

`zexec M T q L R` runs `M` on the tape whose cells left of the head are `L`
(nearest first), whose cells from the head rightward are `R`, and whose cells after
`R` are blank. `exec_z` links it to `exec`. `Lead M q L R q' L' R' T` says that `T`
steps lead from `(q, L, R)` to `(q', L', R')`; `Sub M base rows` says that the table
of `M` holds `rows` from state `base` on. The step lemmas `Lead.pR`, `Lead.pL`,
`Lead.pL0` read a row off `rows` by `rfl`; the tactic `zs` applies one of them.
-/

namespace ZP.Cx

def zexec (M : Mach) : Nat → Nat → List Bool → List Bool → Option Bool
  | 0, _, _, _ => none
  | T + 1, q, L, R =>
    match M.act q R.head? with
    | .halt b => some b
    | .go w true q' => zexec M T q' (w :: L) R.tail
    | .go w false q' =>
      match L with
      | [] => zexec M T q' [] (w :: R.tail)
      | b :: l => zexec M T q' l (b :: w :: R.tail)

def ztape (L R : List Bool) : Nat → Option Bool := fun i => (L.reverse ++ R)[i]?

theorem ztape_head (L R : List Bool) : ztape L R L.length = R.head? := by
  unfold ztape
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_reverse, Nat.sub_self]
  cases R <;> rfl

theorem ztape_shift (L : List Bool) (w : Bool) (X : List Bool) :
    ztape (w :: L) X = ztape L (w :: X) := by
  unfold ztape
  simp

theorem ztape_write (L R : List Bool) (w : Bool) :
    write (ztape L R) L.length w = ztape L (w :: R.tail) := by
  funext i
  unfold write ztape
  by_cases h : i = L.length
  · subst h
    rw [if_pos rfl, List.getElem?_append_right (by simp)]
    simp
  · rw [if_neg h]
    rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getElem?_append_left (by simpa using h1),
        List.getElem?_append_left (by simpa using h1)]
    · rw [List.getElem?_append_right (by simp; omega),
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_reverse]
      obtain ⟨j, hj⟩ : ∃ j, i - L.length = j + 1 := ⟨i - L.length - 1, by omega⟩
      rw [hj]
      cases R <;> simp

theorem exec_go {M : Mach} {T q : Nat} {tape : Nat → Option Bool} {hd : Nat} {w r : Bool}
    {q' : Nat} (h : M.act q (tape hd) = .go w r q') :
    exec M (T + 1) q tape hd = exec M T q' (write tape hd w) (move r hd) := by
  rw [exec_succ, h]

theorem exec_halt {M : Mach} {T q : Nat} {tape : Nat → Option Bool} {hd : Nat} {b : Bool}
    (h : M.act q (tape hd) = .halt b) : exec M (T + 1) q tape hd = some b := by
  rw [exec_succ, h]

theorem zexec_goR {M : Mach} {T q : Nat} {L R : List Bool} {w : Bool} {q' : Nat}
    (h : M.act q R.head? = .go w true q') :
    zexec M (T + 1) q L R = zexec M T q' (w :: L) R.tail := by
  show (match M.act q R.head? with
    | .halt b => some b
    | .go w true q' => zexec M T q' (w :: L) R.tail
    | .go w false q' =>
      match L with
      | [] => zexec M T q' [] (w :: R.tail)
      | b :: l => zexec M T q' l (b :: w :: R.tail)) = _
  rw [h]

theorem zexec_goL0 {M : Mach} {T q : Nat} {R : List Bool} {w : Bool} {q' : Nat}
    (h : M.act q R.head? = .go w false q') :
    zexec M (T + 1) q [] R = zexec M T q' [] (w :: R.tail) := by
  show (match M.act q R.head? with
    | .halt b => some b
    | .go w true q' => zexec M T q' (w :: []) R.tail
    | .go w false q' => zexec M T q' [] (w :: R.tail)) = _
  rw [h]

theorem zexec_goL {M : Mach} {T q : Nat} {b : Bool} {l R : List Bool} {w : Bool} {q' : Nat}
    (h : M.act q R.head? = .go w false q') :
    zexec M (T + 1) q (b :: l) R = zexec M T q' l (b :: w :: R.tail) := by
  show (match M.act q R.head? with
    | .halt b => some b
    | .go w true q' => zexec M T q' (w :: b :: l) R.tail
    | .go w false q' => zexec M T q' l (b :: w :: R.tail)) = _
  rw [h]

theorem zexec_halt {M : Mach} {T q : Nat} {L R : List Bool} {b : Bool}
    (h : M.act q R.head? = .halt b) : zexec M (T + 1) q L R = some b := by
  show (match M.act q R.head? with
    | .halt b => some b
    | .go w true q' => zexec M T q' (w :: L) R.tail
    | .go w false q' =>
      match L with
      | [] => zexec M T q' [] (w :: R.tail)
      | b :: l => zexec M T q' l (b :: w :: R.tail)) = _
  rw [h]

theorem exec_z (M : Mach) : ∀ (T q : Nat) (L R : List Bool),
    exec M T q (ztape L R) L.length = zexec M T q L R
  | 0, _, _, _ => rfl
  | T + 1, q, L, R => by
    cases hA : M.act q R.head? with
    | halt b =>
      have h1 : M.act q (ztape L R L.length) = .halt b := by rw [ztape_head]; exact hA
      rw [exec_halt h1, zexec_halt hA]
    | go w r q' =>
      have h1 : M.act q (ztape L R L.length) = .go w r q' := by rw [ztape_head]; exact hA
      rw [exec_go h1, ztape_write]
      cases r with
      | true =>
        rw [zexec_goR hA, ← ztape_shift]
        exact exec_z M T q' (w :: L) R.tail
      | false =>
        cases L with
        | nil =>
          rw [zexec_goL0 hA]
          exact exec_z M T q' [] (w :: R.tail)
        | cons b l =>
          rw [zexec_goL hA, ztape_shift]
          exact exec_z M T q' l (b :: w :: R.tail)

theorem inTape_z (x : List Bool) : inTape x = ztape [] x := by
  funext i
  simp [inTape, ztape]

/-! ## Leads -/

def Lead (M : Mach) (q : Nat) (L R : List Bool) (q' : Nat) (L' R' : List Bool) (T : Nat) :
    Prop :=
  ∀ F, zexec M (T + F) q L R = zexec M F q' L' R'

theorem Lead.refl {M : Mach} {q : Nat} {L R : List Bool} : Lead M q L R q L R 0 :=
  fun F => by rw [Nat.zero_add]

theorem Lead.trans {M : Mach} {q q1 q2 : Nat} {L R L1 R1 L2 R2 : List Bool} {T1 T2 : Nat}
    (h1 : Lead M q L R q1 L1 R1 T1) (h2 : Lead M q1 L1 R1 q2 L2 R2 T2) :
    Lead M q L R q2 L2 R2 (T1 + T2) :=
  fun F => by rw [Nat.add_assoc, h1, h2]

theorem Lead.cast {M : Mach} {q q' : Nat} {L R L' R' : List Bool} {T T' : Nat}
    (h : Lead M q L R q' L' R' T) (e : T = T') : Lead M q L R q' L' R' T' := e ▸ h

theorem Lead.halts {M : Mach} {q q' : Nat} {L R L' R' : List Bool} {T : Nat} {b : Bool}
    (h1 : Lead M q L R q' L' R' T) (h2 : M.act q' R'.head? = .halt b) :
    ∀ F, T < F → zexec M F q L R = some b := by
  intro F hF
  obtain ⟨G, rfl⟩ : ∃ G, F = T + (G + 1) := ⟨F - T - 1, by omega⟩
  rw [h1]
  exact zexec_halt h2

/-! ## Rows of a table -/

def pick (a : Act × Act × Act) (s : Option Bool) : Act :=
  match s with
  | none => a.1
  | some false => a.2.1
  | some true => a.2.2

def Sub (M : Mach) (base : Nat) (rows : List (Act × Act × Act)) : Prop :=
  ∀ j r, rows[j]? = some r → M.tbl[base + j]? = some r

theorem Sub.act {M : Mach} {base : Nat} {rows : List (Act × Act × Act)} (hs : Sub M base rows)
    {j : Nat} {r : Act × Act × Act} (h : rows[j]? = some r) (s : Option Bool) :
    M.act (base + j) s = pick r s := by
  unfold Mach.act
  rw [hs j r h]
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

theorem Sub.left {M : Mach} {base : Nat} {A B : List (Act × Act × Act)} (hs : Sub M base (A ++ B)) :
    Sub M base A := fun j r h => hs j r (by
  have hj : j < A.length := by
    rcases Nat.lt_or_ge j A.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.getElem?_append_left hj]
  exact h)

theorem Sub.right {M : Mach} {base : Nat} {A B : List (Act × Act × Act)}
    (hs : Sub M base (A ++ B)) : Sub M (base + A.length) B := fun j r h => by
  have := hs (A.length + j) r (by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact h)
  rwa [Nat.add_assoc]

theorem Sub.act' {M : Mach} {base : Nat} {rows : List (Act × Act × Act)} (hs : Sub M base rows)
    {j : Nat} {s : Option Bool} {a : Act} (h : (rows[j]?).map (fun r => pick r s) = some a) :
    M.act (base + j) s = a := by
  cases hr : rows[j]? with
  | none => rw [hr] at h; cases h
  | some r =>
    rw [hr] at h
    rw [hs.act hr]
    exact Option.some.inj h

theorem Lead.pR {M : Mach} {base j : Nat} {rows : List (Act × Act × Act)} {L R L2 R2 : List Bool}
    {w : Bool} {q' q2 T : Nat} (hs : Sub M base rows)
    (h : (rows[j]?).map (fun r => pick r R.head?) = some (.go w true q'))
    (rest : Lead M q' (w :: L) R.tail q2 L2 R2 T) : Lead M (base + j) L R q2 L2 R2 (T + 1) :=
  fun F => by
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goR (hs.act' h)]
    exact rest F

theorem Lead.pL {M : Mach} {base j : Nat} {rows : List (Act × Act × Act)} {b : Bool}
    {l R L2 R2 : List Bool} {w : Bool} {q' q2 T : Nat} (hs : Sub M base rows)
    (h : (rows[j]?).map (fun r => pick r R.head?) = some (.go w false q'))
    (rest : Lead M q' l (b :: w :: R.tail) q2 L2 R2 T) :
    Lead M (base + j) (b :: l) R q2 L2 R2 (T + 1) :=
  fun F => by
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL (hs.act' h)]
    exact rest F

theorem Lead.pL0 {M : Mach} {base j : Nat} {rows : List (Act × Act × Act)}
    {R L2 R2 : List Bool} {w : Bool} {q' q2 T : Nat} (hs : Sub M base rows)
    (h : (rows[j]?).map (fun r => pick r R.head?) = some (.go w false q'))
    (rest : Lead M q' [] (w :: R.tail) q2 L2 R2 T) : Lead M (base + j) [] R q2 L2 R2 (T + 1) :=
  fun F => by
    rw [show T + 1 + F = (T + F) + 1 by omega, zexec_goL0 (hs.act' h)]
    exact rest F

set_option hygiene false in
/-- One step of a gadget whose rows are `Sub M base _` under the name `hs`. -/
macro "zs" : tactic => `(tactic| first
  | (refine Lead.pR hs ?_ ?_; rfl)
  | (refine Lead.pL hs ?_ ?_; rfl)
  | (refine Lead.pL0 hs ?_ ?_; rfl)
  | (refine Lead.pR (j := 0) hs ?_ ?_; rfl)
  | (refine Lead.pL (j := 0) hs ?_ ?_; rfl)
  | (refine Lead.pL0 (j := 0) hs ?_ ?_; rfl))

/-! ## Common rows -/

abbrev H : Act := .halt false

/-- Write back the scanned bit and move. -/
def same (right : Bool) (q : Nat) : Act × Act × Act := (H, .go false right q, .go true right q)

/-! ## Return to cell 0

The left end is found by a probe. At cell `h` with bits `a a'` at `h, h+1`: write
`1 0`, step left and right again. If `h > 0` the head is back on the `1`; if `h = 0`
the left move stayed, and the head is on the `0` at cell 1. Then `a a'` are put back.
-/

def bn (b : Bool) : Nat := if b then 1 else 0

def retRows (s exit : Nat) : List (Act × Act × Act) :=
  [ (H, .go true true (s + 1), .go true true (s + 2)),                       -- 0
    (H, .go false false (s + 3), .go false false (s + 4)),                   -- 1: a = 0
    (H, .go false false (s + 5), .go false false (s + 6)),                   -- 2: a = 1
    (H, .go true false (s + 7), .go true false (s + 7)),                     -- 3..6
    (H, .go true false (s + 8), .go true false (s + 8)),
    (H, .go true false (s + 9), .go true false (s + 9)),
    (H, .go true false (s + 10), .go true false (s + 10)),
    (H, .go false true (s + 11), .go true true (s + 11)),                    -- 7..10
    (H, .go false true (s + 12), .go true true (s + 12)),
    (H, .go false true (s + 13), .go true true (s + 13)),
    (H, .go false true (s + 14), .go true true (s + 14)),
    (H, .go false false (s + 17), .go false true (s + 15)),                  -- 11: a a' = 0 0
    (H, .go true false (s + 17), .go false true (s + 16)),                   -- 12: 0 1
    (H, .go false false (s + 18), .go true true (s + 15)),                   -- 13: 1 0
    (H, .go true false (s + 18), .go true true (s + 16)),                    -- 14: 1 1
    (H, .go false false (s + 19), .go false false (s + 19)),                 -- 15: a' = 0
    (H, .go true false (s + 19), .go true false (s + 19)),                   -- 16: a' = 1
    (H, .go false false exit, .go false false exit),                         -- 17: a = 0
    (H, .go true false exit, .go true false exit),                           -- 18: a = 1
    same false s ]                                                           -- 19

theorem ret_step {M : Mach} {base exit : Nat} (hs : Sub M base (retRows base exit))
    (a a' c : Bool) (l rest : List Bool) :
    Lead M base (c :: l) (a :: a' :: rest) base l (c :: a :: a' :: rest) 7 := by
  cases a <;> cases a' <;> cases c <;> (zs; zs; zs; zs; zs; zs; zs; exact Lead.refl)

theorem ret_end {M : Mach} {base exit : Nat} (hs : Sub M base (retRows base exit))
    (a a' : Bool) (rest : List Bool) :
    Lead M base [] (a :: a' :: rest) exit [] (a :: a' :: rest) 6 := by
  cases a <;> cases a' <;> (zs; zs; zs; zs; zs; zs; exact Lead.refl)

/-- From any cell with a written right neighbour, `retRows` returns to cell 0 and
restores the tape. -/
theorem ret {M : Mach} {base exit : Nat} (hs : Sub M base (retRows base exit)) :
    ∀ (L : List Bool) (a a' : Bool) (rest : List Bool),
      Lead M base L (a :: a' :: rest) exit [] (L.reverse ++ a :: a' :: rest) (7 * L.length + 6)
  | [], a, a', rest => ret_end hs a a' rest
  | c :: l, a, a', rest => by
    have h := (ret_step hs a a' c l rest).trans (ret l c a (a' :: rest))
    have e : (c :: l).reverse ++ a :: a' :: rest = l.reverse ++ c :: a :: a' :: rest := by simp
    rw [e]
    exact h.cast (by simp only [List.length_cons]; omega)

end ZP.Cx
