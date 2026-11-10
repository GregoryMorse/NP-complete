module

public import ZP.AllDefs

@[expose] public section

/-!
# P and NP, in core Lean

The machine model is a one-tape Turing machine on the tape `ℕ` with blank `none`
and the bits `some false`, `some true`. It reads one of the three symbols, writes a
bit, and moves one cell (moving left at cell 0 stays at cell 0). The guest
semantics of `ZP/Defs.lean` have exactly this tape, so a guest code is such a
machine (`ZP/GuestTM.lean`).

* `exec M T q tape h` runs `M` for at most `T` steps (a halting step counts) and
  returns `some b` if it halts with answer `b`, `none` if the fuel runs out.
* `InP A`: some machine halts on every input `x` within `(|x|+2)^k` steps with
  the answer `A x`.
* `InNP A`: `A x` holds iff some certificate `c` with `|c| ≤ m·(|x|+2)^k` makes the
  verifier accept the pair tape of `x` and `c` within `(|x|+2)^k` steps. On that tape
  each bit `b` takes the two cells `1 b`, and `x` and `c` are each followed by `0 1`.
* `PeqNP`: the two classes are equal.

Any polynomial bound is dominated by some `(n+2)^k`, so these are the usual
classes.
-/

namespace ZP.Cx

/-- An action: halt with an answer, or write a bit, move, and change state. -/
inductive Act where
  | halt (b : Bool)
  | go (w : Bool) (right : Bool) (q : Nat)

/-- A machine: row `q` gives the actions on reading blank, `0`, `1`. Start state 0.
A state past the end of the table rejects. -/
structure Mach where
  tbl : List (Act × Act × Act)

def Mach.act (M : Mach) (q : Nat) (s : Option Bool) : Act :=
  match M.tbl[q]? with
  | none => .halt false
  | some (a0, a1, a2) =>
    match s with
    | none => a0
    | some false => a1
    | some true => a2

def write (tape : Nat → Option Bool) (h : Nat) (w : Bool) : Nat → Option Bool :=
  fun i => if i = h then some w else tape i

def move (right : Bool) (h : Nat) : Nat := if right then h + 1 else h - 1

/-- Run for at most `T` steps. -/
def exec (M : Mach) : Nat → Nat → (Nat → Option Bool) → Nat → Option Bool
  | 0, _, _, _ => none
  | T + 1, q, tape, h =>
    match M.act q (tape h) with
    | .halt b => some b
    | .go w r q' => exec M T q' (write tape h w) (move r h)

/-- The input tape. -/
def inTape (x : List Bool) : Nat → Option Bool := fun i => x[i]?

/-- Each bit `b` written as the two cells `1 b`. -/
def dbl (x : List Bool) : List Bool := x.flatMap fun b => [true, b]

/-- Input `x` and certificate `c`, each doubled and followed by the end mark `0 1`. -/
def pairTape (x c : List Bool) : Nat → Option Bool :=
  inTape (dbl x ++ false :: true :: (dbl c ++ [false, true]))

def InP (A : List Bool → Prop) : Prop :=
  ∃ (M : Mach) (k : Nat), ∀ x, ∃ b, exec M ((x.length + 2) ^ k) 0 (inTape x) 0 = some b ∧
    (b = true ↔ A x)

def InNP (A : List Bool → Prop) : Prop :=
  ∃ (V : Mach) (k m : Nat), ∀ x, A x ↔ ∃ c, c.length ≤ m * (x.length + 2) ^ k ∧
    exec V ((x.length + 2) ^ k) 0 (pairTape x c) 0 = some true

def PeqNP : Prop := ∀ A, InP A ↔ InNP A

/-! ## Basic facts -/

theorem exec_mono (M : Mach) : ∀ (T : Nat) (q : Nat) (tape : Nat → Option Bool) (h : Nat)
    (b : Bool), exec M T q tape h = some b → ∀ T', T ≤ T' → exec M T' q tape h = some b
  | 0, _, _, _, _, e, _, _ => by simp [exec] at e
  | T + 1, q, tape, h, b, e, T', hT => by
    obtain ⟨T', rfl⟩ : ∃ T'', T' = T'' + 1 := ⟨T' - 1, by omega⟩
    unfold exec at e ⊢
    split at e
    · exact e
    · exact exec_mono M T _ _ _ b e T' (by omega)

end ZP.Cx
