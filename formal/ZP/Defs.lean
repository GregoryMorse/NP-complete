module

@[expose] public section

/-!
# Definitions of the advertised statement

Everything the main theorem mentions is defined in this file, in core Lean only:

* `TM`, `TM.conf`, `Quasihalts`: one-tape two-symbol Turing machines with a
  designated beep state, run from the blank tape (Aaronson's beeping busy beaver
  convention: a machine *quasihalts* if it is in the beep state only finitely often).
* `run`, `inL`, `clock`, `Sentence`: the guest "offset machine" semantics and the
  Σ₂ sentence S of `docs/spec.md` (§1). These mirror `ref/zp_ref.py` line for line.

All recursions are structural on an explicit fuel argument, so every function is
total and can be evaluated by the kernel.
-/

namespace ZP

/-! ## Host Turing machines -/

/-- A machine is a table of rows `(code on 0, code on 1)`, start state 0, and a
beep state. A transition code is `0` (undefined: the machine halts) or
`1 + w + 2*d + 4*q'`: write `w`, move right if `d = 1` and left if `d = 0`, then go to
state `q'`. A state past the end of the table also halts. -/
structure TM where
  table : List (Nat × Nat)
  beep  : Nat

/-- Configuration: state, tape (`true` = 1), head position. -/
structure Conf where
  q    : Nat
  tape : Int → Bool
  head : Int

/-- One step; `none` means the machine has halted. -/
def TM.step (M : TM) (c : Conf) : Option Conf :=
  match M.table[c.q]? with
  | none => none
  | some (c0, c1) =>
    let code := if c.tape c.head then c1 else c0
    if code = 0 then none
    else
      let x := code - 1
      some { q := x / 4
             tape := fun i => if i = c.head then decide (x % 2 = 1) else c.tape i
             head := if (x / 2) % 2 = 1 then c.head + 1 else c.head - 1 }

/-- Configuration after `k` steps from the blank tape (`none` once halted). -/
def TM.conf (M : TM) : Nat → Option Conf
  | 0 => some ⟨0, fun _ => false, 0⟩
  | k + 1 => (M.conf k).bind M.step

/-- The machine is in its beep state at only finitely many times. -/
def Quasihalts (M : TM) : Prop :=
  ∃ N, ∀ k, N ≤ k → ∀ c, M.conf k = some c → c.q ≠ M.beep

/-! ## Guest offset machines (docs/spec.md §1, ref/zp_ref.py) -/

/-- `|s|` for `N = rep(s) = int('1' ++ s, 2)`. -/
def len (N : Nat) : Nat := Nat.log2 N

/-- Right stack for input `X = rep(c)`: `c = b₁…bₘ` is written `1 b₁ 1 b₂ … 1 bₘ`
from the head cell (least significant bit = head cell). -/
def encAux : Nat → Nat → Nat → Nat
  | 0, _, R => R
  | fuel + 1, X, R => if X ≤ 1 then R else encAux fuel (X / 2) (2 * (2 * R + X % 2) + 1)

def encodeInput (X : Nat) : Nat := encAux X X 0

/-- Entry number `idx` of the code `P`, read from the least significant bit:
entries are unary `1^e 0`; the result is `(w, d, k)` with `e = 4k + 2d + w`, or
`none` if the code ends first. -/
def lookupAux : Nat → Nat → Nat → Nat → Option (Nat × Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, pc, idx, e =>
    if pc ≤ 1 then none
    else if pc % 2 = 1 then lookupAux fuel (pc / 2) idx (if idx = 0 then e + 1 else e)
    else if idx = 0 then some (e % 2, (e / 2) % 2, e / 4)
    else lookupAux fuel (pc / 2) (idx - 1) e

def lookup (P idx : Nat) : Option (Nat × Nat × Nat) := lookupAux P P idx 0

inductive Out | acc | rej | timeout
  deriving DecidableEq, Repr

/-- `t` guest steps. `R`: head cell and the cells to its right, `Lt`: the cells to its
left (nearest = least significant bit), `q`: offset. -/
def runAux (P : Nat) : Nat → Nat → Nat → Nat → Out
  | 0, _, _, _ => .timeout
  | t + 1, R, Lt, q =>
    match lookup P (q + R % 2) with
    | none => .rej
    | some (w, d, k) =>
      if k = 0 then (if w = 1 then .acc else .rej)
      else if d = 1 then runAux P t (R / 2) (2 * Lt + w) (k - 1)
      else runAux P t (2 * (2 * (R / 2) + w) + Lt % 2) (Lt / 2) (k - 1)

/-- Guest program `P` on input `X` for at most `t` steps. -/
def run (P X t : Nat) : Out := runAux P t (encodeInput X) 0 0

/-- `S ∈ L`: some certificate `1 ≤ C ≤ S` makes program `S` accept within `|S|` steps. -/
def inL (S : Nat) : Bool :=
  (List.range S).any fun c => run S (c + 1) (len S) == .acc

def verdict (S : Nat) : Out := if inL S then .acc else .rej

/-- Clock for candidate `J` on instance `S`: `(|s| + 2) ^ |code(J)|`. -/
def clock (J S : Nat) : Nat := (len S + 2) ^ len J

/-- Candidate `J` answers instance `S` correctly within its clock. -/
def Correct (J S : Nat) : Prop := run J S (clock J S) = verdict S

instance (J S : Nat) : Decidable (Correct J S) :=
  inferInstanceAs (Decidable (run J S (clock J S) = verdict S))

/-- The Σ₂ sentence S of docs/spec.md. On paper (docs/spec.md §2) S ⟺ P = NP. -/
def Sentence : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → Correct J S

end ZP
