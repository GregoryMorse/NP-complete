module

@[expose] public section

/-!
# Definitions of the advertised statement

Everything the main theorem mentions is defined in this file, in core Lean only:

* `TM`, `TM.conf`, `Quasihalts`: one-tape two-symbol Turing machines with a
  designated beep state, run from the blank tape (Aaronson's beeping busy beaver
  convention: a machine *quasihalts* if it is in the beep state only finitely often).
* `run`, `inL`, `clock`, `Sentence`: the guest semantics of the native machine and
  the Σ₂ sentence of `docs/native.md`. These mirror `ref/zp2_ref.py` line for line.

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

/-! ## Guest programs (docs/native.md, ref/zp2_ref.py)

Bit strings are `List Bool` (`true` = 1). A code `P` is run on the cyclic string
`R = reverse P ++ [0]`. The entry at the front of `R` is parsed cyclically as
`w d 1^k 0`. -/

/-- Cyclic bit `i` of `R`. -/
def cyc (R : List Bool) (i : Nat) : Bool := R.getD (i % R.length) false

/-- Length of the run of 1s in `R` starting at cyclic position `i`, capped at `f`. -/
def onesFrom (R : List Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i => if cyc R i then onesFrom R f (i + 1) + 1 else 0

/-- The one-count `k` of the entry `w d 1^k 0` at the front of `R`. -/
def entryOnes (R : List Bool) : Nat := onesFrom R R.length 2

/-- `R` rotated past the entry at its front. -/
def rot (R : List Bool) : List Bool :=
  R.drop ((entryOnes R + 3) % R.length) ++ R.take ((entryOnes R + 3) % R.length)

/-- `n` rotations. -/
def rotN : Nat → List Bool → List Bool
  | 0, R => R
  | n + 1, R => rotN n (rot R)

/-- ι(blank, 0, 1) = 0, 1, 2. -/
def iota : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

/-- At most `T` guest steps; `true` = accept. Guest tape cells are `none` (blank)
or a bit; the head `h` is a natural number and a left move at cell 0 stays. -/
def runAux : Nat → List Bool → (Nat → Option Bool) → Nat → Bool
  | 0, _, _, _ => false
  | T + 1, R0, tape, h =>
    let R := rotN (iota (tape h)) R0
    if R.getD 2 false then
      runAux T (rotN (entryOnes R + 1) (rot R))
        (fun i => if i = h then some (R.getD 0 false) else tape i)
        (if R.getD 1 false then h + 1 else h - 1)
    else R.getD 0 false

/-- Guest program `P` on input `x` for at most `T` steps (a time-out rejects). -/
def run (P x : List Bool) (T : Nat) : Bool :=
  runAux T (rot (P.reverse ++ [false])) (fun i => x[i]?) 0

/-- All bit strings of length `n`. -/
def strings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (strings n).flatMap fun c => [false :: c, true :: c]

/-- `s ∈ L`: some certificate of length `|s|+1` makes program `s` accept within
`|s|+1` steps. -/
def inL (s : List Bool) : Bool :=
  (strings (s.length + 1)).any fun c => run s c (s.length + 1)

/-- Clock for candidate `J` on instance `s`: `(|s|+2)^(|J|+1) - 1`. -/
def clock (J s : List Bool) : Nat := (s.length + 2) ^ (J.length + 1) - 1

def strAux : Nat → Nat → List Bool → List Bool
  | 0, _, acc => acc
  | f + 1, N, acc => if N ≤ 1 then acc else strAux f (N / 2) ((N % 2 == 1) :: acc)

/-- The `N`-th bit string in shortlex order (`N ≥ 1`; `str 1 = []`): the binary
digits of `N` after its leading 1. Shortlex successor is `N + 1`. -/
def str (N : Nat) : List Bool := strAux N N []

/-- Candidate number `J` answers instance number `S` correctly within its clock. -/
def Correct (J S : Nat) : Prop :=
  run (str J) (str S) (clock (str J) (str S)) = inL (str S)

instance (J S : Nat) : Decidable (Correct J S) :=
  inferInstanceAs (Decidable (run (str J) (str S) (clock (str J) (str S)) = inL (str S)))

/-- The Σ₂ sentence of docs/native.md. On paper it is equivalent to P = NP. -/
def Sentence : Prop := ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → Correct J S

end ZP
