/-
  ZP.lean — Tier-1 skeleton (UNCHECKED DRAFT: not yet compiled, see README).

  Core Lean 4 only (no Mathlib).  Definitions follow docs/spec.md.
-/

namespace ZP

/-! ## Turing machines with a designated beep state -/

inductive Dir | L | R

structure Tr (n : Nat) where
  write : Bool
  dir   : Dir
  next  : Fin n

/-- `delta q a = none` is an undefined (never reached) transition. -/
structure TM where
  n     : Nat
  delta : Fin n → Bool → Option (Tr n)
  start : Fin n
  beep  : Fin n

structure Conf (M : TM) where
  q    : Fin M.n
  tape : Int → Bool
  head : Int

def Conf.init (M : TM) : Conf M := ⟨M.start, fun _ => false, 0⟩

def step (M : TM) (c : Conf M) : Option (Conf M) :=
  match M.delta c.q (c.tape c.head) with
  | none => none
  | some t =>
    some { q := t.next
           tape := fun i => if i = c.head then t.write else c.tape i
           head := match t.dir with | .L => c.head - 1 | .R => c.head + 1 }

/-- configuration after `k` steps (stays put once undefined). -/
def run (M : TM) : Nat → Conf M
  | 0 => Conf.init M
  | k + 1 => (step M (run M k)).getD (run M k)

/-- Aaronson's convention: the beep state is entered only finitely often. -/
def Quasihalts (M : TM) : Prop :=
  ∃ N, ∀ k, N ≤ k → (run M k).q ≠ M.beep

/-! ## Counter machines -/

inductive Ins (r : Nat) (n : Nat)
  | inc  (reg : Fin r) (nxt : Fin n)
  | dec  (reg : Fin r) (nz z : Fin n)
  | beep (nxt : Fin n)

structure CM where
  r : Nat
  n : Nat
  code  : Fin n → Ins r n
  entry : Fin n

/-! ## The abstract program (spec §1.5) -/

def len (N : Nat) : Nat := Nat.log2 N

/-- offset-machine interpreter, `none` = TIMEOUT, `some b` = ACC/REJ. -/
opaque runGuest (P X t : Nat) : Option Bool

/-- membership in L (bounded search over certificates 1..S) -/
def inL (S : Nat) : Bool :=
  (List.range S).any (fun c => runGuest S (c + 1) (len S) == some true)

def clock (J S : Nat) : Nat := (len S + 2) ^ len J

/-- The Σ₂ sentence S of the spec. -/
def Sentence : Prop :=
  ∃ J, 1 ≤ J ∧ ∀ S, 1 ≤ S → runGuest J S (clock J S) = some (inL S)

/-! ## Statements to prove (Tier 1) -/

/-- the literal machine, generated from machines/zp.txt -/
opaque zp : TM

/-- abstract program beeps finitely often -/
opaque AbstractQuasihalts : Prop

theorem abstract_iff_sentence : AbstractQuasihalts ↔ Sentence := by
  sorry

theorem zp_iff_abstract : Quasihalts zp ↔ AbstractQuasihalts := by
  sorry -- layers L0–L3 of formal/README.md

theorem zp_iff_sentence : Quasihalts zp ↔ Sentence :=
  zp_iff_abstract.trans abstract_iff_sentence

end ZP
