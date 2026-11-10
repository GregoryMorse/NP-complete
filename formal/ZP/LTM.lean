module

public import ZP.AllDefs
public import ZP.Abstract

@[expose] public section

/-!
# Four-symbol logical machines

The native table is compiled from a 4-symbol *logical* machine (`native/zp2.py`).
Symbols are numbered `B = 0`, `M = 1`, `'0' = 2`, `'1' = 3`; the compiler stores
symbol `s` as the two cells `(s / 2, s % 2)`.

A logical transition code is `0` (undefined) or `1 + w + 4*d + 8*q'`: write `w`,
move right if `d = 1`, go to `q'`.

`LMacroSim L` is a macro simulation of the abstract program by `L` that also
records that `L` never halts. `ZP/Compile.lean` turns one for `zpLogic` into a
`MacroSim` of the table.
-/

namespace ZP

structure LTM where
  table : List (List Nat)
  beep  : Nat

structure LConf where
  q    : Nat
  tape : Int → Nat
  head : Int

def LTM.step (L : LTM) (c : LConf) : Option LConf :=
  match L.table[c.q]? with
  | none => none
  | some row =>
    let code := row.getD (c.tape c.head) 0
    if code = 0 then none
    else
      some { q := (code - 1) / 8
             tape := fun i => if i = c.head then (code - 1) % 4 else c.tape i
             head := if (code - 1) / 4 % 2 = 1 then c.head + 1 else c.head - 1 }

/-- Configuration after `k` steps from the blank tape, start state 0. -/
def LTM.conf (L : LTM) : Nat → Option LConf
  | 0 => some ⟨0, fun _ => 0, 0⟩
  | k + 1 => (L.conf k).bind L.step

/-- A beep-exact simulation of the abstract program of `C` by a logical machine that never
halts. -/
structure LMacroSimC (C : Nat → Nat → Prop) [∀ J S, Decidable (C J S)] (L : LTM) where
  time : Nat → Nat
  mono : ∀ n, time n < time (n + 1)
  total : ∀ k, ∃ c, L.conf k = some c
  beeps : ∀ n,
    (∃ k, time n ≤ k ∧ k < time (n + 1) ∧ ∃ c, L.conf k = some c ∧ c.q = L.beep) ↔
      ¬ C (absStateC C n).1 (absStateC C n).2

abbrev LMacroSim (L : LTM) : Type := LMacroSimC Correct L

end ZP
