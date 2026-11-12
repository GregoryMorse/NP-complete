#!/usr/bin/env python3
"""Write ZP/Compile<SUF>.lean for a generated machine (python3 scripts/gen_compile.py name SUF slots).
The file is the compilation certificate of `<name>Logic` against `<name>Machine`, in the
shape of ZP/CompileBPP.lean."""
import sys
name, suf, slots = sys.argv[1], sys.argv[2], int(sys.argv[3])
desc = sys.argv[4] if len(sys.argv) > 4 else name
chunks = [(32 * i, 32) for i in range(slots // 32)]
if slots % 32:
    chunks.append((32 * (slots // 32), slots % 32))
out = [f'''module

public import ZP.Compile
public import ZP.Logic{suf}
public import ZP.AllDefs

@[expose] public section

/-! The certificate of the {desc} machine: the table simulates `{name}Logic` gadget by gadget. -/

namespace ZP

def {name}Cert : Cert := ⟨{name}Logic, {name}Machine, {name}Entry, {name}Side, {name}Glen⟩
''']
for i, (a, b) in enumerate(chunks):
    out.append(f'theorem {name}Chk{i} : Cert.allFrom {a} {b} (Cert.checkQ {name}Cert) = true := by decide +kernel')
out.append(f'''
theorem {name}Logic_len : {name}Logic.table.length = {slots} := by decide +kernel

def {name}BeepOK : Bool :=
  Cert.allFrom 0 {slots} fun q =>
    decide ((Cert.cEntry {name}Cert q = {name}Machine.beep) ↔ (q = {name}Logic.beep))

theorem {name}BeepOK_true : {name}BeepOK = true := by decide +kernel

theorem {name}Cert_ok : {name}Cert.OK where
  chk q hq := by
    have hq' : q < {slots} := by
      have : {name}Cert.L.table.length = {slots} := {name}Logic_len
      omega''')
def nest(i, ind):
    a, b = chunks[i]
    sp = ' ' * ind
    if i == len(chunks) - 1:
        return [f'{sp}exact Cert.allFrom_spec _ _ {a} q {name}Chk{i} (by omega) (by omega)']
    r = [f'{sp}by_cases h{i} : q < {a + b}',
         f'{sp}· exact Cert.allFrom_spec _ _ {a} q {name}Chk{i} (by omega) (by omega)']
    sub = nest(i + 1, ind + 2)
    r.append(f'{sp}· ' + sub[0].lstrip())
    r += sub[1:]
    return r
out += nest(0, 4)
out.append(f'''  beep q hq := by
    have hq' : q < {slots} := by
      have : {name}Cert.L.table.length = {slots} := {name}Logic_len
      omega
    exact of_decide_eq_true (Cert.allFrom_spec _ _ 0 q {name}BeepOK_true (by omega) (by omega))
  e0 := by decide +kernel
  s0 := by decide +kernel

/-- A macro simulation of the abstract program of `C` by `{name}Logic` gives one by the table. -/
def {name}MacroSimC {{C : Nat → Nat → Prop}} [∀ J S, Decidable (C J S)]
    (S : LMacroSimC C {name}Logic) : MacroSimC C {name}Machine :=
  Cert.macroSimC_of_logic {name}Cert {name}Cert_ok S

end ZP
''')
open(f'ZP/Compile{suf}.lean', 'w').write('\n'.join(out))
