module

public import ZP.Defs
public import ZP.Table

public section

/-!
# Advertised statement

`ZP.zpMachine` is the literal 2-symbol table `machines/zp_native.txt` (278 states,
`ZP/Table.lean`, generated from the build output). `ZP.Quasihalts` and `ZP.Sentence` are defined in
`ZP/Defs.lean`. Those two files are the whole trusted surface, in core Lean only.

The claim: run from the blank tape, the machine is in its beep state only finitely
often iff some candidate guest program `J` decides the language `L` correctly on
every instance within the clock `(|s|+2)^(|J|+1) - 1`.

The further equivalence `ZP.Sentence ↔ P = NP` is proved on paper
(`docs/native.md`, `docs/spec.md` §2) and is **not** part of this statement.
-/

theorem ZP.zp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpMachine ↔ ZP.Sentence := by
  sorry
