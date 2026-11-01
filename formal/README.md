# Formal verification (Lean 4, Palomar layout)

This directory is a self-contained Lake project. It uses **core Lean only, no
Mathlib**: a clean CI build takes about a minute instead of the usual Mathlib
cache download and build. The layout follows the
[Palomar](https://palomar-registry.org/) template:

| file | role |
|---|---|
| `Challenge.lean` | the advertised statement (one deliberate `sorry`) |
| `Solution.lean` | the same declaration, proved from the development |
| `ZP/Defs.lean` | **trusted surface**: TMs, quasihalting, guest semantics (`ref/zp2_ref.py`), the Σ₂ sentence |
| `ZP/Table.lean` | the literal 278-state table, generated from `machines/zp_native.tbl` by `gen_table.py` |
| `ZP/Abstract.lean` | L4: the abstract program quasihalts ⟺ `Sentence` (**proved**) |
| `ZP/Bridge.lean` | macro simulation ⟹ same quasihalting (**proved**); the table has a macro simulation (**open, one `sorry`**) |
| `ZP/Checks.lean` | kernel-evaluated (`decide`) agreement with `ref/zp2_ref.py` on small cases |
| `comparator.json`, `formalization.yaml`, `LICENSE` | Palomar submission metadata |

The advertised theorem:

```lean
theorem ZP.zp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpMachine ↔ ZP.Sentence
```

The machine is Z_P v2, the 278-state native design (`docs/native.md`); until
2026-11 the development targeted the 1371-state v1 table.

`Sentence ↔ P = NP` is **not** formalized. It is the paper proof (`docs/native.md`, `docs/spec.md` §2),
and formalizing it needs a polynomial-time theory of TMs (Cook–Levin scale).

## Status
* CI (`.github/workflows/ci.yml`, job *Lean*) builds everything and prints a census of the
  open `sorry`s. It also checks that `ZP/Table.lean` matches the current `machines/zp_native.tbl`.
* The *Comparator* job runs `lake comparator` as Palomar does. It is marked
  `continue-on-error` and is **expected to fail** while `ZP.zp_macroSim` (`ZP/Bridge.lean`) has its
  `sorry`, because `sorryAx` is not a permitted axiom. Once it passes, the repository
  can be submitted at <https://submit.palomar-registry.org/> with config path
  `formal/comparator.json`.

## Local use
```bash
cd formal && lake build                 # needs elan; toolchain from lean-toolchain
./scripts/verify-comparator.sh          # needs bwrap
python3 gen_table.py                    # after python3 build.py changed machines/zp_native.tbl
```

## The open bridge (plan)
`ZP/Bridge.lean` reduces the bridge to one structure, `MacroSim zpMachine`: strictly
increasing times `time n`, one per abstract step, such that the table visits its beep
state in `[time n, time (n+1))` iff `absState n` is a refutation. The transfer of
quasihalting from such a simulation is proved. What remains is to construct it:

| Layer | Statement | Evidence today | Planned proof |
|---|---|---|---|
| N0 table | `ZP/Table.lean` is `machines/zp_native.txt` | CI regenerates and diffs it | done by construction |
| N1 merge | the table is the exact-merge quotient of the pair-compiled machine; the beep class is a singleton | `build.py` replays and checks the map | the class map (`native/exact_zp_native.json`) as a certificate checked by `decide`; a quotient agrees with the original on every run that avoids undefined transitions |
| N2 pair compile | each transition of the 4-symbol logical machine (129 states, `native/zp2.py`) is carried out by its 2-symbol gadget on the pair encoding `B=00 M=01 0=10 1=11` | `tests/test_native.py` (logical and compiled runs agree beep for beep) | one lemma per gadget shape (`KNOWN`, `KNOWNCELL`, `WRITESKIP`), plus a `decide`-checked map from compiled states to (logical state, phase) |
| N3 logical machine | from the layout `M_g J M_1 s M_2 C M_3 M B_R … M B_1` of pair `(J, s)` the logical machine reaches the layout of `absStep (J, s)`, beeping once iff `J` is wrong on `s`, and never meets an undefined transition | `tests/test_native.py`, `ref/zp2_ref.py` | segment lemmas: one guest step = the rotation walk; fuel odometer = clock `(|s|+2)^(|J|+2)-1`; certificate countdown = `inL`; outer loop = `absStep` |
| N4 abstract ⟺ `Sentence` | | **proved** (`ZP/Abstract.lean`) | |

Certificates must be checked by `decide` or `rfl` in the kernel. `native_decide` adds
the axiom `Lean.ofReduceBool`, which Palomar does not permit.
