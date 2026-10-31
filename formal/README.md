# Formal verification (Lean 4, Palomar layout)

This directory is a self-contained Lake project. It uses **core Lean only, no
Mathlib**: a clean CI build takes about a minute instead of the usual Mathlib
cache download and build. The layout follows the
[Palomar](https://palomar-registry.org/) template:

| file | role |
|---|---|
| `Challenge.lean` | the advertised statement (one deliberate `sorry`) |
| `Solution.lean` | the same declaration, proved from the development |
| `ZP/Defs.lean` | **trusted surface**: TMs, quasihalting, guest semantics, the Σ₂ sentence |
| `ZP/Table.lean` | the literal table, generated from `machines/zp.tbl` by `gen_table.py` |
| `ZP/Abstract.lean` | L4: the abstract program quasihalts ⟺ `Sentence` (**proved**) |
| `ZP/Bridge.lean` | L0–L3: the table simulates the abstract program (**open, one `sorry`**) |
| `ZP/Checks.lean` | kernel-evaluated (`decide`) agreement with `ref/zp_ref.py` on small cases |
| `comparator.json`, `formalization.yaml`, `LICENSE` | Palomar submission metadata |

The advertised theorem:

```lean
theorem ZP.zp_quasihalts_iff_sentence : ZP.Quasihalts ZP.zpMachine ↔ ZP.Sentence
```

`Sentence ↔ P = NP` is **not** formalized. It is the paper proof in `docs/spec.md` §2,
and formalizing it needs a polynomial-time theory of TMs (Cook–Levin scale).

## Status
* CI (`.github/workflows/ci.yml`, job *Lean*) builds everything and prints a census of the
  open `sorry`s. It also checks that `ZP/Table.lean` matches the current `machines/zp.tbl`.
* The *Comparator* job runs `lake comparator` as Palomar does. It is marked
  `continue-on-error` and is **expected to fail** while `ZP/Bridge.lean` has its
  `sorry`, because `sorryAx` is not a permitted axiom. Once it passes, the repository
  can be submitted at <https://submit.palomar-registry.org/> with config path
  `formal/comparator.json`.

## Local use
```bash
cd formal && lake build                 # needs elan; toolchain from lean-toolchain
./scripts/verify-comparator.sh          # needs bwrap
python3 gen_table.py                    # after python3 build.py changed machines/zp.tbl
```

## The open bridge (plan)
Quasihalting must be preserved, not just halting, so every layer proves a
*beep-exact* simulation: every macro step terminates and emits exactly the beeps of the
step it simulates (progress obligations (a)–(c) of `docs/spec.md`).

| Layer | Statement | Evidence today | Planned proof |
|---|---|---|---|
| L0 table | `ZP/Table.lean` is `machines/zp.txt` | CI regenerates and diffs it | done by construction |
| L1 templates | each counter instruction is implemented by its TM template, from a well-formed register tape with the head on E | lockstep test `tests/test_tm.py` | one symbolic lemma per template shape (INC, DEC-last, DEC-twopass, DEC-carry, MOVE-adj, navigation), plus a generated certificate mapping every state to (instruction, template, phase), checked by `decide` |
| L1′ inlining + minimization | the shipped table is bisimilar to the template machine, beep visits one-for-one | `tests/test_tm.py` | generated partition certificate checked by `decide`; the beep class is a singleton |
| L2 coalescing | the physical counter program simulates the virtual one with phys = Σ class | `tests/test_regalloc.py` | the must-zero sets are emitted as a certificate; the kernel checks it is an inductive invariant |
| L3 counter program ⟺ abstract | same beeps; every loop terminates | `tests/diff_tm_ref.py` | loop-by-loop ranking functions |
| L4 abstract ⟺ `Sentence` | | **proved** (`ZP/Abstract.lean`) | |

Certificates must be checked by `decide` or `rfl` in the kernel. `native_decide` adds
the axiom `Lean.ofReduceBool`, which Palomar does not permit.
