# A beeping busy beaver that quasihalts iff P = NP

An explicit 1-tape, 2-symbol Turing machine **Z_P** with a designated beep state such that

> **Z_P quasihalts (beeps only finitely often) on the blank tape ⟺ P = NP.**

| machine | states | file |
|---|---|---|
| **Z_P v2 (native design)** | **294** | `machines/zp_native.txt` (`docs/native.md`) |
| Z_P v1 (compiled from a counter machine; Lean-formalized statement) | 1371 | `machines/zp.txt` (SHA-256 in `machines/zp.json`) |
| Z_FACTOR (quasihalts iff integer factoring is in P) | 1909 | `machines/zfactor.txt` |
| Z_GI (quasihalts iff graph isomorphism is in P) | 3476 | `machines/zgi.txt` |
| Z_PP (quasihalts iff P = PP) | 1599 | `machines/zpp.txt` |
| Z_PSPACE (quasihalts iff P = PSPACE) | 1646 | `machines/zpspace.txt` |
| Z_coNP (quasihalts iff NP = coNP) | 1738 | `machines/zconp.txt` |
| Z_DLOG (quasihalts iff discrete log mod primes is in P) | 2958 | `machines/zdlog.txt` |
| Z_MUL (quasihalts iff multitape TMs multiply in linear time) | 3623 | `machines/zmul.txt` |
| Z_NTT (quasihalts iff the number-theoretic transform has linear-size linear circuits) | 6106 | `machines/zntt.txt` |
| twin-prime beeper (quasihalts iff finitely many twin primes) | 265 | `machines/twinprime.txt` |

Z_P v2 is designed directly as a tape machine (`native/`, spec `docs/native.md`) and is
tested beep-for-beep against its Python reference `ref/zp2_ref.py`. The other rows are
compiled from counter machines and are expected to drop once ported to the native design.
History is in `docs/history.md`.

**What is new and what is not.** That P = NP is a Σ₂ sentence, and that Σ₂ sentences can be
encoded as quasihalting, is folklore (Donat; da Costa–Doria; Aaronson's survey). The
contribution is the explicit, reproducible, state-counted table, the construction
machinery, and the validation. To our knowledge this is the first explicit machine for
P vs NP. That claim has not yet been checked against the bbchallenge Discord history.

**What this does not do.** Knowing BBB(n) does not settle P vs NP by simulation alone
(`docs/spec.md` §2, *Caution*). The equivalence has a paper proof (`docs/spec.md`). The
compiler is validated by tests at every layer. The Lean development (`formal/`, Palomar layout, core Lean only) states
`Quasihalts zpMachine ↔ Sentence` for the literal table. It proves the abstract layer and
leaves the table-simulation bridge open (one `sorry`). See `formal/README.md`.

## How it works (one paragraph)
L is a self-padded NP-complete language. An instance s *is* a guest program; s ∈ L iff
that program accepts some certificate c with rep(c) ≤ rep(s) within |s| steps. Z_P
enumerates candidate deciders J = 1, 2, …. For each instance s = 1, 2, … it computes
[s ∈ L] by brute force and runs J on s with clock (|s|+2)^{|J|}. On the first mismatch
it beeps and moves to J+1. A correct polynomial-time decider for L exists iff P = NP, and
by padding it eventually appears with a large enough clock. One guest interpreter serves
both as the brute-force checker and as the candidate executor. Spec and proofs:
[`docs/spec.md`](docs/spec.md).

## Pipeline
```
ref/zp_ref.py        executable specification (Python)
compiler/zp_cm.py    the same algorithm as a counter (Minsky) machine, ~177 instructions
compiler/regalloc.py must-zero analysis + register coalescing (41 virtual -> 17 physical)
compiler/tm.py       counter machine -> 2-symbol TM: unary register blocks, INC/DEC/move
                     templates, two-ended navigation, layout search, bisimulation
                     minimization with a protected beep state
build.py             reproducible build of all variants -> machines/
sim/tmsim.c, cmsim.c fast simulators
```

## Reproduce
```bash
python3 build.py                 # writes machines/*.txt|.tbl|.json|.cm (deterministic)
python3 tests/test_cm.py         # counter program vs reference
python3 tests/test_regalloc.py   # coalescing soundness (lockstep, phys = sum of class)
python3 tests/test_tm.py         # TM vs counter machine at every instruction boundary
python3 tests/test_truth.py      # FACTOR / DIGRAPH-ISO brute force vs reference
python3 tests/diff_tm_ref.py     # compiled TMs (C simulator) vs reference; needs gcc
cd formal && lake build          # Lean (CI does this on every push)
```

## Machine format
`machines/<name>.txt` holds one line. States are separated by `_` and numbered from 0 (the start
state). Each state is `w0M0n0,w1M1n1`: write w, move L/R, go to state n, on reading 0
and on reading 1. `---` marks an unreachable transition. The beep state's index is in the
`.json`. Machines are too large for single-letter state names, so states are decimal.

## Validation summary
See `docs/spec.md` §5. In brief:
- **Counter machine vs reference:** beep-for-beep agreement.
- **TM vs counter machine:** lockstep at every instruction boundary.
- **Controlled candidate lists:** exactly the predicted beeps, then silence.
- **P-language swaps:** beep-for-beep agreement.
- **Twin-prime beeper:** beeps exactly on the twin pairs.
- **Z_FACTOR, Z_GI:** the brute-force deciders agree with the reference on every instance
  up to the tested size. Both machines agree beep-for-beep with the reference prefix.
  The theorem for general A is in `docs/spec.md` §2.1.

## Layout
`docs/` spec and history · `formal/` Lean project (Palomar layout) ·
`machines/` build outputs · `tests/` · `ref/` · `compiler/` · `sim/`

## Credits
Gregory Morse (project brief, design decisions); construction, compiler and tests were
built with AI assistance (Claude).
