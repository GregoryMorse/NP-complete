# A beeping busy beaver that quasihalts iff P = NP

An explicit 1-tape, 2-symbol Turing machine **Z_P** with a designated beep state such that

> **Z_P quasihalts (beeps only finitely often) on the blank tape ⟺ P = NP.**

| machine | states | file |
|---|---|---|
| **Z_P v2 (native design; Lean-formalized statement)** | **278** | `machines/zp_native.txt` (`docs/native.md`) |
| Z_P v1 (compiled from a counter machine) | 1371 | `machines/zp.txt` (SHA-256 in `machines/zp.json`) |
| **Z_FACTOR native (quasihalts iff integer factoring is in P)** | **324** | `machines/zfactor_native.txt` (`native/zfac.py`, ref `ref/zfac_ref.py`) |
| Z_FACTOR (counter-machine compile) | 1909 | `machines/zfactor.txt` |
| **Z_GI native (quasihalts iff graph isomorphism is in P)** | **415** | `machines/zgi_native.txt` (`native/zgi.py`, ref `ref/zgi_ref.py`) |
| Z_GI (counter-machine compile) | 3476 | `machines/zgi.txt` |
| **Z_PP native (quasihalts iff P = PP)** | **295** | `machines/zpp_native.txt` (`native/zpp.py`, ref `ref/zpp_ref.py`) |
| Z_PP (counter-machine compile) | 1599 | `machines/zpp.txt` |
| **Z_PSPACE native (quasihalts iff P = PSPACE)** | **291** | `machines/zps_native.txt` (`native/zps.py`, ref `ref/zps_ref.py`) |
| Z_PSPACE (counter-machine compile) | 1646 | `machines/zpspace.txt` |
| **Z_coNP native (quasihalts iff NP = coNP)** | **317** | `machines/zconp_native.txt` (`native/zconp.py`, ref `ref/zconp_ref.py`) |
| Z_coNP (counter-machine compile) | 1738 | `machines/zconp.txt` |
| **Z_DLOG native (quasihalts iff discrete log mod primes is in P)** | **400** | `machines/zdlog_native.txt` (`native/zdl.py`, ref `ref/zdl_ref.py`) |
| Z_DLOG (counter-machine compile) | 2958 | `machines/zdlog.txt` |
| **Z_MUL native (quasihalts iff multitape TMs multiply in linear time)** | **403** | `machines/zmul_native.txt` (`native/zmul.py`, ref `ref/zmul_ref.py`) |
| Z_MUL (counter-machine compile) | 3623 | `machines/zmul.txt` |
| **Z_NTT native (quasihalts iff the number-theoretic transform has linear-size linear circuits)** | **469** | `machines/zntt_native.txt` (`native/zntt.py`, ref `ref/zntt_ref.py`) |
| Z_NTT (counter-machine compile) | 6106 | `machines/zntt.txt` |
| **Z_BPP native (quasihalts iff promise-P = promise-BPP)** | **333** | `machines/zbpp_native.txt` (`native/zbpp.py`, ref `ref/zbpp_ref.py`) |
| **Z_PPOLY native (quasihalts iff NP ⊆ P/poly)** | **362** | `machines/zppoly_native.txt` (`native/zppoly.py`, ref `ref/zppoly_ref.py`) |
| **Z_LP native (quasihalts iff L = P)** | **426** | `machines/zlp_native.txt` (`native/zlp.py`, ref `ref/zmh_ref.py`) |
| **Z_LNL native (quasihalts iff L = NL)** | **468** | `machines/zlnl_native.txt` (`native/zlnl.py`, ref `ref/znl_ref.py`) |
| **Z_MATMUL native (quasihalts iff multitape TMs compute the GF(2) matrix product in linear time)** | **494** | `machines/zmm_native.txt` (`native/zmm.py`, ref `ref/zmm_ref.py`) |
| **twin-prime beeper native (quasihalts iff finitely many twin primes)** | **19** | `machines/twinprime_native.txt` (`twin/`; 18 with a beep transition, tying the best known) |
| twin-prime beeper (counter-machine compile) | 265 | `machines/twinprime.txt` |

Z_P v2 is designed directly as a tape machine (`native/`, spec `docs/native.md`) and is
tested beep-for-beep against its Python reference `ref/zp2_ref.py`. The other rows are
compiled from counter machines and are expected to drop once ported to the native design.
History is in `docs/history.md`.

**What is new and what is not.** That P = NP is a Σ₂ sentence, and that Σ₂ sentences can be
encoded as quasihalting, is folklore (Donat; da Costa–Doria; Aaronson's survey). The
contribution is the explicit, reproducible, state-counted table, the construction
machinery, and the validation. It is **not** the first explicit machine for P vs NP: the bbchallenge
wiki records a P = NP beeper by Mira (GPT-6.1 Terra) on 2026-10-31 (BBB(290); [TMBR October 2026](https://wiki.bbchallenge.org/wiki/TMBR:_October_2026)),
with a Lean-formalized 285-state P = NP beeper announced by Mira-Cult on 2026-11-04 and 284- and 266-state
NP = coNP beepers on 2026-11-06 ([TMBR November 2026](https://wiki.bbchallenge.org/wiki/TMBR:_November_2026)).
The same page records this repository's 278-, 295- and 291-state machines (P = NP, P = PP, P = PSPACE;
announced 2026-11-01) and the ten Lean formalizations completed on 2026-11-09. State counts are not directly comparable:
this repository uses a designated beep state, Mira-Cult's headline counts use designated beep transitions.

**What this does not do.** Knowing BBB(n) does not settle P vs NP by simulation alone
(`docs/spec.md` §2, *Caution*). For the submitted 278-state machine the account of the construction is
`docs/native.md` and the Lean development in `formal/` (including `ZP.Cx.sentence_iff_PeqNP`); `docs/spec.md` is the
**earlier specification** of the 1371-state v1 machine (a different guest model, certificate bound and clock), kept for
history and for the general method. The
compiler is validated by tests at every layer. The Lean development (`formal/`, Palomar layout, core Lean only) states
`Quasihalts zpMachine ↔ Sentence` for the literal 278-state table. It proves every
layer: the abstract program, the bridge, the logical machine's simulation of the
abstract program, and the compilation to the table. No `sorry` is left. See `formal/README.md`.

## How it works (one paragraph)
L is a self-padded NP-complete language. An instance s *is* a guest program; s ∈ L iff
that program accepts some certificate c ∈ {0,1}^(|s|+1) within |s|+1 steps (Z_P v2, the
submitted 278-state machine; see `docs/native.md`). Z_P
enumerates candidate deciders J = 1, 2, …. For each instance s = 1, 2, … it computes
[s ∈ L] by brute force and runs J on s with clock (|s|+2)^(|J|+1) − 1. On the first mismatch
it beeps and moves to J+1. A correct polynomial-time decider for L exists iff P = NP, and
by padding it eventually appears with a large enough clock. One guest interpreter serves
both as the brute-force checker and as the candidate executor. Construction of the native machines:
[`docs/native.md`](docs/native.md); earlier (v1) specification: [`docs/spec.md`](docs/spec.md).

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
See `docs/spec.md` §5 (earlier specification). In brief:
- **Counter machine vs reference:** beep-for-beep agreement.
- **TM vs counter machine:** lockstep at every instruction boundary.
- **Controlled candidate lists:** exactly the predicted beeps, then silence.
- **P-language swaps:** beep-for-beep agreement.
- **Twin-prime beeper:** beeps exactly on the twin pairs (native: `twin/test_twin.py` checks every round).
- **Z_FACTOR, Z_GI:** the brute-force deciders agree with the reference on every instance
  up to the tested size. Both machines agree beep-for-beep with the reference prefix.
  The theorem for general A is in `docs/spec.md` §2.1.
- **Z_BPP, Z_PPOLY, Z_LP, Z_LNL, Z_MATMUL** (`tests/test_native.py`): logical machines beep-for-beep
  against their references; Z_BPP's two counters on every instance up to the tested size;
  Z_PPOLY's advice events; the multihead act on every storage with |x| ≤ 3 and ≤ 3 heads;
  the matrix-product check on random instances with m ≤ 3.
  Not yet formalized in Lean; the plans are `formal/plans/11`–`15`. The links from each
  sentence to its complexity statement (promise classes, P/poly, log space) are on paper
  (`docs/native.md`).

## Layout
`docs/` spec and history · `formal/` Lean project (Palomar layout) ·
`machines/` build outputs · `tests/` · `ref/` · `compiler/` · `sim/` · `twin/` native twin-prime beeper

## Credits
Gregory Morse (project brief, design decisions); construction, compiler and tests were
built with AI assistance (Claude).
