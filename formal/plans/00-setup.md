# 00 — Session setup, build loop, Lean conventions

Read this first in every session. It is short on purpose.

## 1. Install Lean locally (do this before anything else)

`elan toolchain install` **fails** in the cloud container: it downloads from
`release.lean-lang.org`, and the proxy refuses that host (403). GitHub release assets
**are** reachable, so install elan, then fetch the toolchain from GitHub by hand and
link it:

```bash
cd ~ && curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh && sh elan-init.sh -y --default-toolchain none
```

```bash
mkdir -p ~/lean-dl && cd ~/lean-dl && curl -sSfL -o lean.zip https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.zip
```

```bash
cd ~/lean-dl && python3 -c 'import zipfile; zipfile.ZipFile("lean.zip").extractall(".")' && rm lean.zip && chmod -R +x lean-4.35.0-linux/bin
```

```bash
export PATH=$HOME/.elan/bin:$PATH && elan toolchain link leanprover/lean4:v4.35.0 $HOME/lean-dl/lean-4.35.0-linux
```

```bash
export PATH=$HOME/.elan/bin:$PATH && cd /home/user/np-complete/formal && lean --version && lake build
```

Notes:
- Use the `.zip` asset. The `.tar.zst` one needs `zstd`, which the container lacks.
  Python's `zipfile` drops the exec bits, hence the `chmod`.
- The download is ~900 MB. Delete the zip after extracting, because disk is a fixed
  allowance.
- A full `lake build` takes about 1 minute on 4 cores. **Build locally; do not wait
  on GitHub CI.** CI is the final check after a push.
- Every Bash call starts a fresh shell, so prefix commands with
  `export PATH=$HOME/.elan/bin:$PATH`.
- To skip this setup next time, put the five commands into the environment's setup
  script (claude.ai → environment settings → Setup script).

### Fast iteration

- To build one file and its dependencies: `lake build ZP.Foo`.
- To check a scratch file: `lake env lean /path/Scratch.lean`. The scratch file must
  start with `module` and `public import ZP.Foo` (or `import ZP` for everything).
- To see errors only: `lake build 2>&1 | grep -E 'error|warning: declaration uses' | head -40`.
- The linter fails CI on deprecated names (`if_pos` → `ite_eq_left`, `if_neg` →
  `ite_eq_right`) and on unused simp args. Fix every warning before pushing.

## 2. Repository rules (enforced by CI / `scripts/check_sources.py`)

- Core Lean 4.35.0 only. No Mathlib and no `native_decide`. Use `decide +kernel`
  for evaluation.
- Every file starts with `module`, then `public import …`, then
  `@[expose] public section`. Namespace is `ZP` (machine layer) or `ZP.Cx`
  (complexity layer).
- No file may exceed 10 000 lines. Split long files (the convention is ≤ ~1200
  lines each).
- Every new file is appended to `formal/ZP.lean` in dependency order.
- Generated files (`ZP/Logic*.lean`, `ZP/Table*.lean`) are produced by
  `formal/gen_logic.py` / `formal/gen_table.py`. CI regenerates them and fails on
  a diff. Never hand-edit them; edit the generator.
- The trusted surface is `ZP/Defs.lean` + `ZP/Table.lean` (+ the new `Defs*`/`Table*`
  files you add). Keep definitions there minimal and line-for-line with `ref/*.py`,
  and add `decide` sanity checks against the Python reference in `ZP/Checks.lean`
  (or a new `Checks*.lean`).
- The comparator (`comparator.json`) checks that each theorem named there has
  exactly the statement in `Challenge.lean`, using only
  `propext, Quot.sound, Classical.choice`. When you add a machine's advertised theorem:
  add it to `Challenge.lean` (with `sorry`), prove it in `Solution.lean`, and add its
  name to `comparator.json`.
- Git: work on branch `lean-n3`, commit often, and push with `git push -u origin lean-n3`.
  Do not open a PR unless asked. Commit messages end with the attribution lines the
  session's system reminder gives you.

## 3. Proof patterns that work here (learned the hard way)

**Machine lemmas**
- Segment lemmas on the logical machine are symbolic checks:
  `checkFF … (by decide +kernel) (by osimp) …` (see `ZP/Pair.lean`, `ZP/Outer.lean`).
  Design them in Python with `formal/scripts/symexec.py`. It mirrors
  `ZP/SymExec.lean`: build the start/end `SC`, call `reachN`, and `lean_sc` prints
  the Lean term. Copy an existing lemma of the same shape and change the items.
- Compose segments with `LTM.Reach.trans`, and fix up tape shapes with
  `.of_eq (by simp [...]) (by simp [...])`.

**Simp and rewriting**
- To unfold a definition by cases, use `simp only [f, h, ↓reduceIte]`, not
  `unfold f; rw [if_pos h]`. The latter often fails on compiled matchers.
- Give implicit arguments of big constructors explicitly (`(S := …)`, `(P := …)`)
  rather than hoping unification finds them.
- When `decide` fails because of a free variable, case-split first
  (`cases b <;> decide`).
- For equalities of stacks/lists in the toolkit layer, use `stk_eq`, or prove an
  `h'` helper and `rw`. `(by simp)` is fragile for these.
- Use `ac_rfl` for associativity/commutativity goals.

**omega**
- `omega` does no nonlinear arithmetic. `generalize` products/powers to fresh
  variables first, and state the needed facts (`Nat.mul_le_mul`,
  `Nat.pow_le_pow_right`) as hypotheses.
- `omega` does not understand `2^30`; write `1073741824`.

**Bits and counters**
- Bits are `List Bool`. The logical symbols are `B=0, M=1, '0'=2, '1'=3`; use
  `bitsOf`/`bn` to convert. Counters written least-significant-first use `bv`
  (`ZP/Pair.lean`), with `bv_dec`, `bv_le`, `bv_inj`, `bv_zero`.

**Working method**
- Before proving a machine phase, run the Python machine (`native/<m>.py` through
  `native/logic.py`) on a tiny instance and print the tape at each phase boundary.
  The Lean invariant should be that printout with variables.
- Write the *statement* of every lemma first, `sorry` the proofs, and get the
  composition (the top theorem) to typecheck. Then fill in the sorries bottom-up.
  This catches wrong invariants before you invest in proofs.
- Commit after each lemma that compiles. Never leave `main` of the branch red.
