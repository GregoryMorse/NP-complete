# Formal verification plan (Tier 1)

**Status:** plan + unchecked skeleton. `ZP.lean` has not been compiled: the build
environment for this commit could not install a Lean toolchain. Treat every statement
in it as a draft.

Goal (brief §8, Tier 1): a kernel-checked proof that

> the literal table `machines/zp.txt` quasihalts (designated beep state, blank tape)
> ⟺ the abstract program of `docs/spec.md` §1.5 beeps finitely often ⟺ S.

Tier 2 (S ⟺ P = NP) stays on paper (`docs/spec.md` §2). It needs the
polynomial-time equivalence of offset machines and standard TMs.

## Proof chain (modelled on the 215-state ZF project's layering)

| Layer | Statement | Evidence today | Planned proof technique |
|---|---|---|---|
| L0 table | `machines/zp.txt` parses to the `TM` value `zp` | SHA-256 in `machines/zp.json` | generated Lean literal + `decide` |
| L1 template bridge | every counter instruction t is implemented by its TM template: from a well-formed tape encoding registers ρ, with the head on E in `ent t`, the TM reaches `ent t'` with a tape encoding ρ′, where (t′, ρ′) is the CM successor (or several successors for native moves) | lockstep test (`tests/test_tm.py`) at every boundary | one symbolic lemma per template *shape* (INC-near, INC-home, DEC-last, DEC-twopass, DEC-carry, MOVE-adj), parameterized by block distances, plus a generated certificate listing each instruction's template |
| L1′ inlining + minimization | the shipped table is bisimilar to the uninlined template machine, with beep visits preserved one-for-one | `tests/test_tm.py` (same beeps) | a generated partition certificate checked by `decide`; the beep state is a singleton class |
| L2 coalescing | the physical CM simulates the virtual CM with phys = Σ class | `tests/test_regalloc.py` | the must-zero analysis result is emitted as a certificate (the Z sets); the kernel checks it is an inductive invariant, then the simulation |
| L3 CM ⟺ abstract | the virtual CM program refines the abstract program: same beeps, every abstract check terminates (**progress (a)**) | differential tests (`tests/diff_tm_ref.py`) | loop-by-loop ranking functions plus the invariant "popped register ≥ 1" (`docs/spec.md` §4) |
| L4 abstract ⟺ S | finitely many beeps ⟺ ∃J ∀s correct | paper proof (`docs/spec.md` Theorem) | direct |

Quasihalting must be preserved, not just halting. Each layer therefore proves a
*beep-exact* simulation: every macro step terminates and emits exactly the beeps of the
step it simulates. That is progress obligations (a)–(c).

## Sizes to expect
The table has ~1.4k states, so L0/L1′ certificates are large but mechanical. L1 is the
real work, about one lemma per template shape (six shapes). L3 is a few hundred lines of
loop invariants.
