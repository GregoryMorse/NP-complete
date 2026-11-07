# 08 — Z_NTT (`native/zntt.py`, 469 states): `Quasihalts znttMachine ↔ SentenceNTT`

Do this last. It shares nothing with zp2 except the compile layer (plan 01 step C) and
the toolkit:
- no guest interpreter;
- a different enumeration;
- a different abstract program;
- 294 logical states, all new.

## 1. Trusted definitions (`ZP/DefsNTT.lean`, mirrors `ref/zntt_ref.py`)

```lean
def isPrimeN (p : Nat) : Bool                       -- as the ref (trial division)
def primeOf (n : Nat) : Nat                         -- least prime p ≡ 1 (mod n), p ≥ n+1: see ⚠ below
def evalC (n p : Nat) (recs : List (Option Nat × Nat)) : Bool   -- ref `evaluate`, literally
def recChoices (j p : Nat) : List (Option Nat × Nat)            -- [None] + range j  ×  range p
def hasCircuit (c n : Nat) : Bool                   -- any over the product of recChoices
def SentenceNTT : Prop := ∃ c, ∀ n, 1 ≤ n → hasCircuit c n = true
```

**⚠ The least prime `≡ 1 (mod n)` is the main mathematical obstacle.** The ref is
`p = n + 1; while not is_prime(p): p += n`. The machine runs the same search, so it
never beeps at an `n` with no such prime: it is stuck. So **both** directions of the
theorem need "for every `n ≥ 1` some prime `p ≡ 1 (mod n)` exists", in core Lean.

- The standard elementary proof takes a prime factor of `Φ_n(k·n)` for a suitable `k`.
  That needs cyclotomic-polynomial values over `Nat`/`Int`. It is doable without
  Mathlib, but it is a project of its own (~1500+ lines).
- With existence in hand, define `primeOf n` as a search with explicit fuel equal to
  the bound from the proof, so it stays computable and `decide` can still evaluate
  small cases. Then prove it is the least such prime.
- Do not use a fuel that may run out (the statement would be false for the machine).
  Do not use a "least prime" `Prop` that is vacuous when no prime exists (the
  equivalence breaks the same way).

**Settle this with the user before starting plan 08.** It is the one place where the
formal statement and the needed number theory interact.

## 2. Abstract program (new `ZP/AbstractNTT.lean`)

The step keeps `n` on a refutation: `(c, n) ↦ (c, n+1)` if `hasCircuit c n`, else
`(c+1, n)`. Prove `AbstractQuasihaltsNTT ↔ SentenceNTT` from these facts:

1. **Padding** (`ZP/PadNTT.lean`): `2 ≤ c → hasCircuit c n → hasCircuit (c+1) n`.
   Insert `n` records `(none, 0)` after the inputs. Values: `val'[j] = val[j]` for
   `j < n`, `val'[n..2n-1] = val[n-1]`, `val'[j+n] = val[j]` for `j ≥ n`, and pointers
   `≥ n` shift by `n`. Prove it by induction on `j`.
2. **n = 1 holds for every c ≥ 1.** Witness: all pointers `none`, all `b = 1`. Every
   value is 1, `p = 2`, the root is `z = 1`, and the power-sum check passes. Prove
   it by unfolding `evalC` on a `List.replicate`.
3. **Small facts by `decide`:** `hasCircuit 1 2 = false`, `hasCircuit 2 2 = false`.
   `p = 3`; the 2·2 = 4 records give 3·6·9·12 = 1944 candidates, which is fine for
   `decide +kernel`. Time it in a scratch file first.

**Proof sketch, (⇐).** `SentenceNTT` with `c*` forces `c* ≥ 3` by fact 3. The abstract
`c` only grows, and only on beeps. Once `c ≥ c*`, padding gives
`hasCircuit c n` for every `n`, so there are no more beeps. Hence there are at most
`c*` beeps.

**Proof sketch, (⇒).** After the last beep `c = c_f` is fixed from some `n0` on, so
`hasCircuit c_f n` holds for `n ≥ n0`. For `n < n0`, the program passed `n` at some
`c_n ≤ c_f`:
- `n = 1` holds by fact 2;
- for `n ≥ 2`, `c_n ≥ 3` by fact 3 and monotonicity of the trace, so padding lifts
  it to `c_f`.

Write a small `Bridge` variant (`MacroSim` for this abstract step) by copying
`ZP/Bridge.lean` and generalizing it over the step function.

## 3. Machine proof (`native/zntt.py`; design notes in `docs/native.md` §NTT)

These are the subroutines, each a separate file with one main lemma:

1. **Rulers.** `P` grows by `n` until it is prime. The primality test copies `P` to
   `D` and tests `d = p−1 … 2` by marking. It mirrors plan 04's primality, so share
   the lemma if the state shapes allow. Spec: `P = primeOf n`.
2. **Record build.** For each cell of `C` (a round), one record per cell of `Nn` is
   appended. A record is a header `F O P`, three copies of `P` (acc, E, b) and one of
   `W` (u). The pointer ruler `W` grows by one per record. Spec: a tape relation
   `RecRel recs tape` with `recs.length = c * n`.
3. **Odometer over `(b, u)`** for all records. Spec: it enumerates the product of
   `recChoices` in some order and visits each assignment once. The existential form
   of `hasCircuit` makes the order irrelevant; prove a coverage lemma as in plan 05's
   `machineOrder_complete`.
4. **Evaluation pass `t`.**
   - Reset `acc_j := [j = t]`, then push values forward in column order.
   - The pointer decrement/capture mechanism: a pointer is decremented once per
     earlier column and is captured (exactly two unmarked 1s) in its own column.
   - Each unit of `acc_j` adds 1 to record `j+1` and `b_r` to every capturing record
     `r`.
   - At an output, it also adds `z` to `E` and to `S`, checking `acc = E`
     destructively.
   - Spec: after pass `t`, the tape relation reflects `val` from the ref's inner loop
     for that `t`, and the run fails iff a check fails.
5. **Power sums.** `S = 0` is checked after passes `t < n−1`, and `S ≠ 0` (one look
   at `P`'s first cell) after the last.
6. **Success/exhaustion merge.** The erase code is shared, and the last cell of `Nn`
   distinguishes the two cases. Prove both continuations land in the next pair's
   start `layNTT c n'`.
7. **Pair lemma, then `lmacroSim` for the NTT abstract step, then the top theorem.**

The docs mention a fixed bug: after a success the pass marks on `Nn` were not
cleared. Any invariant you state must say that `Nn` is clean at the pair start.

## Estimate

~7000–10000 lines across ≥ 6 sessions, plus the prime-existence library. Settle §1
with the user first. Before writing Lean for item 4, write each subroutine's invariant against
a Python trace on `DFT_2` (`c = 3, n = 2`, which the tests already run).


## Status (in progress)

Decision (user): the prime is handled with the **hypothesis option** `PrimeEx`
(`∀ n ≥ 1, ∃ i ≥ 1, isPrimeN (1 + n i)`); `primeN` is the least such prime, defined classically.

Done, building without sorry (`ZP/DefsNTT.lean`, `ZP/PadNTT.lean`, `ZP/AbstractNTT.lean`; not yet imported by `ZP.lean`):
- `evalC`, `allRecs`, `hasCircuit pr c n` (literal mirror of the ref, prime as a parameter);
- padding `hasCircuit_pad` (`2 ≤ c` => one more round keeps a circuit) with `evalC_pad`;
- n = 1 witness, `decide +kernel` facts for `n = 2`, `c ≤ 2`;
- the abstract program `absN`, `abstractQN_iff : AbstractQN pr ↔ SentenceN pr` for any `pr` with `NPrime pr`,
  and `sentenceN_iff (h : PrimeEx)` for `primeN`.

Still to do: the generalized bridge for this step function (copy of `Bridge.lean`), all of §3 (the machine proof),
and the Challenge/Solution entries (the headline theorem carries the hypothesis `PrimeEx`).

Update: `DefsNTT`, `PadNTT`, `AbstractNTT` are now imported by `ZP.lean` (full build green, no `sorry`).
The machine proof (§3: rulers, record build, odometer, evaluation passes, power sums, merge, pair lemma,
generalized bridge, `Challenge`/`Solution` entries) has been started (estimated 7000–10000 lines in all).

Machine-proof progress: the NTT machine is generated and certified (`TableNTT`, `LogicNTT`, `CompileNTT`:
469 table states, 254 logical states, certificate `znttCert_ok`). `RulerNTT` proves the `P += n` ruler
(`pa0Scan`, `pa1Walk`, `pa1Mark`, `pa2Scan`, `pa1M`, `pauSweep`, `pt0Scan`, `paLoop`, `paEnd`, and the
composite `padd`: from `PA0` on `P M Mid M 1^n` to `DC1` with `P` advanced by `n` and the separator `M`
written). `PrimeNTT` proves the primality test and the whole ruler: copy phase `dcAll`; shrink steps (`xsMore`,
`xsFinal`); marking cycle (`x4CycleLt/Eq`, `x4Cycle` with `Dm c d`, `x4Loop` giving `c = p % d`); `x4End`, `xdFull`,
`xdMarked`, `ceErase`; the trial-division loop `testRun` (D of length e: reaches `WX` iff no d in [2,e-1] divides p,
else back at `PA0`); `isPrimeN_iff`; `primeRuler` (P runs over 1+n*i until prime) and
`primeRuler_primeN` (under `PrimeEx`, from P = 1 the machine reaches `WX` with P = `primeN n`).
Next: records (`WX`..`RC*`), odometer, evaluation passes, power sums, merge, pair lemma.

Record build (`ZP/RecordNTT.lean`, no sorry, imported by `ZP.lean`): `recordBuild` takes
`hd WX [0,3] (1 :: P M K M C M Nn)` (P = j+1 cells, K = k1+1, C = c ≥ 1, Nn = n+1) to
`hd WI0 (Pfx (wEnd n c 1 + 1) j k1 ++ 1^c) (1 :: Nn ++ recsFlat j (k1+1) (roundsPs n c 1 []))`.
Pieces: copy engine (`copyP`, `copyW`, `kLoop`), `recordOne`, `roAll` (header reset), `nnLoop`,
`roundStep` (one C cell), `roundLoop`, setup `wxStep`..`wc0Walk`. Next: evaluation passes.

Evaluation phase (`ZP/EvalNTT.lean`, no sorry): `witnessInit` proves `WI0` .. `RZ0` (restore parameters, input flag
`1` on record 0 and `0` on the others, `E := 1` in every record) for records modelled by `Rc` / `Rc.body`
(`tailB` / `tailI` for the lists). Next: pass start `RZ0` .. `RH*`, `FA*` (advance, decrement/capture), `CP*`
(compare `acc = E`), `BU*`/`BS*`/`IA*`/`AB*` (broadcast, `+1`, `+b`), `CA*`, `PE*`, `SC*`/`PM*`, `FL*`.

