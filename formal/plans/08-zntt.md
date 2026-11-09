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

Evaluation phase, update: the record model is `Rc` = `F O Pf M acc M E M b M u` (the machine has K = 3 `P`-wide
fields, not 4 as the file header says: checked on a trace of `native/zntt.py`). `EvalNTT` now also has the pass-start
primitives (`rz0Scan`, `rz1*`, `rh*`, `ra*`, `rse`, `rsb`, `ru`, `ru2`, `rnStep`) and the per-record lemmas
`recPass2`/`recPass3` (`RH0` .. `RU2`: `F := 0`, `acc := 1` or `2` by the input flag, `u` restored).
Next: close the record loop (`RU2` -> `RN` -> `RH0` / `FAL`), then `FA*`, `DU*`, `RF*`, `CP*`, `BU*`, `BS*`, `IA*`, `AB*`.

Evaluation phase, update 2 (`EvalNTT`, no sorry): `passStartAll` (pass start `RZ0` .. `FAL` over all records, with
`Rc.ps`), `faN` (cursor on the first record, non-output: `FAL` .. `RFL` with `decAll` decrementing every pointer by
`decU`), `rfFind` (`RFL` .. `BU0n`/`BU0o`: finds the cursor record, `F = 1`, for any position). Next: the broadcast
loop `BU0n`/`BU1n`/`BU2n` .. `BS*`, `IA*`, `LA..LB`, `CU*`, `AB*` (acc += 1 for the next record, acc += b for captured
records, modular counters), `CA*` (next column), the output branch `FAo`/`CP*`/`BU*o`/`BZ*`/`IE*`/`TS*`, `PE*`, `SC*`/`PM*`/`FL*`.


### Progress: broadcast primitives (EvalNTT)
Done: counter increment `iaInc`, LA/LE/LB/LH/AB skips, CU test primitives
(`cu0*`, `cu1*`, `cu2Three`, `cu2Cap*`), LN primitives, and `ab0Sweep`
(captured record: AB0 sweep over the unit). Remaining: AB1..AB9, IR*, ABR*,
`abUnit`/`abLoop`, non-captured visit, cursor-record marking, CA*, output
branch, PE*, SC*/PM*/FL*.

### Progress: captured-record visit (EvalNTT)
`abUnit` (one unit: acc += 1 mod w, one mark of b consumed), `abLoop` (n units),
`capVisit` (AB0 .. LN0: acc incremented n times, b restored to all marks,
head back in `LN0` after u). Layout: `.. M acc M E M b M u`, b = 0^m 1^(n+1) 0^s.
Next: non-captured visit, cursor-record marking (BU*/BS*), CA*, output branch,
PE*, SC*/PM*/FL*, odometer, power sums, merge, final theorem.

### Progress: non-captured visit, cursor unit (EvalNTT)
Model `VR` (record with `acc = fld w k`, `E`, `b = 0^m 1^(n+1) 0^s`, `u = 0^a 1^(c+1) 0^t`);
`VR.vis` (captured iff c = 1: acc += n, b restored), `VR.inc` (+1 for the first record
after the cursor). Proved: `visitPre`, `visitCap`, `visitNoLn`, `visitSpecialEnd/Next`,
`visitEnd/Next`, `visitAllS/visitAll` (sweep over all later records, ends in `RFL`),
`incPre/incVisitAll` (IA0 + sweep), `cursorMark` (BU0n..BS0), `bsTailEnd/Next`, and
`cursorUnit`: one unit of the cursor's acc, whole sweep, back to `RFL`;
effect on later records: `stepList`.
Next: loop of cursor units (+ rfFind between), `BU1n` exit to `CA0..CA5` (column advance),
output-record branch (`BU*o`), bridge VR <-> Rc, then PE*, SC*/PM*/FL*, odometer, ...

### Progress: cursor loop and column advance (non-output nodes)
`VR`<->`Rc` bridge (`toRcA`, `toRc`, `tailB_toRc`, `tailD_toRc`, `VR.dec`), NoB lemmas,
`cursorLoop` (all units of the cursor's acc: rfFind + cursorUnit, `stepN`),
CA primitives, `caNext` (F := 0, walk to next header), `fa0N`, and
`colAdvance`: cursor (O = 2) with all units broadcast -> next non-output record is the new
cursor, later pointers decremented (`curTape` form again, so it can be iterated).
Next: end of pass (CA4 -> PE0 .. SC/PM/FL), output-record branch (BU*o, BZ*, IE*, TS*, CP*),
iterating `cursorLoop`/`colAdvance` over a whole pass, pass-start interface, odometer.

- Output compare (CP*/CPE*) single-step/sweep primitives proved in `ZP/EvalNTT.lean` (`cp0Hit` … `cpe7`).
  Remaining: `cpLoop`/`cmpAcc`, `fa0O`, output cursor unit (BU*o/BZ*/IE*/TS*), pass loop, pass end,
  odometer, power sums, pair lemma, Challenge/Solution entries.
- `cpRound`, `cpTerm`, `cmpAcc` proved: `acc = E` compare (n+1 ones each) restores acc to ones and leaves `E = 1 0^(z+n)`, ending at `hdR DAc`.
- `fa0O` proved: `FA0` on an output record whose `E` has as many ones as `acc`: mark, compare (`cmpAcc`), set `E := 1 0^(z+n)`, decrement later pointers, ends at `RFL`.
  Next: output cursor unit (`BU1o`, `BZ*`, `IE*`, `TS*`, `BZR*` → `BS0`), which needs the `S` register layout inside `Pm` (`GoodW`).
- Output cursor unit proved: primitives (`bu0oSkip` … `bzr6Mark`), `ieStep` (`E += 1`), `tsStep` (`S += 1`; `S` is the second
  header field `0^j 1^q`, `sInc`/`sNext`/`sAdv`), `rfO` (RF0 → BU0o), `oStep` (one `b`-step), `oLoop`, `oLast`, `oMark`,
  `cursorTail` (factored out of `cursorUnit`), `outUnit` (BU0o → RFL for a whole accumulator unit; `E` advances by `eAdv`).
  Remaining: output-node cursor loop over all units (like `cursorLoop`), `colAdvance` into/out of output records, pass end
  (`CA4 → PE*`, `SC*`/`PM*`/`FL*`), the pass loop, odometer, power sums, merge, pair lemma, Challenge/Solution.

- `outLoop`: iterates `outUnit` over all accumulator units of an output record (E, S counters advance by `r*n`).
- `fa0G` (+ `VR.curG`, `curG_tl`): FA0 on the next record for either kind; output case resets E to `fld |E| 1` after the compare. Remaining: `curTapeG`, `buEnd`, `rfG`, `colAdvanceG`.
- `colAdvanceG` (+ `curTapeG`, `curToCA0`, `bu1oAny`): column advance for cursor/next records of either kind (`c.O ∈ {2,3}`; output next record needs the compare hypothesis). Remaining: pass loop, pass end, odometer, power sums, merge, bridge.
- `colStepN` / `colStepO`: a whole column step (broadcast all units of the cursor record, then `colAdvanceG`) for a non-output / output cursor record; the output version advances `E` (`eAdv`) and the `S` register inside `Pm` (`sAdv`). The next record's compare condition (`hcmp`) is an explicit hypothesis on `stepN r vs = w :: ws`. Next: iterate over the columns of a pass (needs a semantic invariant giving `hcmp`), then pass end `CA4 → PE*`.
- Pass end proved (`pe0Scan` … `pe5Last`, `pe1Good`): from `PE0` on the whole tape (`Pm = … ++ Nn`, `Nn = 1^(a+2) 0^b` or `1 0^b`), unmark the last pass mark of `Nn`; `peMore` ends in `SC`, `peLast` in `FL0` (head on the last cell of the preceding field). Next: `SC`/`PM*` (re-mark `P`, restart at `RZ0`), `FL*`, odometer, `SU*`/`BX*`.
- `SC`/`PM*`/`FL*` proved: primitives (`fl0Scan` … `pm7Set`, `pm0Good`, `pm4Good`, `sc2Ones`), `pmSkip`, `pmPre`, `pmAct`,
  `scPm` (more passes: `S` is checked to be `0` in `SC`, the input flag moves from record `r` to the next record `r2`,
  ends in `RZ1` of the next pass; `Pf := 2` / `Pf := 3`), `flOk` (last pass, `S` has a leading `0`: `FL0` → `SU1`).
  Remaining: failure branches (`SC2` on `0`, `FL2` on `1` → `ODL`), odometer `OD*`, `SU*`/`BX*`/`BEEP`/`PA*`, semantic layer.
- Success path proved (`su3Sweep` … `su10Set`, `su1Good`, `suOk`): when `Nn` ends in a `0` (fully marked) the records are erased
  (blank cells), `Nn := 1^(|Nn|+1)`, `W` and `S` are erased and `P := 1`; ends at `hdR PA0 [3] (1 :: K ++ 1 :: C ++ 1 :: Nn' ++ 0^(|recs|+1))`
  (leading blanks are normalised with `ZP.F.hdR_zeros`). Next: beep path (`SUX` on `1`, `BX*`), failure branches into `ODL`, odometer `OD*`, then the
  primality phase restarts (`PA0`, existing `PrimeNTT`/`RulerNTT`), semantic layer.
- Beep path proved (`suxOne`, `bx1M` … `bx3One`, `suPre`, `suTail`, `beepOk`): `Nn` all ones: `C += 1`, `Nn` shifted right by one, then the same erase of `W`,`S` and `P := 1`, ending at `PA0`.
  Remaining: failure branches into `ODL` (`SC2` on `0`, `FL2` on `1`), the odometer `OD*`/`WI*`, the pass loop and the semantic layer.

### Progress: odometer primitives
`EvalNTT.lean` now has the odometer scanning primitives (odlScan, od0*, odh/oda/odeSkip, odi3, odm3, odj*, odn*, odr*)
and `beepStepZ`. The BEEP→SU0 step is a single `zstep` (the checker's `Reach` never leaves the beep state, as in
`Pair.beepStep`), not a `Reach`. Remaining: odometer semantic walk (`OR`/`odo`), pass loop, restart interface, power sums,
merge, pair lemma, bridge, spec, entries.

### Progress: odometer field lemmas
Added `odInc` (no-carry increment → `WI0`), `odCarry` (reset string, set first cell, → `ODM`), `od0Walk`, `beepStepC`
(BEEP→SU0 as one `zstep` for any last cell). Remaining odometer work: the `OR`/`odo` semantic walk over whole records.

### Odometer spec (read from `ref/zntt_ref.py`, to be formalised)
`has_circuit c n` quantifies over `recs : Π j < N, (Option (Fin j)) × Fin p` (N = c·n): for record `j`, `u_j ∈ {None} ∪ [0, j)`
and `b_j ∈ [0, p)`. The machine counts per record a `b` string of length `p` (thermometer `1^(b+1) 0^…`: `ODI/ODJ` pass the
ones, the first `0` becomes `1`) and a `u` string of length `j+1` (`ODM → ODI/ODJ`, leading `0`s allowed). A full string
(`ODJ` hits `M`) is reset to `1 0…` (`odCarry`) and the carry moves to the next string, `odCarryNext` to the next record,
`odCarryEnd` past the last one (beep). The semantic walk to prove: `odoNext` on the list of (digit, radix) pairs is a
mixed-radix successor, visits every element of `∏ recChoices` exactly once, and the machine step lemmas
(`odRecInc`, `odCarryInc`, `odCarryInc0`, `odCarryNext`, `odCarryEnd`) realise it.

### Resolved: the `u` digit encoding
`native/zntt.py` pass start (`RU`: `0→1`) and `WI1` (`0→1`) restore a string's leading zeros to ones; the pointer decrement of a
pass eats `1`s from the left. So at odometer time a `b`/`u` string is a *window* `0^z 1^k 0^m` (`k ≥ 1`) and its digit is the
right end `e = z + k ∈ [1, z+k+m]` of the run of ones; the increment (`odInc`, `odCarryInc`, `odCarryInc0`, `odRecInc`) moves it
to `e + 1`, overflow resets to `1 0…` (`e = 1`) and carries. `b` strings are the case `z = 0` (`therm`). The `OR`/`odo` walk
therefore matches `odoNext` on `(e - 1, L)` pairs; leading zeros are invisible to it because `WI1` normalises them.

### Progress: odometer on a record list (done)
`ORec` (header/acc/E, `b` = `therm d r`, `u` = `winStr z k m`), `tapeL`, `ORec.next`, `odoStepR`, `resetAll`.
`odoWalk`: from `ODH` at the first record, `odoStepR os = some os'` gives `WI0` with `X ++ 3 :: R = A ++ tapeL os'`, and
`odoStepR os = none` gives `BEEP` on `A ++ tapeL (resetAll os)`. `odoStepR_digs`: the record step realises `odoNext`
on the digit list. Remaining: pass loop, restart interface, power sums, merge, pair lemma, bridge, `evalC`, entries.

### Progress: pass loop (done up to the last cursor)
`passLoop`: iterates `colStepN`/`colStepO` over a column list, with invariants `CurInv` (cursor), `OutM` (`O = 3 → m = 0`),
`PreOk`, the register shape `Wf ++ 1 :: (0^p.1 1^p.2 ++ 1 :: P2)` and the semantic obligation `PassCmp n r vs` (the compare
hypothesis `hcmp` for every cursor reached; to be proved by the semantic layer). It ends at the last cursor (`vs = []`).
Remaining: the last-record broadcast and `CA4 → PE0`, compare failure branch, `PA0` interface, power sums, merge, pair lemma, bridge.

### Progress: last record of a pass
`caLast` (`CA1 → PE0` at the last record), `lastEnd` (from `curTapeG … c a 0 s []` to `PE0` on `Pm ++ tailB (pre ++ [c.done a s])`),
`lastStepN`/`lastStepO` (non-output / output last cursor). Together with `passLoop` a whole pass reaches `PE0`. Remaining: compare failure
branch, `PE0 → PM/FL → …` composition of a pass with `peMore/peLast`, restart interface, power sums, merge, pair lemma, bridge.

### Progress: whole pass (non-final)
`passMore`: `passLoop` + `lastStepN/O` + `peMore` — from the first cursor `RFL` to the check state `SC`, when `Nn = 1^(a+2) 0^b`
(more passes follow). Remaining for a pass: the final-pass variant (`peLast` → `FL0`), then `SC`/`PM` → next pass, failure branches,
restart interface, power sums, merge, pair lemma, bridge.

### Where plan 08 stands (summary for the next session)
Proved (all in `ZP/EvalNTT.lean`, sorry-free): primality/record build, `witnessInit`, pass start `RZ0 → FAL → RFL`, column steps,
`passLoop`, `lastStepN/O`, `passMore` (→ `SC`), `passLast` (→ `FL0`), `scPm`/`flOk`, success/beep `suOk`/`beepOk`, the odometer
(`odoWalk`, `odoStepR_digs`), failure leaves into `ODL`.
Remaining, in order:
1. *Bridge* `Rc` (after `scPm`/`passStartAll`: `r.ps` records) ↔ `VR` (cursor form) for the next pass; chain `scPm → passStartAll → FAL→RFL → passMore/passLast`.
2. *Semantics*: `PassCmp` and the value recursion (`stepN` = push evaluation `val`), power sums, tie to `evaluate` of `ref/zntt_ref.py`.
3. Failure compositions into `ODL`, then `odlScan`/`od0Walk`/`odoWalk` → `WI0` (`witnessInit`) for the next assignment.
4. `PA0` restart interface with `PrimeNTT`/`RulerNTT`, merge, pair lemma, `evalC`, Challenge/Solution entries.

### Progress: bridge `ORec` → pass-start `VR`
`ORec.toRc o x` (record after `witnessInit`, flag `x`), `ORec.vr o x` (cursor form), `restoreU_win`, `accI_fld`, and
`toRc_ps_vr : 1 :: 1 :: (o.toRc x).ps.body = (o.vr x).recd`. Next: lift to lists (`tailP (os.map toRc) = tailVR (os.map vr)`
and the first-record entry `faN/faO` ↔ `curTapeG`), then chain `scPm → passStartAll → FAL → RFL → passMore/passLast`.
