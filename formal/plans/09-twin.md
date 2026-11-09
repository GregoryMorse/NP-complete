# 09 — Twin primes (`twin/`, 19 states): `Quasihalts twinMachine ↔ ¬ TwinPrimes`

Prerequisites: none of plans 01–08 (only `ZP/Defs.lean` and the `TM.exec`/`TM.conf_add`/`TM.act` lemmas
of `ZP/Compile.lean`). The machine is small, so this plan works directly on the 2-symbol table: there is no
logical machine, no compilation certificate and no guest interpreter. Read `twin/README.md` first. The tape
invariants are tested round by round by `twin/test_twin.py`.

Target (comparator-checked, added to `Challenge.lean`/`Solution.lean`/`comparator.json`):

```lean
theorem ZP.twin_quasihalts_iff : ZP.Quasihalts ZP.twinMachine ↔ ¬ ZP.TwinPrimes
```

## 1. Trusted definitions (`ZP/DefsTwin.lean`)

Core Lean has no `Nat.Prime`; define primality plainly:

```lean
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, 2 ≤ d → d < p → p % d ≠ 0
instance : DecidablePred IsPrime := …            -- bounded ∀ (Nat.decBallLT or a List.range check)
def TwinPrimes : Prop := ∀ n, ∃ p, n ≤ p ∧ IsPrime p ∧ IsPrime (p + 2)
```

`ZP/TableTwin.lean` is already generated (`python3 formal/gen_table.py twinprime_native`, in the CI loop):
`twinMachine : TM := ⟨twinMachineTable, 5⟩`. State numbers (`machines/twinprime_native.json`, `state_names`):

| 0 C4 | 1 C5 | 2 C1 | 3 G1 | 4 G2 | 5 BP | 6 B | 7 Y1 | 8 Y2 | 9 A | 10 W | 11 Z1 | 12 Z2 | 13 V | 14 X1 | 15 X2 | 16 X3 | 17 H0 | 18 H1 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|

Add `decide` checks in `ZP/ChecksTwin.lean`: `twinMachine.table.length = 19`, `IsPrime` on 0..30, and that the
machine's state at steps 28 and 174 (the first two beeps, `python3 twin/design.py 2`) is 5 (`decide +kernel`
on `twinMachine.conf 28`; drop it if the kernel is too slow).

## 2. Zipper configurations (`ZP/TwinTM.lean`)

Work with list zippers and translate to `Conf` once:

```lean
/-- State q, cells left of the head L (nearest first), head cell and right R; blank beyond; head at p. -/
def zc (q : Nat) (L R : List Bool) (p : Int) : Conf
def TM.Reach (M : TM) (c c' : Conf) (n : Nat) : Prop := M.exec n c = some c'
/-- n steps from c to c'; `b` iff the beep state is visited at one of the times 0 .. n-1. -/
def TM.Seg (M : TM) (c : Conf) (n : Nat) (c' : Conf) (b : Prop) : Prop
```

Step lemmas `stepR`/`stepL` (read the row with `TM.act` by `rfl`/`decide`). Translation invariance (moving
everything by a constant `p`) is free if `zc` takes `p` as an argument. Prefer stating every lemma with `p`
universally quantified.

Scanner lemmas, each one induction on a list of `true`s:
- `scanR q n` / `scanL q n`: a state whose 1-transition is `1 R q` (resp. `1 L q`) crosses `n` ones;
- used by `Y1 Y2 W Z1 Z2 V H0 H1 C1 C4`.

None of these states is `BP`, so every `Seg` built from them has `b = False`. Prove a generic
`Seg.no_beep` for runs whose states avoid 5.

## 3. The round lemmas (`ZP/TwinRound.lean`)

Layouts (head position `p` arbitrary; the tape blank outside the shown cells):

```
K m d   := G2 on R's first cell; tape 1^(d-1) 0 0 1^(m-d)       -- walk start, 2 ≤ d < m
Wk m d j := B on R's cell j; D's hole at (d-1+j) mod d; R's cells < j are 1 (filled), j ≥ 1
```

1. **Walk step** `walk_step (j < r)`: from `Wk m d j` (or `K m d` for `j = 0`) to `Wk m d (j+1)`.
   Pieces: `B` makes R's hole and steps left, `scanL` over `j` ones (`Y1`), separator, `scanL` over
   `d-1-c` ones (`Y2`), fill, then two cases: `c+1 < d` (`A` makes the hole) and `c = d-1` (`A` at the
   separator → `W` scans `d` ones to the blank → `A` on cell 0). Then `Z1` over the ones up to the
   separator, `Z2` over `j` ones to R's hole, fill, step to `j+1`. Write the D block as
   `1^c 0 1^(d-1-c)` and do the case split on `c + 1 = d` only.
2. **Walk** `walk`: induction on `j`, from `K m d` to `Wk m d r` (`B` on the blank after R).
   `c_end = (d - 1 + r) % d = (m - 1) % d`: a `Nat.mod` lemma (`omega` after `Nat.add_mod`).
3. **Check** from `Wk m d r`: `B` reads 0 → `V` crosses `r` ones → `X1`. Three outcomes by `c_end`:
   - `c_end = d-1` (X1 reads 0), or `d ≥ 3 ∧ c_end = d-3` (X3 reads 0): **fail**: `C1` crosses to the
     separator, fills it, `C4` crosses back over D's `d` ones to the blank, writes 1, `C5` writes the hole, `G1` the
     separator, `G2` is on R's first cell: `K (m+1) 2`. (Here R has `m-1 ≥ 2` cells, so `G2` reads 1.)
   - otherwise **pass**: `X2` (c = d-2) or `H0` fills the hole, `H1` crosses to the separator, which stays 0,
     `G1` erases R's cell 0: `G2` on the next cell. If `d + 1 < m` that is `K m (d+1)`.
     If `d + 1 = m` (R had one cell), `G2` reads 0: **beep** (`BP`), then `BP` (on the new separator) steps left onto `X1`, which
     reads the hole on D's last cell (the old separator) and fails: `K (m+1) 2`.
   State these as one lemma `round m d` with the arithmetic predicate as the case split:
   ```lean
   theorem round (m d : Nat) (h2 : 2 ≤ d) (hd : d < m) :
       (m % d = 0 ∨ (m + 2) % d = 0) → ∃ n, Seg twinMachine (K m d) n (K (m+1) 2) False
     ∧ ¬(m % d = 0 ∨ (m + 2) % d = 0) → d + 1 < m → ∃ n, Seg … (K m d) n (K m (d+1)) False
     ∧ ¬(…) → d + 1 = m → ∃ n, Seg … (K m d) n (K (m+1) 2) True
   ```
   The hole-position ↔ divisibility facts: `(m-1) % d = d-1 ↔ m % d = 0` and, for `d ≥ 3`,
   `(m-1) % d = d-3 ↔ (m+2) % d = 0`; for `d = 2` the `d-3` case does not arise (X3 is reached only if
   `c_end ∉ {d-1, d-2}`).
4. **One candidate** `cand m (3 ≤ m)`: from `K m 2` to `K (m+1) 2`, visiting `BP` iff
   `∀ d, 2 ≤ d → d < m → m % d ≠ 0 ∧ (m+2) % d ≠ 0`. Induction on `d` upward with `round`; the
   beep flag is `True` only on the last `round` (all `d` passed), every other piece is `False`.
5. **Arithmetic** `twin_iff (3 ≤ m)`: `(IsPrime m ∧ IsPrime (m+2)) ↔ ∀ d, 2 ≤ d → d < m → m % d ≠ 0 ∧ (m+2) % d ≠ 0`.
   The only non-obvious direction: a divisor `d` of `m + 2` with `m ≤ d < m + 2` is `m` or `m + 1`; `m ∣ m + 2`
   forces `m ∣ 2`, impossible for `m ≥ 3`; `m + 1 ∣ m + 2` forces `m + 1 ∣ 1`.
6. **Start** `start`: from `twinMachine.conf 0` (state 0 `C4` on the blank tape) to `K 3 2` in 8 steps,
   no beep (`decide` or explicit steps): states `C4 C5 C1 C4 C4 C4 C5 G1 G2`; the tape is `1 0 0 1`.

## 4. Top (`ZP/MainTwin.lean`)

Build `MacroSimB (fun n => IsPrime (n+3) ∧ IsPrime (n+5)) twinMachine` (`ZP/GenStep.lean`). There `MacroSimB`
is stated for a `TM`, but `PairDataN` is for logical machines (`LTM`). Either copy `PairDataN`, `ztime`,
`interval_conf`, `beep_in` for `TM` (about 120 lines, with `TM.conf` in place of `L.zconf`), or prove the three
`MacroSimB` fields directly: `time n` = start time of `K (n+3) 2`, `mono` from `0 < n` in `cand`, `beeps` from the
`Seg` flag of `cand`.

Then `quasihalts_iff_of_macroSimB` gives `Quasihalts ↔ ∃ N, ∀ n ≥ N, ¬ (IsPrime (n+3) ∧ IsPrime (n+5))`, and
`¬ TwinPrimes ↔ ∃ N, ∀ p ≥ N, ¬ (IsPrime p ∧ IsPrime (p+2))` is classical logic plus the shift `p = n + 3`
(lesser twin primes below 3: none, since `IsPrime 2 ∧ IsPrime 4` is false).

## Estimate

~800–1200 lines, 1–2 sessions. The hard part is bookkeeping, not ideas: keep D as `1^c 0 1^(d-1-c)`
and R as `1^j 0 1^(r-1-j)` (or `1^r` between walks), so each scanner lemma applies with no list surgery.

## Checklist

- [x] `DefsTwin`, `ChecksTwin` (table length, primes; first-two-beeps check not done)
- [x] `TwinTM`: stream zipper (`BZ`, `TM.zrun`, `zconf`) as in `Zip.lean`
- [x] `TwinRound`: walk step, walk, check/fail/pass/beep, `roundFail/Pass`, `trial`, `cand`, `twin_iff`, `start`
- [x] `MainTwin`: `MacroSimB`, `twinQuasihalts_iff`; Challenge/Solution/comparator (DONE, 2026-11)
