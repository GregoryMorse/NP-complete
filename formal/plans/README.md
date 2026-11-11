# Plans for the remaining machines

Status: `Quasihalts zpMachine ↔ Sentence` and `Sentence ↔ P = NP` are proved
(`ZP.zp_quasihalts_iff_sentence`, `ZP.Cx.sentence_iff_PeqNP`). These plans cover the
other native machines, the native twin-prime beeper (09), Z_coNP (10) and the newer
machines (11–15).

| # | plan | machine | depends on | size (lines) | difficulty |
|---|---|---|---|---|---|
| 00 | [setup](00-setup.md) | — | — | — | read first, every session |
| 01 | [generic pipeline](01-generic-pipeline.md) | refactor | — | 600–900 | mechanical; everything depends on it |
| 02 | [Z_PP](02-zpp.md) | 295 states | 01 | 1500–2500 | easy: zp2 + accept counter |
| 03 | [Z_FACTOR](03-zfac.md) | 324 states | 01 | 2500–3500 | medium: builds the FACTOR glue |
| 04 | [Z_DLOG](04-zdl.md) | 400 states | 03 | 2500–3500 | medium: primality + mod-mult |
| 05 | [Z_GI](05-zgi.md) | 415 states | 03 | 4000–5500 | hard: search over injective maps |
| 06 | [Z_PSPACE](06-zps.md) | 291 states | 01 (02) | 1200–2000 | easy-medium: one game-tree induction |
| 07 | [Z_MUL](07-zmul.md) | 403 states | 01 (03) | 5000–7000 | hard: new guest model (queue of stacks) |
| 08 | [Z_NTT](08-zntt.md) | 469 states | 01 | 7000–10000+ | hardest: new everything + primes ≡ 1 (mod n) |
| 09 | [twin primes](09-twin.md) | 19 states | — | 800–1200 | easy: a 2-symbol machine, no interpreter |
| 10 | [Z_coNP](10-zconp.md) | 317 states | 01 (06, 07's base lesson) | 4000–6000 | medium-hard: choices at fresh cells, DFS = ∃ |
| 11 | [Z_BPP](11-zbpp.md) | 333 states | 01, 02 | 2000–3000 | easy-medium: Z_PP with two counters and an outside-the-promise branch |
| 12 | [Z_PPOLY](12-zppoly.md) | 371 states | 01 | 4000–5500 | medium: new four-level abstract program; charge lemma |
| 13 | [Z_LP](13-zlp.md) | 426 states | 01 (07's base lesson) | 5000–7000 | hard: new guest model (multihead read-only input) |
| 14 | [Z_LNL](14-zlnl.md) | 471 states | 13 | 2500–3500 | medium: zp2 verifier with a one-way head + 13's decider |
| 15 | [Z_MATMUL](15-zmm.md) | 577 states | 07 | 3000–4500 | medium: Z_MUL's proof shared through a common base, new check |

**Order:** 01 → 02 → 06 → 03 → 04 → 05 → 07 → 08; 07, 09 and 10 are independent of each other. Of the newer plans, 11 needs 02;
13 comes before 14; 12 is independent; 15 needs 07 (done). Plans 02 and 06 are the cheapest
wins and exercise the refactor. 06 can move earlier or later freely.

**Targets.** Each machine X gets `Quasihalts xMachine ↔ Sentence_X`, the advertised,
comparator-checked theorem. For the machines on the zp2 guest (PP, PSPACE, FACTOR,
DLOG, GI), plan 01 step H also gives `Quasihalts xMachine ↔ InP L_X` almost for free.
The following stay on paper unless the user asks for them:
- the class-level equivalences (`P = PP`, `P = PSPACE`, promise-P = promise-BPP,
  NP ⊆ P/poly, L = P, L = NL);
- the function-problem statements ("factoring in P", "discrete log mod primes in P",
  "GI in P", "linear-time multiplication", "linear-time GF(2) matrix product").

For DLOG, `L_D` includes "p is prime", so the function version would need AKS.

## How to run a session

- **Model:** Sonnet, low thinking, 400k context. Opus only for designing an invariant
  that resists two attempts.
- **Scope:** one plan, or one bullet group of a big plan, per session. Each plan's
  steps are sized so a session can finish a step, build green, commit and push.
- **Start:** run [00-setup](00-setup.md) §1, then `lake build` (about 1 min), then read
  the plan.
- **Order of work:** statements first with `sorry`, then the top composition, then
  fill in bottom-up. Commit after every green step.
- **Finish:** update `formal/README.md`'s file table and the plan file's checklist,
  noting what is done and any deviations from the plan. The next session reads that.

## Handoff prompt (paste into a new session)

> Work in `/home/user/np-complete/formal` on branch `lean-n3`. Read
> `formal/plans/README.md` and `formal/plans/00-setup.md`, install Lean as described
> there, run `lake build`, then execute the next unchecked step of
> `formal/plans/<NN>-<name>.md`. Rules:
> - core Lean only, no `native_decide`;
> - build locally;
> - commit and push to `lean-n3` after each green step;
> - no PR;
> - update the plan's checklist when done.

## Checklist

- [x] 01 generic pipeline (steps A–H; F partial, see the status section)
- [x] 02 Z_PP (`ZP.zppQuasihalts_iff_sentence`, `zpp_quasihalts_iff_InP`; comparator-checked)
- [x] 06 Z_PSPACE (`ZP.zpsQuasihalts_iff_sentence`, `zps_quasihalts_iff_InP`; comparator-checked)
- [x] 03 Z_FACTOR (`ZP.zfacQuasihalts_iff_sentence`, `zfac_quasihalts_iff_InP`; comparator-checked)
- [x] 04 Z_DLOG (`ZP.zdlQuasihalts_iff_sentence`, `zdl_quasihalts_iff_InP`; comparator-checked)
- [x] 05 Z_GI (`ZP.zgiQuasihalts_iff_sentence`, `zgi_quasihalts_iff_InP`; axioms checked, `lake comparator` not run here: no `bwrap`)
- [x] 07 Z_MUL (`ZP.zmulQuasihalts_iff_sentence`, proved)
- [x] 08 Z_NTT (`ZP.zntt_quasihalts_iff_sentence`, hypothesis `PrimeEx`; comparator-checked)
- [x] 09 twin primes (`ZP.twin_quasihalts_iff`, proved)
- [x] 10 Z_coNP (`ZP.zconpQuasihalts_iff_sentence`)
- [ ] 11 Z_BPP (promise-P = promise-BPP)
- [ ] 12 Z_PPOLY (NP ⊆ P/poly)
- [ ] 13 Z_LP (L = P)
- [ ] 14 Z_LNL (L = NL)
- [ ] 15 Z_MATMUL (linear-time GF(2) matrix product)
