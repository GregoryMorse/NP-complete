# Z_P: specification, theorem and construction

**Status:** revision 1, 31 Oct 2026. This document is normative for `ref/zp_ref.py`
(the executable specification), `compiler/zp_cm.py` (the counter program) and
the compiled Turing machine `machines/zp.txt`. The conventions here supersede
§3.1 of the project brief wherever they differ; the differences are deliberate
and noted in §1.6.

**Beep convention.** Aaronson's: a machine *quasihalts* iff it enters its
designated beep state only finitely often. The machine has exactly one beep state.

---

## 1. Conventions

### 1.1 Strings and numbers
A bitstring s = b₁…bₘ is represented by **rep(s) = int('1'·s, 2)** (shortlex rank + 1).
rep(ε) = 1, and |s| = ⌊log₂ rep(s)⌋. Every natural N ≥ 1 is rep of exactly one string.

### 1.2 Guest model: offset machines
A *code* is a bitstring s, read **right to left**: β₁β₂… is s reversed. (Equivalently,
β₁ is the least significant bit of rep(s); reading past the end means rep has
been reduced to 1.) The read sequence is cut into **entries**, each a unary block
1^e 0. A trailing block of 1s with no terminating 0 is incomplete and is not an entry.
Let e₀, e₁, …, e_{r−1} be the entries.

Each entry value decodes as **e = 4k + 2d + w** with w, d ∈ {0,1}, k ≥ 0.

A configuration is (o, τ, h): the *offset* o ∈ ℕ, the tape τ : ℤ → {0,1} (blank 0), and
the head h. The start offset is o = 0. One **step**: let a = τ(h) and i = o + a.
- If i ≥ r: halt, **REJECT**. The code is exhausted, so missing transitions reject.
- Otherwise decode eᵢ = (k, d, w). If k = 0: halt with output **ACCEPT iff w = 1**.
  Otherwise τ(h) := w, h := h + (d ? +1 : −1), o := k − 1.

run(P, X, t) executes at most t steps of the offset machine with code rep⁻¹(P) on
input rep⁻¹(X). It returns ACC, REJ, or TIMEOUT (no halt within t steps). A halting
step counts as a step, so run(·,·,0) = TIMEOUT.

*Why offsets?* A 1-tape 2-symbol TM with states 0..m−1 is coded by putting the
transition of (state q, symbol a) in entry 2q + a, with next state q′ written as
k = 2q′ + 1 and halting transitions as k = 0. Each such entry costs O(m) bits, so the
code has length O(m²). Conversely every code is a finite 2-symbol TM whose states
are the offsets 0..r. Offsets let the interpreter skip "o + a" entries without
doubling a state register.

### 1.3 Input convention (self-delimiting)
Input c = c₁…cₘ is written as **1 c₁ 1 c₂ … 1 cₘ** in cells 0, 1, …, 2m−1. All other
cells are 0, and the head is at cell 0. A machine finds the end of the input at the first
pair whose marker cell is 0. (With blank = 0 and two symbols, a raw encoding
could not distinguish `1` from `10`, which is the issue raised in brief §3.1.)

### 1.4 The language
> **L = { s : ∃c with rep(c) ≤ rep(s) such that run(rep(s), rep(c), |s|) = ACC }**

Every string is an instance. The instance length is the verifier's time bound, and
the certificate range is "rep(c) ≤ rep(s)". That range contains every c with
|c| < |s|, is contained in {c : |c| ≤ |s|}, and is cheaper to enumerate than
"|c| ≤ |s|".

### 1.5 The sentence and the machine
Clock: **T(J, s) = (|s| + 2)^{|code(J)|}**, where code(J) = rep⁻¹(J).

> **S :≡ ∃J ≥ 1 ∀s : run(J, rep(s), T(J, s)) = (ACC if s ∈ L else REJ).**

Z_P (abstract program):
```
J ← 1
loop:                                  # candidate loop
    for S = 1, 2, 3, …:                # instance loop: S = rep(s)
        want ← [∃C ≤ S: run(S, C, |s|) = ACC]
        if run(J, S, T(J,s)) ≠ want:   # TIMEOUT is never equal
            BEEP; J ← J + 1; restart the instance loop
```

### 1.6 Differences from the brief (§3.1–3.2)
| Brief | Here | Reason |
|---|---|---|
| guest = TMs, entry layout unspecified | offset machines, unary entries e = 4k+2d+w | one pop site in the interpreter, no state doubling, total decoding is trivial |
| certificates \|c\| ≤ \|s\| | rep(c) ≤ rep(s) | one countdown register; NP-hardness unchanged (Lemma 3) |
| T_j(n) = (n+2)^j | (n+2)^{\|code(J)\|} | cofinal for the same reason (padding). It keeps clocks small for wrong candidates, which makes differential testing feasible. |
| codes read in order | codes read right to left | reading = popping the least significant bit of rep |

---

## 2. Theory

**Lemma 1 (model equivalence).**
(a) For every deterministic multi-tape TM M deciding a language A ⊆ {0,1}* in time t(n),
there is a code D such that for every x, run(rep(D), rep(x), p(t(|x|)+|x|)) outputs [x ∈ A],
for a polynomial p.
(b) Conversely, a standard TM computes run(P, X, t) in time polynomial in
|P| + |X| + t (bit lengths; t in binary).

*Proof.* (a) Standard: simulate M by a 1-tape TM over {0,1} working on the
self-delimiting encoding of §1.3, with polynomial overhead. Then code that 1-tape
machine as in §1.2: one guest step per TM step, plus one halting step. (b) A step
costs one scan of the code (O(|P|)) and O(1) tape work. The tape has at most
2|X| + t non-blank cells. ∎

**Lemma 2 (padding).** For every code s and every ℓ₀ there is a code s′ with |s′| ≥ ℓ₀
such that run(rep(s′), X, t) = run(rep(s), X, t) for all X, t.

*Proof.* First drop the incomplete trailing entry, i.e. the maximal block of leading 1s
of s. It is never an entry, so behaviour is unchanged. Then prepend 0ᵖ. This appends p entries
with e = 0 (k = 0, w = 0) after the last entry in reading order. A lookup that hit the
end of the code (REJECT in that step) now hits an e = 0 entry (REJECT in that same step).
Every other lookup is unchanged. ∎

**Lemma 3.** L is NP-complete.

*Membership.* Guess C ≤ rep(s) (|C| ≤ |s| + 1 bits) and simulate |s| guest steps. By Lemma 1(b)
this is polynomial in |s|.

*Hardness.* Let A ∈ NP with polynomial-time verifier V and certificate bound q:
x ∈ A ⟺ ∃c, |c| ≤ q(|x|), V(x, c) accepts. Given x, construct the 1-tape TM M_x that, on
an input in the encoding of §1.3:
1. scans at most q(|x|) + 1 input pairs and REJECTs if a (q(|x|)+1)-th pair exists;
2. writes x (hard-wired) and runs V(x, c), accepting iff V accepts.

On **every** input, M_x halts within r(|x|) steps for a polynomial r. Step 1 bounds the
work independently of the input length. That is why the explicit length check is
needed: padding makes |s| large, so the range rep(c) ≤ rep(s) admits long
certificates. Let s_x be the code of M_x (§1.2), padded with 0s (Lemma 2) to length
≥ max(r(|x|), q(|x|) + 1). Then s_x is computable in time poly(|x|), and:
- if x ∈ A, take an accepting c with |c| ≤ q(|x|) < |s_x|. Then rep(c) < 2^{|c|+1} ≤ 2^{|s_x|} ≤ rep(s_x),
  and M_x accepts c within r(|x|) ≤ |s_x| steps, so s_x ∈ L;
- if s_x ∈ L via some c, then M_x accepted c, so |c| ≤ q(|x|) and V(x, c) accepts, so x ∈ A. ∎

**Lemma A.** S ⟺ P = NP.

*Proof.* (⇐) If P = NP then L ∈ P. By Lemma 1(a) some code D decides L within
c(n+2)^k guest steps on inputs of length n. By Lemma 2 there are codes D′ with the same
behaviour and any length ℓ ≥ |D|. Choose ℓ ≥ k + log₂ c. Then (n+2)^ℓ ≥ 2^{ℓ−k}(n+2)^k ≥ c(n+2)^k
for all n, so J = rep(D′) witnesses S.
(⇒) If J witnesses S, the code rep⁻¹(J) decides L within (n+2)^{|code J|} steps. By Lemma 1(b)
L ∈ P, and since L is NP-complete (Lemma 3), P = NP. ∎

**Theorem.** Z_P quasihalts ⟺ S ⟺ P = NP.

*Proof.* Every iteration of the instance loop is a finite computation: two bounded
runs and one finite certificate sweep (progress obligation (a), §4). Candidate J is
abandoned, with exactly one beep, iff some instance refutes it. If S holds with witness J*,
the candidate counter can never pass J*, so there are finitely many beeps. If S fails,
every candidate is refuted after finitely many instances, so beeps never stop. ∎

**Caution.** Knowing BBB(n) for n ≥ |Z_P| does not by itself decide P vs NP (brief §1).
It reduces the question to a Π₁ statement about a derived machine.

### 2.1 The same template for other languages (FACTOR, GRAPH ISOMORPHISM)

The proof of Lemma A uses only two facts about L: membership is decidable (the
brute-force truth computation terminates), and Lemma 1/2 relate guest codes to
polynomial-time TMs. Hence for **any decidable** A ⊆ {0,1}*, the machine Z_A that
replaces the truth computation by a terminating decider for A satisfies

> **Z_A quasihalts ⟺ ∃J ∀s run(J, rep(s), T(J, s)) = [s ∈ A] ⟺ A ∈ P.**

(⇐ of the second ⟺ is Lemma 1(a) plus Lemma 2. ⇒ is Lemma 1(b).) The first ⟺ is
the Theorem's argument verbatim, and it does not use NP-completeness.

Two instances are built (`ref/np_intermediate.py`, `compiler/truth_cm.py`):

| machine | A | Z_A quasihalts iff |
|---|---|---|
| `zfactor` | FACTOR: s = a‖k with \|a\| = \|k\| = m. s ∈ A iff a has a divisor d with 2 ≤ d ≤ k and d < a | integer factoring is in polynomial time (FACTOR ∈ P ⟺ FP-factoring, by binary search on k) |
| `zgi` | DIGRAPH-ISO: s = G‖H, two m×m adjacency matrices (\|s\| = 2m²). s ∈ A iff G ≅ H as directed graphs with loops | GI ∈ P (digraph isomorphism is GI-complete) |

Both encodings are polynomial-time equivalent (many-one, both ways) to the standard
ones. Malformed strings are simply non-members, which is a polynomial-time check.
Brute force is trial division, and enumeration of all maps [m] → [m] with an
injectivity check.

**Which other questions fit?** Exactly the Σ₂ ones, i.e. "∃ algorithm ∀ inputs". Some examples:
P = PSPACE (A = TQBF), P = PP (A = MAJSAT), NP = coNP (∃ verifier J ∀ formulas: J's bounded
certificate search agrees with unsatisfiability), and discrete logarithm ∈ P all have the
same shape. Statements of the form "for every ε > 0 there is an algorithm" are Π₃. Examples
are NP ⊆ SUBEXP, i.e. SAT ∈ TIME(2^{n^ε}) for all ε, ω = 2, and the negation of ETH. They
are not quasihalting statements: a BBB machine captures Σ₂ only. They would need a
machine whose *beep-free stretches* encode a further quantifier, i.e. the next level of
the busy-beaver hierarchy.

---

## 3. Construction: three refinement layers

```
ref/zp_ref.py        abstract program (§1.5), executable
     ║ (1) same algorithm, counters
compiler/zp_cm.py    counter (Minsky) machine: INC r / DEC r (branch on zero) / BEEP
     ║ (2) template compilation, compiler/tm.py
1-tape 2-symbol TM   machines/zp.txt (one designated beep state)
```

### 3.1 Counter program
Data are naturals in registers. Strings are their rep values, and the guest tape is a pair of
binary stacks: R holds the head cell and everything to its right, Lt everything to its left,
least significant bit nearest the head. A guest step is: halve R (the parity is the scanned
symbol a, and o += a); copy the code P into Pc; pop bits of Pc, counting down o over 0-bits
and accumulating the target entry's 1-bits in A; decode A = 4k+2d+w by two halvings;
push w onto Lt (right move) or rebuild R from Lt (left move). One subroutine `run` serves
both the decider (call-site flag F = 0) and the verifier (F = 1). Its outcome is returned
by branching on F.

Registers that are never live at the same time share storage. The register list and the
layout order are recorded in `machines/zp.json`.

### 3.2 Turing machine layout and templates
Register v is stored in unary as the block 1^{v+1}, with blocks separated by single 0s.
The cell after the last block, E, is the canonical head position. Every counter
instruction t has an entry state ent_t meaning "head on E, reading 0". Templates:

| op | navigation | body | states |
|---|---|---|---|
| INC r | walk left from E across m blocks, or from the left end across p blocks, whichever is cheaper | write 1 on the separator, carry-shift the tail right (2 states) | min(m+1, p+5) + 2 (1 if r is last) |
| DEC r | same | zero test (2), delete the last cell, propagate the hole to the end (6), or a carry-shift variant from E | min(m+1, p+5) + 10 (4 if r is last) |
| move X→Y (adjacent) | same | 1^{x+1}01^{y+1} → 1 0 1^{x+y+1}: two writes, O(1) states regardless of the values | nav + 3 + 2 |
| BEEP | – | E → step left into the beep state → step right into the successor | 1 dedicated state |

Two peephole rules remove most entry states.
- A transition that ends with the head on E, having just read 0, inlines the
  0-transition of the successor's entry state.
- A transition that writes 1 on E−1 and steps right into an entry state, whose only
  action is to step back left into a left-skipping walk, instead steps left into that
  walk directly. The tape is identical; only the detour through E is removed.

Neither rule bypasses the beep state. BEEP's own entry transition targets the beep
state, so inlining copies a transition that still enters it, and the beep state is not
a left-skipping walk.

**Minimization** is Moore partition refinement (bisimulation). The beep state is placed in a
singleton class and is never merged (progress obligation (c)). Undefined transitions
form their own value, so merging never invents behaviour.

### 3.3 Machine format
`machines/zp.txt` is one line: states separated by `_`, each state `w0M0n0,w1M1n1`,
where n is a decimal state number, start = 0, and `---` marks an undefined
(unreachable) transition. `machines/zp.json` gives the state count, the beep state, the
register order and the SHA-256 of the `.txt` line.

---

## 4. Progress obligations

The main soundness risk is a **false quasihalt**: a macro that loops forever stops
the beeps (brief §5). For each refinement step:

**(a) Every abstract finite check terminates in the counter program.** Loop by loop:
- `clear r`, `move`, `copy`: the source register strictly decreases.
- `pop X` inner loop: X decreases by 2 per iteration. The outer loops that pop
  repeatedly (|s|, |code J|, enc, entry scan) terminate because they pop from
  a register holding a rep ≥ 1, and every pop halves it until it reaches 1
  (the empty exit). **Invariant needed:** the popped register is ≥ 1 on entry. It holds
  because S, J, C ≥ 1 and P ∈ {S, J}. `pop` on 0 would loop, so this
  invariant is a formal-proof obligation.
- certificate sweep: K strictly decreases and `run` does not touch K.
- `run` step loop: Tb strictly decreases once per guest step.
- `pow`/`mul`: E and V strictly decrease.

**(b) Beep observations are preserved exactly.** The counter program has one BEEP
instruction, executed exactly once per refutation (label `bad`). The TM has one beep state,
entered exactly once per execution of that instruction (template table, §3.2).

**(c) The beep state is protected** in minimization. It is a singleton class (`tm.minimize`),
and no other state's transitions are rewritten to bypass it.

**Machine-checked status:** none yet. (a)–(c) are argued above and tested (§5). The
Lean/Rocq Tier-1 proof is the planned next step: see `formal/README.md`.

---

## 5. Validation (brief §5)

| Test | What it establishes | Where |
|---|---|---|
| Counter program vs reference | identical (J, S) at every beep, for L and two P-languages (`nonempty`, `odd`) | `tests/test_cm.py`, `tests/diff_tm_ref.py` (C interpreter) |
| **Lockstep** TM vs counter machine | at **every** instruction boundary the TM is in the right entry state and the tape decodes to exactly the counter registers. Run on Z_P and on 30 random counter programs × 3 DEC templates. | `tests/test_tm.py` |
| Optimized TM (inlined, minimized) vs counter machine | same beep sequence and the same registers at every beep | `tests/test_tm.py` |
| **Controlled enumerations** (brief §5.3) | hand-picked candidate lists (reject-all, accept-all, a looping candidate, then a known-correct decider for the P-language) produce exactly the predicted beeps and then silence, at the counter and TM levels | `ctl_*` variants, `tests/diff_tm_ref.py` |
| P-language swap (brief §5.2) | the real enumeration with L replaced by a P-language agrees beep for beep with the reference | `pswap_*` variants |
| Twin-prime beeper (§11 shakedown) | the same backend compiles a machine that beeps exactly on twin pairs | `twinprime` |

A full P-swap run to silence is checked only at the reference level. At the counter and
TM levels the guest stacks are unary-coded binary numbers, so a wrong candidate that keeps
writing costs 2^Θ(guest steps) host steps. This is expected and does not affect correctness.
