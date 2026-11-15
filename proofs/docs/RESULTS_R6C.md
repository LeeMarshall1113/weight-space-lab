# this study, rung 6c results: a necessary radius for every token-blind network (2026-11-14)

Pre-registration: `PREREG_R6C.md` (commit 02ef7d5). No amendment was needed. Verdicts
are read from `runs/r6c/*/attempts/*.json` and from the compile of the
assembled file `runs/r6c/final/R6C.lean` (exit 0), not from agent reports.

## Whose phenomenon this is

Hahn and Rofin (arXiv:2402.09963, Theorem 6) show in general, for soft-attention
encoders with layer norm, that transformers computing highly sensitive functions sit at
sharp points of parameter space (average case, a limit statement). This rung does not
discover that effect. It gives a worst-case, explicit-constant, kernel-checked form of
it for a decidable class of hard-attention networks in exact arithmetic. Neither result
formally implies the other.

## Result

**Pass bar met, with every registered statement proved.** Kernel-checked in Lean 4
(Mathlib; axioms `propext`, `Classical.choice`, `Quot.sound`; `native_decide` attempted
0 times), statements exactly as registered in `Lane4/TokenBlind.lean`:

1. **`Invariance`.** For a token-blind network, two variants that differ only in
   embedding entries on the token coordinates `T`, and two valid inputs of equal length
   whose embedded tokens have equal column sums on `T`, give equal outputs at every
   position.
2. **`Collision`.** For a token-blind network, two real tokens `s`, `o`, `τ ≤ 1`,
   `a, b ≥ 1`, `1 ≤ τ(2a+1)`, `1 ≤ τ(2b+1)`: two networks in the relative ball of radius
   `τ` give equal outputs at every position on `s^a o^(b+1)` and `s^(a+1) o^b`.
3. **`ParityBound`.** A token-blind network whose relative ball of radius `τ ≤ 1` is
   correct for a counting-parity task up to length `2a+1` has `τ(2a+1) < 1`.
4. **`SortBound`.** The same for sort rank (the rung-2 spec, exact integer output).

**Membership, by one mechanical tactic (`decide`) for all five:** `tokenBlind net ntok T
= true` for p05, p10, p29 (`T = [0]`), s00 (`T = [1]`), s01 (`T = [0, 1]`), with the
exact network text proved correct at rung 2.

**Per network, derived by the study team and compiled in the same file:** `radius` (a ball
correct up to length `2a+1` has radius below `1/(2a+1)`) and `noBall` (for every `τ > 0`
some length fails), for all five: the three parity networks on their parity tasks, the
two sort networks on sort rank.

Headline, in the pre-stated wording: **for every rung-2 network that reads tokens only
through global uniform averages (a decidable condition; 5 of our 10 proved networks),
kernel-checked: no relative weight ball of radius 1/L or more is correct for parity or
sort rank up to odd length L. A known effect (Hahn and Rofin) made worst-case, explicit
and machine-checked for this class; hard attention, exact arithmetic.**

## Attempts

| case | statement | model | submissions | verdict | proof lines |
|---|---|---|---|---|---|
| iHead | head step (a token-blind head gives equal outputs under the invariant) | Sonnet | 3 | PASS | 225 |
| iBlock | block step (a token-blind block preserves the invariant) | Sonnet | 1 | PASS | 158 |
| iNet | `Invariance` (initial states, induction over blocks, read-out) | Sonnet | 1 | PASS | 156 |
| cColl | `Invariance → Collision` | Sonnet | 5 | PASS | 269 |
| cBounds | `Collision → ParityBound`, `Collision → SortBound` | Sonnet | 2 | PASS | 98 |
| members | five memberships | lane, `decide` | 1 compile | PASS | 1 line each |
| final | the four statements composed; `radius`, `noBall` for five networks | lane | 1 compile | PASS | about 60 |

Five agent episodes, each the first attempt at its statement; about 513k subagent
tokens; about 12 minutes of agent time. No Fable step was needed or asked for. The
intermediate statements (`Agree`, `HeadStep`, `BlockStep`) were written by the study team and
were true as written. Each check: 10 to 13 s, about 4 GB peak commit.

## What this does and does not show

- **It is a class theorem with mechanical membership.** Unlike rung 6b, a new network of
  this architecture is covered by evaluating a Boolean; no proof per network. The class
  is closed under the perturbations the proof uses.
- **The class is "permutation-invariant by construction".** A network that reads tokens
  positionally (through causal or strict heads, or content-dependent selection) is not
  in it. Our three Dyck and two addition networks are not members, and each of those is
  not permutation-invariant even unperturbed (`[1, 2]` against `[2, 1]`), so the
  exclusion is not an artefact of the syntax. `Lane4.Conj.ParityNoBall` (every network
  of the architecture) stays a conjecture.
- **Constant.** `τ < 1/L` at odd length `L`, universal for the class. For the three
  parity networks rung 6b's bound `1/(2L−1)` is about twice sharper (their uncounted
  tokens have zero embeddings), and the measured full-ball threshold is about `1/(8L)`.
- **Tasks.** Parity and sort rank are proved. The collision theorem is task-free: it
  applies to any target that separates the count vectors `(a, b+1)` and `(a+1, b)`,
  for example majority or an exact count threshold; those corollaries were not stated
  or proved.
- **Not shown:** anything about soft attention, floats, trained networks, additive
  perturbations, Dyck or addition. The five member networks come from one model family
  and two task families.
- **Not proved here:** that the ball of radius 0 is correct (rung 2 proves the
  unperturbed networks correct; "radius 0 means the same network" is not formalised),
  so `radius` is a necessary condition only.

## Together with rungs 2 and 6b

For p05, p10, p29, s00 and s01 there are now two kernel-checked facts side by side: the
written network computes its task exactly at every length (rung 2), and no relative
weight ball around it of radius `1/L` or more survives to odd length `L` (this rung).
The 2x2 screen's breaks at relative 1/200 and length 1,000 for these five networks are
now implied by a theorem (odd lengths from 201 on).
