# this study, rung 6b results: a necessary radius for the rung-2 parity networks (2026-11-14)

Pre-registration: `PREREG_R6.md` (commit 565e994), amendment 1 (commit 5ed45c6).
Every verdict below is read from `runs/r6b/*/attempts/*.json` and from the a job wrapper
compile of the corollary files, not from agent reports.

## Result

**Pass bar met.** Kernel-checked in Lean 4 (Mathlib, standard axioms `propext`,
`Classical.choice`, `Quot.sound`; `native_decide` attempted 0 times):

1. **The collision bound** (`runs/r6b/kColl2`; statements in `Lane4/Collision.lean`). For
   every counting-parity task with wanted parity 0 or 1, a counted and an uncounted valid
   token, and every rung-2 network `N` with a count channel: if every network in the
   relative weight ball of radius `τ ≤ 1` around `N` is correct on every valid input of
   length at most `L ≥ 2`, then `τ·(2L − 1) < 1`. Also in witness form: at any radius
   with `1 ≤ τ(2L − 1)` there is a network in the ball and a valid input of length at
   most `L` that it gets wrong.
2. **Membership of all three proved rung-2 parity networks** (`runs/r6b/m05`, `m10`,
   `m29`): p05, p10 and p29, with the exact network text proved correct at rung 2, each
   have a count channel.
3. **Corollaries per network**, derived by the study team (`tools/r6b_assemble.py`,
   `runs/r6b/m*/_Corollary.lean`, each compiled under a memory reservation, exit 0):
   - `radius`: a relative ball correct up to length `L` has `τ < 1/(2L − 1)`.
   - `noBall`: for every `τ > 0` there is a length `L` at which the ball of radius `τ`
     is not correct.

Headline, in the pre-stated wording: **for 3 of the 3 proved rung-2 parity networks,
kernel-checked: no relative weight ball of radius 1/(2L − 1) or more is correct up to
length L; the bound holds for every network with a count channel; it is a restricted
class, one weight is moved, hard attention, exact arithmetic.**

## Attempts

| case | statement | model | submissions | verdict |
|---|---|---|---|---|
| kColl | collision bound as first registered | Sonnet | 4 | FAIL: statement false as written (see below) |
| kColl2 | collision bound, corrected | Sonnet (fresh) | 1 | PASS |
| m05 | p05 is a member | Sonnet | 1 | PASS |
| m10 | p10 is a member | Sonnet | 2 | PASS (submission 1 was a probe file) |
| m29 | p29 is a member | Sonnet | 4 | PASS |

Five agent episodes, about 450k subagent tokens, about 10 minutes of agent time in all.
No Fable step was needed or asked for. Each check: about 11 s, 3.9 GB peak commit.
Proof sizes: 102 lines (bound), 232, 216 and 207 lines (memberships).

## The registered statement was false, and how that was handled

The first agent stopped after four submissions and reported that the bound was false as
registered: the task's wanted parity was an arbitrary natural number, and with `par = 2`
no count has the wanted parity, so a constant network is correct on every ball and has a
count channel. The counterexample is the agent's hand argument, not a Lean theorem; it
agrees with where its Lean proof stopped. The pre-registration had named this case in
advance ("Statement 1 false as written"). Amendment 1 adds the hypothesis `par < 2` to
both forms of the statement and changes nothing else. The three membership tasks have
`par` 0, 0 and 1. A fresh agent proved the corrected statement at its first submission,
reusing the first agent's compiled partial file.

## What this does and does not show

- It is a theorem about three networks we built, and about any network with the stated
  property. It is not `ParityNoBall` (every network of the architecture), which stays a
  conjecture.
- The class is semantic: "along a one-parameter family in the ball, the output depends on
  the input only through the number of positions and `(1 + d)·k/n`". Membership is proved
  per network. The decoder in each membership proof is the second block's own argmax
  expression, so the membership proofs do not need to know which position wins.
- The argument is elementary (the bound's proof is 102 lines, most of it monotonicity of
  the ball). The general phenomenon is known: Hahn and Rofin (arXiv:2402.09963, Theorem
  6) bound average sharpness for soft-attention transformers computing sensitive
  functions. Ours is a worst-case, explicit-constant instance for hard attention,
  machine-checked, for specific written networks.
- The three networks share one construction; three memberships are close to one result.
- The bound moves one weight. The exact-rational check in the pre-registration finds
  breaks at about `1/(8L)` when every weight on the count path moves, so the full-ball
  radius is about four times smaller than the theorem says. The single-weight threshold
  is `1/(2L)`; the theorem's `1/(2L − 1)` is within 2.6% of it at `L = 20` and closer
  beyond.
- Not proved in this rung: that the ball of radius 0 is correct (that is the rung-2
  theorem for the unperturbed network; the step "radius 0 means the same network" is
  not formalised here), so `radius` is stated as a necessary condition only.
- Relative ball with zeros fixed, exact rationals, hard attention with ties averaged,
  parity only. Nothing here is about soft attention, floats, Dyck or sort.

## Together with rung 2

For p05, p10 and p29 there are now two kernel-checked facts side by side: the written
network computes the task exactly at every length (rung 2), and no relative weight ball
around it of radius `1/(2L − 1)` or more survives to length `L` (this rung). The 2x2
screen had shown breaks at relative 1/200 at lengths 100 and 1,000 as a finite search;
for length 1,000 that is now implied by a theorem (`1/1999 < 1/200`), and for length 100
the theorem is silent by a hair (`1/199 > 1/200`).

## Not done (the stretch items of the pre-registration)

Dyck depth and sort rank; a class where the second block reads the sequence; Lean
witnesses for the full-ball `1/(8L)` threshold. None started.
