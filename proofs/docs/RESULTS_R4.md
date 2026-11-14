# Lane 4, rung 4 results: transformers proved correct at every length, across a weight ball, with a rounded forward pass

Run 2026-11-13, 1:15 to 7:25 am EST. Pre-registration `PREREG_R4.md` (commit 5fdefc9,
freeze amendment f905339). All counts below come from the checker's attempt logs and the
lane's own numeric checks, not from doctor reports. `results/rung4-test.json` has every row.

## Headline (pre-registered wording)

**11 of 12 written transformers kernel-checked correct at every length for every weight
setting within 0.5% (relative), and under a modelled rounded forward pass up to 65,535
positions; non-counting tasks only.**

Pass bar was 6 of 12 with at least 2 families; kill bar was 2 or fewer. Passed.

## What each proof says

One Lean theorem per network, standard axioms only (propext, Classical.choice,
Quot.sound), no `native_decide` (0 attempts in any arm):

for every rounding function in the model with unit error u ≤ 2^-24, every relative
perturbation of every weight by at most 1/200, every input whose position count n has
u·n ≤ 1/256, and every position: |output − target| ≤ 1/4.

- u = 0: exact arithmetic, **every input length**, every weight setting in the ball.
- u = 2^-24: float32-style rounding of every operation, up to 65,535 positions (the Lean
  condition u·(length + 1) ≤ 1/256 in fact allows 65,535 input tokens, 65,536 positions with BOS).

## Table

| arm | proved | carry | last | first | induct | submissions (median) | solution lines (median) |
|---|---|---|---|---|---|---|---|
| net (Sonnet) | **11/12** | 3/3 | 3/3 | 3/3 | 2/3 | 1 to 5 (2) | 389 to 969 (559) |
| prog control (Sonnet) | 12/12 | 3/3 | 3/3 | 3/3 | 3/3 | 1 to 5 (2) | 31 to 235 (54) |

The one net-arm miss, i03, is not a failed proof: the doctor agent died after about 70
minutes with an API error (one response over the 128,000-token output limit) before it
submitted anything. It counts as a fail. A fresh Sonnet doctor on an untouched copy
(`net-rerun/i03`, reported separately, not added) died the same way. The other two
induct cases with the same token count passed, so nothing marks i03's setting as harder.
No Fable agent was used: the pre-registered Fable step applied only below the pass bar.

Dev pilot (not results): 4 of 4, submissions 2, 2, 2, 1. Nothing was changed after it.

## Lane checks on the 11 proved networks (numeric, no proof)

Networks exported from the kernel-checked files. Tolerance 0.25.

| id | family | blocks | width | worst deviation inside the ball | first multiple of the radius that breaks it | float32, worst up to 65,534 tokens | float32 at 200,000 / 2,000,000 tokens |
|---|---|---|---|---|---|---|---|
| c07 | carry | 2 | 8 | 0.131 | 4 | 0.119 | not run (2 blocks) |
| c14 | carry | 1 | 6 | 0.111 | 2 | 0.100 | holds / holds |
| c21 | carry | 1 | 8 | 0.045 | 8 | 0.055 | holds / holds |
| f05 | first | 2 | 10 | 0.075 | 4 | 0.030 | not run |
| f08 | first | 1 | 7 | 0.045 | 8 | 0.035 | holds / holds |
| f24 | first | 1 | 8 | 0.025 | 16 | 0.025 | holds / holds |
| i09 | induct | 2 | 15 | 0.096 | 4 | 0.076 | not run |
| i10 | induct | 2 | 15 | 0.096 | 4 | 0.076 | not run |
| l11 | last | 1 | 6 | 0.045 | 8 | 0.045 | holds / holds |
| l25 | last | 2 | 6 | 0.045 | 8 | 0.045 | not run |
| l38 | last | 1 | 6 | 0.045 | 8 | 0.045 | holds / holds |

- **No contradiction with any theorem:** inside the ball (120 perturbations per network,
  lengths 6 to 2,000) every output stayed within 0.131 of its target.
- **The ball is not vacuous:** every network leaves the tolerance at 2 to 16 times the
  proved radius (median 8), so each proved radius is within about one order of magnitude
  of that network's real limit. This is a search, so the true limits may be smaller.
- **Real float32:** a numpy float32 forward pass in the framework's operation order,
  with written weights and with 5 corner perturbations at the radius, stayed within 0.119
  at 1,000, 16,000 and 65,534 tokens. No failure inside the theorem's range.
- **Beyond the theorem:** the six one-block networks still give exact outputs in float32
  at 200,000 and 2,000,000 tokens with written weights (no perturbation). The proof's
  length limit is conservative for them. Lengths past 2^24 were not tested.
- **Against rung 2:** rung 3 measured that the rung-2 addition transformers break when one
  weight moves by 0.0001 (absolute; 0.00001 did not break them in rung 3's screen). The three carry networks
  here are proved against all weights moving by 0.5% at once. The ball type, the
  architecture's position features and the task encoding differ, so this is a contrast,
  not a like-for-like factor.

## How the doctors did it

All eleven use the same idea, which the kit did not show: a score that subtracts a
length-scaled penalty from unwanted positions, with the wanted positions' penalty written
as exactly 0 so that no perturbation can touch it. The two induct proofs use one head per
token. Five networks use two blocks. Doctor cost: 170k to 360k tokens and 10 to 70
minutes per net case; 72k to 97k tokens and under 4 minutes per prog case.

## The float-versus-exact gap, stated

- Rungs 1 to 3 proved statements in exact real arithmetic only. Rung 4's theorem covers a
  rounding model: relative error u per operation, monotone, exact on integers to 2^24.
- IEEE float32 round-to-nearest satisfies that model only while nothing overflows or
  underflows. Overflow, underflow, subnormals, fused multiply-add, reordered or
  vectorised sums, and softmax are not modelled.
- So the link from theorem to a real float32 run is the numeric check above (no failure
  found), not a proof. A different operation order (any BLAS or GPU kernel) is outside
  the theorem.

## What this does not show (limits, as pre-registered)

- **Counting tasks are excluded.** Parity, dyck and sort (three of rung 2's four
  families) need a ball that shrinks like 1/n; no doctor arm was run and nothing is
  proved for them.
- **The ball is relative, zeros stay zero.** This is weaker than rung 3's absolute ball
  and does not cover additive noise or pruning. With these position features no task has
  a length-independent absolute ball.
- **The tasks are easy for Sonnet with this kit**: 11 of 12 at a median of 2
  submissions, and the lane chose the families knowing which mechanism works. The pass
  bar was low.
- **The plain-code control was easier still** (12 of 12, about a tenth of the proof
  length). The transformers add nothing practical over a verified program; the result is
  about what can be proved of weights.
- Hard attention with ties averaged, not softmax. Hand-written weights, not trained.
  Width at most 15. One model, one radius, one tolerance, 12 cases.
- Novelty rests on a web search over abstracts (`NOVELTY.md`): nothing found that proves
  a transformer correct in a proof assistant at every length over a weight ball or under
  modelled rounding. "Not found" is weaker than "does not exist".

## Process notes

- Every Lean run and doctor batch ran under memory reservations. The pilot's two memory reservations were
  extended twice with `heartbeat --extend` to cover the test arms.
- The submit tool shows only the tail of Lean's output; three doctors lost a submission
  to errors hidden behind linter warnings. Worth fixing before another rung.
- Two checker rejections in the prog arm (a `def` below the PROOF marker).
