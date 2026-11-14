# Lane 4, rung 3 results: proofs that hold for every nearby weight setting

**Status: CLOSED (2026-11-12).** 25 doctor episodes on the test set (12 robust net, 12
plain code, 1 twin), all Sonnet, none rerun; 36 twins trained. Every number is read from
attempt logs and check files by `tools/collect3.py`, not from doctor reports.
Pre-registration: PREREG_R3.md (two dated amendments, both before the step they affect).

## Headline

On all **12 of 12** test specs a Sonnet doctor wrote a ReLU network and a Lean 4 proof,
accepted by the kernel with the standard axioms, that **every network whose weights and
biases are each within 1/1000 of the written ones** stays within the pre-registered
tolerance of the spec on the whole input box. No Fable episode was needed.

The pre-registered "advantage over verified code" test is **met by the letter**: on 11 of
12 proven networks, fine-tuning inside the proven ball on shifted noisy data lowers the
held-out error by 16% to 83% against the fixed verified program, while the theorem still
applies. **Read the limits before repeating that.** A program with four fitted constants
captures about 99% of the same shift (post hoc), so the advantage is over a *frozen*
program only, on a task built to have something to adapt to.

None of the ideas is new for trained networks with numerical tools (weight-ball
certificates: Weng et al., AAAI 2020; fine-tuning inside a certified region:
arXiv 2512.01899). What is measured here is the kernel-checked version against an exact
written spec, for LLM-written networks.

## The statement

For every perturbation of every weight and bias by at most τ = 1/1000 (including the
weights written as 0), and every real x in the box: |network(x) − spec(x)| ≤ δ, where
δ = max(5% of the spec's output range, 0.2). δ ran from 0.20 to 0.75 on the test set.

Not covered: rounding inside a float forward pass. The ball covers rounding of the stored
weights only.

## Table (12 test specs, the same 12 in each arm)

| | robust net (weights + weight-ball proof) | prog (verified-code control) | twin (trained, same δ) |
|---|---|---|---|
| Kernel-checked | **12 / 12** | **12 / 12** | 1 / 1 attempted (see Twins) |
| Sonnet-only count | 12 / 12 | 12 / 12 | - |
| Submissions per case (sorted) | 1,1,1,1,2,2,2,2,2,2,2,3 | 1,1,1,1,1,2,2,2,2,2,3,4 | 2 |
| Median submissions | 2 | 2 | - |
| Lean seconds per case, median | 42 | 20 | - |
| Solution lines, range | 91-584 | 13-57 | 138 |
| `native_decide` attempts | **0** | **0** | **0** |
| Banned-token rejections / timeouts / memory kills | 0 / 0 / 0 | 0 / 0 / 0 | - |

Bars: kill (S3 < 4) not triggered; pass (S3 ≥ 8) **met**, S3 = 12.

Networks written: 1 to 4 hidden layers, widths up to 9. Eleven equal the spec exactly
when unperturbed. One (p177) only approximates it, by design: the doctor spent 1/12 of
the 0.3 tolerance on a shallower network.

## Checks on each proven network (lane, no doctor)

| Spec | Hidden widths | δ | Worst deviation found inside the ball | as share of δ | δ first broken at | float32 deviation |
|---|---|---|---|---|---|---|
| p001 | 3, 2 | 0.20 | 0.022 | 11% | 16 τ | 2.4e-7 |
| p007 | 4, 2 | 0.20 | 0.031 | 16% | 8 τ | 2.4e-7 |
| p030 | 9, 5, 3 | 0.30 | 0.125 | 42% | 4 τ | 2.4e-6 |
| p119 | 3 | 0.72 | 0.047 | 7% | 16 τ | 9.5e-7 |
| p134 | 4, 3 | 0.38 | 0.128 | 34% | 4 τ | 1.1e-6 |
| p142 | 4 | 0.55 | 0.027 | 5% | 32 τ | 6.1e-7 |
| p177 | 5, 4, 2 | 0.30 | 0.172 | 57% | 4 τ | 0.083 (by design) |
| p179 | 4, 4, 3 | 0.25 | 0.063 | 25% | 4 τ | 8.3e-7 |
| p196 | 5, 2 | 0.75 | 0.067 | 9% | 16 τ | 1.7e-6 |
| p244 | 5 | 0.20 | 0.070 | 35% | 4 τ | 1.7e-6 |
| p249 | 6, 3 | 0.40 | 0.054 | 14% | 8 τ | 7.2e-7 |
| p281 | 5, 4, 4, 2 | 0.50 | 0.231 | 46% | 4 τ | 2.0e-6 |

- **Inside the ball:** 10,000 perturbations per network (uniform, sign corners,
  adversarial), 2,000 box points per batch. **No violation on any network.**
- **Outside the ball:** an adversarial search breaks δ at 4 to 32 times the proven radius
  on every network. So the proven balls are within a factor of 4 to 32 of the true limit
  for this δ; they are not vacuous.
- **Float32:** a float32 forward pass of the written weights is within 2.4e-6 of the exact
  spec on the eleven exact networks. Nothing about float arithmetic is proved.

## The comparison with verified code

Target: spec plus an affine shift of size δ/4, training data with noise δ/4, 2,000 Adam
steps with every weight clipped to the proven ball, seeds 0-2. Control: the spec itself,
which is what the verified program computes and cannot change.

| Spec | Gain over the fixed program, fine-tuned inside the ball (median of 3 seeds) | Unconstrained fine-tuning (reference) | Fitted affine correction to the program (post hoc) |
|---|---|---|---|
| p001 | 30% | 97% | 99% |
| p007 | 24% | 68% | 99% |
| p030 | 66% | 96% | 99% |
| p119 | 27% | 99% | 100% |
| p134 | 70% | 97% | 99% |
| p142 | 16% | 95% | 99% |
| p177 | **−220%** (worse than the program) | 92% | 99% |
| p179 | 37% | 74% | 99% |
| p196 | 26% | 92% | 99% |
| p244 | 66% | 99% | 100% |
| p249 | 49% | 95% | 99% |
| p281 | 83% | 95% | 99% |

Gain = 1 − (held-out mean squared error after fine-tuning) / (error of the fixed program).

- Pre-registered criterion (at least two thirds of proven nets gain at least 10%, inside
  the ball): **met, 11 of 12.** Every fine-tuned weight stayed inside the ball and every
  fine-tuned network stayed within δ of the spec on 20,000 sampled points, so the theorem
  covers each fine-tuned network.
- p177 fails it: an approximating network starts 0.083 from the spec, and the ball is too
  small to make that up.

What this is worth, plainly:

1. **The advantage is only over a frozen program.** Post hoc (not pre-registered,
   `tools/r3_posthoc.py`): adding a least-squares affine correction to the program, which
   is three or four tunable constants, captures 98% to 100% of the shift on every spec.
   That beats the fine-tuned network everywhere. The shift was affine by construction, so
   this reference is as favourable to the program as it can be; it still shows that
   "code cannot adapt" is true only of code with no parameters.
2. **The ball was not needed for safety in these runs.** Unconstrained fine-tuning with the
   same recipe gained 68% to 99% and never left δ on sampled points, moving weights by up
   to 0.32 (320 τ). The ball's value here is that the bound is proved rather than sampled,
   not that it produced better numbers. It cost most of the available gain.
3. **The task was built by the lane** to have something to adapt to, sized relative to δ.
   It is one synthetic shift, not real data.
4. So the honest reading: the proven region is large enough to be worth something
   (double-digit gains on 11 of 12), and it is small relative to what the data wanted.

## Twins (trained networks, tolerance capped before training)

Same trainer as rung 1 (unchanged), the proven network's shape, seeds 0-2, weights rounded
to multiples of 1/1024. The twin's tolerance is the case δ, fixed before training.

- Seed-0 twins: **1 of 12 eligible** (sampled error at most δ/2): p142, error 0.006
  against δ = 0.55. **10 of 12 already miss δ with no perturbation**, so they fail the
  statement by evaluation; one (p249) sits between δ/2 and δ.
- All seeds: 5 of 36 eligible (p142 three times, p119 and p134 once each).
- The one eligible twin got a doctor: **PASS on submission 2** (138 lines, one hidden layer of 4 units).
  So a trained network that is close enough can be given the same weight-ball proof.
- Reading: with the tolerance capped at 5% of the range, this small fixed training recipe
  usually does not get close enough for the statement to be true at all. That is a fact
  about this trainer at these tiny widths (the widths are the doctor's hand-built ones,
  with no spare units), not about trained networks in general. Solvers that certify
  trained networks were not run.

## Part B: the rung-2 transformers (lane analysis, no doctor)

Pre-registered expectation: no rung-2 network has a weight ball of radius τ. Result
(`tools/r3_transformers.py`, `results/r3-transformers.json`):

- For **all 10** proved rung-2 transformers, moving a **single** weight by τ = 1/1000 makes
  the network wrong at some length ≤ 20. Each case has a witness confirmed with the exact
  rational evaluator.
- 8 of 10 still break when the single weight moves by 1e-6, the smallest size tried. The
  two addition networks break at 1e-4 and not at 1e-5 in the float64 screen.
- Breaking entries per network: 3-6 (add), 64-75 (parity, dyck), 127-184 (sort, including
  s00), mostly attention score entries. These constructions rely on exactly tied scores.
- "Wrong" for the sequence tasks means an output at least 1/2 from the target (exact
  equality cannot survive any perturbation). The screen's float64 weights were loaded
  through float32; the witnesses are exact.
- Part B2 (a doctor arm for transformers with exact attention scores and perturbed other
  weights) was **not run**. It needs a new framework and its own pre-registration.

So rung 2's all-lengths theorems are about a measure-zero point in weight space. That fits
the rung-2 float32 failure of the sort network s00.

## Float versus exact arithmetic

Every theorem is over the real numbers with rational written weights. The weight ball
covers any rounding of the stored weights up to 1/1000, which includes float32 storage
of weights of this size. It does not cover rounding inside the arithmetic
of a forward pass; that is measured above (float32, at most 2.4e-6), not proved.

## Seeds and frozen inputs

- Pool: rung-1 spec pool (seed 20261111), the 266 specs not drawn at rung 1. Draw seed
  4044: 2 dev, 12 test, 6 reserve (none used). Test-set hash and the frozen prompt,
  framework and tool hash are in PREREG_R3.md amendments 1 and 2.
- Dev pilot (not a result): 4 of 4. Fine-tune seeds 0-2; twin seeds 0-2.

## Limits

- **n = 12**, one model, one prompt, one τ and one δ rule. Specs have at most 3 inputs and
  the networks at most 4 hidden layers of at most 9 units.
- **τ and δ were chosen by the lane** after a calibration on rung-1 networks, so that the
  bar would be "neither trivial nor hopeless". A larger τ or smaller δ would lower the
  count; this was not explored.
- **The worked example** shows the whole proof pattern on a toy spec, and the lemma kit
  was written for it. Several doctors report following it step by step.
- **The proof is hand-shaped interval reasoning.** Doctors tuned per-unit scales with
  numeric search to make loose bounds fit; proofs run to 584 lines for a 4-layer network.
  Nothing here says this scales to networks of practical size.
- **The plain-code control was again as easy**: 12 of 12, same median submissions, proofs
  a fifth of the length. The robust statement is a different and stronger kind of theorem
  than the program's exact equality, so the two arms are not proving the same thing.
- **Compute incidents** (in the run log (not released)): the doctor memory reservation was preempted once mid-run and
  re-granted in about four minutes with no submission lost; the service memory reservation overran its
  stated estimate by 37 minutes; two memory reservation wrappers failed on first use from path typos.
- Doctors' reports are not evidence; one doctor reported patching its file with a script,
  against the rules, before rewriting it with the file tool. The passing file was checked
  by the same checker as all others.

## How to check a case

    python tools/check.py runs/rung3-test/net/p281      (under a memory reservation)

Per-case records: `results/rung3-test.json`. Lane checks: `r3_checks.json` in each case
folder. Twins: `results/r3-twins-test.json`. Transformers: `results/r3-transformers.json`.
Post-hoc affine reference: `results/r3-posthoc-affine.json`.
