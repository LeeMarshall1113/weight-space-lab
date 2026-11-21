# the proofs study, rung 6a results: gated softmax transformers proved correct at every length for an additive ball on every weight

Run 2026-11-14 (registration, one dev case), then 2026-11-18 1:05 am to 1:08 pm EST (rest
of the dev pilot, Amendment 1, both test arms, export, numeric checks). Pre-registration
`PREREG_R6A.md` (commit f9b1c0e; Amendment 1, commit 8dc0547, freeze
`scratch/freeze_r6a_a1.sha256`). Counts come from the checker's attempt logs and the
study team's numeric checks, not from doctor reports. Rows: `results/rung6a-test.json`
(`tools/collect6a.py`).

## Headline (pre-registered wording)

**12 of 12 written gated softmax transformers kernel-checked correct at every length in
exact arithmetic and up to 65,535 tokens in binary32 arithmetic, for every additive
change of every weight by at most 1/1000; the gate is a non-standard component;
non-counting tasks only.**

Pass bar was 6 of 12 with at least 2 families; kill bar 2 or fewer. Passed.

**To be read with the headline.** The lemma kit was strengthened after the dev pilot
(Amendment 1): one dev case (induct) failed with the registered kit, and the study team then
added a per-coordinate dot-product lemma and one sentence to the task file. This was done
before the test cases were built and before the test ids were read. 7 of the 12 test
proofs use the added lemma (c08, c19, f12, f22, i16, i17, i18), so the 12 of 12 is a
result for the amended kit, not for the registered one.

## What is proved for each of the 12 networks

Architecture `Lane4/AGate.lean`: softmax attention with one relative-position slope per
head (standard) and one gate neuron per head that removes a key from the candidate set
unless a clipped ReLU of the key's state is exactly 0 (not standard). Three Lean theorems
per network, standard axioms only (propext, Classical.choice, Quot.sound), no
`native_decide` (0 attempts in any arm):

1. **The statement**: for every rounding function meeting `Rnd u η M fl`
   (u ≤ 2^-24, η ≤ 2^-149), every float exponential meeting `ExpM u η ex`, every additive
   perturbation `APert.Within (1/1000)` (one `d` with |d| ≤ 1/1000 on every weight:
   embedding, score and value matrices, slopes, gate weights and gate biases, MLP,
   read-out; written zeros move too; the stored weight is `fl (w + d)`), and every input
   whose position count n has u·n ≤ 1/256, η·n ≤ 2^-100 and 2^40·n² ≤ M: the output is
   within 1/4 of the target.
2. **`exact_all_lengths`** (derived by the study team's `Final.lean`): exact real arithmetic
   with the real exponential, every input length, every perturbation in the ball.
3. **`binary32`** (derived likewise): any arithmetic that agrees on the finite range with
   a round-to-nearest onto the binary32 grid; any float exponential within the assumed
   accuracy; inputs of at most 65,535 tokens.

This is the statement the rung-4 and rung-5 theorems do not make: there the ball is
relative, so a weight written as 0 stays 0. Here nothing stays exactly zero.

## Table

| arm | proved | carry | last | first | induct | submissions (median) | proof lines (median) |
|---|---|---|---|---|---|---|---|
| gated softmax net (Sonnet) | **12/12** | 3/3 | 3/3 | 3/3 | 3/3 | 1 to 10 (3.5) | 664 to 2,080 (1,202) |
| prog control (Sonnet) | 12/12 | 3/3 | 3/3 | 3/3 | 3/3 | 1 to 4 (2) | 49 to 267 (54) |

Per case, net arm (submission of the pass, of 12; proof lines; doctor tokens; minutes):

| id | family | pass at | lines | tokens | minutes |
|---|---|---|---|---|---|
| c19 | carry | 1 | 1,059 | 416k | 28 |
| c01 | carry | 3 | 890 | 291k | 16 |
| c08 | carry | 3 | 995 | 335k | 21 |
| l16 | last | 1 | 664 | 173k | 6 |
| l15 | last | 2 | 711 | 226k | 9 |
| l27 | last | 2 | 717 | 202k | 7 |
| f22 | first | 7 | 1,345 | 366k | 40 |
| f12 | first | 8 | 1,452 | 342k | 35 |
| f37 | first | 10 | 1,439 | 347k | 36 |
| i17 | induct | 8 | 1,528 | 397k | 42 |
| i18 | induct | 4 | 2,080 | 613k | 49 |
| i16 | induct | 8 | 1,614 | 440k | 48 |

Net arm total: about 4.15M doctor tokens and 337 doctor minutes. One Sonnet doctor at a
time, fresh agent per case. No stronger-model agent in any arm, kit or dev case. The `first` and
`induct` cases (two blocks) passed at submissions 4 to 10 of 12: f37 was two submissions
from the limit. The control arm cost 72k to 118k tokens and 0.5 to 5 minutes per case.

**Dev pilot (not results).** With the registered kit: 3 of 4 (c03, l39, f36, each at
submission 2). i06 (induct) failed with 0 submissions used: the doctor estimated the
error from the kit's uniform dot-product lemma at above 1.2 against the 1/4 budget and
stopped. After Amendment 1 a fresh doctor passed the rebuilt i06 at submission 4
(2,142 lines). The three passing dev cases and the worked example were not rerun.

## Numeric checks on the 12 proved networks (numeric, no proof)

`tools/r6a_checks.py` under reservation wrapper, numpy, 2 threads, 3 h 24 min, peak commit 0.24 GB;
log `logs/r6a-checks-test.log`; per-case `r6a_checks.json`. Tolerance 0.25, δ = 1/1000.
Networks exported from the passing Lean files (`net.json`); the exported network at
written weights reproduces the target to within 8e-11.

| id | family | blocks | heads | width | largest written weight | inside ball, worst | breaks at | float32 to 65,534 tokens, worst | relative 1/200, worst | additive 1/1000 breaks at 100 / 1,000 (of 50) |
|---|---|---|---|---|---|---|---|---|---|---|
| c01 | carry | 1 | 1 | 3 | 24 | 0.017 | 16δ | 0.013 | 0.130 | 0 / 0 |
| c08 | carry | 1 | 1 | 5 | 24 | 0.019 | 16δ | 0.015 | 0.139 | 0 / 0 |
| c19 | carry | 1 | 1 | 5 | 24 | 0.026 | 16δ | 0.016 | 0.129 | 0 / 0 |
| f12 | first | 2 | 1, 1 | 6 | 24 | 0.015 | 16δ | 0.012 | 0.025 | 0 / 0 |
| f22 | first | 2 | 1, 1 | 6 | 24 | 0.016 | 16δ | 0.013 | 0.025 | 0 / 0 |
| f37 | first | 2 | 1, 1 | 6 | 24 | 0.015 | 16δ | 0.012 | 0.025 | 0 / 0 |
| i16 | induct | 2 | 1, 3 | 7 | 32 | 0.044 | 8δ | 0.027 | 0.071 | 0 / 0 |
| i17 | induct | 2 | 1, 2 | 7 | 24 | 0.024 | 16δ | 0.014 | 0.065 | 0 / 0 |
| i18 | induct | 2 | 1, 3 | 10 | 24 | 0.031 | 16δ | 0.033 | 0.068 | 0 / 0 |
| l15 | last | 1 | 1 | 3 | 24 | 0.011 | 32δ | 0.009 | 0.045 | 0 / 0 |
| l16 | last | 1 | 1 | 3 | 24 | 0.013 | 32δ | 0.007 | 0.045 | 0 / 0 |
| l27 | last | 1 | 1 | 3 | 24 | 0.013 | 32δ | 0.013 | 0.045 | 0 / 0 |

Reading the columns:

- **Inside the ball** (uniform and sign-corner perturbations of size δ on every weight,
  lengths 6 to 2,000): worst deviation 0.011 to 0.044 of the 0.25 tolerance. No violation,
  as the theorems require.
- **Non-vacuity** (multiples 2, 4, ..., 64 of δ): every network leaves the tolerance at 8
  to 32 times δ. The proved ball is within a factor 8 to 32 of the largest uniform ball
  this search can rule out; the theorems are not vacuous, and they are not tight.
- **float32, stated order** at 1,000, 16,000 and 65,534 tokens, perturbed inside the
  ball: worst 0.007 to 0.033. Consistent with the `binary32` corollary.
- **Relative ball of 1/200** (the rung-4 and rung-5 ball, 40 sign corners, zeros fixed):
  worst 0.025 to 0.139; no network leaves the tolerance. Measured, not proved.
- **2x2 contrast row** (additive 1/1000 on every weight, 50 sign corners per length):
  0 breaks at length 100 and 0 at length 1,000 on all 12. For comparison, the 11 proved
  rung-4 networks under the same noise: 8 of 11 break at length 100 and 11 of 11 at
  length 1,000 (`writeup/NOTE_2x2_v2.md`). The comparison is across architectures and
  across different drawn task settings of the same four families.

Check 4 of the pre-registration (a PyTorch module) was dropped at registration and was
not run: no PyTorch module exists for the gated architecture.

## Limits (the first six were written down before any run)

- **The gate is non-standard.** It is a content-dependent hard mask: a key is removed
  when a clipped ReLU of its state is not exactly 0. Real transformers have no such
  component, and a finite attention penalty in its place would work only up to a length
  of about penalty/slope. Key gating is not our idea (TRA, Opper et al.,
  arXiv:2503.23174, in trained models without proofs).
- **The kit carries the analysis**, more than at rung 5, and was strengthened after a dev
  failure (Amendment 1). What a doctor supplies is the network, the gate margin, the
  content-score bound, the slope gap and the bookkeeping; the softmax tail, the rounded
  sums and the stored-weight dot-product bounds come from the study team's kit.
- Same four task families as rungs 4 and 5, chosen by the study team; non-counting only.
  Nothing is said about counting tasks (rungs 6b and 6c give a necessary radius there).
- δ = 1/1000 is small and was set by the study team from its own worked example.
- exp accuracy is assumed (`ExpM`); stated left-to-right operation order; no fused
  multiply-add; no PyTorch module.
- The plain-code control passes with far shorter proofs (median 54 lines against 1,202).
- Nothing is said about trained networks or `nn.TransformerEncoder`, and it is not
  proved that the rung-4 or rung-5 architecture has no absolute ball (that remains the
  conjecture `Lane4.Conj.LastNoAbsBall`).
- The numeric checks are searches over corners and random draws, not proofs; "breaks at
  16δ" is where this search first found a violation, not the true threshold.
- The 12 test proofs have not been replayed on a second machine.

## Process notes

- Parked by usage on 2026-11-14 after dev case c03; resumed 2026-11-18. A doctor reservation
  (5677) stayed held for about 2.5 hours after the park because the stop file carried the
  wrong tag; no doctor was running. Rule since: after a stop, read the scheduler status.
- another study's run could not be reached on 2026-11-18 to announce the check service; no
  another study reservation was active. Recorded in the study's private log (not included).
- Usage was to be checked before each case. In the control arm it was checked before the
  first case and after the last (6% of the usage budget both times), not in between. In the net arm
  it was checked before each case (5% to 6% of the usage budget).
- The service and doctor reservations overran their filed estimates and were extended once
  (7:03 am); both were released at 9:41 am. The checks reservation was released at 1:08 pm.
