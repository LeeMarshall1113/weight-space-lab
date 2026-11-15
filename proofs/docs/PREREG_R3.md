# Pre-registration: rung 3 (proofs with weight tolerance)

Written 2026-11-12, after rung 2 closed (commit 6fdeeca) and after the project lead relayed
the project owner's go, bounded to about a week. Written before any rung-3 doctor run.
PREREG.md and PREREG_R2.md stay unchanged. Later changes go in a dated "Amendments" list
at the end of this file.

Read first: NOVELTY.md, "Re-check for rung 3". Weight-ball certificates (Weng et al.,
AAAI 2020) and fine-tuning inside a certified weight region (arXiv 2512.01899) are
published for trained networks with numerical tools. This rung does not claim either
idea. What it tests is whether an LLM can write a network and a **kernel-checked** proof
of a weight-ball statement against an **exact written spec**, at a measured rate.

## Question

Can a doctor write a ReLU network and a Lean 4 proof, accepted by the kernel, that the
network stays within δ of the spec on the whole input box for **every real weight setting
within τ of the written weights**? And does that proven ball buy anything a verified
program cannot have?

## The statement (fixed before any run)

For a spec on a box, a written network `net` with rational weights, and the fixed
constants τ and δ below:

    for all perturbations dW, db with every entry |·| ≤ τ,
    for all real x in the box:   | net.evalP dW db x  −  spec x | ≤ δ

`evalP` and `Within` are defined in `Lane4/Robust.lean` (written by the study team). The ball
is per weight and per bias (an ℓ∞ box in weight space) and includes the entries written
as 0, so any same-shape network with weights within τ is covered.

- **τ = 1/1000**, the same for every case. Why this size: (a) it contains float32
  rounding of every stored weight (relative error 2⁻²⁴, so below 10⁻⁶ for |w| < 16);
  (b) it contains at least one ordinary fine-tuning step (learning rate 10⁻³, gradient
  entries of order 1), and the fine-tuning test below moves weights up to the full τ.
- **δ = max(range / 20, 1/5)**, rounded up to a multiple of 1/100, where range is the
  spec's output range over the box (exact evaluation at the corners and 20,000 grid
  points). So the output may move by at most 5% of the spec's range (or 0.2 for specs
  with a range under 4). Exact equality is impossible under perturbation; this is the
  pre-registered meaning of "correct".
- What the ball does **not** cover: rounding inside the arithmetic of a float forward
  pass. It covers rounding of the stored weights only. A float32 forward pass is measured,
  not proved.

Design calibration, done before writing this (not a result; `tools/r3_calibrate.py` on
the 20 rung-1 nets): at τ = 1/1000 a simple layer-by-layer bound stays under 5% of the
range for 10 of the 20 existing nets, all with at most 3 hidden layers; the deep ones need
a tighter argument or a shallower network. So the bar is neither trivial nor hopeless.

## Part A: MLPs (primary)

**Cases.** `tools/specpool.py` pool of rung 1 (seed 20261111). New draw, seed 4044, from
the 266 specs not drawn at rung 1: 2 dev, **12 test**, 6 reserve (generator faults only).

**Arms** (the same 12 test specs in each):

| Arm | Doctor writes | Theorem |
|---|---|---|
| **robust net** (primary) | `net` and `net_robust` | the weight-ball statement above |
| **prog** (verified-code control) | `prog` (if-then-else only) and `prog_correct`, as at rung 1 | `prog x = spec x` exactly |
| **twin** (trained, capped tolerance) | only the proof; weights given | the same weight-ball statement around the twin's rounded weights, with the **same δ** |

Twin rule, fixed before any twin is trained: twins are trained as at rung 1 (same
trainer, shape of the passing robust net, seed 0 given to the doctor). The twin's
tolerance is **not** derived from its own error; it is the case's δ. A twin whose sampled
error to the spec is already above δ/2 is "not eligible": it is reported as failing the
statement by evaluation and gets no doctor. At most 6 eligible twins get a doctor.

**Doctor protocol.** As rungs 1 and 2: one episode per case and arm, 12 submissions,
600 s and 4.5 GB per check, the same banned tokens (`native_decide` banned and counted),
scratch folder inside the case folder. Sonnet first. A robust-net case Sonnet fails gets
one Fable episode (one Fable agent at a time machine-wide, cleared with the
compute scheduler, reason in the run log (not released)). Sonnet-only and Sonnet-plus-Fable counts are
reported separately.

**Bars.**

- Primary: **S3 = number of the 12 test specs with a kernel-checked weight-ball proof.**
- **Kill: S3 < 4 → stop rung 3 and report it as a negative result.**
- Pass: S3 ≥ 8. 4-7 is "partial".

## Checks the study team runs on every proven net (no doctor)

1. **Inside the ball.** 10,000 random perturbations (uniform, sign corners, and
   gradient-ascent adversarial starts) at 2,000 box points each batch. The largest
   deviation from the spec must be ≤ δ. One violation would mean the framework or checker
   is wrong, and stops the rung.
2. **Outside the ball (the ball is not vacuous).** Adversarial search at radius s·τ for
   s = 2, 4, 8, ... 4096. Reported: the smallest s at which a violation of δ is found. If
   none is found up to 4096, that is reported as "no violation found" and the ball may be
   very conservative.
3. **Float32.** A float32 forward pass of the written weights at 10,000 float32 box
   points; the largest deviation from the exact spec is reported against δ.

## The comparison with verified code (the point of this rung)

A program has no weights, so it cannot adapt. The test, per proven net:

- Target: f* = spec + g, where g is an affine function of the inputs with a seeded random
  direction, scaled so that max |g| over the box is δ/4. Training data: 2,000 box points
  with Gaussian noise of standard deviation δ/4. Held-out data: 5,000 noise-free points.
- **Fine-tune inside the ball**: Adam on squared error, 2,000 steps, with every weight
  clipped back to within τ of its written value after each step (float64). Seeds 0, 1, 2.
- Measured: held-out mean squared error to f* for (a) the written network, which equals
  the spec and therefore equals the verified program, and (b) the fine-tuned network.
  Also checked: every fine-tuned weight is inside the ball, so the theorem applies to the
  fine-tuned network, and its sampled deviation from the spec is ≤ δ.
- Reference only: unconstrained fine-tuning with the same recipe, and whether it leaves δ.
- **"Advantage over verified code" is claimed only if**, on at least two thirds of the
  proven nets, fine-tuning inside the ball lowers the held-out error by at least 10%
  (median over seeds) while staying inside the ball. Otherwise "no advantage shown".
- Stated now: this advantage is by construction limited. The ball is small, so the
  network can only move a little; the target shift is chosen independently of the network
  and may not lie in directions the ball allows. And a program with tunable constants
  would be a network by another name. The test asks only whether the proven region is
  large enough to be worth something.

## Part B: transformers (after Part A; includes sort s00)

Background: rung 2's proved sort network s00 fails in float32 from length 300.

- **B1, lane analysis, always done.** For each of the 10 rung-2 nets, an exact search for
  a single-weight perturbation of size ≤ τ that makes the network wrong at some length
  ≤ 20. Expected result, stated in advance: every construction that relies on exactly
  tied attention scores (uniform averaging by an all-zero score matrix) or on margins of
  order 1/n breaks under arbitrarily small perturbations, so **no rung-2 network has a
  positive weight ball for all lengths**. The count and the breaking weights are reported.
- **B2, doctor arm, conditional.** Only if Part A reaches the pass bar and the week
  allows: a perturbed-transformer framework in which attention score weights stay exact
  and all other weights (embedding, value, MLP, read-out) move within a tolerance, at
  bounded length. Its statement, tolerance and bars would be fixed by amendment before any
  such doctor run. If it is not run, the table says so.

## Not claimed

Not a first for weight-ball certificates or for fine-tuning inside a certified region.
Not a proof about float arithmetic. Not softmax transformers. Not that trained networks
cannot be certified (solvers do this; they are not run here).

## Compute

As rung 2: one lean.exe at a time under a 3 GB memory reservation, doctors under a 1 GB memory reservation per two
doctors, service and doctor memory reservations requested as a pair, slots agreed with lanes 2 and 5.
Before releasing a memory reservation, check it has no live job. Numeric checks and fine-tuning are
numpy on CPU, 2 threads, under a memory reservation when over 15 minutes.

## Amendments

1. **2026-11-12, about 8:45 am EST, before any doctor run; test specs unread.**
   - Draw made (`tools/draw3.py`, seed 4044, 266 unused specs): dev p109 and p233; test-set
     sha256 `45d6ff83dfcd05f88b427a7e3d9a0512003c3ba10ebd53ef82bc4c58ce15e661`.
   - Framework `Lane4/Robust.lean` compiled (kit: `pert_abs_mul`, `pert_mul`, `relu_sub_le`,
     `relu_pert`, `abs_add3_le`, `relu_nonneg'`, `relu_le_of_le`). The study team's worked example
     (`examples/EXAMPLE_robust.lean`: `max x0 x1` on a box, one hidden layer of 3 units,
     δ = 2/5) passed the checker on its first compile. Smoke test: the example passes; a
     tighter δ, a larger τ, a changed output weight and a `native_decide` are each rejected.
   - A written network at this rung need not equal the spec exactly, so in the fine-tuning
     comparison the verified-code control is **the spec itself** (what the verified program
     computes), not the written network. The written network's error is reported next to it.
   - Fine-tuning details fixed in `tools/r3_checks.py` before any run: full-batch Adam,
     learning rate 1e-4, seed s uses generator seed 1000 + s for the shift direction, the
     data and the noise. Inside-ball check: 4,000 uniform, 4,000 sign-corner and 2,000
     adversarial perturbations (30 sign-gradient steps); outside-ball: 100 adversarial
     starts per radius, stopping at the first radius that breaks δ.
   - Tool trial on the worked-example net only (not a result): the largest deviation found
     inside the ball is 0.031 (the proof's bound is 0.044, δ is 0.4), and δ first breaks at
     16 τ.
2. **2026-11-12, 9:27 am EST, after the dev pilot, before any test case was built or read.**
   Dev pilot (not a result), all Sonnet: net p109 PASS (2 submissions), net p233 PASS (2),
   prog p109 PASS (1), prog p233 PASS (2). Both networks have 3 hidden layers; the doctors
   report proved bounds of about 0.22 against 0.25 and 0.21 against 0.24, so the bar is
   close for specs of this depth. No prompt, framework or generator change after the pilot.
   Frozen hash (make_r3_cases.py, make_cases.py, r3_twins.py, train_twin.py, r3_checks.py,
   check.py, service.py, submit.py, doctor_prompt_r3.txt, EXAMPLE_robust.lean,
   EXAMPLE_prog.lean, Basic.lean, Robust.lean, concatenated in that order), sha256:
   `cc28487ee7b7b69733985dba67f4b5413307498d5be3d77333e8fd9c7d97ff0b`
