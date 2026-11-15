# this study, rung 5 pre-registration: softmax transformers proved correct at every length, over a weight ball, in binary32 arithmetic

Written 2026-11-13 evening, before any doctor episode on a rung-5 task. Before this file
the study team wrote and compiled the framework and one worked example, and four framework
lemmas were proved by Sonnet agents as kit tasks (below). Changes after this point go in
dated amendments at the bottom.

## Why this rung

Rung 4 proved hard-attention transformers against a rounding model that left out
overflow, underflow and subnormals, with attention that is not what any real transformer
computes. Rung 5 asks for the same kind of theorem about softmax attention and about
IEEE binary32 arithmetic, for a network that can be loaded and run in PyTorch.

## The claim under test, and what is NOT claimed

Novelty (NOVELTY.md, rung-5 section): a narrow first survives a web search over
abstracts: no proof-assistant-checked theorem was found that a softmax transformer
computes a stated function at every length up to a bound, for every weight setting in a
ball, under a model of binary32 arithmetic. Not claimed:

- That soft attention can simulate hard attention with length-independent parameters:
  Yang, Strobl, Chiang and Angluin (arXiv 2412.09925) and C-RASP (arXiv 2404.04393)
  prove that by hand, in exact arithmetic. The score-gap idea used here is theirs.
- A Lean model of float32: TorchLean (arXiv 2602.22631) has a bit-level one.
- Anything about trained networks, counting tasks, or the standard PyTorch layers.

## The statement (one theorem per case, plus two corollaries the study team derives)

    ∀ u η M fl ex, Rnd u η M fl → ExpM u η ex → 0 ≤ u ≤ 2^-24 → 0 ≤ η ≤ 2^-149 →
    ∀ p : Pert, p.Within (1/200) →
    ∀ w (tokens in 1..V), with n = length w + 1:
        u·n ≤ 1/256 → η·n ≤ 2^-100 → 2^40·n² ≤ M →
    ∀ i in 1..length w,  |sout net fl ex p w i − target w i| ≤ 1/4

`Final.lean` (written by the study team, the same text for every case) then derives, and the
kernel checks:

- **`exact_all_lengths`**: exact real arithmetic, the real exponential, **every input
  length**, every weight setting in the ball.
- **`binary32`**: for every `fl` that agrees with a round-to-nearest onto the binary32
  grid on the finite range, every float exponential within the stated error, every
  weight setting in the ball, **every input of at most 65,535 tokens**.

A case counts only if the statement, both corollaries and the shape check are all
kernel-checked with the standard axioms. No partial credit.

### The float model, and what "IEEE" covers

- `Rnd u η M fl`: for `|x| ≤ M`: `|fl x − x| ≤ u·|x| + η`, monotone, idempotent; exact on
  integers up to 2^24. **Nothing is assumed for `|x| > M`.** So a proof cannot use any
  operation whose exact result leaves the range: overflow is ruled out by the proof
  itself, not assumed away.
- `Lane4/Bin32.lean` (kit case kC2, kernel-checked): with the binary32 grid `m·2^e`,
  `|m| < 2^24`, `e ≥ −149` (subnormals included), any `fl` that agrees on
  `|x| ≤ maxF = (2^24 − 1)·2^104` with a round-to-nearest onto the grid (any tie rule)
  satisfies `Rnd 2^-24 2^-150 maxF fl`. This is IEEE 754 binary32 `+ − × ÷` on finite
  values with finite results. Not modelled: the bit encoding, signed zeros (identified),
  NaN and infinities (shown not to arise), other rounding modes.
- **exp is a hypothesis.** IEEE 754 does not fix `exp` and PyTorch does not document
  its error. `ExpM u η ex`: `ex x ≥ 0`, `ex 0 = 1`, and for `x ≤ 0`
  `|ex x − e^x| ≤ 4u·e^x + η` (about two units in the last place, plus underflow). The
  theorem holds for every such `ex`. Whether numpy's and PyTorch's float32 `exp` meet
  it is tested by the study team on sampled arguments, not proved.
- **Operation order is stated, and it is not PyTorch's default.** Scores by rounded
  left-to-right dot products; softmax as `ex (fl (s − max))`, the weights and the
  weighted values summed left to right, then one division; zero weights contribute an
  exact zero; an empty candidate list gives 0. Fused multiply-add, SIMD or pairwise
  summation orders, and `torch.softmax` itself are outside the theorem.

### The PyTorch object

`tools/r5net.py` builds, from an exported network, a `torch.nn.Module` whose `forward`
performs exactly the stated order with float32 elementwise operations and
`torch.cumsum` (the study team checks it equals a numpy implementation bit for bit), and a
`forward_fast` using `torch.softmax` and matrix products. The theorem is about the first.
The second is compared numerically only. The module is our own small architecture
(position features `[1, i, n]`, no layer norm), not `nn.TransformerEncoder`.

### Ball, tolerance

As rung 4: relative ball, `fl (w·(1 + d))`, `|d| ≤ 1/200`, every weight; a written zero
stays zero. Tolerance 1/4 around an integer target in 0..3. One τ for all cases, set
before any doctor ran; the study team's own softmax carry construction has worst deviation
0.03 to 0.08 at τ in a numeric probe (two settings, `scratch/r5_feas.py`).

## Tasks

The four rung-4 families (carry, last, first, induct) from the same pool
(`pool/rung4_pool.json`, sha256 1448b52f...). Counting tasks stay out (rung 6). Draw seed
4046, excluding every setting drawn at rung 4 (dev, test, reserve) and the 12
feasibility settings: per family 1 dev, 3 test, 2 reserve. **4 dev, 12 test.**
Test-set sha256 (ids) 0a40dd3c3484e137beeef985478879632bc81caf390958a52acfdc491bb137f7.
The draw was run just before this file was committed so the dev cases could be
smoke-tested; the study team has not read the test ids. A reserve case is used only for a lane
fault, never because a doctor failed or crashed.

The families are the same as rung 4 on purpose: the rung changes the attention and the
arithmetic, not the tasks. Doctors are fresh agents and see nothing from rung 4.

## Arms

1. **net**: weights + proof of the statement. 12 test episodes.
2. **prog** (plain-code control): as rung 4, a one-pass fold with an exact proof, on the
   same 12 specs. It is expected to pass easily and proves a different statement.

Doctors: Sonnet, fresh agent per case, 12 submissions, 600 s and 4.5 GB per check, at
most 2 at once. `native_decide` banned and counted. Prompt
`prompts/doctor_prompt_r5.txt`: the rung-3 prompt with one sentence added ("Keep each of your responses
short: write files with the file-writing tool, not as long text in your reply"), because
both rung-4 crashes were agents exceeding the output limit in one reply.

**What doctors are given** (part of the result): `RSoft.lean` (model, softmax
definitions, a kit of rounding, stored-weight, product and position lemmas with range
conditions), `RSoftKit.lean` (`soft_near`: a winner with a score gap of at least
`16·|j − k|` gets its value returned within `B/100`; `soft_zeros`), one worked example on
a task outside the families ("output the previous token", one head, no MLP,
position-only score with slope 17), and a paragraph of advice. As at rung 4 the
exact-zero penalty score is not shown. The kit carries the softmax analysis entirely:
doctors never reason about exponentials.

**How the kit was made.** The study team wrote the definitions, the statements and the basic
lemmas. Four lemmas were proved by Sonnet agents through the same checker, as framework
tasks with hints from the study team (`runs/r5-kit`): rounded sums and a geometric distance
sum (kA2), the softmax lemma (kB), binary32 satisfies the model (kC2). Each passed
within 2 submissions. No Fable agent has been used.

## Fable (a lab rule)

Sonnet first on every case. If the net arm ends below the pass bar, the study team may run one
Fable doctor at a time on failed test cases after clearing each use with the coordinator
session and logging the reason. Fable results go in a separate column.

## Bars (set now)

S5 = number of the 12 test specs whose net-arm statement and corollaries are
kernel-checked by a Sonnet doctor. A doctor that crashes or runs out of submissions
counts as a fail.

- **Kill: S5 ≤ 2.**
- **Pass: S5 ≥ 6, with at least 2 families fully or partly solved.**
- **Headline wording if passed:** "N of 12 written softmax transformers kernel-checked
  correct at every length in exact arithmetic and up to 65,535 tokens in binary32
  arithmetic (stated operation order, exp accuracy assumed), for every weight setting
  within 0.5% (relative); non-counting tasks only."

Dev pilot (4 cases, net arm): only to find faults in kit, example, task file and tools.
Faults may be fixed; then everything is frozen by hash before test cases are built.

## Checks the study team runs on every proved network (no doctor)

`tools/r5_checks.py`, numpy and PyTorch on CPU, under a memory reservation.

1. **Inside the ball, float64 with float64 exp** (stands in for exact arithmetic): 40
   uniform and 40 sign-corner perturbations at τ, lengths 6 to 2,000, the four input
   patterns of rung 4. Any output further than 1/4 from the target contradicts a
   theorem and stops the rung.
2. **Non-vacuity:** sign-corner perturbations at 2τ, 4τ, ... 64τ, lengths up to 20,000;
   report the smallest multiple that breaks the tolerance.
3. **binary32 in the stated order:** numpy float32, written weights and 5 corner
   perturbations at τ, at 1,000, 16,000 and 65,534 tokens. The PyTorch module's
   `forward` must give bit-identical outputs to numpy on the same inputs (reported as a
   count of mismatching outputs).
4. **Ordinary PyTorch (`forward_fast`)**, same inputs: worst deviation from the target.
   Outside the theorem; reported as is.
5. **The exp hypothesis:** numpy and PyTorch float32 `exp` against float64 `exp` on
   200,000 arguments in [−110, 0] (uniform, plus points near zero and near the
   underflow threshold): the worst value of `|ex x − e^x| / (4u·e^x + η)`. Above 1
   means the installed `exp` does not meet the hypothesis; reported, not hidden.
6. **Beyond the theorem** (one-block networks): float32 at 200,000 tokens, written
   weights.

## What would make the result weak, written down now

- The kit does the hard analysis; doctors assemble. If S5 is high, the finding is that
  the softmax and float analysis can be packaged into two lemmas, not that Sonnet can
  do float analysis.
- Same task families as rung 4, chosen by the study team; non-counting only.
- Relative ball; zeros stay zero.
- `exp` accuracy is assumed; the operation order is not PyTorch's default; the module
  is our own architecture.
- The length bound 65,535 comes from the model, and is conservative.
- 12 cases, one model, one τ.
- The plain-code control will almost certainly pass with far shorter proofs.

## Logging and stopping

Every run goes in `lab log/`. Results per case in `results/rung5-*.json`. All Lean and
doctor batches under memory reservations with honest ETAs (rung-4 doctor episodes took 10 to
70 minutes; a 12-case net arm at 2 at a time is budgeted at 4 to 5 hours). Stop for a go
after the final table, or as soon as the kill bar is certain.

## Amendment 1, 2026-11-13 about 8:50 pm EST, before any doctor episode

- **exp gets a larger underflow allowance in the binary32 corollary.** Running check 5
  ahead of time showed numpy's and PyTorch's float32 `exp` at 0.99999 of the bound
  `4u·e^x + 2^-150` right at the underflow threshold (the result is a subnormal one unit
  away), which leaves no room. The corollary `binary32` now assumes
  `ExpM 2^-24 2^-149 ex` and uses the rounding model with the same `2^-149` (a weaker
  model, proved from the `2^-150` one by `rnd_weaken`). The per-case statement is
  unchanged (it already allowed any `η ≤ 2^-149`). Check 5 uses `η = 2^-149`.
- With that, measured on 200,001 arguments (`results/r5-exp-check.json`): worst ratio to
  the bound 0.83 for numpy 2.5.4 (relative error up to 3.3 u in the normal range) and
  0.50 for torch 2.15 CPU (1.05 u in the normal range, 0.50 at the underflow threshold).
  So the hypothesis holds on the sample for both, with little slack for numpy.
- `Final.lean` text is fixed as `scratch/FinalR5Test.lean` (with the token count filled
  in); smoke re-run clean (`logs/smoke5-02.log`).

## Amendment 2, 2026-11-13 about 10:15 pm EST: dev pilot done, freeze

- Dev pilot, net arm, Sonnet, 4 cases: l26 PASS at submission 1, c11 PASS at 4, f33 PASS at 1,
  **i13 (induct) FAIL**: the doctor stopped after 7 of 12 submissions with the proof about
  half built (2 blocks, width 20). These are not results.
- What the i13 failure shows: with softmax the first block no longer copies exact zeros
  (its output is the value within B/100, not the value), so a two-layer construction
  needs a ReLU step that restores exact zeros before the second selection, and a much
  longer proof. That is the difficulty of the task under this rung's rules, not a fault
  in kit, example, task file or checker. **Nothing was changed after the pilot.** The
  induct family may score 0 of 3; the bars stay as set.
- Frozen files: sha256 list in `scratch/freeze_r5.sha256`, whose own sha256 is
  49f7d5efbaabff228e72a9974ac732ec0d8bd3f87b9cd323000698104b5e3c9b.
- Test cases are built after this commit.

## Amendment 3, 2026-11-14 about 2:40 am EST: check tool fixed after a memory kill

- After both doctor arms were complete (net 12/12, prog 12/12, from attempt logs), the
  lane's check run was killed by the machine's memory guard at 2:30 am: on the first
  two-block network (i00) the ordinary-PyTorch path of `tools/r5net.py` built an
  n x n score matrix for all 65,534 positions (17 GB) under a 3 GB reservation, and commit
  reached 98%. Six one-block networks had been checked before that.
- Fix (after the freeze, lane tools only, no doctor-facing file): `_attend_fast` now
  works in row chunks (same computation); `tools/r5_checks.py` exits if its own commit
  passes 2.5 GB; the reservation ETA is raised. The six finished networks are not re-run.
- Check 3 result so far that needs saying now: the PyTorch module's stated-order forward
  is NOT bit-identical to numpy on one of the first six networks (c04: 142 of 9,576
  outputs differ). Reported as the pre-registered count. A likely cause, to be measured
  and not assumed: numpy's and PyTorch's float32 `exp` are different implementations
  (check 5 found different error profiles), so the two stated-order passes can differ
  in the last bits wherever a softmax weight is not 0 or 1.
