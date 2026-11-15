# This study, transformer stage: pre-registration

**FROZEN 2026-11-07 (late evening EST), before any doctor run.** The "Frozen design" section
below overrides anything earlier in this file that conflicts with it.

## Frozen design

**Cases.**
- **T-random:** `xf/cases_xf_20261111.json`. 28 networks were trained and all 28 kept
  (2 layers, d = 64, 4 heads, no LayerNorm, AdamW for 2,000 steps; every one scores at least
  0.99 exact-sequence accuracy).
  - Counted set: the first 20 by index.
  - Templates are counting-based or permutation-based (see `xf/gen.py`).
- **Calibration:** `xf/cases_tracr_20261112.json`, n = 20 Tracr-compiled networks.
  - My numpy forward was validated against Tracr on 60 inputs per network.
  - Six permute-template programs were replaced, because Tracr does not compile a
    categorical Aggregate that has a default. So the calibration set has **no permutation
    programs**, and that is a stated difference from T-random.

**Conditions.**
- T-random: W, IO-unlim and IO-20, n = 20 each.
- Calibration: W and IO-unlim, n = 20 each.
- W is a superset of IO-unlim: it gets the weights plus the same unlimited oracle.
- Sonnet subagent doctors, one run per case.
- There is no time limit. The pilot step is dropped: the earlier stages showed that runs
  finish on their own.

**Dropped and deferred.**
- **Length-generalisation stratum: dropped.** Our learned position table covers only
  lengths up to 8, so there is no length-9-16 test.
- **T-classic and the study team-1 networks: deferred.** This keeps cost low.
- **The 2602.08857 baseline: deferred.** It needs a second install approval.
- **Enumerative-synthesis and attention-pattern baselines: deferred** to after the doctor
  arms. They are reported when run, labelled as added after the freeze.

**Primary test.** W against IO-unlim on T-random functional match, using a one-sided exact
McNemar test, alpha 0.05. The positive, null and kill rules are as stated below.

**Calibration comparison.** W and IO-unlim functional rates on the calibration set, side by
side with Thurnherr & Riesen's 73% functional and 26% exact. Also reported: our
exact-structure rate, judged by hand against `program.txt`.

**Audit.** All tool calls are audited. Doctors must not read `xf/cases*`, `program.txt` or
`residual_labels.json`.

## Amendment A1 (2026-11-07, after 2 of 10 first-batch reports; a request)

The first W report (e02) fitted the queries and ignored the weights, which is the RNN-stage
pattern. W against IO-unlim can therefore only show that weights plus queries are about the
same as queries alone. Added:

**W-0 arm** (T-random n = 20 and calibration n = 20):
- The doctor gets the weights and the equations, with no queries and no examples.
- **It may not run the network on token sequences.** It may analyse the weight matrices
  themselves:
  - embeddings and positional tables;
  - QK and OV products, and attention patterns computed from embedding rows;
  - MLP input/output maps on residual directions.
- Running the full forward pass on inputs, or any loop over input sequences, breaks the
  rule. The audit greps for this and I review flagged runs by hand. A run that breaks the
  rule is reported as a violation, and scored separately as "W-0 (simulated)".
- **The decisive comparison is W-0 against IO-20** (20 examples, no weights), plus the
  prior baseline below.

**Prior baseline (simplest program consistent with 20 examples).**
- Draw 200,000 programs from the same pool generator, `xf.gen.random_program` with seeds
  from a fixed stream. This baseline knows the generating distribution, which makes it a
  strong upper bound for a prior-only guesser.
- Keep the programs that agree with the case's 20 IO-20 examples.
- Score the expected functional match of a uniformly chosen survivor, weighted by how
  often each distinct program occurs.

**Per-run provenance label.** I read each run's tool calls and label it:
- *weight-traced*: the final program came from analysis code on the weights;
- *query-fitted*: it came from queries or examples;
- *simulated*: it came from self-simulating the network;
- *mixed*.

These labels are reported for every arm.

**Decision rule for "weight reading is real" at this scale.** W-0 must beat IO-20 on
functional match (one-sided McNemar, alpha 0.05) **and** exceed the prior baseline's
expected rate. Otherwise the result is "no evidence of weight reading". W against IO-unlim
stays as pre-registered (secondary now).

## Amendment A2 (2026-11-07, after the first 5 runs of each T-random arm; budget)

First-five results (functional matches):

| Arm | Matches | Note |
|---|---|---|
| W | 5/5 | after a scorer fix |
| IO-unlim | 5/5 | every program fitted to queries; no W doctor used the weights |
| W-0 | 0/5 | per-token maps sometimes read correctly, routing never |
| IO-20 | 3/3 so far | |

W and IO-unlim are at ceiling, and the W runs are query-fitted, so further runs in those
two arms carry no information. 

Changes:
- **W and IO-unlim** stop at n = 5. They are reported as such, and are not part of any
  decision.
- **W-0 and IO-20** run to n = 20. W-0 against IO-20 plus the prior baseline is the
  decision, as in A1.
- **Calibration** runs **W-0** (n = 20) and a new **IO-20** arm (n = 20: 20 examples, no
  weights). It drops the planned W and IO-unlim calibration arms for the same ceiling
  reason.
- **Thurnherr comparison:** calibration W-0 functional rate against their 73%. Their
  decompiler also sees weights only.

## Amendment A3 (2026-11-07, during the W-0 / IO-20 e05-e12 batch; a request)

The interim pattern is that W-0 reads *pieces* of the program but does not assemble
working programs. Two additions, each fixed before it runs.

**(1) Component-level scoring, blind to arm.**
- **Rubric.** For every case, a rubric is fixed from the true program (`program.txt`) and
  its template (`xf/gen.py`):
  - **C1, value table:** does the program's token→value or count→value mapping equal the
    true one, for every token (or for the modulus and threshold)?
  - **C2, routing:** which position or positions are read. The candidates are self, next,
    previous, mirror, or all.
  - **C3, comparison:** for Select, the compared quantities (tokens, indices or a Map
    group) and the comparison operator. This covers any token grouping.
  - **C4, combination:** how the parts combine, for example mod m, a threshold, (x+y) mod m,
    or an Aggregate default.

  Each component scores 0, 0.5 or 1. Components that don't apply to a template are N/A.
- **Judge.** One Sonnet subagent per arm-batch, given only (true program, submitted
  program.py) pairs. Pairs are shuffled across arms and stripped of arm, episode id and
  comments, so the judge is blind to the arm. The rubric text is in
  `xf/component_rubric.md` (written before judging).
- **Reported:** mean component score per arm, with a bootstrap CI.
- **Test:** W-0 against IO-20 on the mean component score, paired by case, with a
  one-sided Wilcoxon signed-rank test at alpha 0.05.
- **Claim this supports:** "partial weight-reading" if W-0 is above IO-20 *or* above the
  prior baseline's component score. The prior baseline's component score comes from
  judging a uniformly drawn survivor.

**(2) W-5 hybrid against IO-5, n = 20 each, T-random first 20.**
- **W-5:** the weights, the equations and **5 queries**. No other examples. Simulating
  the network is forbidden, as in W-0.
- **IO-5:** 5 queries, no weights.
- **Primary outcome:** functional match.
- **Test:** W-5 against IO-5 with a one-sided exact McNemar test, alpha 0.05.
- **Positive claim** ("weight reading reduces the queries needed"): W-5 beats IO-5.
- **Secondary:** components, as in (1).

## Amendment A4 (2026-11-08): perturbation curve. How far from Tracr structure does reading survive?

**Starting point.** The 20 Tracr-compiled calibration nets, where W-0 was 20/20. Every
variant keeps the architecture, the parameter names and the doctor-facing spec, so the
doctor is blind to which perturbation it got. Only the weights change.

**ROT, n = 20.** A random orthogonal rotation R of the residual basis (QR of a Gaussian
matrix, seeded per case):
- emb and pos become emb·R and pos·R;
- every matrix that reads the residual becomes Rᵀ·W;
- every matrix that writes to it becomes W·R, and its bias b becomes b·R;
- unembed becomes Rᵀ·U.

The function is exactly unchanged (checked to 1.0 agreement on 1,000 inputs), and
sparsity and basis alignment are gone.

**FT-k, k ∈ {10, 100, 1000}.** Fine-tune all weights for k AdamW steps (lr 3e-3, batch 64)
on the case's own task: inputs of length 4-8, with the compiled net's outputs as labels,
under a cross-entropy loss on the unembed logits.
- n = 10 for k = 10 and k = 100, and n = 20 for k = 1000.
- A variant is kept only if its exact-sequence agreement with the original stays at least
  0.99. Otherwise it is reported and replaced by the next case in order.
- Also reported per variant: relative L2 weight drift, and the fraction of near-zero
  weights (|w| < 1e-6), which measures the sparsity left.

**Not run:** (iii) Gaussian noise (optional; skipped to keep cost low). ROT+FT is also
skipped.

**Doctor.** W-0 exactly as in A1: weights and equations only, no queries, no simulation.
One Sonnet run per case. The audit and provenance labels are as in A1.

**Primary outcome.** Functional match per level, with exact 95% CIs. k = 0 is the
existing 20/20.

**Decision rule** (exact one-sided McNemar against k = 0, paired by case):
- **ROT ≤ 10/20** (half or less): "reading depends on basis alignment".
- **ROT ≥ 18/20:** "reading survives rotation". The doctor then reads algebraic structure
  (QK/OV products), not sparse coordinates.
- **The FT-k curve** is reported as is: the k at which success first falls below 50%.

## Amendment A5 (2026-11-08, before any A4 doctor run): FT-k replaced; the ladder is exact transforms

**FT-k is infeasible.** Gradient fine-tuning destroys the function of compiled nets at
once. This was probed on 4 cases, in float64:
- One AdamW step at lr 3e-3 drops agreement with the original to 0.00-0.33. AdamW
  normalises updates, so it shifts every near-zero weight by about lr.
- 10-100 steps at lr 1e-4 or 3e-4 do the same (0.02-0.46 on 3 of 4 cases).
- SGD at lr 0.1 or 1.0 diverges to NaN.

Tracr nets cannot be drifted toward "trained" while keeping their function. That is
reported as a finding in its own right: the compiled solution is not a stable point of
gradient training.

**A note on float32.** A float32 copy of the compiled weights alone dropped agreement to
0.02 on one case, which is why the probe used float64. Doctors always get the float64 npz.

**Replacement ladder.** Every step preserves the function exactly (checked at agreement
1.0 on 1,000 inputs) and removes more structure:
- **L1 = ROT (n = 20):** the residual-basis rotation, as in A4.
- **L2 = ROT+HEAD (n = 10):** L1, plus inside every attention head a random
  well-conditioned invertible A (Wq→Wq·A, Wk→Wk·A⁻ᵀ, with the biases transformed the same
  way) and B (Wv→Wv·B, Wo→B⁻¹·Wo). The singular values of A and B lie in [0.5, 2].
- **L3 = ROT+HEAD+MLP (n = 20):** L2, plus a random permutation of the MLP hidden units and
  a positive per-unit scaling s ~ logU[0.5, 2] (W1 columns ×s, b1 ×s, W2 rows ×1/s). After
  this, the only exact structure left is what any trained net also has.

**Decision rules.** As in A4 for ROT. In addition, the level at which success first drops
below 50% is reported. If L3 is at or below 5/20, the 20/20 at k = 0 is attributed to
reading sparse, aligned coordinates and not to reading the computation.

## Amendment A6 (2026-11-08): does training for discreteness bring weight reading back?

**Programs.** The same 20 T-random programs (the n20 manifest), the same architecture
(2 layers, d = 64, 4 heads, no LayerNorm) and the same 2,000 AdamW steps. There are three
training variants.

**(a) ANNEAL.** Every attention logit is divided by a temperature T that is annealed
linearly from 1 to **T_end = 0.2** over training. At export, the final factor 1/T_end is
folded into Wq, so the doctor-facing equations are identical to the T-random spec.

T_end was set by a pre-run pilot on 3 pool programs (seed-7 stream, not in the n20 set):
- T_end = 0.05: loss 3.5, accuracy 0.31. Training is unstable.
- T_end = 0.1: accuracy 0.68 / 0.99.
- T_end = 0.2: accuracy 0.93 / 1.00. Chosen.

**(b) SPARSE.** An L1 penalty λ·mean(|relu(x·W1 + b1)|) is added to the loss, with
λ = 1e-3 on the MLP hidden activations of both layers.

**(c) BOTH.** (a) and (b) together, with T_end = 0.2.

**Accuracy gate.** At least 0.99 exact-sequence accuracy on 1,000 held-out inputs (lengths
4-8), measured through the standard forward (that is, after folding). A program whose net
fails the gate gets one retrain with a new seed. If it fails again, it is reported as a
gate failure and excluded from that variant. If fewer than 15 of 20 pass, the variant is
reported as "accuracy cost" and its doctor results are secondary.

**Doctors.**
- W-0 (A1 rules), n = 20, on each of (a), (b) and (c).
- IO-20, n = 20, on (c) only. This keeps cost low: IO-20 was 19/20 on the standard
  trained nets.

**Primary test.** W-0 functional on (c) against W-0 on the standard trained nets (0/20),
with an exact one-sided McNemar test paired by program. Also W-0(c) against IO-20(c).

**Constructive claim, made only if all three hold:**
- W-0(c) ≥ 10/20;
- W-0(c) beats standard W-0 (p < 0.05);
- at least 15/20 of (c) pass the gate.

The claim would be: "training for discreteness makes trained transformers decompilable
from weights, at no accuracy cost". (a) and (b) are reported as the ablation.

**Audit and provenance** as in A1, with a simulation check on every W-0 run.

---

(Original draft text follows.)

## Question

Can an LLM doctor that reads the weights of a small, normally trained transformer write a
RASP program that reproduces the network's function better than:
- the same doctor given only behaviour, under a matched budget (the MIPS-style control); and
- automatic baselines?

**If reading the weights does not beat behaviour-only, the weights add nothing, and the
results will say so.**

## Networks

**T-random (primary), n ≥ 20.** These are random RASP programs drawn from a generated pool
(the RNN stage's lesson from 2611.08070: no famous task to guess).
- Each program has depth 2-3, built from Map with random lookup tables, SequenceMap,
  Select with random comparisons, Aggregate and SelectorWidth.
- The vocabulary has 4-6 tokens; training lengths are 4-8.
- Programs are rejected if their output is constant or depends only on length.
- For each program I train a 1-2 layer transformer with gradients (AdamW, d = 32-64, no
  LayerNorm, the same family as another study's).
- A network is kept if it gets at least 0.99 exact-sequence accuracy on held-out inputs.
- **Stratified by length generalisation** (tested on lengths 9-16). The analytic
  decompiler of arXiv 2602.08857 succeeds on length-generalising models and fails on the
  others, so an LLM-doctor advantage, if there is one, is expected on the
  non-generalising stratum.

**T-classic (secondary), n = 6 tasks x 2 seeds.** Reverse, hist, sort_unique,
most_frequent, Dyck-1 balance, and frac_prevs. These are reported separately, because the
doctor can guess them from I/O alone.

**Lane-1 nets (secondary), 20 multi-op networks**, copied read-only per `xf/SOURCES.md`.
They implement rev, inc, dec, shl, shr, swp and cpy, selected by an op token.

**Calibration (owner decision A, 2026-11-07), n = 20 Tracr-compiled networks.**
- **Programs:** the next 20 acceptable programs from `xf.gen.draw(seed=20261112)`.
  - They come from the same pool, but a different seed from the trained set.
  - They are compiled with `tracr.compiler.compile_rasp_to_model`, using the program's
    vocabulary, `max_seq_len=8` and `compiler_bos="BOS"`.
  - A program that fails to compile (Tracr issues #24, #25, #11) is replaced, and the
    replacement is logged.
- **What the doctor gets:** in the W condition, the compiled weights as an npz with Tracr's
  parameter names, plus a short note on Tracr's residual layout (BOS at position 0, the
  categorical one-hot residual). In the IO conditions, the same as for trained networks.
- **Scoring:** the same functional-match rule.
- **Reported against Thurnherr & Riesen 2410.00061** (autoregressive decompiler, TracrBench):
  73% functional and 26% exact.
- **Caveat for the comparison.** Their "functional equivalence" and test distribution
  differ from ours: they used their own program generator and their own equivalence check.
  So this is a side-by-side, not a matched test. Our exact-structure rate is reported too.
- **Run order:** calibration runs only after the Tracr install succeeds (it is blocked by
  auto mode as of 2026-11-07), and after the T-random arms.

## Conditions (Sonnet subagent doctor, sandbox with numpy, no optimisers on weights)

| id | gets | forward passes |
|---|---|---|
| W | the weights and the architecture equations | free (it can simulate the network itself) |
| IO-unlim | a black-box oracle only, with no weights | unlimited queries |
| IO-20 | 20 input/output examples | none |

W against IO-unlim is the clean test of whether the weights carry information beyond
behaviour. Both conditions get the same tools and time.

## Output and scoring

- The doctor writes a program using `xf/rasp.py`, whose names match `tracr.rasp`.
- It is scored by running the program in the interpreter against the network on 1,000
  held-out inputs: in-distribution lengths, plus the 9-16 stratum where applicable.
- **Primary:** exact-sequence agreement of at least 0.99 ("functional match").
- **Secondary:**
  - mean per-token agreement;
  - whether the program compiles under Tracr, if available;
  - program size;
  - exact structural match to the true program (T-random and calibration only).

## Baselines

1. Enumerative RASP synthesis from I/O: breadth-first search over programs up to depth 3,
   scored on 200 examples, under the same time budget.
2. Attention-pattern analysis: read each head's argmax pattern on probe inputs, map it to
   Select comparisons, and fill the Maps by lookup.
3. arXiv 2602.08857's analytic decompiler (github.com/lacoco-lab/decompiling_transformers).
   It decompiled 8/8 length-generalising algorithmic models and 9/14 formal languages, and
   it assumes linear LayerNorm, which suits our nets since they have no LayerNorm.
   Installing it is external code and needs approval, like Tracr.

## Decision rules (fixed at freezing)

- **Positive:** W beats IO-unlim on functional match (one-sided McNemar, alpha 0.05) on
  T-random.
- **Null (weights add nothing):** W is not above IO-unlim.
- **Kill (at this scale):** W gets 2/20 or fewer functional matches.
- **Stretch** (a Qwen-0.6B induction head, scored by loss recovered): only after a positive
  result.

## Open items

- The install was approved, but the install is still blocked by auto mode: it needs a permission
  rule, or the project owner runs the command. A second install approval is needed for the 2602.08857 code.
- Pilot one W and one IO-unlim doctor to set the time budget.
- 2602.08857 has been read (HTML, first 100k characters); notes are in
  the lab log.
