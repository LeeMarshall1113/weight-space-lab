# the proofs study, rung 9-LN15 pre-registration: a NEW, post-hoc LayerNorm rung at ball 2^-15

Written 2026-11-22 (Sunday, early morning EST). Registered on the project owner's decision to run it staged. No doctor tokens are spent
before that decision is recorded.

## Post-hoc disclosure, stated first

**This is not rung 9-LN.** Rung 9-LN (`PREREG_R9LN.md`, ball 2^-14) stopped at its kill rule K2
(5 of 18 tuning networks accepted; the line was 6) and stays recorded as stopped
(`RESULTS_R9LN.md`). This rung exists because of what was seen after that kill. **All of the
following were chosen after seeing the tuning table, on the same 18 tuning networks:**

- **the radius 2^-15** (chosen after seeing 13 of 18 accepted there and 5 of 18 at 2^-14);
- **the enclosure design** ("design 4": one symbol per perturbed weight, LayerNorm linearised
  with second-order remainders), the fourth design fitted to these 18 networks; the first three
  accepted 0 of 18 at 2^-14;
- **the symbol merging** ("mode 2": 40 to 45 symbols), chosen among four variants by acceptance;
- **fixed-point arithmetic** in the checker, chosen after a kernel timing probe.

So the tuning count (13 of 18) is not evidence of anything. The only count that can be read as a
result is the one on fresh seeds, trained after the checker is frozen. Any headline carries the
sentence: "the radius 2^-15 and the checker design were chosen after a registered attempt at
2^-14 failed its kill rule on the tuning networks."

## What had been seen when this was written

Everything in `RESULTS_R9LN.md` and its addendum: four prototype designs on the 18 screened
tuning networks (seeds 100 to 119 of recipe n1 less 110 and 111) at seven radii; four
symbol-merging variants at two radii; a synthetic kernel timing probe. No Lean exists for the
LayerNorm model, the checker or any lemma. **Seeds 400 to 419 have never been trained** (rung
9-LN stopped before reaching them) and no directory for them exists.

## Statement

**Task, network, training, screen:** exactly as `PREREG_R9LN.md`: task A; one block, width 8, two
heads (strict, causal), slope 24, MLP hidden 12, three LayerNorms in the pre-LN places, ε = 10^-5;
recipe n1 from the frozen `tools/r9ln.py`; the frozen screen (s1, and s3′ at radius 2^-14, which
is stricter than this rung's ball and is kept so that no screen was tuned for this rung).

**Ball.** 2^-15 around W14 (weights rounded to the 2^-14 grid), additive, every weight including
the LayerNorm gains and biases. Rounding to the 2^-14 grid moves a weight by at most 2^-15, so
this closed ball is the smallest ball around W14 that contains the trained network. It is half
of rung 8's radius and 1/32 of rung 7's; near 1 it spans 256 float32 steps.

**Theorem aimed at.** `SoundLN`: if the checker accepts at radius δ, then every network within
the additive δ-ball of the stored weights, evaluated in the rounding model, is within 1/4 of the
task target at every position of every input of every covered length (exact arithmetic: every
length; binary32 model: up to 65,535 tokens, as rung 8). The rounding model is rung 8's with two
additions that are assumptions about binary32, not theorems: square root is correctly rounded;
the model is used in its relative form (each operation's error at most 2^-24 times the result's
magnitude plus an underflow term). The model definition (`Lane4/LNNet.lean`, new) follows the
operation order of `tools/r9ln.py run` and is fixed before the first kit case. Per network: the
four rung-8 theorems, generated, `decide +kernel`, standard axioms; `native_decide` and `sorry`
banned.

**Checker.** Design 4 with mode-2 symbols (`tools/r9ln_proto4r.py --mode 2` is the reference for
its decisions), written in Lean over integers scaled by 2^56 with floor and ceiling division.
The checker's Lean text may differ from the prototype in details that soundness requires; every
such change is logged with the tuning count before and after. A Python mirror must give the
kernel's decision on every file.

**Headline sentence if passed (fixed now).** "N of M gradient-trained one-block softmax
transformers with LayerNorm, from fresh seeds, are proved by one soundness theorem and a
kernel-checked certificate each to compute the task at every position of every input length, for
every weight setting within 2^-15 of the rounded weights, in a binary32 rounding model. The
radius and the checker design were chosen after a registered attempt at 2^-14 failed its kill
rule on the tuning networks." No "first"; teal-sea, Gross et al., Stambler et al. and Somani
cited for what each has.

## Stages (report at each boundary with tokens spent, including a kill)

1. **Soundness only.** Lean model, checker text, kit cases proved by doctors, `SoundLN` assembled
   and kernel-checked. If this fails under the kit rules: stop and report. No generator, no
   fresh network.
2. **Kernel limits.** Mirror, generator, the 13 accepted tuning networks through the kernel.
3. **Freeze by hash; fresh seeds; bar; controls; numericchecks.**

## Kill rules

- **KS (soundness).** A kit case fails two Sonnet doctors and the one stronger-model step: stop. Doctors:
  Sonnet, one retry per case, at most 3 Sonnet doctors running lab-wide, no nested agents. The
  one stronger-model step is held for the LayerNorm remainder lemma.
- **KT (tokens).** Budget 3.5 to 5 million Sonnet doctor tokens for the whole rung. At 5 million
  with soundness not assembled: stop.
- **KK (kernel).** Every file within 900 s and 6 GB under the 5 GB reservation, one Lean job at a time.
  The largest accepted tuning network (780 table rows: seeds 113, 114) must pass in at most four
  files; if it does not, stop. The probe's estimate for it is 3 to 4 files, so this rule is live.
  On fresh seeds a network that needs more than four files counts as not certified.
- **KM (mirror).** The kernel's decision differs from the mirror's on any file and the cause is
  not found: stop.
- **Usage.** usage budget read and logged before each kit case; no new case at 60%; hard stop
  at 75%.

## Bar and counts

- **Fresh seeds 400 to 419**, trained only after checker, mirror, generator and screen are frozen
  by hash, in ascending order. If fewer than three pass the screen, seeds 420 to 439 are trained
  and this is said.
- **Bar:** of the first three networks from seed 400 that pass the screen, at least 2 have all
  four theorems kernel-checked.
- **Count on the twenty:** trained; compute the task; pass the screen; accepted; rejected with the
  mirror's reason. No adjustment of the checker after the freeze. The tuning count is reported
  beside it and labelled as fitted.

## Controls (each must be rejected in the kernel; on one tuning network unless said)

Task B's automaton; embedding rows 1 and 2 swapped; read-out negated; read-out bias raised by
1/2; the gains of LN2 negated; radius 16 and 64 times larger (2^-11, 2^-9; not 2 times, because
5 of the 18 tuning networks are genuinely accepted at 2^-14); every fresh network that fails s1.
An accepted control voids the result until explained.

## Numericchecks on every accepted network (searches, not proofs)

As `PREREG_R9LN.md`: float64 and float32 to 65,534 tokens; W14 under sampled perturbations in
the 2^-15 ball; the breaking multiple; the numeric interval test against the mirror's table.

## What would make the result weak, written down now

- Everything in the disclosure above: radius, design, symbol merging and arithmetic all post hoc,
  four designs on 18 networks.
- The ball is the smallest that contains the trained network: there is no robustness margin
  beyond rounding to the grid, unlike rungs 7 and 8.
- Five tokens, one block, width 8, a local task, a fixed slope, the study team's own recipe.
- LN1 sees embeddings only; LN2 and LNf see a residual stream that takes few values. That is why
  this works here and did not in E3.
- The relative rounding model and the square-root assumption are the study team's reading of binary32.

## Frozen now

`scratch/freeze_r9ln15.sha256`: this file and the unchanged `tools/r9ln.py`. Its hash is in the
private log. The rung 8, mechanism, rung 9 and rung 9-LN freeze lists stay in force. Checker, mirror
and generator are frozen by a second list before any fresh seed is trained.

## Amendment 1, 2026-11-21 (Saturday) about 10:30 pm EST: before the first doctor

Written before any doctor token was spent and before any fresh seed was trained. The project owner's decision is
recorded.

**Date correction.** The first line of this file says "2026-11-22 (Sunday, early morning EST)".
That was wrong: the file was written and committed on 2026-11-21 (Saturday) about 8:45 pm EST. The line is left as it was and corrected here.

**Design changes to the checker, each with the tuning count at 2^-15 (18 screened networks,
interval test 0 violations every time):**

| step | checker | accepted |
|---|---|---|
| registered reference | prototype, mode 2 | 13 |
| 1 | integers scaled by 2^56; head-output radius as one symbol per coordinate; my prototype's copy of rung 8's head tables | 12 |
| (tried) | the same with rung 8's proved `headOK8` on the LN1 boxes | 4 |
| 2 | own head check `headOKLN`: `headOK8` conjunct for conjunct with score table, value table, value bounds and score guards on relative rounding charges | 14 |
| 3 | hardening for provability (below) | 14 |

Step 3, found by re-deriving every charge before cutting the kit: (a) the rounding of a STORED
BIAS was not charged (`chg (|b| + δ)` added in `lnOne` and `dotF`; without it the soundness
statement would be false when a row output and its bias nearly cancel); (b) one more term
`cdiv dv SC` in `rinvF` (the `+ 1` of the slope constant); (c) run-time guards that a symbol slot
is zero before it is set and that forms still in use are free of new slots, so that freshness of
a symbol is checked, not proved; (d) magnitude guards (15) on LayerNorm outputs, row outputs,
hidden units after the ReLU, the residual and the read-out. The 14 accepted tuning networks are
100 to 105, 108, 109, 112 to 115, 117, 118. **All of this was fitted to the same 18 networks.**

**Per-network file form.** One `decide +kernel` theorem per case (5 per abstract state), not one
per state: a state lemma peaked at 6.5 GB commit on a 30-case network; per case it is 4.55 GB.

**Kernel pre-check (no tokens; with the checker of step 2, re-run with step 3 before the first
doctor):** seed 104 (30 cases) 75 s; seed 100 (155 cases) 364.9 s, 4.76 GB; seed 113 (780 cases)
3 files of 611.1, 595.6 and 594.7 s, at most 4.96 GB. Kernel decision equals the mirror's on
every piece. With step 3 (the frozen text): seed 104 84.6 s, 4.59 GB; seed 100 388.7 s,
4.80 GB; both accepted. KK is unchanged and is re-measured in stage 2 with the final generator.

**What rung 8 proofs are reused.** Unchanged: `Lane4.R8KB` (softmax arithmetic), `R8KC`
(exponential enclosure), `R8KD` (shared attention), `R8KF` (windows automaton), and `headAF`
itself. Ported to `headOKLN`: `R8KA` (kit case lb), `R8KG` (lc), `R8K` (li). For lb and lc the
the study team generates a draft by text substitution (`tools/ln_port.py`) and submits it through the
ordinary check; a doctor repairs it only if it does not compile.

**Kit cases (statements in `Lane4/LNDefs.lean`):** la rounded chains and tables with relative
error; lb `ScoreWinLN`; lc `HeadSoundLN`; ld small lemmas on integer forms; le a stored row on
forms; lf LayerNorm centre and variance; lg LayerNorm reciprocal square root (the lemma the
stronger-model step is held for); lh LayerNorm assembled; li `SoundLN`. KS, KT, usage stops unchanged.

**Frozen with this amendment** (`scratch/freeze_r9ln15_a1.sha256`): this file, `Lane4/LNNet.lean`,
`Lane4/LNCert.lean`, `Lane4/LNDefs.lean`, `tools/r9ln15_cert.py`. A kit case that shows a
statement or a constant to be wrong leads to a dated amendment with counts, as in rung 7.
