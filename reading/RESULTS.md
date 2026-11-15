# Transformer stage: decompiling to RASP (PREREG_XF, amendments A1-A3), 2026-11-08 early

Design: Sonnet doctors, n = 20 per decisive arm, every run audited. Functional match means
at least 0.99 whole-sequence agreement with the network on 1,000 held-out inputs.

## Trained transformers (2 layers, d = 64, random RASP programs, gradient-trained)

| arm | gets | functional | blind component score [95% CI] |
|---|---|---|---|
| W-0 | weights only, no queries, no simulation | **0/20** | 0.11 [0.03-0.21] |
| IO-20 | 20 examples | **19/20** | 0.89 [0.79-0.96] |
| W-5 | weights + 5 queries | 7/20 | 0.50 |
| IO-5 | 5 queries | 8/20 | 0.50 |
| W / IO-unlim | weights + unlimited queries / queries only | 5/5 / 5/5 (stopped at n = 5, A2) | - |
| prior baseline | knows the generator, filters by the 20 examples | 17.0/20 expected | - |

- **W-0 against IO-20:** components, one-sided Wilcoxon p ≈ 1.0. Functional, 0 against 19.
  **No evidence of weight reading.**
- **W-5 against IO-5:** 1 against 2 discordant cases, McNemar p = 0.88. **The weights do
  not reduce the queries needed.**
- **Provenance** (audit of the tool calls):
  - W-0: 15 guesses, 3 weight-traced, 2 mixed. Three runs are borderline on the
    no-simulation rule: single rows through the MLPs. None ran full forward passes.
  - W-5: 19 query-fitted.
  - W and IO-unlim: query-fitted throughout.
- **Anecdote, not supported by the blind scores.** A few W-0 doctors read a correct token
  map or token grouping from the OV→unembed products (e00, e02, e03). Attention routing
  was never recovered. The dense trained weights look near-random apart from a few
  directions.

## Tracr-compiled calibration (20 programs, the same pool without the permute template)

| arm | functional |
|---|---|
| W-0 (weights only) | **20/20** (19 weight-traced, 1 borderline) |
| IO-20 | 14/20 |
| prior baseline | 18.0/20 expected |
| Thurnherr & Riesen 2410.00061, autoregressive (their own generator and equivalence check, so not a matched comparison) | 73% functional |

- **W-0 against IO-20:** 6 against 0 discordant cases, McNemar p = 0.016.
- **Exact-structure rate:** not yet judged. The one example read by hand (e00) is
  functionally equal but written differently.
- **By the pre-registered rule, weight reading is real on compiled networks.** W-0 beats
  IO-20 and exceeds the prior baseline.
- **This is the expected easy case.** Compiled weights are sparse and structured, and the
  doctors read them by pushing hand-built residual vectors through the MLPs.

## Verdict

An LLM agent decompiles **Tracr-compiled** transformers from weights alone at 20/20
functional (n = 20, CI 0.83-1.00). That is above a matched I/O-only control and above
the 73% of a purpose-trained neural decompiler, though that comparison is not matched.

On **gradient-trained** transformers of the same programs it gets 0/20 from weights. It
loses to 20 I/O examples (19/20), and weights plus 5 queries do no better than 5 queries.

The gap between the two is the finding: **weight reading works where weights are
structured by construction, and does not transfer to trained weights at this scale.**
This is in line with 2602.08857's need for an exact re-parameterisation, and with
2611.08070's critique.

**Not done:**
- 2602.08857's analytic decompiler on our trained nets: needs an install approval.
- Exact-structure judging of the calibration programs.
- T-classic and the other networks of the study.

**2602.08857 baseline: not applicable without retraining** (project coordination's
decision B, 2026-11-08). The code was cloned locally to `ext/` (gitignored, not
redistributed). Four reasons:
1. The repository has no LICENSE file.
2. The pipeline only handles its own HuggingFace GPT-2 models (causal attention, LayerNorm
   under the linear-LayerNorm assumption, its own datasets). Our trained nets are
   bidirectional with no LayerNorm, and the Tracr nets are Haiku, so neither can be ported
   while keeping functional equivalence.
3. Its pruning-coefficient search submits HTCondor jobs over SSH.
4. Every model needs gradient-trained causal-pruning masks over several stages.

A fair comparison would mean re-training our programs as their GPT-2 models: about a day
of engineering, for a null result.

## Exact-structure judging, Tracr calibration (blind Sonnet judge)

Of the 20 functionally correct W-0 programs:
- 3 have exactly the true structure;
- 6 are partial (same template, an operation expressed differently);
- 11 have a different structure.

So the doctor recovers the function, mostly not the source program. Thurnherr & Riesen
report 26% exact, but their generator and equivalence check differ from ours.

## Perturbation ladder (PREREG_XF A4/A5): how far from Tracr structure does reading survive?

Fine-tuning compiled nets turned out to be infeasible. One AdamW step drops agreement to
0.00-0.33; SGD diverges to NaN; float32 alone can break a net. So the ladder uses
transforms that keep the function exactly (1.0 agreement on 1,000 inputs). W-0 doctors,
with a spec identical across levels:

| level | transform | functional | vs k = 0 |
|---|---|---|---|
| k = 0 | original compiled weights | 20/20 | - |
| L1 ROT | random rotation of the residual basis | **16/20** | lost 4, gained 0, p = 0.06 |
| L2 +HEAD | + random invertible QK / OV per head | 9/10 | lost 1, p = 0.5 |
| L3 +MLP | + random MLP permutation and positive scaling | **20/20** | lost 0 |

**Audit:**
- 0/50 runs simulated the network on sequences.
- Method labels: 38 token-space circuits, 12 mixed, 0 coordinate-reading, 0 guesses.
- In practice, doctors analyse single (token, position) rows through the QK, OV and MLP
  weights. Those products are exactly invariant to every transform in the ladder.

**Reading.** Reading survives basis scrambling. A4's ROT rule falls in between: 16/20 is
not ≤10 and not ≥18. L3 is 20/20, so the "sparse-coordinate" attribution from A5 does not
apply. The 20/20 on compiled nets is algebraic analysis in token space, not
basis-alignment pattern-matching.

**What that means for the trained/compiled gap.** The 0/20 on trained nets is therefore
not explained by dense coordinates. It comes from the computation itself:
- compiled nets implement discrete, saturated lookups and selections, so token-space
  circuits produce clean tables;
- gradient-trained nets spread the same function across soft attention and MLPs, where
  those tables are not clean.

**Caveats:**
1. Exact zero columns (unused units) survive these transforms. Near-zero weight fractions
   stay at about 0.55-0.6, so some sparsity is left.
2. The audit used keyword scans plus selected full reads.
3. n = 10 at L2.
4. One model, one run per case.

## Training for discreteness (PREREG_XF A6), 2026-11-08

The question was whether training the nets to be more discrete makes them readable from their
weights alone. The setup:
- The same 20 programs and architecture as the standard trained nets.
- Three training variants:
  - **ANNEAL:** attention temperature annealed 1 → 0.2, then folded into Wq.
  - **SPARSE:** L1 penalty of 1e-3 on the MLP activations.
  - **BOTH:** the two together.
- Accuracy gate: at least 0.99 exact-sequence accuracy, with one retrain allowed.
- Doctors: Sonnet, at most 3 running at once, the A1 rules.
- Commit `6d37bb1` (the nets and the prepared episodes) went in before any doctor ran.

| Variant | Passed the gate | W-0 functional | W-0 mean seq-agree | IO-20 functional |
|---|---|---|---|---|
| ANNEAL | 9/20 (accuracy cost) | 0/9 | 0.07 | not run (by design) |
| SPARSE | 20/20 | 0/20 | 0.09 | not run (by design) |
| BOTH | 12/20 (accuracy cost) | **0/12** | 0.05 | **10/12** (mean 0.99) |

**Primary test.**
- **W-0(BOTH) against standard W-0** on the same 12 programs: 0 against 0, with no
  discordant pairs. The one-sided McNemar test gives p = 1.
- **W-0(BOTH) against IO-20(BOTH):** 0 against 10, with 10 discordant pairs. The one-sided
  test favouring IO gives p = 0.001.

**Constructive claim: not made.** It fails all three of its conditions:
- W-0(c) is 0/20, not at least 10;
- W-0(c) does not beat standard W-0 (p = 1);
- only 12/20 nets passed the gate (15 was required).

SPARSE is the one variant that costs no accuracy, and it is also 0/20.

**Audit.**
- All 53 runs: 0 flags (private files, optimisers).
- Simulation check (string loops through a softmax forward): 0 suspect.

**What the doctors reported.**
- Almost every W-0 doctor described near-uniform attention, or a direct-path argmax table,
  and called its answer a guess. One exception: ANNEAL e01 read a next-position attention
  pattern, but its value table was wrong.
- At this scale and with these penalties, training for discreteness gives no circuit that a
  doctor can read. The gap between trained and Tracr-compiled nets is not closed by
  sharper attention or sparser MLPs.

# Legibility decay curve (PREREG_DECAY, cut version), 2026-11-14: stopped by kill rule 1

**Verdict.** A gated decay curve cannot be built from Tracr nets. Every arm fails the
pre-registered feasibility rule: ≥ 15/20 nets keeping ≥ 0.99 agreement at ≥ 0.05 drift,
or at d′/d ≤ 0.9 for COMP. No doctor episodes were spent.

| Arm | Nets kept at the gate (points 1 / 2 / 3) |
|---|---|
| FT, FT+WD, SHIFT (pilot, 6 learning rates) | 0/20 at every setting. Slow rates do not move the weights (drift ≤ 0.0014 after 3,000 steps); faster rates break the function before 0.05 drift. |
| NOISE (ε 0.01 / 0.10 / 0.40, then Adam 1e-3 repair, ≤ 2,000 steps) | 6 / 7 / 6 |
| COMP (d′/d 0.9 / 0.7 / 0.5, learned E) | 6 / 6 / 6 |

**The survivors are the same 6 nets in every arm and point:**
- 5 count_cmp and 1 count_combine;
- one more count_combine net survives NOISE point 2 only.

The other 14 of the 20 compiled nets have essentially no robustness margin: any
gradient step, noise or compression breaks them, and repair does not bring them back.
This fits A4's finding that one optimiser step or float32 rounding breaks them.

**Cheap metrics on the survivors.** These are descriptive only. The set is small and
selected by robustness, so it is not a curve.

| Set | n | M1 | M1_qk | M1_write | M3 | M4-pass |
|---|---|---|---|---|---|---|
| k = 0 | 20 | 1.00 | 1.00 | 1.00 | 1.00 | 20 |
| NOISE p1 (0.01) | 6 | 0.74 | 0.86 | 0.63 | 0.59 | 5 |
| NOISE p2 (0.10) | 7 | 0.68 | 0.85 | 0.51 | 0.61 | 7 |
| NOISE p3 (0.40) | 6 | 0.66 | 0.95 | 0.37 | 0.56 | 6 |
| COMP p1-p3 | 6 | 0.65-0.67 | 0.95 | 0.36-0.39 | 0.48-0.52 | 5-6 |

**What the first write-up said this shows (the first two points are withdrawn; see "Withdrawn" below).**
- **Compiled nets are isolated points, not one end of a continuum.** For 14 of 20, the
  function does not survive a move of drift ~0.001-0.01 in any direction tried.
- **That is a concrete reason gradient training never lands on Tracr-like weights.** The
  readable solution is a knife-edge, and trained nets sit in the wide basins around it.
- **On the robust minority, write-table discreteness collapses first.** M1_write falls to
  0.4-0.6 while the hardened-attention proxy (M4) still passes and QK stays sharp. This
  is a hint, from 6-7 nets, that the value/MLP side is where legibility goes first.

**Not done, as pre-registered:**
- doctor READ and EDIT;
- the arm choice;
- kill rules 2-3.

**Possible re-scope (needs a new prereg and a go):**
- build the curve the other way, starting from robust nets: Tracr with widened margins,
  or the 6 survivors, or a trained net sharpened toward discreteness;
- or report the brittleness itself as the finding.

**Compute.** Four reservations, peak commit 3.5-5.4 GB. One NOISE build had a repair-loop bug
(it exited at step 0); it was fixed and rebuilt, and the bad build was not used.

## Correction to the decay section (2026-11-15, after an independent AI reviewer's review, point 10)
Some sentences above went further than the data. **What was shown, exactly:**
- **Gradient arms (FT, FT+WD, SHIFT).** At 6 learning rates (SGD 1e-4, 1e-3; Adam 1e-5 to
  1e-2), with batch 64 and a 3,000-step cap, 0/20 nets met the pre-registered rule: reach
  0.05 relative parameter drift without dropping below the gate at any checkpoint before
  that.
  - At the gentlest settings the nets stayed gated but barely moved (drift ≤ 0.0014).
  - At Adam 1e-5, 13/20 dipped below the gate at least once.
- **NOISE.** One repair schedule (Adam 1e-3, ≤ 2,000 steps, one seed): 6/7/6 of 20 were
  gated after repair at ε = 0.01/0.10/0.40.
- **COMP.** One schedule (Adam 1e-2 on E, ≤ 3,000 steps, one seed): 6/20 were gated at
  each ratio.
- **The gate** is sampled agreement (≥ 0.99 on 1,000 random inputs, seed 7), not verified
  function preservation. The same inputs were reused to pick checkpoints, which can
  overfit the gate.

**Withdrawn:**
- "The other 14 have essentially no robustness margin: any gradient step, noise or
  compression breaks them"
- "the function does not survive a move of drift ~0.001-0.01 in any direction tried"
- "compiled nets are isolated points, not one end of a continuum"
- "a concrete reason gradient training never lands on Tracr-like weights"

These schedules, at these budgets, failed. That does not show that function-preserving
paths do not exist: exact rotations and scalings (the A4/A5 ladder) are large in parameter
norm and preserve the function exactly.

**Survivor bias.** The metric table covers the same 6-7 robust nets, chosen by surviving.
It describes them only, and the "write tables lose discreteness first" hint is withdrawn
as a finding.

**Corrected headline.** Under the pre-registered budgets, no gradient schedule moved Tracr
nets to 0.05 drift while keeping sampled agreement ≥ 0.99 (0/20). One noise-repair schedule
and one compression schedule kept 6-7/20. Kill rule 1 stopped the curve. This rules out
these schedules, not function-preserving movement in general.

**If the curve is ever re-run:**
- a held-out gate separate from the checkpoint-selection inputs;
- rare and adversarial sequences in the gate;
- gate failures reported next to read success;
- functional distance reported next to parameter drift.

# Bridge stage 1: kernel-checked weight-ball certificates for tiny trained ReLU nets (PREREG_BRIDGE), 2026-11-15

**Setup.** popcount(x) mod 3 = 0 on all 64 inputs of 6 bits; nets 6 → 16 → 16 → 1, quantized
to multiples of 1/256. The statement, checked in Lean: every weight and bias within
τ = 1/1000, every input, correct sign. The framework (`bridge/lean/Bridge/IBP.lean`) was
frozen in A3 before any test seed was trained. Test seeds 100-107 were run once.

| Arm | Eligible (64/64 quantized) | Kernel-checked at τ = 1/1000 (primary) | Rational IBP at 1/1000 and 1/300 (B2) | Largest certified τ, median (range) | Min margin, median | τ / margin, median | Falsifier violations at 1/1000 |
|---|---|---|---|---|---|---|---|
| ORD | 8/8 | **8/8** | 8/8 and 8/8 | 0.0074 (0.0058-0.0105) | 8.5 | 0.0009 | 0 |
| STR | 8/8 | **8/8** | 8/8 and 8/8 | 0.0057 (0.0035-0.0088) | 1.04 | 0.0055 | 0 |
| RND (own sign, B3) | 0/8 against the task | not run (SpecN fixes the task label) | 5/8 at 1/1000 | 0.0016 (0-0.035) | 0.03 | 0.10 | 3 (exactly the 3 IBP could not certify) |

**Kernel-check details.**
- Every certificate depends only on [propext, Classical.choice, Quot.sound]. There is no
  `native_decide`.
- 59-67 s per net, at 4.2 GB peak commit.
- The kernel result agrees with the outside-Lean rational IBP (B2) on all 16.

**Bars.**
- **Pass met:** P_ORD = 8/8 ≥ 6.
- **Structured effect not met:** STR − ORD = 0, and STR's median certified τ is 0.77× ORD's,
  not 4×.
- **Kill:** not triggered.

**What it means, stated narrowly.**
- **Tiny trained nets cross the proofs study's weight-ball boundary at this size.** With exact
  finite inputs and a sign tolerance, ordinary training already gives nets whose quantized
  weights carry a kernel-checked τ = 1/1000 weight-ball certificate, 8 of 8. So at this
  scale the lab's "written works, trained fails" wall does not appear for this kind of
  statement.
- **This is weight-space IBP, kernel-checked.** Weng et al. 2020 did the method;
  TorchLean/LeanCert-style tools check IBP in Lean. Nothing here is a new technique.
- **"Certified radius" alone is not evidence.** Random near-constant nets, certified
  against their own sign, reach larger radii (up to 0.035) than any trained net. Radius has
  to be read relative to margin and tightness.
  - STR has about 6× more certified radius per unit of margin than ORD (0.0055 vs 0.0009),
    though less absolute radius.
  - That is a description, not a pre-registered effect.
- **The certificate is about the quantized net**, not the float weights (the 1/512 rounding
  step is larger than τ). Stage 2b tests the float weights.

**Stage 2 opens (A1).**
- **S2a, tightness gap:** CPU only.
- **S2b, unquantized weights:** Lean.
- **S2c, size scaling:** n = 8 and 10, CPU training plus Lean.

None has started; each Lean batch waits for the maintainer's go and a slot agreed with
the proofs study.

**Stage 1 verdict, both halves (2026-11-15).**
- **Pass met:** 8/8 ORD.
- **Structured effect not met:** STR − ORD = 0, radius 0.77×.
- STR's margin-normalised advantage stays labelled **descriptive**.

**What would make this more than kernel-checked IBP.** It would need a statement that
bound propagation over a finite input list cannot produce. Two examples:
- a property over unbounded inputs, such as all lengths through a recurrent net and a
  proved invariant;
- a certificate about a net the lab's doctors could not read, such as the gradient-trained
  XF transformers.

Stage 2 (tightness, float weights, n ≤ 10) stays inside finite-input IBP. It can measure
tightness and cost but cannot get there, so a different statement is needed.

# Bridge stage 2 (PREREG_BRIDGE A1, A4-A8), 2026-11-15

**S2a, tightness gap** (16 stage-1 test nets).
- Method: the smallest *exactly confirmed* breaking τ, divided by the largest IBP-certified
  τ.
- Median 1.29 (ORD 1.57, STR 1.16); range 1.01-2.47.
- **Bar met (median ≤ 4).** Here weight-space IBP is within about 1.3× of the true limit.
  The proofs study reported 4-32× for written nets.

**S2b, float weights** (8 ORD test nets, retrained deterministically).
- All 8 match their stage-1 quantization exactly.
- Kernel-checked certificates on the exact dyadic float64 weights: **8/8**.
- 78-100 s each at 4.2 GB peak commit; standard axioms only.
- **Bar met.** The "only the quantized net" caveat is removed at n = 6.

**S2c and the A6 ladder: popcount mod 3, ORD, τ = 1/1000.**

| n | Inputs | w | Exact | IBP-certified | Median certified τ | Kernel-checked | Lean per certificate |
|---|---|---|---|---|---|---|---|
| 6 | 64 | 16 | 8/8 | 8/8 | 0.0074 | 8/8 | ~65 s, 4.2 GB |
| 8 | 256 | 24 | 8/8 | 8/8 | 0.0025 | 8/8 | 434-480 s, 4.7 GB |
| 10 | 1,024 | 32 | 7/8 | 5/8 | 0.0013 | **stop**: s100 timed out at 900 s | — |
| 12 | 4,096 | (ladder running on CPU) | | | | not attempted (per-input stopped at 10) | |

**What the curve shows so far:**
- **Per-input kernel cost** grows about linearly in the number of inputs: about 1.0 s per
  input at n = 6, 1.8 s at n = 8, and more than 0.88 s per input at n = 10 with w = 32. So
  Lean cost tracks 2^n, and per-input checking stops at n = 10.
- **Certified radius** falls about 2.4× per +2 bits (0.0074 → 0.0025 → 0.0013).
- **The certified fraction** falls to 5/8 at n = 10.
- **The registered "scales" bar fails:** ≥ 6/8 kernel-certified at n = 10, with every
  certificate under 15 min.

**A6(c), region certificates at n = 10.**
- **mod 3:** trees need 1,023-1,024 leaves for 1,024 inputs. There is no saving, as
  predicted, because no label-constant subcube has dimension ≥ 2.
- **Majority (companion task):**
  - all 8 exact and all 8 IBP-certified at 1/1000, with radii about 0.008, about 6× the
    mod-3 nets at the same n;
  - trees of 495-796 leaves, 1.3-2.1× fewer than inputs.
- **In Lean:**
  - majority s104's 495 leaf lemmas checked in 384 s;
  - the first full batch certificate, s100 with 547 leaves, **hit the 15-min stop**.
- **The region-method bar fails:** ≥ 6/8 certified, at ≥ 4× below per-input cost.
  Achievable savings are about 2×.

**Against A6(d), provisional until the n = 12 CPU columns land.**
- Even on the low-sensitivity task, interval-relaxed regions shrink the cover only about
  2×. Interval bounds over relaxed free bits are too loose to close large subcubes of a
  trained net. So kernel cost still tracks 2^n, which is the pre-stated **closure**
  condition.
- The n = 12 leaf counts will show whether the region fraction falls with n (a route) or
  stays about constant (closure).
- The route to all-lengths statements for trained nets is not through enumerated or
  interval-region certificates of this kind. It would need a symbolic or relational
  certificate, or a different statement, as noted under stage 1.

**n = 12 rung (CPU columns, A6 / A8), 2026-11-15/16.**
- **mod 3:** w = 64 by the dev rule; 6/8 test nets are exact.
  - **IBP-certified at τ = 1/1000: 0/8.**
- **Majority:** w = 64; 8/8 exact and 8/8 IBP-certified.
  - Region trees: 2,269-2,971 leaves for 4,096 inputs (median fraction about 0.67).
  - At n = 10 the trees had 495-796 leaves for 1,024 inputs (median about 0.55).
  - So the region fraction does **not** fall with n.
- Single-threaded, under 0.8 GB; 3-6 min per net.

**Verdict against A6(d): closure, on both pre-stated conditions.**
1. The certified fraction on the main task falls to ≤ 1/8 by n = 12. It is 0/8; the
   sequence was 8/8, 8/8, 5/8, 0/8 at n = 6, 8, 10, 12.
2. Kernel cost tracks 2^n even on the low-sensitivity companion task. Region leaves stay at
   about 0.5-0.7 of 2^n, with no polynomial trend.

**Conclusion.** Trained-net certificates of this kind (weight-space IBP, per input or over
interval regions) do not get beyond enumeration of small input spaces. They cannot carry to
unbounded inputs, so this line is closed as a route to the proofs study's all-lengths statements for
trained transformers.

**What a route would need instead:**
- a certificate that is not interval-relaxed, i.e. relational or symbolic;
- or a different statement, such as a recurrent net with a proved invariant.

**Ladder stop.** The ladder stops at n = 12 for this question. n = 14 and 16 can only
repeat 0/8 and add CPU hours, so they are left unrun unless the maintainer asks for them.

# Bridge: finished unit (PREREG_BRIDGE + A1-A8), 2026-11-16

**Statement tested.** A tiny *trained* ReLU classifier (6 → w → w → 1) on an exact finite
Boolean spec is given a Lean-kernel-checked certificate. The certificate says: for every
weight and bias within τ = 1/1000 of the trained values, the output has the correct sign on
every input. Method: weight-space interval bound propagation in exact rationals, proved
sound once (`Bridge/IBP.lean`), checked per input by kernel reduction.
- Standard axioms only; no `native_decide`.
- No proof agents.

| Part | Result | Bar |
|---|---|---|
| Stage 1, primary: n = 6, test seeds | ORD 8/8, STR 8/8 kernel-checked | **pass** (≥ 6/8). Structured effect **not met** (STR − ORD = 0, radius 0.77×); STR's radius per margin (about 6×) is descriptive only |
| S2a, tightness | median break/certified ratio 1.29 (range 1.0-2.5) | **pass** (≤ 4) |
| S2b, float64 weights | 8/8 kernel-checked | **pass** (≥ 6/8) |
| S2c and ladder, size | certified fraction 8/8, 8/8, 5/8, 0/8 at n = 6, 8, 10, 12. Per-input Lean stops at n = 10. Majority region trees cover about 0.55 → 0.67 of 2^n | **closure** on both A6(d) conditions |

**The two curves:**
- **Certified fraction against n** (mod 3, τ = 1/1000): 1.0, 1.0, 0.63, 0.0. Median certified
  τ: 0.0074, 0.0025, 0.0013, then not computed at n = 12.
- **Certificate size against inputs:**
  - per-input lemmas = 2^n, with Lean time about 1-2 s per input;
  - majority region leaves, as a fraction of 2^n: about 0.55 at n = 10 and about 0.67 at
    n = 12.
  - Cost tracks 2^n in both.

**Level-2 reading.**
- At small n, ordinary training already yields nets that carry kernel-checked weight-ball
  certificates. These are nearly tight, and they hold on the float weights.
- The method is known (weight-space IBP; Weng et al. 2020), checked in Lean. Its cost
  grows with the input space, and its certified fraction collapses by n = 12.
- So it does not reach statements over unbounded inputs. Random near-constant nets certify
  at larger radii, so radius alone is not evidence.

Pre-registration and amendments: `PREREG_BRIDGE.md`. Code: `bridge/`. Logs: `results/bridge_*`.



# RNN invariant (PREREG_RNN), dev finding, 2026-11-14: trained RNNs implement finer automata than the minimal DFA
Clipped-ReLU Elman RNNs, trained ordinarily, pass the exactness gate (all strings of length
≤ 12, plus 1,000 strings of length 200) at d = 8 (parity), d = 16 (mod-3) and d = 8
(Tomita 4).

**Their reached hidden states are almost fully saturated but not one point per DFA state.**

| Net | Distinct points (rounded 0.01) per DFA state |
|---|---|
| Parity, 3 ORD nets plus 1 SAT net | 2-22 |
| mod-3, d = 16 | 85-104 |
| Tomita 4, d = 8 | 2-5 |

- One box per DFA state therefore spans most of [0, 1]^d. It overlaps the other states'
  boxes, and no sign-correct read-out exists on it, even with unperturbed weights.
- The box-per-DFA-state invariant certified **no** parity dev net, in either arm.
- The method works when a net happens to use one point per state. The single Tomita 4 net
  that passed the gate at d = 4 has that property and certifies at τ = 1/1000.

**SAT arm (dev observation).** The saturation-margin penalty lowered trainability: 1/4,
2/4 and 2/4 dev nets passed the gate, against 4/4 for ORD.


# RNN invariant (PREREG_RNN + A1/A2), test result, 2026-11-14: no pass; L3 meets the effect bar at p = 0.14; 9/9 certificates kernel-checked
One blind run of the frozen procedure (A2 hashes, commit a4aa12c). Test seeds 100-107. Clusters
are counted under the A1 rule. Certification is at τ = 1/1000.

**Lean checks: all 9 confirmed.** All 9 Python-certified nets  were kernel-checked one at a
time. Each check took 11.7-13.9 s and
peaked at 4.3 GB of commit. Each certificate uses only the standard axioms (propext,
Classical.choice, Quot.sound). The counts below are therefore final.

**Certified counts, out of 8 test seeds per language and arm:**

| Language (d) | ORD: gate / certified | SAT: gate / certified | RND certified | Clusters, certified nets | Clusters, gate-passing but uncertified |
|---|---|---|---|---|---|
| L1 parity (8) | 5 / **3** | 1 / **1** | 0/8 | 5-8 | 13, 24 |
| L2 mod-3 (16) | 4 / **0** | 2 / **0** | 0/8 | none | 24-149 |
| L3 Tomita 4 (8) | 6 / **1** | 5 / **4** | 0/8 | 7-20 | 12-82 |

**Trivial-language control:** 4/4 certified, with 2-4 clusters. All four reach the search ceiling of τ = 1/20.

**Bars:**
- **Pass (level 2), not met.** No arm reaches ≥ 6/8 on L1, and L2 is 0/8 in both arms. Stage 2 stays closed.
- **Structured effect, met on L3 only, and weakly.**
  - L3: SAT − ORD = 4 − 1 = 3. One-sided Fisher exact p = 0.14.
  - L1 goes the other way: SAT − ORD = −2. Most SAT nets fail the gate there (1/8 pass, against 5/8 for ORD).
- **Level-3 candidate, not met.** The best L3 arm is 4/8.
- **Kill, not fired.** L1 ORD is 3/8.
- **Random control** is 0/8 on every language, as expected.

**Tightness, as registered.**
- One net has a confirmed break: L3 SAT s105 breaks at r = 0.0263, ratio 1.21.
- The other 8 return "no break found up to 1/2".
- This is a limit of the instrument, not evidence that the nets are robust:
  - The clip saturates, so the sign-gradient attack sees zero gradient on W, U and b. Only the read-out moves.
  - On the non-dev pipeline net, the same attack found a break at ratio 1.72.
- No bar depends on tightness here, because the level-3 bar fails on count.

**Certificate size (A1, condition 3).**
- A certificate has n_C boxes, 2·n_C step checks and n_C read-out checks.
- n_C is 5-20 on the certified nets. That size is constant in input length, but it is set by
  how many state clusters the net actually uses, not by the minimal DFA (2-4 states).
- Failure tracks n_C:
  - The gate-passing nets that did not certify use 12-149 clusters.
  - mod-3 nets, at d = 16, use 24-149, and none certifies.

**What this supports:**
- Kernel-checked, all-lengths, weight-ball correctness certificates exist for some ordinarily
  trained RNNs: 3/8 on parity and 1/8 on Tomita 4.
- The penalty arm ("trained to be certifiable") helps on Tomita 4 but costs trainability on parity.
- The method does not scale to the mod-3 nets, which spread over many saturated points.
- A1 was the one design revision allowed, so there is no further revision under this prereg.

**Date correction.** The headings of PREREG_RNN, its scope note and the two earlier
sections here read 2026-11-16. Every commit is dated 2026-11-14, so they were relabelled
2026-11-14. The commit order, which is the audit trail, is unchanged.

Rows: `results/rnncert_test_*.jsonl`, `results/rnncert_breaks.jsonl`.
