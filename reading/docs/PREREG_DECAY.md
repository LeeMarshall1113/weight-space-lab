# PREREG_DECAY: legibility decay curve (cut version), 2026-11-14

Cleared by the project owner. Scope is from STRETCH.md.
This file is committed before the pilot, the cheap metrics or any doctor episode. Any later
change is an amendment, dated, with its reason.

## Question
Take the 20 Tracr nets that W-0 doctors read at 20/20 (XFT-W0). Move them along
function-preserving paths that each mainly induce one mechanism, as in the arms below.
How do weights-only read success and the cheap legibility metrics fall with distance from
the compiled weights?

## Nets
The 20 cases of `xf/cases_tracr_20261112.json`, the same set as XFT-W0, XFT-IO-20 and the
A4/A5 ladder. Templates: 9 count_cmp, 9 count_combine, 2 count. All work is in float64.

## Gate (function preservation)
Every net used anywhere in this experiment must match a reference on ≥ 0.99 of 1,000
inputs, using `sample_inputs` with seed 7 (the same check as `xf/perturb.py`).
- **Reference:** the original net, except in SHIFT (below).
- **Failures:** a net that fails the gate is dropped from that point and counted. The
  dropped count per point is reported.

## Arms (all gate-checked)

| Arm | Movement | Mainly induces |
|---|---|---|
| FT | Continued training (cross-entropy) on the original net's own outputs, schedule from the pilot | desaturation + dense drift |
| FT+WD | FT with decoupled weight decay (AdamW wd or SGD L2, value from the pilot) | desaturation (shrinks saturating scales) |
| NOISE | Gaussian noise with ‖noise‖ = ε‖W‖ added per tensor, then FT repair until the gate passes (cap of 2,000 steps) | dense small perturbation |
| COMP | Learned residual compression: x' = xE with E ∈ R^{d×d'}; reads use Eᵀ (Wq' = EᵀWq, etc.) and writes use E (Wo' = WoE, etc.); E is trained by gradient to pass the gate, all other weights frozen | superposition |
| SHIFT | FT toward a shifted target: at positions whose input token is t*, output class c is replaced by c′ (one table entry). The gate is against the shifted target. t*, c and c′ are fixed per case from the case seed. | drift + a done edit |

COMP keeps the doctor's view honest: the npz has the same tensor names, now with a d′-wide
residual, and the spec text is unchanged.

**Points.** Three per arm, picked by the pilot schedule, at target relative drift
‖W−W0‖/‖W0‖ ≈ **0.01, 0.10, 0.40**.
- **Checkpoint rule:** each point uses the first checkpoint at or past its target that
  passes the gate.
- **COMP points:** d′/d ≈ 0.9, 0.7, 0.5.
- **Unreachable points:** if an arm cannot reach a drift level while gated for at least 15
  of the 20 nets, that point is marked unreachable and not run.
- k = 0 is the existing XFT-W0 result, 20/20.

## Pilot (before any arm is built)
**Grid:**
- SGD lr {1e-4, 1e-3, 1e-2};
- Adam lr {1e-6, 1e-5, 1e-4};
- batch 64, up to 3,000 steps;
- gate checked every 25 steps, on the 20 nets.

**Rule:** the schedule is the largest lr that keeps ≥ 15/20 nets gated through drift 0.05.
FT+WD uses the same lr with wd ∈ {1e-4, 1e-3}, again picking the largest that meets the
rule.

**Kill rule 1 (pilot):** if no FT schedule meets the rule, FT, FT+WD and SHIFT are
dropped and the experiment continues with NOISE + COMP. If those also cannot keep ≥ 15/20
gated at ≥ 0.05 drift (or at d′/d ≤ 0.9 for COMP), stop and report.

## Cheap metrics (no agents; computed on every gated net)
- **M1 table sharpness.** It is computed on the token-space circuits the doctors use:
  - for every (token, position) row: QK logits over keys, OV→unembed logits, and
    single-row MLP outputs projected on the unembed;
  - for each row, take the softmax top-1 mass and the logit gap between the top two
    entries;
  - M1 = mean top-1 mass over all rows.
- **M2 attention saturation.** Mean of max attention weight over heads, positions and 200
  held-out inputs.
- **M3 table fidelity.** Spearman correlation of the flattened M1 tables with the k = 0
  tables of the same case.
- **M4 hardened-net agreement.** Replace every softmax with a hard argmax (ties are
  averaged) and measure agreement with the original on the gate inputs.
  - **M4-pass** = M4 ≥ 0.99.
  - It is a deterministic proxy for "readable as a discrete program".
  - **Amendment to STRETCH.md:** STRETCH proposed a full scripted decompiler. That is
    replaced by this proxy, because a decompiler would cost days of engineering. M4-pass
    is the non-LLM baseline in kill rule 3.
- **Also reported:** relative drift, effective rank of each matrix, and the near-zero
  (< 1e-6) fraction.

## Choosing the two doctor arms (fixed now)
1. Among arms with all 3 points reachable, compute mean M1 at each point.
2. Pick the pair whose M1 curves differ most, by the sum over points of |ΔM1|.
3. Tie-break: the larger sum of |ΔM4-pass|.
4. If fewer than 2 arms are reachable, use the 1 that is.

**Stop.** Report the cheap-metric table before any doctor episode.

## Doctor stage (Sonnet only, 1 at a time unless the project owner clears 2)
**READ.** W-0 with the XFT-W0 brief, unchanged apart from paths, for the 2 chosen arms ×
3 points × 20 = 120 episodes.
- **Order:** point 1 for both arms first (40 episodes).
- **Score:** functional ≥ 0.99 against the gated net, as in XF.
- **Audit:** same audit as XF; a simulation suspect counts as a failure.

**Kill rule 2.** If READ at point 1 (≈ 0.01 drift) is ≤ 4/20 in both arms, the decay is a
cliff. Report it in one line and stop; points 2-3 and EDIT are not run.

**EDIT at k = 0 (20 episodes, only if kill rule 2 passes).**
- **Task:** on the original Tracr weights, make the net compute the SHIFT target.
- **Success:** ≥ 0.99 agreement with the shifted target, and no rewrite (the same rule as
  this study (b)).
- **Also reported:** weights changed.
- **Baseline:** the SHIFT arm's FT (gradient) reaching the target, with its drift.

**Kill rule 3.** If M4-pass matches doctor READ within 2/20 at every doctor point, there
is no LLM-specific claim. Report it as a table-statistics finding and stop spending agents.

## Analysis
- READ success per point, with Clopper-Pearson 95% CIs.
- Arm vs arm at matched points: exact McNemar, paired by case.
- Point 1 vs k = 0 within each arm: McNemar.
- **Collapse (exploratory, n is small):** a logistic fit of READ against M1, pooled over
  both arms, then a per-arm fit. Report the deviance difference.
- Every number is reported, including dropped nets and unreachable points.

## Compute
- **Compute:**
  - one reservation-run job at a time, CPU only, 4-6 GB;
  - `--match` contains a job-specific pattern;
  - absolute interpreter path;
  - honest eta;
  - yield to another study's server and the proofs study's check service if they queue.
- **Gaming flag:** the job checks it every checkpoint and exits cleanly.
- **Budget:** stop if the budget runs low.

## Amendment A1 (2026-11-14, before the pilot ran; no arm or doctor data exists)
**What the smoke test on one net showed.** This was 200 steps, run only to check the code.
- SGD at lr 1e-2 goes to NaN.
- Adam at lr 1e-4 drifts only 0.0007 per 200 steps and stays gated. At that rate it would
  not reach 0.05 drift within the 3,000-step cap, so the original grid could fail the
  pilot rule because of the step cap rather than the gate.

**Change.** The pilot grid becomes:
- SGD lr {1e-4, 1e-3};
- Adam lr {1e-5, 1e-4, 1e-3, 1e-2}.

The rule is unchanged: the largest lr that keeps ≥ 15/20 nets gated through drift 0.05,
with a cap of 3,000 steps.

**Implementation.**
- Code: `xf/decay.py`.
- Batched forward checked equal to `np_forward_tracr` on 200/200 inputs.

## Amendment A2 (2026-11-14, before any arm net or metric data existed)
**Problem with M1 as first defined.** Measured on k = 0 nets, it fails in two ways:
- Tracr's OV and MLP layers write to intermediate residual directions, not to the unembed.
  So the OV→unembed and MLP→unembed tables are identically zero for every layer but the
  last.
- A Select attends uniformly to all matching keys, so top-1 mass reads a perfect Select
  as 1/9.

**New M1** = mean of two parts, computed on tables that are live (non-zero) at k = 0:
- **M1_qk:** for each query row, max over s of 1 − TV(softmax row, uniform over the top-s
  keys). It is 1 for a hard Select.
- **M1_write:** for each OV and MLP write table (54 single-row writes × d_resid), the
  fraction of row pairs whose distance is < 5% or > 50% of the table's maximum pairwise
  distance. It is 1 for a clean lookup.

**M3** is the Spearman correlation over these same live tables. The arm-choice rule uses
the new M1, otherwise unchanged.

**Sanity check (3 nets).** k = 0 gives M1_qk = M1_write = M3 = 1.0. Noise at 5% of each
tensor's max lowers all three (M1_qk 0.81-0.93, M1_write 0.32-0.43, M3 0.43-0.77).

## Pilot verdict and amendment A3 (2026-11-14, before NOISE/COMP were built)
**Pilot result** (`results/decay_pilot.jsonl`, peak commit 3.5 GB): **0/20 nets pass the
rule at any setting.** Every learning rate either does not move the weights or breaks the
function:

| Setting | Behaviour |
|---|---|
| SGD 1e-4, SGD 1e-3, Adam 1e-5 | Drift 0.0004-0.0014 after 3,000 steps |
| Adam 1e-4 to 1e-2 | Agreement falls below the gate long before 0.05 drift. Adam 1e-2: median drift 0.020 at agreement 0.83 |

Even Adam 1e-5 drops some nets below the gate at drift ~1e-4: 13/20 dip at least once.

**Kill rule 1 fires for the gradient arms.** FT, FT+WD and SHIFT are dropped. By the same
rule, the experiment continues with NOISE + COMP.

**A3: NOISE repair schedule.** Fixed now, before any noise data exists: Adam lr 1e-3 with a
cap of 2,000 steps. It is the setting that moves fastest without the instant collapse of
1e-2. COMP is as pre-registered: Adam on E at lr 1e-2, with a cap of 3,000 steps.

**If NOISE and COMP also fail** the second half of kill rule 1 (≥ 15/20 gated at ≥ 0.05
drift, or at d′/d ≤ 0.9), stop and report.
