# the proofs study, rung 9-LN pre-registration: the rung 8 theorem for a trained network with LayerNorm

Written 2026-11-21 (Saturday evening EST). Registered on the project owner's go-ahead: a toy-scale LayerNorm one-block rung.

**Scope, stated first.** This rung is about a five-token network. It does not
scale to real text, and I know why: experiment E3 (`SCOPE_6.md`) showed that on a small
TinyStories model an enclosure of the residual stream by token classes carries no information
through LayerNorm (median output radius 682 against a limit of 0.25), and the two papers nearest
to this (`SCOPE_6.md`, addendum E0) do not have a residual-stream LayerNorm bound either:
Stambler et al. (2502.06038) apply LayerNorm only to embeddings, exactly, at depth one, and say
that deeper models need new ideas; Somani (2605.24033) removes LayerNorm by fine-tuning. What
this rung can add is a sound, kernel-checked enclosure of LayerNorm **acting on the residual
stream after attention**, with a rounding model and a weight ball, on trained networks at every
length, at toy scale. That is the missing lemma in miniature, not a result about a model that
matters.

**Stage authorised now:** this file, K1 and K2, no doctor tokens; report at each. Kit cases are
approved once K1 and K2 pass (2 to 3.5 million Sonnet tokens, one Sonnet retry per case),
with the usage budget reported before the first. One stronger-model step is reserved for the
LayerNorm enclosure lemma.

## What had been seen when this was written

`RESULTS_R8.md`, `RESULTS_R9.md`, `RESULTS_MECH.md`, `SCOPE_6.md` with its addenda. **No network
with LayerNorm has been trained by this study on any of its tasks.** Before this file was committed
the only run of `tools/r9ln.py` was `selftest` (60 steps, dev seed 0, into `scratch/`), which also
confirmed that the NumPy evaluator and the training code give the same deviation (2.883) on that
network. No prototype of the LayerNorm enclosure exists.

## Statement

**Task.** Rung 8's task A, unchanged: five tokens, token t is digit t − 1, target at position i =
(digit of token i + digit of token i−1) mod 5. I keep it because the question here is LayerNorm,
and the comparison with rung 8 (19 of 20) is only clean on the same task and recipe.

**Network.** One block, state width 8, two heads (strict, causal), every earlier position a
candidate key, relative-position slope fixed at 24, MLP hidden 12, scalar read-out, and three
LayerNorms in the standard pre-LN places:

    h   = LN1(x)                                x = token embedding (no position embedding)
    y   = x + Σ_heads attention(h)              scores, keys and values read h
    z   = y + W2 · relu(W1 · LN2(y) + b1) + b2
    out = oW · LNf(z) + oB

LN(v) = (v − mean v) / sqrt(mean (v − mean v)² + ε) · gain + bias, ε = 10^-5, a learned gain and
bias per coordinate. LN1 acts on embeddings only (known exactly per token, as in Stambler et
al.); **LN2 and LNf act on the residual stream after attention and after the MLP, which is the
new part.**

**Theorem aimed at.** `SoundLN`: the statement of `Sound8` for a new network model with the three
LayerNorms and a new checker: if the checker accepts at radius δ, every network within the
additive δ-ball (all weights, including the LayerNorm gains and biases; ε is a constant), in the
rounding model extended by one assumption for the square root (binary32 square root is correctly
rounded, so it has the shape of `Rnd`), is within 1/4 of the task target at every position of
every input of every covered length. Per network: the four rung 8 theorems, generated, `decide
+kernel`, standard axioms, `native_decide` banned. The model definition is new Lean
(`Lane4/AGate.lean` has no normalisation) and is fixed, with its stated operation order, before
the kit cases; `tools/r9ln.py run` is the executable version of that order.

**Ball.** 2^-14 around W14, as in rung 8.

**Headline sentence if passed (fixed now).** "N of M gradient-trained one-block softmax
transformers with LayerNorm, from fresh seeds, are proved by one soundness theorem and a
kernel-checked certificate each to compute the task at every position of every input length, for
every weight setting within 2^-14 of the rounded weights, in a binary32 rounding model." No
"first"; teal-sea, Gross et al., Stambler et al. and Somani cited for what each has.

## Design of the enclosure, on paper (may change before the freeze; each change logged)

Rung 8's checker and table are kept: LayerNorm acts on one position at a time, so the abstract
cases and the induction over the input do not change. Inside a case, with affine forms:
centring is linear and exact on the forms; the variance is enclosed by an interval from the
centred forms' ranges, plus ε; a rational enclosure of the square root and of the reciprocal gives
an interval [r_lo, r_hi] for 1/σ; each centred form is scaled by the midpoint and charged
(r_hi − r_lo)/2 times its magnitude to its radius; then gain and bias as an affine map with the
weight ball. LN1 is applied to the embedding intervals per token before the head tables.

## Route

1. This file, committed. 2. **K1**, tuning seeds. 3. **K2**, exact-rational prototype with the
numeric interval test. **Report at each.** 4. Lean model, checker, mirror, generator; **K3**.
5. Kit cases (**K4**). 6. Freeze by hash, fresh seeds, bar, controls.

## Training (fixed now)

`tools/r9ln.py`, frozen with this file. Rung 8's recipe u3 (L1 3e-4 to the end, slope ramp to 24,
Adam 3e-3, batch 64, lengths 2 to 40, hinge 0.03) with the three LayerNorms; gains start at 1,
biases at 0, and neither is shrunk by the L1 step. Recipes in this order on tuning seeds 100 to
119, the first with at least 10 of 20 computing the task is the rung's recipe and later ones are
not run:

| recipe | steps | L1 |
|---|---|---|
| n1 | 6,000 | 3e-4 |
| n2 | 6,000 | 1e-4 |
| n3 | 12,000 | 1e-4 |

No other recipe without an amendment written first. The no-cheating line of `PREREG_R7.md` holds.

**Screen** (`tools/r9ln.py screen`): s1, the trained network in float32 in the stated order, worst
deviation at most 1/4 on the rung-7 sampling plan up to 65,534 tokens ("computes the task"); s3′,
W14 under 20 uniform and 20 sign-corner perturbations of every weight, gain and bias at radius
2^-14, worst deviation at most 0.10. Pass = both.

## Kill rules

- **K1.** No recipe has at least 10 of 20 tuning seeds computing the task: stop and report.
- **K2.** The exact-rational prototype accepts fewer than 6 of the screened tuning networks of the
  chosen recipe at 2^-14, after at most three design changes (each logged with counts). An
  acceptance counts only if the numeric interval test shows no violation on that network.
- **K3.** The largest accepted tuning network does not pass the kernel in at most 4 files of 900 s
  and 6 GB each. Measured so far without LayerNorm: about 1 s per table row and a single-file
  limit near 850 rows (`SCOPE_R9.md` addendum); square roots will add to that.
- **K4.** A kit case fails two Sonnet doctors and the one stronger-model step.
- **Usage.** Read and logged before each kit case.

## Bar and counts

- **Fresh seeds 400 to 419**, never used. Trained only after checker, mirror, generator and screen
  are frozen by hash. Ascending seed order.
- **Bar** (rung 8's): of the first three networks from seed 400 that pass the screen, at least 2
  have all four theorems kernel-checked. If fewer than three of the twenty pass the screen, seeds
  420 to 439 are trained and this is said.
- **Count on the twenty:** trained; compute the task; pass the screen; accepted; rejected with the
  mirror's reason. Kernel decision must equal the mirror's on every file. No adjustment of the
  checker after the freeze. The tuning-set count is reported beside it and labelled.

## Controls (each must be rejected in the kernel; on one tuning network unless said)

The rung 8 controls carried over: task B's automaton; embedding rows 1 and 2 swapped; read-out
negated; read-out bias raised by 1/2; radius 16 and 64 times larger; every fresh network that
fails s1. New: the gains of LN2 negated. An accepted control voids the result until explained.

## Numericchecks on every accepted network (searches, not proofs)

As rung 8, with `tools/r9ln.py run`: the trained network in float64 and float32 to 65,534 tokens;
W14 under sampled perturbations in the ball; the breaking multiple; the numeric interval test
against the mirror's table.

## What would make the result weak, written down now

- Five tokens, one block, a local task, width 8, a fixed slope of 24, the study team's own recipe.
- LN1 is the easy case and LN2, LNf see a residual stream that takes few values (one per abstract
  case); that is why an enclosure can work here and did not in E3.
- The ball, ε, the operation order and the square-root assumption are the study team's choices.
- Constants of the checker will be fitted to at most 20 tuning networks.
- If LayerNorm makes these networks easier to certify than rung 8's, the write-up must say that
  the difficulty the field names lies at real scale, not here.

## Frozen files

`scratch/freeze_r9ln.sha256`: this file, `tools/r9ln.py`, and unchanged `tools/r7.py`,
`tools/r6net.py`, `tools/r4_checks.py`, `tools/r5_checks.py`. Its own hash is
in the study's private log (not included). The rung 8 and mechanism freeze lists stay in force and are not touched.
