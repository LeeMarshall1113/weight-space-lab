# PREREG_BRIDGE: kernel-checked weight-ball certificates for tiny TRAINED ReLU nets (2026-11-15)

**Origin.** An independent AI reviewer's points 11, 13 and 14. This is written before any training. Changes after this point
are dated amendments made before the step they affect.

**Question.** The proofs study rung 3 gave kernel-checked proofs that every weight within 1/1000 of a
*written* ReLU net keeps it within tolerance (12/12). Do tiny *trained* ReLU nets on an
exact finite spec cross the same boundary? Does a structured training recipe change how
many do, and how far?

## Task
- **Inputs:** x ∈ {0,1}^6, all 64 points enumerated.
- **Target:** y(x) = +1 if popcount(x) mod 3 = 0, else −1. That gives 22 positives and
  42 negatives.
- **Training data:** all 64 points; the spec is the whole truth table. No generalisation
  claim is made.
  - Reported anyway: accuracy on all 64, and a separate 48/16 split run on dev seeds only.
    That run is diagnostic, not an outcome.

## Nets
- **Architecture:** 6 → w → w → 1, ReLU, scalar logit z(x).
- **Width w:** chosen on dev seeds from {8, 12, 16}. It is the smallest w at which ≥ 3/4 dev
  seeds of **both** arms reach 64/64 after quantization. It is frozen (amendment) before any
  test seed is trained.
- **Precision and threads:** float64, torch on CPU with ≤ 2 threads.

## Arms (same architecture, same accuracy bar, so size- and accuracy-matched)

| Arm | Recipe |
|---|---|
| ORD (ordinary) | Full-batch BCE-with-logits, Adam lr 1e-2, 4,000 steps, torch default init, seed s |
| STR (structured) | Hinge loss max(0, 1 − y·z) (margin 1), AdamW lr 1e-2 with weight decay 1e-3, 4,000 steps; then 500 steps of quantization-aware training (straight-through rounding to the grid below), seed s |
| RND (baseline) | The same architecture at init, untrained, seed s |

STR is the "trained-to-structured" variant: it asks for margin relative to weight scale,
which is exactly what a weight-ball certificate consumes. The proofs study did not use it.

**Seeds** (fixed now):

| Set | Seeds | Rule |
|---|---|---|
| Dev | 0-3 per arm | Used to set w and to build the Lean framework |
| Test | 100-107 per arm, so 8 | Trained, quantized and certified by one script run after the framework hash is frozen. Not inspected or re-run before scoring |

## Quantization
Every weight and bias is rounded to the nearest multiple of **q = 1/256**, giving the
rational net N_q.
- **Eligibility:** N_q classifies all 64 inputs correctly by exact rational evaluation.
- Float-net accuracy and N_q accuracy are reported separately.
- **The certificate is about N_q.** The ball radius below (1/1000) is smaller than the
  rounding step (1/512), so it does **not** cover the float original.

## Statement certified (radius and tolerance)
For every perturbation dW, db with every entry at most τ in absolute value, including
entries written as 0 (the proofs study's `Within τ`), and every one of the 64 inputs x:

    y(x) · z_perturbed(x) > 0

That is, correct sign everywhere in the closed ball. The certificate proves y·z ≥ γ_x > 0
with explicit rational γ_x.
- **Primary radius: τ = 1/1000**, the same as the proofs study.
- **Secondary:** τ ∈ {1/300, 1/100, 1/30}, plus the largest τ certified by bisection
  (rational IBP, below).

## Certificate pipeline (no proof agents in the primary outcome)
- **C1. Rational weight-space IBP, per input.** Each input is a fixed point, so the first
  pre-activation is exact ± τ(‖x‖₁ + 1). Later layers use interval arithmetic on
  (w + d)·h with h an interval, d ∈ [−τ, τ], and ReLU applied to intervals. This gives a
  lower bound on y·z. Everything is exact rational arithmetic.
- **C2. Lean framework**, reusing the proofs study's `Lane4/Basic.lean` and `Lane4/Robust.lean`
  (read-only, imported or copied with attribution):
  - a computable ℚ function `ibpLower N τ x`;
  - one soundness theorem: `Within τ dW db → y·(N.evalP dW db x) ≥ ibpLower N τ x`.

  Each per-net theorem then closes by kernel evaluation of the 64 rational bounds
  (`decide` or `norm_num`; **no `native_decide`**). The standard axioms only, as checked by
  the proofs study's checker.
  - The soundness proof is written once, on dev nets, by me or by a proof agent **only when
    the project owner confirms a slot**.
  - Its hash is frozen before test.
- **C3. Falsifier search** on every net: 10,000 perturbations inside the ball (uniform,
  sign corners, gradient-adversarial), all 64 inputs. A found violation is a failure. A
  timeout is reported as unknown, not as a counterexample.

## Primary outcome
**P_arm** = number of the 8 test nets in an arm that are eligible **and** have a
kernel-checked certificate at τ = 1/1000. It is reported for ORD, STR and RND.

## Baselines
- **B1. Exhaustive unperturbed check:** N_q correct on all 64. This is eligibility. It is
  trivially kernel-checkable.
- **B2. Ordinary IBP certificate:** C1 alone, outside Lean, in exact rationals.
  - P_arm must equal the B2 count.
  - Any difference is a bug in one of them and is reported.
- **B3. Random net:** RND nets certified against *their own* sign function.
  - This tests whether certification is trivial for any net. A net with a small margin
    should fail.
  - RND against the task spec is expected 0/8 eligible.
- **Reference, not matched:** the proofs study's written nets, 12/12 at τ = 1/1000 on a different
  task and statement.

## Bars (fixed now)
- **Dev stop.**
  - Stop and report if, at every w ∈ {8, 12, 16}, < 3/4 dev seeds of either arm reach
    64/64 after quantization.
  - Stop and report if the Lean per-net check exceeds 30 minutes or the 10 GB reservation on dev.
- **Pass ("a trained net crosses the boundary"):** P_ORD ≥ 6/8.
- **Structured effect.** Either counts as a positive:
  - P_STR − P_ORD ≥ 3 (one-sided Fisher exact, reported with p);
  - median largest certified τ for STR ≥ 4× ORD's, with every test net reported.
- **Kill ("the wall holds even here"):** P_ORD ≤ 1/8 **and** P_STR ≤ 1/8.
- **In between:** reported as is, with no claim.

**Also reported per net:**
- float and quantized accuracy;
- the smallest margin;
- the largest certified τ;
- the falsifier's smallest breaking τ outside the ball;
- Lean seconds and lines;
- CPU seconds.

## What would merely re-do interval bound propagation, and what would not
**Not new, said plainly:**
- The primary pipeline *is* weight-space IBP. Certifying a weight-perturbation ball by
  bound propagation is Weng et al. (AAAI 2020, "Towards Certificated Model Robustness
  Against Weight Perturbations"). They also use the certified region to guide
  quantization, which is close to STR.
- IBP is Gowal et al. (1810.12715).
- Checking IBP or CROWN bounds inside Lean is done by TorchLean (2602.22631: native IBP,
  CROWN/LiRPA certificate checking) and by LeanCert (an interval or DeepPoly
  `robustness_certificate` for small nets). Both target *input* perturbations, as far as
  their abstracts and docs say. Weight-ball statements were not found there, but this is
  not verified in full text.
- So P_ORD and P_STR alone are "IBP over weights, kernel-checked". That is a reproduction
  with an assurance upgrade, not a method.

**What would go beyond that** (none of it is in the primary outcome):
- **(a)** A proof agent certifying nets or radii that C1 fails on. For example, ReLU phase
  case splits per input are exact here because inputs are points. This needs proof-agent
  slots and a later amendment with its own bars.
- **(b)** A measured reason why trained nets do or do not cross the proofs study's boundary at this
  scale, from ORD vs STR vs written nets on margins and radii. This is lab-internal value:
  it tests whether the lab's "written works, trained fails" wall is about training per se,
  or about scale and structure.
- A level-4 claim would need a transferable theorem or technique, and nothing here
  promises one.

## Novelty check (2026-11-15, web search over abstracts and docs; not full text)
- **Weng et al. AAAI 2020:** weight-perturbation certificates and certified-region-guided
  quantization. Closest prior.
- **TorchLean (2602.22631, ICML 2026):** Lean 4 nets, IBP/CROWN, certificate checking,
  float32 semantics. Closest Lean prior.
- **LeanCert:** Lean 4 interval certificates for small MLPs.
- **Compression-aware certified training (2506.11992):** certified training with
  quantization.
- **No proof-assistant (Lean, Coq, Isabelle) weight-ball certificate for trained nets was
  found.** Re-check TorchLean's full text for weight perturbation before any claim.

## Compute and agents
- **Training:** CPU, ≤ 2 threads, one reserved job. It is small, under 1 GB, but reserved
  anyway, with `--match` a job-specific pattern and an absolute
  interpreter path.
- **Lean builds:** an 8-10 GB reservation each, one at a time.
- **Proof agents:** none until the project owner confirms a slot (lab cap 3). Sonnet by
  default; Fable only for a genuinely hard step, cleared first.

## Honest odds (before any data)
- **Dev reaches 64/64 at some w ≤ 16:** about 85%.
- **P_ORD ≥ 6/8 at τ = 1/1000:** about 60%. Margins of a few units against IBP slack of
  roughly τ · fan-in · activation scale probably clear it, so the wall may simply not
  exist at this size.
- **STR shows the pre-registered structured effect:** about 30%. If ORD already passes,
  the radius ratio is the live test.
- **The Lean framework works within budget:** about 70%.
- **Anything level 3 or above from the primary outcome alone:** under 10%.

## Amendment A1 (2026-11-15, during dev training, before any test seed)
**1. Exact label.**
- The net has one output, and the label is Boolean: y(x) = +1 iff popcount(x) mod 3 = 0,
  else −1.
- Popcounts 0, 3 and 6 give 1 + 20 + 1 = 22 positives (34%); the other 42 are negatives
  (66%). The three-valued residue is not the target; only "residue = 0" is.
- A constant net fails eligibility. Constant −1 scores 42/64, constant +1 scores 22/64,
  and eligibility needs 64/64.
- The statement is the sign condition y·z > 0 on all 64 inputs in the ball. A zero logit
  counts as wrong.

**2. Stage two.** Pre-stated now; it opens only if the primary passes (P_ORD ≥ 6/8 or the
structured effect). It is what would lift the result above kernel-checked IBP.
- **S2a. Tightness gap.** For every certified test net:
  - the ratio of the falsifier's smallest breaking τ (gradient-adversarial search over
    the weight ball, all 64 inputs) to the largest IBP-certified τ;
  - an exact upper bound from a found counterexample, checked in rationals.
  - **Bar:** median ratio ≤ 4. That is a certificate within 4× of the true limit; the proofs study
    reported 4-32× for written nets.
  - If the median ratio is > 4, a proof-agent arm (ReLU phase splits per input) may try to
    close the gap. It needs a slot from the project owner, and these bars would apply:
    certified τ raised ≥ 2× on ≥ 4/8 nets.
- **S2b. Unquantized weights.**
  - The same statement for the *float64 trained weights*, read as exact rationals
    (dyadic), with no rounding step. The ball is centred on the trained net itself.
  - **Bar:** ≥ 6/8 ORD test nets are certified at τ = 1/1000 by the same Lean framework.
  - This removes the "it is only the quantized net" caveat.
- **S2c. Size as a parameter.**
  - The same task, popcount(x) mod 3 = 0 on n bits, for n ∈ {6, 8, 10} (64, 256 and 1,024
    inputs).
  - Width w_n is the smallest of {w, 1.5w, 2w} at which ≥ 3/4 dev seeds reach full
    accuracy.
  - 8 test seeds per n, ORD only.
  - **Reported:** certified fraction, largest certified τ and Lean seconds against n.
  - **Bar:** certified fraction at n = 10 ≥ 6/8, with Lean check time ≤ 30 min per net.
    This turns one data point into a scaling statement.

**Lean framework.** A Lean framework (or proof agents) for stage 2 starts only on the
project owner's go. Stage 1 uses no proof agents.

## Amendment A2 (2026-11-15): width frozen from dev; no test seed trained yet
Dev results (`results/bridge_dev.jsonl`, peak commit 0.75 GB), 64/64 after quantization:

| w | ORD | STR |
|---|---|---|
| 8 | 1/4 | 2/4 |
| 12 | 4/4 | 2/4 |
| 16 | 4/4 | 3/4 |

By the A1/w rule, **w = 16 is frozen.**

Dev observations (not outcomes):
- **Every eligible dev net, in both arms, has a rational IBP certificate** at τ = 1/1000
  and at 1/300. The largest certified τ is 0.007-0.011 for ORD and 0.006-0.009 for STR.
- **RND nets certified against their own sign certify at similar or larger τ**, up to
  0.038. They are mostly near-constant functions.
- **The 48/16 diagnostic** (ORD trained on 48 points) reaches 52-62/64. There is no
  generalisation, as expected, and it is not an outcome.

## Amendment A3 (2026-11-15): kernel check method and cost measured on dev; framework frozen before test

**How a certificate is checked.**
- `Bridge/IBP.lean` defines a computable rational interval function and proves it sound
  for every perturbation in the proofs study's `Within τ` ball, over the proofs study's perturbed real
  forward pass `Net.evalP`. The theorems are `net_sound`, then `cert` and `certF`.
- It imports `Lane4.Robust` read-only.
- `SpecN 6 N τ` is the statement in the prereg. For every dW, db with `Within τ`, and every
  x in `boolVecs 6` (all 64 inputs): the output is > 0 if popcount(x) mod 3 = 0, and
  < 0 otherwise.
- **Per-net file** (generated by `bridge/export_lean.py --split`):
  - 64 lemmas `checkOneF N τ x_i = true`, each closed by `decide +kernel`, which is
    kernel reduction of the rational computation;
  - one assembling lemma (`rfl` for the input list, then `simp` with the 64 lemmas);
  - `certF`.
- **No `native_decide`.** `#print axioms` on dev gives
  [propext, Classical.choice, Quot.sound] only.
- **Why split per input.** A single `decide +kernel` over all 64 inputs was killed at
  7 GB at width 16, because the kernel cache grows within one declaration. Split per
  input, peak commit stays at 4.2 GB.

**Measured cost, dev, one lean.exe:**

| Item | Time | Peak commit |
|---|---|---|
| Framework compile | 12 s | 3.9 GB |
| Width-8 certificate (ORD_w8_s2) | 26 s | 4.2 GB |
| Width-16 certificate (ORD_w16_s0) | 72 s | 4.2 GB |

**Also frozen:**
- **Falsifier (C3):** 10,000 uniform and sign-corner perturbations, plus 50-step sign PGD
  per input.

**Frozen hashes (sha256):**
  - `*bridge/lean/Bridge/IBP.lean` fbb8086cbcda3c10361d1c4ceef285c41dc0956456ebf84fe5ed45413f35c7a9
  - `*bridge/export_lean.py` 9a5e5440ba2d0465f4c3c3364b3c1c6e453c508f4256c9a45d179473d3bae0e5
  - `*bridge/train.py` 9c7ee396eaa25c42f60eecbb6092bfd749a8b3b9a03bdcd97124fdab27014f2a
  - `*bridge/lean/build.py` fcca396b1d68064d634b0084c08fdbd8c748cb5bb2460f87ec848fed58eb9f09
  - `*bridge/lean/build_chain.sh` c820abf0d562049d2cfbed2523236b762847cbf795c3da95bd52c89bacbc98f6

## Amendment A4 (2026-11-15, after stage 1, before any stage-2 run): stage 2 details
**S2a (tightness, CPU).**
- **Nets:** the 16 stage-1 test nets.
- **Smallest breaking τ:** bisection over τ ∈ (max certified τ, 1/4]. A τ "breaks" when
  the falsifier (C3, frozen) finds y·z ≤ 0 on some input.
- **Exactness:** each found counterexample is re-evaluated in exact rationals, with the
  float64 perturbation read as a dyadic rational. Only exactly confirmed breaks count.
- **Ratio:** smallest exactly confirmed breaking τ / largest IBP-certified τ.
- **Bar (A1):** median ratio ≤ 4.
- No proof agents. The A1 proof-agent follow-up is not opened without a slot.

**S2b (float weights, Lean).**
- **Nets:** the 8 ORD test nets, retrained deterministically from the same seeds.
  - The float64 weights were not saved in stage 1.
  - A retrain is accepted only if its quantization equals the stage-1 quantized net
    exactly; any mismatch is reported.
- **Statement:** weights are the exact dyadic rationals of the float64 values, so the ball
  is centred on the trained net itself.
- **Framework:** the same frozen one.
- **Bar (A1):** ≥ 6/8 at τ = 1/1000.
- **Stop:** one certificate > 15 min or > 8 GB stops S2b, and the rest are not run.

**S2c (size scaling).**
- **Task:** popcount(x) mod 3 = 0 on n bits, n ∈ {8, 10} (256 and 1,024 inputs). ORD only.
- **Width w_n:** smallest of {16, 24, 32} at which ≥ 3/4 dev seeds (0-3) reach full
  quantized accuracy.
- **Test seeds:** 100-107.
- **Numbers reported per n** (6 from stage 1):
  - eligible and kernel-certified fraction at τ = 1/1000;
  - median largest IBP-certified τ;
  - median Lean seconds and peak commit per certificate.
- **"Scales" means:** at n = 10, ≥ 6/8 kernel-certified, with every certificate under
  15 min and 8 GB.
- **Stop rule:** one certificate > 15 min or > 8 GB stops that n, and the rest are not run.
  Runs go in order n = 8 then n = 10, with Lean done for n = 8 before n = 10 starts.
- **Expected cost before running:** at n = 6, w = 16 the check costs about 1 s per input.
  So n = 10 means 1,024 inputs at width ≥ 16, about ≥ 17 min, likely past the stop. That
  is a pre-stated likely failure of the "scales" bar for this method.

## Amendment A5 (2026-11-15): S2c widths from dev, per the A4 rule, before any S2c test seed

| n | Width chosen | Dev seeds at full quantized accuracy | Dev IBP at τ = 1/1000 (not an outcome) |
|---|---|---|---|
| 8 | 24 | 4/4 (w = 16 gave 2/4) | all 4 certified |
| 10 | 32 | 3/4 (w = 16 gave 0/4, w = 24 gave 2/4) | 1 of the 3 eligible certified |

Logs are in `results/bridge_s2c_dev_n{8,10}.jsonl`.

## Amendment A6 (2026-11-15): S2c becomes the main line and asks for a scaling law, not passes
Requested after the project owner's go. Written while the n = 10 test seeds train on
CPU, and before any n = 10 Lean run or any n ≥ 12 run.

**(a) Continuation ladder: n = 12, 14, 16** (4,096 / 16,384 / 65,536 inputs).
- Same task, same ORD recipe and quantization.
- **Width w_n:** smallest of {32, 48, 64} at which ≥ 3/4 dev seeds (0-3) reach exact
  quantized accuracy.
- **Test seeds:** 100-107.
- The ladder climbs until a pre-set stop.

**Stops.** Each stops that rung and every higher one:
- **Training:** no width reaches 3/4 dev seeds exact.
- **Lean:**
  - one certificate over 15 min or over 8 GB;
  - this cuts the Lean column only; the CPU columns continue.
- **CPU cost:**
  - one net's rational IBP plus falsifier over 2 h on 2 threads, or over 6 GB;
  - in that case the rung is recorded as CPU-infeasible.

**(b) Curves reported against n and width** (stage 1 gives n = 6):
- eligible fraction and kernel-certified fraction at τ = 1/1000;
- IBP-certified fraction at τ = 1/1000 (CPU);
- median largest IBP-certified τ;
- tightness gap: the S2a method on the test nets of each rung where CPU allows;
- Lean seconds and peak commit per certificate;
- CPU seconds per net.

**The fit (descriptive).** Log certified radius against n, and log Lean seconds against
log(#inputs). The question is whether cost tracks 2^n, as per-input checking must, and
whether radius and certified fraction decay, and how fast.

**(c) Where per-input lemmas stop, and what replaces them (scoped now; tried at the first
n where the per-input Lean check hits its stop).**
- **Expected stop.** Per-input kernel lemmas cost about 1 s per input at n = 6, w = 16, so
  cost grows linearly in 2^n. The 15-min stop is expected at n = 10 (1,024 inputs at
  w = 32 is roughly ≥ 30-60 min).
- **Replacement: region certificates.**
  - Branch and bound over the Boolean cube: a region is a subcube (some bits fixed, the rest
    relaxed to [0, 1]).
  - IBP runs with interval inputs *and* interval weights. The framework already proves
    soundness for arbitrary input intervals (`hidden_sound` takes any `Bnd ls us vs`), so
    only a region-level check and a cover lemma ("the regions cover `boolVecs n`") need
    adding.
  - A region is closed when its label is constant on it and IBP gives the right sign;
    otherwise it is split on one bit.
- **The obstacle, stated now: this task is the worst case for regions.** popcount mod 3 has
  maximal sensitivity. Flipping any bit changes the residue, so no subcube of dimension
  ≥ 2 has a constant label. Dimension-1 subcubes are constant only for residue pairs
  {1, 2}, which are both negative.
  - So on this task, region certificates can save at most a factor of about 2 over
    per-input lemmas.
  - The per-input wall here is then a property of the task, not only of the method.
- **Region test.** At the first n where per-input checking stops, the region method is run:
  - (i) on this task, where the expected outcome is about 2× and no rescue;
  - (ii) on one pre-stated low-sensitivity companion task, majority (popcount(x) ≥ n/2,
    n even), with the same recipe and seeds.

  Majority has large label-constant subcubes, so it tests whether region certificates make
  cost sub-linear in 2^n for a trained net. The companion task is added now, before any of
  its nets exist.
- **Region-method bar.** On majority at that n:
  - ≥ 6/8 kernel-certified;
  - certificate cost at least 4× below the per-input estimate.

**(d) Route or closure, toward the proofs study's all-lengths statements for trained transformers.**
- **Route:** for a trained net, region certificates whose number of regions, and so kernel
  cost, grows polynomially in n rather than like 2^n. That is a certificate over input
  *families*, not enumerated inputs, which is the shape an all-lengths statement needs. It
  has to come with certified fraction ≥ 6/8 holding to at least n = 14.
- **Closure:** cost tracks 2^n even on the low-sensitivity companion task (regions do not
  shrink the cover), or the certified fraction falls to ≤ 1/8 by n = 12. Either means
  trained-net certificates here do not get beyond enumeration, so this line cannot reach
  unbounded inputs, and a different statement (a recurrent net with a proved invariant) is
  needed.

**Lean turns.** One build at a time, taking turns with the proofs study. S2c has priority over the
rest of stage 2 for this lane.

## Amendment A7 (2026-11-15): assembly fix for n ≥ 8 (statement, framework and stop rule unchanged)
**What happened.** The first n = 8 certificate (N8_w24_s100) checked all 256 per-input
kernel lemmas in 491 s, under the 15-min stop, at 4.7 GB peak commit. It then failed in
the assembling lemma: `simp` over a 256-element list hit Lean's default `maxRecDepth`, so
the file reported `sorryAx`.

**Fix.** The exporter now prefixes only that lemma with
`set_option maxRecDepth 100000 in`.

**What is unchanged:**
- the statement (SpecN);
- `Bridge/IBP.lean`;
- the per-input lemmas;
- the stop rule.

This was a tool limit, not the A4 stop. The batch is re-run from s100.

## Amendment A8 (2026-11-15): n = 10 Lean measurements and tool fixes; ladder CPU columns for n ≥ 12
**Measured at n = 10, w = 32 (15-min / 7 GB caps):**

| Certificate | Time | Peak | Outcome |
|---|---|---|---|
| Per-input, mod 3 (N10_w32_s100, 1,024 kernel lemmas) | **timed out at 900 s** | 3.3 GB | The per-input stop is reached at n = 10, as A6 predicted |
| Region, majority (MAJ10_w32_s104, 495 leaves), all 495 leaf lemmas | 384 s | 5.5 GB | — |

**Tool fixes (statement, soundness proofs and caps unchanged):**
- The region exporter first packed up to 32 leaves per kernel lemma. That hit 7 GB, so it
  is now 1 leaf per lemma.
- Assembly first failed: `simp` could not match a numeral against `k + 1`. A one-line
  lemma `checkT_split` is added to `Bridge/Region.lean` and used by the exporter.

**Ladder (a) CPU columns at n ≥ 12** (`bridge/ladder.py`):
- **mod 3:** width by the A6 rule from {32, 48, 64}.
- **Test seeds**, mod 3 and majority:
  - exact quantized accuracy;
  - exact rational IBP at τ = 1/1000, one pass;
  - majority region-tree leaf count.
- **Deviation from A6(b):** the largest-certified-τ bisection is skipped at n ≥ 12. At
  4,096+ inputs it multiplies an already roughly 20-30 min per net exact computation by
  16-24.
- **Lean at n ≥ 12:** none for mod 3 (the per-input stop was reached at 10). Majority region
  certificates only if their n = 10 cost stays under the cap.
