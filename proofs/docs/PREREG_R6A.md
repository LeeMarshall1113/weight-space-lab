# the proofs study, rung 6a pre-registration: an additive weight ball at every length, with a gated architecture

**STATUS: REGISTERED, 2026-11-14 about 4:45 pm EST.** Written before any doctor episode
on a rung-6a task. Before this point the study team wrote the framework (`Lane4/AGate.lean`) and
the statements of four kit lemmas; Sonnet agents proved the kit lemmas (`runs/r6-kit/kG2`)
and the worked example (`runs/r6-kit/kX`, a task outside the families) as framework
tasks; the study team ran two numeric probes and a smoke test. The private commit holding this
file is not independently verifiable; what a reader can check is that the frozen files
below reproduce the hashes. Changes after this point go in dated amendments at the bottom.

## Why this rung

The 2x2 (`writeup/NOTE_2x2_v2.md`) shows that every proved rung-4 network has a break
under additive noise of 1/1000 at length 1,000 (8 of 11 at length 100), and one such
break is a Lean theorem (`runs/witness/r4abs_c14`). The rung-4 and rung-5 theorems
protect written zeros by construction (relative ball). Rung 6a asks for the stronger
statement: every weight may move additively, zeros included, at every length.

## The claim under test, and what is NOT claimed

Claim: an LLM doctor can write a transformer in the architecture below, and a
kernel-checked proof that it is within 1/4 of the target at every input length for every
additive perturbation of every weight by at most δ, in exact arithmetic, and in binary32
arithmetic up to 65,535 tokens.

Not claimed:
- **That the architecture is a standard transformer.** It has one non-standard component:
  a gate neuron per head that removes keys from the candidate set when a clipped ReLU of
  the key's state is not exactly 0. A sceptic will say this is a content-dependent hard
  mask added to make the proof possible, that real transformers have no such component,
  and that a finite attention penalty in its place would work only up to a length of
  about penalty/slope. All three are true. The relative-position score bias (one scalar
  slope per head) is standard (ALiBi, T5-style biases).
- That the rung-4 or rung-5 architecture has no absolute ball: that is the conjecture
  `Lane4.Conj.LastNoAbsBall`, not proved.
- Anything about counting tasks, trained networks, or `nn.TransformerEncoder`.
- Novelty beyond what a dated search supports (`NOVELTY.md`, rung-6a section, 2026-11-14):
  no proof-assistant theorem of this kind was found. Key gating is NOT our idea: TRA
  (Opper et al., arXiv:2503.23174) removes irrelevant keys from the softmax by a
  threshold and uses relative position for the rest, in trained models without proofs.
  Our gate thresholds a ReLU of the key's own state.

## The statement (one theorem per case, plus two team-derived corollaries)

    ∀ u η M fl ex, Rnd u η M fl → ExpM u η ex → 0 ≤ u ≤ 2^-24 → 0 ≤ η ≤ 2^-149 →
    ∀ p : APert, p.Within δ →
    ∀ w (tokens in 1..V), with n = length w + 1:
        u·n ≤ 1/256 → η·n ≤ 2^-100 → 2^40·n² ≤ M →
    ∀ i in 1..length w,  |ANet.out net fl ex p w i − target w i| ≤ 1/4

Corollaries derived by the study team's `Final.lean`, as at rung 5: `exact_all_lengths` (exact
real arithmetic, real exponential, every length) and `binary32` (round-to-nearest on the
binary32 grid on the finite range, exp within the stated error, at most 65,535 tokens).
A case counts only if the statement, both corollaries and the shape check are
kernel-checked with the standard axioms.

**The ball.** `APert.Within δ`: one additive `d` with `|d| ≤ δ` per weight: embedding
entries, every entry of every score and value matrix, every slope, every gate weight and
gate bias, MLP weights and biases, read-out weights and bias. The stored weight is
`fl (w + d)`. Nothing stays exactly zero.

**Radius: δ = 1/1000, chosen after the worked example and two numeric probes (dev
artefacts, not test cases).** How it was chosen, in order:
- The worked example (`runs/r6-kit/kX`, a kit task on a task outside the families) is
  kernel-checked at 1/1000 with a proved error of about 0.16 of the 0.25 tolerance.
- Numeric check on that example network (`scratch/r6_example_probe.py`,
  `results/r6a-example-probe.json`, float32, 20 sign corners per cell, same draws at
  every length): worst deviation 0.008 at 1/1000, 0.23 at 32/1000, 0.54 at 64/1000, the
  same at lengths 20, 1,000, 20,000 and 65,534. So that network leaves the tolerance at
  64 times 1/1000.
- The study team had planned 1/2000 to leave more room for tasks with an MLP. That was
  rejected by the pre-stated non-vacuity rule: at 1/2000 the example network would only
  break at 128 times the radius, outside the 64-multiple window.
- The hand-built carry network of the first probe (`results/r6-probe.json`) leaves the
  tolerance at 16/1000, i.e. 16 times this radius.
So 1/1000 is where the example is proved and the ball is within a factor 16 to 64 of
the measured limits. The proofs' bounds are much looser than the measured deviations
(about 20 times for the example), so some tasks may be provable only with tight
bookkeeping; that risk is accepted and is part of what the rung measures. One value for
all cases; not tuned on doctor results.

**Float model, exp, operation order:** as `PREREG_R5.md` (`Rnd` with underflow term and
range bound; `Lane4/Bin32.lean`; `ExpM` assumed and measured; stated left-to-right order;
no fused multiply-add). The position bias is `fl (m' · (j − i))` with `j − i` an integer.

## What every proof has to cover (from an external project review, point 12)

1. Gate margin: after perturbing the embedding and ALL gate parameters, wanted keys have
   a non-positive pre-activation, so their gate is exactly 0, and unwanted keys have a
   positive gate. Both directions, with the rounding.
2. BOS and the no-candidate case: say whether the candidate list can be empty for a
   position i ≥ 1 and prove the output in that case.
3. Content-score bound: the bilinear term with a score matrix written as 0 is bounded by
   a multiple of δ from bounded states, uniformly in length.
4. Slope gap: the winner beats every other candidate by at least 16 per unit of distance
   after the slope perturbation, the content noise and the rounding (`soft_near`).
5. Every length in exact arithmetic (the corollary), and the softmax tail (inside
   `soft_near`).
6. Float: every `fl` argument within the range `M`; summation error and exp error bounded
   separately (inside the kit; exp is an assumption).

The kit supplies 5 and most of 6. Items 1 to 4 are the doctor's.

## Tasks

The four non-counting families of rungs 4 and 5 (carry, last, first, induct), pool
`pool/rung4_pool.json`. Draw seed 4047, excluding every setting drawn at rungs 4 and 5
(dev, test, reserve) and the feasibility settings: per family 1 dev, 3 test, 2 reserve;
4 dev and 12 test. The draw is run when this file is registered; test ids are not read
before the freeze. A reserve case is used only for a study-team fault.

## Arms, doctors, budget

1. **net**: weights + proof. 12 test episodes.
2. **prog**: the one-pass plain-code control, same specs.

Doctors: Sonnet, fresh agent per case, 12 submissions, 600 s and 4.5 GB per check.
**One doctor at a time** by default (another study uses two of the lab's three slots during its
runs); two only when another study is idle. Budget from rung-5 rates: about 300k tokens and
30 to 60 minutes per net case, so about 10 hours of wall time for the net arm at one
slot, 30 minutes for the control arm, plus about 3 kit cases and a 4-case dev pilot.
stronger model only under D95, after Sonnet, one at a time, cleared with the scheduler run.
`native_decide` banned and counted. usage budget: stop and report near the limit the
project owner sets.

**What doctors are given:** `AGate.lean`, a kit of additive-perturbation lemmas (stored
weights, approximate dot products with an ideal value plus an error, the position-bias
gap), the rung-5 softmax lemmas unchanged, one worked example on a task outside the
families, and a paragraph of advice. This is part of the result.

## Bars (set now)

S6a = number of the 12 test specs whose net-arm statement and corollaries are
kernel-checked by a Sonnet doctor. Crashes and exhausted budgets count as fails.

- **Kill: S6a ≤ 2.** Also a kill, before any doctor: the study team cannot produce a worked
  example that passes at a δ with a non-vacuity margin (the network must break at some
  multiple of δ up to 64). Then the positive answer of `NOTE_open_problems.md` section 2
  is wrong or out of reach, and the rung reports that.
- **Pass: S6a ≥ 6, with at least 2 families.**
- **Headline wording if passed:** "N of 12 written gated softmax transformers
  kernel-checked correct at every length in exact arithmetic and up to 65,535 tokens in
  binary32 arithmetic, for every additive change of every weight by at most δ; the gate
  is a non-standard component; non-counting tasks only."

## Checks the study team runs on every proved network

Under `reservation wrapper` (hard cap) with an in-process memory guard; self-tested on the largest
shape first. (1) Inside the additive ball: uniform and sign-corner perturbations, lengths
6 to 2,000. (2) Non-vacuity: multiples 2 to 64 of δ. (3) binary32 stated order at 1,000,
16,000, 65,534 tokens, numpy, with the same random draws at every length so the columns
are comparable. (4) PyTorch module: numeric agreement with numpy to a stated tolerance
(NOT bit identity: rung 5 showed the two `exp` implementations differ). (5) The same
networks under the rung-4 relative ball of 1/200: report, do not assume. (6) The 2x2
contrast row: these networks under additive 1/1000 at lengths 100 and 1,000, per length.

## What would make the result weak, written down now

- The gate is non-standard (above).
- The kit carries the analysis, more than at rung 5.
- Same four task families, chosen by the study team; non-counting only.
- δ is small and set by the study team from its own example.
- exp accuracy assumed; own PyTorch module; stated operation order.
- The plain-code control will pass with far shorter proofs.

## Rung 6b note (not part of 6a)

After 6a: an external reviewer's collision lemma (`R6A_DESIGN.md`, last section) as the first theorem
on counting tasks, and the parity witnesses with a memoising mirror.

## Registration record (2026-11-14)

- Radius δ = 1/1000 (section "The ball"): chosen after the worked example and probes.
- Draw run at registration with seed 4047: dev c03, l39, f36, i06. Test-set sha256 (ids)
  3319b0aef662a67c815c632139e07a9447196233db28ba4711d421dc6f79e2c7. Test ids not read.
- Smoke (`tools/smoke6a.sh`, `logs/smoke6a-01.log`): the example passes with both
  corollaries; a slope of 10 in place of 24 fails; `native_decide` is rejected; the four
  dev specs compile.
- Check 4 of "Checks the study team runs" is dropped: no PyTorch module is built for the gated
  architecture at this rung (a torch pass would be a numeric comparison only, as rung 5
  showed). The other checks are implemented in `tools/r6a_checks.py`, self-tested on a
  two-block network at 65,534 tokens under reservation wrapper (peak commit 0.17 GB).
- Doctor prompt: `prompts/doctor_prompt_r5.txt`, unchanged.
- Usage rule (project owner): no new doctor case starts at or above 60% usage budget; hard
  stop at 75%; usage is checked and logged before each case. If that stops the rung
  before the pass bar is decided, the count so far is reported and the rung waits.
- Frozen files: sha256 list in `scratch/freeze_r6a.sha256`, whose own sha256 is
  fecf75ed3adb4114484a45a29ccd33cc90d4008d533d85f3c7812c536a0bf8ed.
  The dev pilot may still expose a fault in kit, example, task file or tools; any fix is
  an amendment and a new freeze before test cases are built.

## Correction (2026-11-14, 5:15 pm EST): the registration time in the status line

The status line says "about 4:45 pm EST". That was an estimate and it was wrong. The
git commit holding the registered file (f9b1c0e) is stamped 3:11 pm EST. Nothing else
changes. One dev case has run since (c03, kernel-checked at submission 2).

## Amendment 1 (2026-11-18, 3:45 am EST): kit and task file after the dev pilot

Made before any test case was built and before the test ids were read (they are still
unread; the test-set hash above is unchanged).

**What the dev pilot showed** (4 dev cases, one Sonnet doctor each, registered kit):
c03, l39 and f36 passed, each at submission 2 of 12. i06 (induct, 3 tokens) failed with
0 submissions used: the doctor designed a width-11 network, estimated the error with the
kit's uniform dot-product lemmas (one entry error and one bound for all coordinates) at
above 1.2 against the 1/4 budget, estimated about 0.16 with a per-coordinate bound, and
stopped without writing a proof. The failed folder is kept as
`runs/rung6a-dev/net/i06_v1`.

**Changes.**
1. Kit: new module `Lane4/AGateKitW.lean` with `CloseL`, `wErr`, `ardot_near_w` (the
   stored-weight dot-product bound with a per-coordinate entry error and bound) and
   `closeL_of_close`. Statements by the study team (type-checked first), proof by a Sonnet
   doctor in kit case `runs/r6-kit/kW` (passed at submission 1 of 30, standard axioms).
   `Lane4/AGateAll.lean` imports it; `Lane4/AGateKit.lean` is unchanged.
2. Task file (`tools/make_r6a_cases.py`): a pointer to the new lemma; the sentence "The
   checker is your only compiler: submit early and in parts ... Stopping with unused
   submissions counts as a FAIL, the same as using all of them."; `AGateKitW.lean` is
   copied into each net case folder.
3. Checker (`tools/check.py`): the module map gains `AGateKitW`. No other change.
   Smoke rerun `logs/smoke6a-02.log`: the seven cases behave as registered.

**Dev check of the amended kit** (not a result): i06 rebuilt and given to a fresh Sonnet
doctor: passed at submission 4 of 12 (width 10, 3 blocks, 2,142 proof lines, uses
`ardot_near_w`). Dev pilot as run: 3 of 4 with the registered kit; 4 of 4 after this
amendment, one case rerun.

**Not changed:** the statement, the radius 1/1000, the architecture, the draw, the bars,
the doctor prompt, 12 submissions, one fresh Sonnet doctor per case, the checks.

**What this does to the reading of the result:** the kit is stronger than registered and
was strengthened after seeing a dev failure in the induct family; that is what a dev
pilot is for, and it is reported with the result. The worked example and c03, l39, f36
were not rerun with the amended kit.

**New freeze:** sha256 list `scratch/freeze_r6a_a1.sha256` (the registered list plus
`Lane4/AGateKitW.lean`, `tools/r6_assemble_w.py`, `runs/r6-kit/kW/Spec.lean`); its own
sha256 is in the commit message and the study's private log (not included).
