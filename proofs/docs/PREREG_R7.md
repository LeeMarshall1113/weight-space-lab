# the proofs study, rung 7 pre-registration: an every-length, kernel-checked theorem for a transformer whose weights came from gradient descent

Status: REGISTERED 2026-11-19 (EST); the commit that adds this file is the registration.
Scope: `SCOPE_R7.md` (commit b1706e2). Project owner's decisions of 2026-11-19 are applied:
B is primary, A is the second statement; S0 is not attempted; both architecture caveats go
in the headline sentence; the no-cheating line is binding; seed counts are reported for
every recipe; the screen is frozen before any seed is trained. Pre-registration is not
independently verifiable: the commits are private. Changes after this point are dated
amendments at the bottom, made before the step they affect.

Before this file was registered, the only training run was a code smoke test: 40
optimiser steps on seed 9999 for each task (`runs/r7-smoke`, `logs/r7-smoke-*.log`),
which fits nothing (worst error 1.9 and 4.3). It is not a seed of any stage.

## Statements

Common to both: architecture `Lane4/AGate.lean`, one block, state width 8, two heads
(masks strict and causal), one relative-position slope per head, a ReLU MLP with 12
hidden units, a scalar read-out, **no LayerNorm**; softmax in the stated order; the
rung-5 float model (`Rnd`, `ExpM` assumed). T is the network with the float32 weights
exactly as the optimiser left them (each float32 is a dyadic rational; no rounding).

- **B (primary).** Gate trained. Task: carry, pool setting c01 (5 tokens, modulus 3):
  the output at position i is (digit of token i + class of the latest non-propagate
  token before i) mod 3, at any distance. Theorem wanted: for every input of tokens
  1..5, |T.out − target| ≤ 1/4 at every position, at every length in exact arithmetic
  (`exact_all_lengths`) and up to 65,535 tokens in binary32 (`binary32`).
- **A (second).** Gate parameters are the constants g = 0, gb = −1, not trained, so
  every key is always a candidate: the standard architecture. Task: the sum mod 5 of the
  digits of the last two tokens (token t is digit t − 1; BOS counts 0), at every
  position of an input of any length. Same theorem shape.

**Headline sentences if passed (fixed now).**
- B: "N gradient-trained softmax transformers with a trained key gate (a non-standard
  component), no LayerNorm and a relative-position slope fixed at 24 [or: learned], are
  kernel-checked correct on a carry task at every length in exact arithmetic and up to
  65,535 tokens in binary32 arithmetic, with the weights exactly as trained."
- A: "N gradient-trained softmax transformers without a gate, with no LayerNorm and a
  relative-position slope fixed at 24 [or: learned], are kernel-checked correct at every
  context length ... on modular addition of the last two tokens; the every-length part
  is robustness to an unboundedly long prefix, not long-range computation."

Not claimed: anything about the standard box on long-range tasks (believed impossible,
`SCOPE_R7.md` section 1; a Lean impossibility theorem for it is noted as a possible
companion rung and is not started); LayerNorm; trained networks in general; novelty
beyond the dated check in `SCOPE_R7.md` section 4.

## Route

1. Train T (below). 2. Skeleton W := every weight of T snapped to the nearest multiple
of the recipe's grid step (1/4 for the recipe without a grid). 3. δ_T := the largest
|T − W| over all weights. 4. A doctor proves the rung-6a ball theorem for W at radius
δ_ball ≥ δ_T (δ_ball ∈ {1, 2, 4}/1000). 5. The study team proves that T is in that ball (a
decidable list of rational comparisons, plus `fl t = t` for binary32-representable t)
and composes. Standard axioms only; `native_decide` banned and counted.

## No-cheating line (binding)

Random initialisation from the seed. Task data only. Regularisers that do not depend on
any written network: L1 (proximal), a penalty pulling every weight to the nearest
multiple of a coarse step, a penalty keeping gate pre-activations away from 0, and, in
the learned-slope recipe, a penalty for slopes under 24. Forbidden: initialising at or
near a written network or a skeleton; a penalty toward a specific network; a sparsity
mask taken from a written network; choosing seeds by anything but the frozen screen.
Disclosed: the study team chose the architecture constants (width, heads, masks, MLP size,
slope 24, grid steps) knowing that written solutions of this shape exist; the widths
are larger than the written ones (rung 6a carry networks: width 3 to 5, one head).
During training the gate is soft (the score of a key is lowered by β times its gate
activation, β raised from 1 to 4,096) and the slope is raised from 2 to 24; the network
that is screened, proved and reported has the hard gate and the final slope. That
difference is measured by the screen, not assumed.

## Training (code `tools/r7.py`, frozen; torch CPU float32, 2 threads)

Adam, 6,000 steps, batch 64, lengths 2 to 40, inputs from the study team's four input patterns;
loss: squared excess of |output − target| over 0.03. Recipes:

| recipe | grid step | L1 | slope |
|---|---|---|---|
| r1 | 1/4 | 1e-4 | fixed 24 |
| r2 | 1/2 | 1e-4 | fixed 24 |
| r3 | 1/4 | 1e-4 | learned |
| r4 | none (skeleton snapped at 1/4) | 1e-4 | fixed 24 |
| r5 | 1/4 | 0 | fixed 24 |
| r6 | 1/2 | 3e-4 | fixed 24 |

## Screen (frozen now, before any seed; `tools/r7.py screen`)

A trained network passes when all three hold, with the hard gate, in numpy:
- **s1.** T in float32, stated order: worst |output − target| ≤ 1/4 on 30 inputs of
  lengths 6, 40, 300 (all positions), 3 inputs of length 2,000, and one each of 16,000
  and 65,534 tokens (sampled positions).
- **s2.** δ_T ≤ 4/1000.
- **s3.** W under 20 uniform and 20 sign-corner additive perturbations of every weight
  at δ_ball, float64, lengths 6 to 2,000: worst deviation ≤ 0.10. (0.10, not 0.25: the
  kit's bounds are loose; the proved rung-6a networks measured 0.011 to 0.044.)
Also recorded, not part of the pass: the multiple of δ_ball at which W breaks, the
number of non-zero weights of W. If s1's short part or s2 fails the screen stops there.

## Stage 0 (no doctors)

- **0a, recipe check on dev seeds 0 to 3**, all six recipes, both tasks: 48 networks.
  If no dev network of a statement passes the screen, the study team may change the training
  hyper-parameters (never the screen, the tasks, the architecture or the no-cheating
  line) on dev seeds 0 to 9 only, within **4 CPU-hours** in total for 0a; every run is
  kept and counted; the final recipes are fixed by a dated amendment before 0b.
  (`SCOPE_R7.md` said the grid would be fixed before any run; this dev phase is a
  change from that, made here, before any run, because untuned hyper-parameters failing
  would say nothing about the wall.)
- **0b, test seeds 100 to 119**, the recipes as fixed after 0a (at most 6), both tasks.
- **Reported for every recipe and task:** seeds trained, seeds passing s1, s2, s3 and
  the whole screen, best and median δ_T, and later seeds proved.
- **Kill (per statement):** no test seed of any recipe passes the screen. Then the best
  distances are the result. If both die, the rung ends.
- Budget: 10 CPU-hours for 0a and 0b together; reservations of 3 GB, one job at a time.

## Stage 1 (dev proof), stage 2 (test)

- **Stage 1.** Per surviving statement, one network: among the passing 0b networks, the
  one with the fewest non-zero skeleton weights (ties: lowest recipe number, then lowest
  seed). One Sonnet doctor, 12 submissions, the rung-6a kit and protocol, task: prove
  the given W at δ_ball. On failure one fresh Sonnet doctor with the first one's notes;
  then one stronger-model step if the project owner clears it. Still unproved: statement dead.
  If a statement gets its dev proof, the scope of the general certificate checker is
  written at once (project owner, point 5).
- **Stage 2.** Three further networks per statement, taken in the same order from the
  passing 0b networks of seeds not used at stage 1. **Pass: at least 2 of 3 proved.**
  One proved network alone is reported as a showcase theorem, not as the rung's result.
  If fewer than three further networks pass the screen, seeds 120 to 139 are trained
  with the same recipes and this is said.
- The membership lemma and composition are study-team work (kit cases by Sonnet doctors where
  a proof is needed), done once at stage 1.
- Doctors: Sonnet, fresh agent per case, one at a time. Usage: no new case at or above
  60% of the usage budget, hard stop 75%, checked and logged before each case.

## Numeric checks on every proved network

The rung-6a checks on W at δ_ball; T itself in float32 to 65,534 tokens; T in torch
against the study team's numpy forward pass (numeric agreement, not bit identity).

## What would make the result weak, written down now

- The gate (B) is non-standard; A's task is local.
- No LayerNorm; the slope 24 is far above what ALiBi uses and is set by the study team.
- The grid penalty drives trained weights to within thousandths of a coarse grid: a
  reader may call that rounding done by the optimiser. It is disclosed; recipe r4 has no
  grid penalty and shows what training gives without it.
- One block, width 8, one carry setting, one modulus. The task families are the study team's.
- The kit carries the analysis; the doctor proves a network close to written ones.
- Soft gate in training, hard gate in the theorem.
- exp accuracy assumed; stated operation order; the study team's own forward pass.

## Frozen files

sha256 list in `scratch/freeze_r7.sha256` (tools/r7.py, tools/r7_lease.sh, tools/r6net.py,
tools/r4pool.py, tools/r4_checks.py, tools/r5_checks.py, pool/rung4_pool.json,
Lane4/AGate.lean, Lane4/AGateKit.lean, Lane4/AGateKitW.lean); its own sha256 is recorded
in the study's private log (not included) entry for the registration.

## Amendment 1 (2026-11-19 9:07 PM EST): skeleton rule and recipes after stage 0a

Written after stage 0a and before any stage 0b seed. **Test seeds 100 to 119 (and 120 to
139) are untouched: none has been trained.** Stage 0a used dev seeds 0 to 5 only, about
1.4 of the 4 CPU-hours allowed; every run is kept under `runs/r7-stage0` with logs
`logs/r7-0a*.log`.

**What had been seen when this was written (dev seeds, hard-gate forward pass, frozen screen).**
- Registered recipes r1 to r6, seeds 0 to 3, both tasks: 0 of 48 pass. Without the grid
  penalty (r4) T's worst error was 0.03 on A for 4 of 4 seeds and on B for 1 of 4
  (seed 2; the others 0.68 to 0.80), but its skeleton at step 1/4 was 0.125 away. With
  the grid penalty δ_T was 0.0005 to 0.0086 and T's worst error 0.6 to 5.5.
- Round 1 (t1 to t3: gentler grid ramp, steps 1/8, 1/4, 1/16; seeds 0, 1): 0 of 12; A's
  best worst-error 0.32 at step 1/16; B 1.6 to 2.3.
- Round 2 (u1 to u3: no grid penalty, skeleton step 1/1024; seeds 0 to 3): A 7 of 8 pass
  (u3 4 of 4; the one failure, u1 seed 3, had 0.104 inside the ball against the 0.10
  bar); B 3 of 12, all on seed 2. Passing networks: T's worst error 0.030 to 0.038 to
  65,534 tokens, skeleton inside the 1/1000 ball 0.047 to 0.094, breaking at 8 to 16
  times the radius (one failing network at 4), 243 to 456 non-zero weights of 545.
- Round 3 (u4, u5: null key in the training softmax; B, seeds 0 to 5): u4 2 of 6, u5
  3 of 6; the failures did not fit in training (worst error 0.8 to 1.8).
- Round 4 (u6, u7: learned slope; seeds 0, 1): A 2 of 2 (learned slopes about 14);
  B 0 of 2.

**Change 1: the skeleton (Route, step 2).** W := every weight of T rounded to the nearest
multiple of 1/1024. Then δ_T ≤ 1/2048 by construction, δ_ball = 1/1000, and screen step
s2 is met automatically and no longer discriminates; s1 and s3 are unchanged and carry
the screen. Reason: the theorem is about T as trained; W is a proof device that only has
to be near T and provable. Forcing weights to a coarse grid broke the function and is
dropped; with it goes the "rounding done by the optimiser" weakness. W is computed from
T alone by this fixed rule.

**Change 2: recipes for stage 0b** (all: no grid penalty, L1 kept on to the last step,
gate-margin penalty weight 1.0, 6,000 steps; code `tools/r7.py`, new freeze below):

| task | recipe | L1 | slope | training softmax |
|---|---|---|---|---|
| A | u3 | 3e-4 | fixed 24 | as registered |
| A | u1 | 1e-4 | fixed 24 | as registered |
| A | u6 | 3e-4 | learned | as registered |
| B | u5 | 3e-4 | fixed 24 | null key |
| B | u4 | 1e-4 | fixed 24 | null key |
| B | u7 | 3e-4 | learned | null key |

The null key (B only, training only): the training softmax has one extra entry with
value 0 and a score one slope below key 0, so that "every key penalised by the soft
gate" trains toward output 0, which is what the hard gate gives when no key is a
candidate. The network that is screened, proved and reported has the hard gate and no
null key, as registered. Recipes r1 to r6 and t1 to t3 are not run at 0b.

**The no-cheating line is unchanged and is repeated word for word:** Random
initialisation from the seed. Task data only. Regularisers that do not depend on any
written network: L1 (proximal), a penalty pulling every weight to the nearest multiple of
a coarse step, a penalty keeping gate pre-activations away from 0, and, in the
learned-slope recipe, a penalty for slopes under 24. Forbidden: initialising at or near a
written network or a skeleton; a penalty toward a specific network; a sparsity mask taken
from a written network; choosing seeds by anything but the frozen screen. (The grid
penalty of that sentence is no longer used by any 0b recipe.) No information about a
written solution enters training or the choice of W beyond T itself and task-agnostic
rules.

**Stage 1 order.** As registered (fewest non-zero skeleton weights), within the
fixed-slope recipes first; a learned-slope network is taken only if no fixed-slope
network of that statement passes the screen.

**What the proof doctor now receives, and what that does to the odds.** A network W of
width 8 with two heads and 12 hidden units whose weights are multiples of 1/1024 and of
which 240 to 460 of 545 are non-zero. It does not read like a written network: there is
no clean mechanism to recognise, and the rung-6a networks had 3 to 10 state coordinates
and 2 or 3 hidden units. What makes a proof possible is that the reachable ideal states
are finite (A: 30 pairs of last two tokens including BOS; B: 5 tokens times 3 carry
classes), so the proof is exact rational evaluation on those cases plus the kit's error
bounds (ReLU is 1-Lipschitz, so no sign pattern is needed), with numeric head-room of
about 0.05 to 0.09 measured against 0.25. The risks are proof size and the 600 s check
limit, and whether the kit's worst-case bounds fit a dense MLP. Doctors may generate the
Lean text with a script.

Revised odds (judgements): screen passes at 0b: A 95%, B 90%. Proof of a screened
network by a Sonnet doctor by hand: about 25% for either; with one stronger-model step about 45%.
Overall A about 40%, B about 40% (B rises because the training side is now largely
answered on dev; A is unchanged because the proof got harder as the training got
easier). If stage 1 fails on proof size rather than on a false bound, the general
certificate checker of `SCOPE_R7.md` section 3 becomes the main route, and I will ask
the project owner before starting it.

**New freeze:** `scratch/freeze_r7_a1.sha256` (same file list); its sha256 is in the
private log entry for this amendment.

## Amendment 2 (2026-11-19 10:44 PM EST): certificate checker replaces the by-hand stage 1

**When this was written, and what had been seen.** After the stage 0b read (commit
8031035) and `SIZE_R7.md` (commit 62486d1), on the project owner's decision, and before any
proof attempt on any rung-7 network: no doctor has run on rung 7 and the only rung-7 Lean
job so far is the type-check of the transfer statements on 11-19 (`logs/r7-kT-typecheck.log`).
What I had seen when fixing the checker below: the screen results of all 120 test-seed
networks; the mechanistic read of B u5 seed 103 and A u3 seed 110 (`scratch/r7_mech.py`);
and the output of the Python prototype of this checker (`tools/r7_cert.py`) on **every**
screened test-seed network of both statements (`results/rung7-cert-prototype.json`),
including runs with the score gap set to 16, 12 and 8 and with single error terms switched
off (`scratch/r7_cert_diag.py`). So the checker's one free constant (gap 12 instead of the
kit's 16) was chosen knowing which B networks each value accepts. That cannot make a
wrong network pass, because acceptance only counts through a kernel-checked soundness
theorem, but it means the pass counts below are not a clean held-out measure of how often
the method works. The clean measure is the reserve seeds (bar, point c).

**Stage 1 as registered is not run.** The by-hand dev proof (one Sonnet doctor, 12
submissions) is skipped: `SIZE_R7.md` puts it under 10%. Stage 2 as registered is replaced
by the bar below. The no-cheating line stands word for word: no information about a
written solution enters training or the choice of W beyond T itself and task-agnostic
rules. The checker and the certificate script are task-agnostic rules in that sense: they
read the network and the task's definition, nothing else.

**1. The checker's statement.** `scratch/R7Cert.lean` (draft, frozen by sha256 with this
amendment; it has not been through Lean yet, so the first Lean job type-checks it, and any
change needed to make it type-check is logged as a diff in the study's private log (not included) before any proof
case starts; a change to what it computes, as opposed to its syntax, needs a new
amendment). In words:

- A task is an automaton over tokens: initial state, step, output; the target at a
  position is the output of the state reached on the earlier tokens and the token there.
  Both registered tasks are of this form by definition (B: the carry fold; A: the previous
  digit), and the study team proves per task that the registered `target` equals it.
- `check δ N T cert : Bool` is a computable function over exact rationals. It supports one
  block, strict and causal masks, any number of heads the architecture allows. It pushes
  an interval (centre, radius) per coordinate through the network using the kit's own
  error terms: stored weights (`asw_near`), stored-weight dot products
  (`ardot_near_w`), content scores (`pdot_near`), position bias (`bias_gap`), softmax
  with a clear winner (the kit's `soft_near` re-proved at a score gap of 12 per position
  in place of 16, same error bound B/100 + 2^-90; a new kit lemma), ReLU by clamping the
  interval at 0 (a unit whose interval excludes 0 is passed through exactly, which is the
  sign-aware part), rounded additions.
- It checks, per head: every token's gate is decided with margin (candidate or not), the
  slope is in range, and for every query token any two candidate tokens differ in content
  score by at most slope - δ - 12 - 3(slope + 2)/64, so the latest earlier candidate
  position wins the softmax at every length. Then, over a set of abstract states (task
  state, and per head the token at the latest earlier candidate position) that contains
  the initial state and is closed under reading a token: the output interval for (query
  token, picks) lies within 1/4 of the automaton's output.
- **ONE soundness theorem** (`Sound`): if `check (1/1000) N T cert = true` then for every
  rounding model and exponential model of the rung-6a `Statement`, every perturbation
  within the additive 1/1000 ball, every input over the task's tokens of every length the
  model covers, and every position, the output is within 1/4 of the target. Proved once,
  for all networks and all automaton tasks. Standard axioms only (`propext`,
  `Classical.choice`, `Quot.sound`); `native_decide` is banned as before and every use is
  flagged.
- Per network: `check ... = true` by `decide` (kernel evaluation), then `Sound`, then the
  transfer lemma (kit case kT: T is in the ball of W by `decide` on the closeness
  predicate, and the unperturbed T equals W perturbed by T - W), giving the registered
  headline for the trained T at every length, and the binary32 corollary as in rung 6a.

**2. The certificate.** Two things: per head, which tokens are candidate keys; and the
closed list of abstract states. Found by `tools/r7_cert.py` from W (that is, from T by
rounding) and the task definition alone, by exact rational arithmetic: the candidate sets
are the signs of the gate centres, the state list is the closure from the initial state.
No doctor per network, no search, no tuning per network. The script is frozen with this
amendment; the Lean checker recomputes everything, so the script's output is only a hint
that the kernel verifies.

**3. The bar.**
- (a) B, primary. u5 networks that passed the screen, in the registered order (fewest
  non-zero skeleton weights): seeds 103, 118, 113, 106, 117, 108. Seed 103 is the dev
  network (pipeline debugging is allowed on it). The bar: at least 2 of the next 3 (118,
  113, 106) get the full kernel-checked headline. Also reported: how many of all 6.
  Prototype prediction, stated now so it can be wrong: 103, 118, 113, 106, 117 accepted
  (worst bounds 0.162, 0.166, 0.153, 0.231, 0.154 against 0.25), 108 rejected (content
  score spread 11.8 against 10.78 allowed).
- (b) A, second. Same rule on u3's 18. Prototype prediction: **0 of 18** (and 0 of 31
  under u1 and u6). Two reasons, both about the method and not about the networks being
  wrong: most A networks pick their key by content score against the position bias
  (spreads of 11 to 27 at slope 24), which this checker's "latest candidate wins" model
  does not cover; and for the one that fits the model (seed 110) plain intervals give
  0.54 against 0.25. So by this route A is expected to be reported as rejected, with
  those reasons. A checker for content-selected keys with tighter (affine) intervals
  would be a separate amendment; I do not start it without the project owner.
- (c) Clean count. After the bar is read, train B u5 on the registered reserve seeds
  120 to 139 (frozen `tools/r7.py`, frozen screen, under a reservation), and report how many
  pass the screen and how many of those the frozen checker accepts in the kernel. Nothing
  about the checker may change between this amendment and that count, except by a dated
  amendment that then also forfeits the word "clean".
- A network the checker rejects is reported as rejected with the reason the script
  prints. Learned-slope networks (u6, u7; slopes near 14) are expected to be rejected for
  slope room; that is a stated limit of the method (it needs slope of about 20 or more).

**4. Non-vacuity (negative controls, fixed now).** The checker must return false on each
of these, in the kernel (`decide` on `check ... = false`), for the dev network B u5 seed
103 unless said otherwise: (i) radius 16/1000 in place of 1/1000; (ii) radius 4/1000;
(iii) the same network against task A's automaton; (iv) embedding rows of tokens 1 and 2
swapped; (v) read-out weights negated; (vi) B u5 seed 100, a trained network that fails
the task (screen s1 failed, error 1.7); (vii) the certificate of seed 103 with its
candidate sets taken from seed 118's second head (a wrong certificate for a right
network). The Python prototype already rejects (i) to (vi). In addition the usual lane
checks on every accepted network: axioms, exact-arithmetic evaluation of T on inputs to
65,534 tokens, sampled perturbations inside the ball, and the first multiple of the
radius at which a sampled perturbation breaks the bound.

**5. Kill rules.**
- **K-a (kernel feasibility).** First Lean jobs after this amendment: type-check
  `scratch/R7Cert.lean`, then `decide` on `check (1/1000) net task cert = true` for the dev
  network and on the closeness predicate of the transfer lemma. If `decide` does not
  finish inside the 600 s limit and 4 GB, split into one lemma per abstract state or per
  table row (the check is a conjunction over a list, so the pieces reassemble) and, if
  needed, restate the arithmetic over integers scaled by a power of two with a proved
  equivalence. If it still does not finish, the route is dead: report, stop.
- **K-b (soundness).** The proof is cut into kit cases fixed now: k1 the softmax lemma at
  gap 12; kT the transfer lemma (already drafted); k2 interval lemmas (dot product, affine
  map, ReLU clamp, addition are sound for the real quantities); k3 the head lemma (gate
  decided per token, latest earlier candidate wins, head output within the head interval
  at every length); k4 the automaton lemma (the abstract state at every position is in the
  closed set, and the target is the automaton's output); k5 composition into `Sound`.
  Each case: one Sonnet doctor (30 submissions, the kit protocol), on failure one fresh
  Sonnet doctor with the first one's notes. **One stronger-model step in total**, asked through the
  project owner, for the first case that fails both Sonnet doctors; I expect k3. A second
  case failing both Sonnet doctors, or the stronger-model step failing, is the kill: report what
  was proved (the lemmas stand as partial results), stop.
- If a case's statement turns out false or unprovable as written (for example a constant
  in the evaluator is too small for the kit bound it mirrors), the fix is a dated
  amendment; if the fix changes a constant of the checker, the prototype is rerun on all
  networks and the changed predictions are logged before any kernel check.

**6. Odds and cost (judgements, 2026-11-19).** K-a passes: 80%. Soundness proved within
K-b: 45% (k3 is a generic version of the argument every rung-6a doctor made per network,
but over lists and for every length, with five kit lemmas to fit together; the constants
in the draft evaluator were set from the kit statements by reading, not by proof). Given
both, B meets the bar: 90%. **B overall about 33%.** A by this route: under 5%.
Doctor tokens: about 2.5 to 4 million Sonnet tokens over six kit cases and their retries
(rung-6a kit cases ran 200k to 600k each), plus one stronger-model step. Lean: kit checks under
the usual 3 GB service reservation, one job at a time.

**What a pass would and would not be.** A pass is a method: a kernel-checked checker that
turns a trained one-block gated transformer and a two-line certificate into an all-length,
whole-ball, binary32 correctness theorem, with no per-network proof work. It would not be
a result on the standard architecture (A is expected to fail), the networks are width 8
with no LayerNorm and slope fixed at 24, and the method accepts only networks whose heads
select "the latest candidate" by position; a trained network that solves the task another
way is rejected, not proved wrong.

**New freeze:** `scratch/freeze_r7_a2.sha256` (`scratch/R7Cert.lean`, `tools/r7_cert.py`,
`tools/r7.py`, `runs/r7-kit/kT/Spec.lean`); its sha256 is in the study's private log (not included) entry.

### Note to Amendment 2 (2026-11-20 12:39 AM EST): which form of `decide` is used

Amendment 2 says "`decide` only, never `native_decide`". The first K-a job
(`logs/r7-ka-1-pieces.log`, 12:37 AM EST) showed that the plain `decide` tactic cannot
evaluate a comparison of rationals: on `(1/3 : ℚ) + 1/6 ≤ 1/2` it reports "reduction got
stuck" inside `Rat.instDecidableLe` (the elaborator will not unfold the definitions behind
rational arithmetic). The form `decide +kernel` evaluates the same proposition, one gate
and the whole first head of the dev network. From here on every per-network check in rung 7
(the checker, the closeness predicate, the negative controls) uses **`decide +kernel`**.

What it is: the same `Decidable` instance, with the kernel itself evaluating
`Decidable.decide p` to `true`; the proof term is `of_decide_eq_true (Eq.refl true)`. It adds
no axiom and does not use `Lean.ofReduceBool` or the compiler, which is what `native_decide`
does and why that stays banned and unused. Evidence, quoted from the log, for the test
theorem `head0` (`headOK` of head 0 of B u5 seed 103, proved by `decide +kernel`):

    'Lane4.KA.head0' depends on axioms: [propext, Classical.choice, Quot.sound]

`#print axioms` is run on every theorem proved this way, and any axiom outside these three
fails the check.

Timing: this note was written and committed after the small-pieces test and before the
whole-network check for seed 103 (`scratch/R7KA2_B_u5_s103.lean`) had finished (that job started within seconds of this note being written and ran 28 s; the note was committed at 12:39:11 AM, the job ended about 12:39:40 AM); its test
file, generated at 12:26 AM EST (commit 22d2c1c), already used `decide +kernel`, a choice
made before any K-a job ran and disclosed in the study's private log (not included) then. The statement file
`scratch/R7Cert.lean` type-checked with no change (`logs/r7-ka-0-cert-typecheck.log`), so
the freeze of Amendment 2 stands.

## Amendment 3 (2026-11-20 1:13 AM EST): magnitude guards in the checker

**When this was written, and what had been seen.** After K-a passed on the Amendment 2
checker (private log, 12:42 AM EST: the kernel accepted B u5 seed 103), after kit cases kT
(transfer) and k1 (softmax at gap 12) were proved, and before any statement of kit cases
k2 to k5 was written or given to a doctor. No per-network result other than the dev
network's K-a acceptance existed. The change was found by me reading the evaluator
against the kit lemmas it mirrors, in preparation for cutting k2 to k5; no doctor and no
failed proof attempt pointed to it.

**The defect.** The Amendment 2 evaluator charges `rnd = 2^-20` for each rounding ("one
rounding of a quantity of size at most 16") and uses the kit's dot-product and
content-score bounds, but it never checked the conditions under which those charges are
valid: that the rounded quantity really is that small, and the range hypotheses of
`ardot_near_w` and `pdot_near`. So `Sound` as stated in Amendment 2 quantified over all
networks while its error terms were only right for networks with small weights and
activations: a network with large activations and a bound sitting exactly at 1/4 could in
principle be accepted wrongly, and in any case the theorem was not provable as written.
This is the case Amendment 2, point 5, last paragraph, provides for.

**The fix (what the checker now computes in addition; nothing is removed or loosened).**
- `weightsOK`: every written weight of the network is at most 15 in absolute value.
- `small`: a rounded quantity's interval satisfies |centre| + radius ≤ 15. Required of
  every gate pre-activation (`gateDec` returns undecided otherwise), every partial sum of
  the residual stream over the heads (`headsOK`), both affine layers of the MLP, the
  block output, and the read-out (`outOK`, a new conjunct of `caseOK`). With size at most
  15, one rounding costs at most 15 · 2^-24 + 2^-149 < 2^-20, which is what `rnd` charges.
- `scoreOK` (new conjunct of `headOK`, per query token and candidate key): the range
  hypothesis of `pdot_near`, and |content score| + radius ≤ 1024, so that rounding the sum
  of position bias and content score is covered by the slack already in `slopeRoom`
  (3(m+2)/64 charged, 5(m+2)/128 needed by `bias_gap` and the two score roundings, the
  remaining (m+2)/128 ≥ 3/128 covers 2 · (1024 · 2^-24 + 2^-149)).
- value bounds of a head at most 2^20 (the range hypothesis of the softmax lemma).
- No constant of Amendment 2 changes: gap 12, `slopeRoom`, `rnd`, `e0`, tolerance 1/4,
  radius 1/1000 are as they were. `Sound` is word for word the same statement, about the
  new `check`. Since the new `check` implies the old one, every network it accepts was
  accepted before; it can only reject more.
- Files: `scratch/R7Cert.lean` (the Amendment 2 text is kept as `scratch/R7Cert_a2.lean`),
  `tools/r7_cert.py` (same guards; one more mirror fix: the content-score error now uses
  the query row's own magnitude, as the Lean file always did, in place of the largest
  magnitude over all rows; this is slightly tighter and matches Lean exactly).

**Prototype rerun on all networks, before any kernel check with the new checker**
(`logs/r7-cert-all-a3.log`, `results/rung7-cert-prototype.json`; the Amendment 2 results
are kept as `results/rung7-cert-prototype-a2.json`): no accept/reject decision changes
and no worst bound changes at four decimals. B u5 5 of 6, B u4 2 of 6, B u7 0 of 1, A 0
of 49; controls (i) to (vi) rejected as before. Two A u6 rows (seeds 106, 109) are
rejected with a different printed reason. So the predictions of Amendment 2, point 3,
stand unchanged.

**What this does to the registered design.** The bar, the order of networks, the negative
controls, the kill rules and the kit cut are unchanged. Point 3(c) of Amendment 2 (the
clean count on reserve seeds 120 to 139) said nothing about the checker may change before
that count "except by a dated amendment that then also forfeits the word clean". This is
such an amendment. I report the reserve-seed count as "after Amendment 3" and do not call
it clean without the project owner's agreement; my own reading is that the guards were added
blind to any reserve-seed network (none is trained yet) and changed no decision on any
test-seed network, so the count is still a held-out measure of the frozen method, but
that is for the reader to judge with this paragraph in front of them.

**K-a is rerun** on the new checker (type-check, split kernel check of seed 103) before
k2 starts; result in the study's private log (not included).

**New freeze:** `scratch/freeze_r7_a3.sha256` (`scratch/R7Cert.lean`, `tools/r7_cert.py`,
`tools/r7.py`, `runs/r7-kit/kT/Spec.lean`).

**K-a rerun on the Amendment 3 checker (recorded with the amendment):** the guarded
`scratch/R7Cert.lean` type-checks (12.8 s, `logs/r7-a3-cert-typecheck.log`); the split
kernel check of B u5 seed 103 (2 head lemmas, 10 state lemmas, `weightsOK`) passes in
36.3 s at 4.31 GB peak commit, standard axioms (`logs/r7-a3-split.log`). These two jobs
ran between the drafting of this amendment and its commit.
