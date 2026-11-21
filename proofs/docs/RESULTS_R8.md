# Rung 8 results: kernel-checked all-length correctness for trained ungated softmax transformers, at a weight ball of 2^-14

Written 2026-11-21 (EST). Registered design: `PREREG_R8.md` with Amendment 1. Every number below
is read from files named here (`results/rung8-kernel.json`, `results/rung8-lane-checks.json`,
`results/rung8-extra.json`, the logs under `logs/r8-*`); nothing is from memory. `native_decide`
is not used anywhere (count over the rung-8 modules and all 76 generated files: 0).

## Headline

**19 of 20** gradient-trained one-block softmax transformers without a gate (fresh seeds 140 to
159, all 20 of which compute the task and pass the screen) are kernel-checked correct, with the
weights exactly as trained, on modular addition of the last two tokens at every context length in
exact arithmetic and up to 65,535 tokens in binary32 arithmetic, with no proof work per network;
each theorem covers an additive weight ball of radius **2^-14, about 16 times smaller than the
ball of rung 7**. No LayerNorm, no position embedding, one block of width 8, and a
relative-position slope fixed at 24; the task is local, so the every-length part is robustness to
an unboundedly long prefix, not long-range computation.

The twentieth network (seed 153) is rejected by the checker in the kernel. The registered bar (at
least 2 of the first 3 screened networks, seeds 140, 141, 142) was met with 3 of 3. The checker
was frozen before any of these 20 networks was trained and was not changed afterwards, so the
count is clean in the registration's sense.

**What the count does not say.** The checker's design, its four constants and the ball size were
fitted to 18 to 20 earlier networks of the same recipe (next section). The fresh seeds measure
whether that fit carries to new seeds of the same recipe, task and architecture; they say nothing
about any other recipe, task, width or depth.

**Prior work.** teal-sea/lean-checked-network has a kernel-checked all-length theorem for a
trained network (a threshold RNN adder in exact integers, by a finite certificate plus
induction). That pattern is theirs as much as ours. What is different here is softmax attention,
floating-point arithmetic and a weight ball, checked by one checker with one soundness theorem;
in the search of 2026-11-20 we found no earlier all-length kernel-checked theorem of that kind.
That is a statement about one search, not a claim that none exists.

## What was tuned before the fresh seeds (disclosure)

- The prototype checker was tuned in four passes on the 18 screened A networks of seeds 100 to
  119. Three designs did not work: (1) the first version at the rung-7 skeleton and the rung-7
  ball of 1/1000 gave 0.44 against the tolerance 0.25 on the network read by hand; (2) the same
  checker at 2^-14 with the rung-7 charges accepted 1 of 18; (3) with two tighter charges, 17 of
  18. The fourth pass (reference key chosen by nominal score) gave 18 of 18.
- **The ball shrank from 1/1000 to 2^-14 to make task A pass.** At the rung-7 ball the prototype
  accepts 1 of the 18. The value 2^-14 was picked after seeing the table of ball sizes.
- The Lean checker and its mirror were then written and changed further on the same tuning set
  before the freeze (Amendment 1 lists the changes: P1 charge 2^-8, softmax-arithmetic charge
  B/2^13, ReLU slope rounded to 2^-20, two extra guards).
- **Amendment 1 raised the kernel-feasibility limits after seeing the result**: from 600 s and
  4.5 GB to 900 s and 6 GB per network, because the largest tuning-set network measured 586 s and
  4.83 GB. A fresh network over the amended limits would have counted as not accepted; none was.
- The screen: the frozen rung-7 screen tests the 1/1000 ball, which is no longer the statement
  for A. Screen 8 is the same screen with the 2^-14 skeleton and radius; it was fixed before the
  fresh seeds. Four fresh A networks (144, 145, 152, 153) pass screen 8 and fail only the 1/1000
  part of the frozen screen; three of them are accepted and 153 is the rejected one.
- Tuning-set count with the frozen checker (mirror; `logs/r8-variants-frozen.log`): A 20 of 20
  at 2^-14, B 15 of 15 at 2^-14, B 15 of 15 at 1/1000. These are fitted numbers, not results.

## What is proved

**One theorem for all networks** (`Lane4/R8K.lean`, `Lane4.R8K.sound8 : Lane4.Cert8.Sound8`; the
statement is in `Lane4/R8Cert.lean`): for every radius δ, if the computable checker
`check8 δ N T cert` returns `true` for a one-block network `N`, a task `T` given as an automaton
and a certificate, then every network within the additive δ-ball of `N`, in the rounding model of
rung 5 (`Rnd`, with a float exponential satisfying `ExpM`), is within 1/4 of the task target at
every position of every input of every length the model covers. Axioms: `propext`,
`Classical.choice`, `Quot.sound`. It was proved in eight kit cases, each passed by its first
Sonnet doctor (submissions used: 1, 1, 4, 3, 3, 3, 6, 1 of 30; about 1.59 M doctor tokens; no
retry and no stronger-model step).

**Per trained network**, a generated file `runs/r8-nets/<tag>/Net.lean` (no doctor and no proof
text written for that network; every closed Boolean by `decide +kernel`) proves four theorems,
each with exactly those three axioms:

- `accept`: `check8 (1/16384) net task cert = true`, where `net` is W14 (the trained weights
  rounded to multiples of 2^-14) and `cert` is found by `tools/r8_cert.py`.
- `skeleton_ok : Statement net`: the registered statement for the whole additive 2^-14 ball.
- `trained_exact_all_lengths`: the network exactly as trained (float32 weights as rationals, no
  rounding of weights, no perturbation), exact real arithmetic, every input over tokens 1 to 5 of
  every length, every position: output within 1/4 of the target.
- `trained_binary32`: the same bound in IEEE binary32 arithmetic (any round-to-nearest, a float
  exponential within the stated error), at most 65,535 tokens.

For a network the checker does not accept, the file proves `reject : check8 … = false` instead.
For task A the generator also emits a lemma, written once by the study team before the freeze, that the
automaton's target equals the registered closed form (sum of the last two digits mod 5).

The architecture is `Lane4/AGate.lean` with the gate fixed open (g = 0, gb = -1, not trained):
one block, width 8, two heads (strict and causal mask), slope 24 per head, ReLU MLP with 12
hidden units, scalar read-out, no LayerNorm, no position embedding.

## Counts on fresh seeds (`results/rung8-kernel.json`, built from each `lean.log`)

| Set (seeds 140 to 159) | Trained | Compute the task (s1) | Pass the screen | Kernel-accepted, all four theorems | Kernel-rejected |
|---|---|---|---|---|---|
| A u3, W14 at 2^-14 | 20 | 20 | 20 (screen 8) | **19** | 1 (seed 153) |
| B u5, W14 at 2^-14 | 20 | 6 | 6 (screen 8) | 6 | 0 |
| B u5, rung-7 skeleton at 1/1000 | 20 | 6 | 6 (frozen rung-7 screen) | 6 | 0 |

- **Bar** (first three A networks passing screen 8, ascending seed: 140, 141, 142; at least 2
  with all four theorems): **3 of 3. Met.**
- **Seed 153**, the mirror's reason: case token 5, keys ((4, 5), (5, 4, 5)), task state 3, output
  2.0300 ± 0.2201 against target 2 (mixed attention); as printed (four decimals) that is a bound
  of about 0.250 against the tolerance 0.25, so it misses narrowly. The network computes the task in float32 (worst deviation 0.036). It is
  reported as "not covered", not as wrong, and the checker was not adjusted for it.
- **B has no bar.** The six B networks are the six of 20 that compute the task at all; the other
  14 fail s1 and are control 7. B at 1/1000 beside the rung-7 checker (its mirror,
  `tools/r7_cert.py`) on the same six networks: 6 of 6 for both. On the tuning set the rung-7
  checker accepted 9 of 15 where the rung-8 checker accepts 15; on these six fresh networks there
  is no difference to see.
- **Kernel against mirror:** the kernel's decision equals the mirror's on all 76 files (32 fresh
  A and B files, 44 control files).
- **Cost per network** (one file, one Lean job, 5 GB reservation): accepted A networks 25 s to 455 s
  and 4.41 to 4.87 GB peak commit (3 networks with 6 abstract states, 15 with 31, one with 156);
  B 29 s to 64 s, at most 4.46 GB; the largest reject file 5.18 GB. All within the amended limits
  of 900 s and 6 GB; nothing was "not checked within limits".

## Controls (fixed in advance; each must be rejected)

All eight are rejected; no control was accepted.

| Control | Files | Result |
|---|---|---|
| 1. Task B's automaton on the A network (dev network A u3 seed 110) | 1 | kernel reject: output 0.03 ± 0.04 against target 2 |
| 2. Embedding rows 1 and 2 swapped | 1 | kernel reject: 1.03 ± 0.06 against 0 |
| 3. Read-out weights negated | 1 | kernel reject: -1.03 ± 0.06 against 1 |
| 4. Read-out bias raised by 1/2 | 1 | kernel reject: 0.53 ± 0.04 against 0 |
| 5. Radius 1/1024 (16 times larger) | 1 | kernel reject: 0.04 ± 0.26 against 0 |
| 6. Radius 1/256 (64 times larger) | 1 | kernel reject: 0.08 ± 1.00 against 0 |
| 7. Every fresh network failing s1: 14 B networks, both balls | 28 | 28 kernel rejects |
| 8. Old task-failing B networks: first five by seed, both balls | 10 | 10 kernel rejects |
| 8. The other twenty, both balls, mirror only | 40 | 40 mirror rejects |

Controls 5 and 6 are rejections the theorem does not need (a larger ball could be true); they
show that the radius enters the check. No fresh A network failed s1, so control 7 is B only, as
the registration expected.

## Numeric checks on every accepted network (searches, not proofs)

`tools/r8_checks.py lane` -> `results/rung8-lane-checks.json`. No violation of any kind.

| Set | Networks | T float64, worst deviation | T float32 to 65,534 tokens | Skeleton inside its ball (sampled) | Sampling breaks the bound at | Interval test |
|---|---|---|---|---|---|---|
| A, W14 at 2^-14 | 19 | 0.031 to 0.035 | 0.031 to 0.035 | 0.033 to 0.039 | 32x (1), 64x (7), not up to 64x (11) | 77,314 positions, 0 violations, smallest slack 0.0078 |
| B, W14 at 2^-14 | 6 | 0.031 to 0.037 | 0.030 to 0.037 | 0.032 to 0.038 | not up to 64x (6) | 24,225 positions, 0 violations, smallest slack 0.0042 |
| B, rung-7 skeleton at 1/1000 | 6 | 0.031 to 0.037 | 0.030 to 0.037 | 0.043 to 0.063 | 16x (6) | 24,225 positions, 0 violations, smallest slack 0.0246 |

The interval test compares forward passes (float64 on short inputs with sampled perturbations
inside the ball; float32 at 2,000 and 65,534 tokens) with the mirror's interval for the abstract
case of each position. The break multiple comes from the rung-6a lane check, which tries 2 to 64
times the radius.

## What makes this result weak

- **The ball is 2^-14**, chosen on the tuning set, 16 times smaller than rung 7's. The theorems
  for the network as trained do not depend on it; the robustness claim does, and it is small:
  sampling breaks the A networks only at 32 to 64 times the radius or not at all up to 64 times, so the proved ball is far
  inside what the networks appear to tolerate.
- The checker's design and four constants (window tail e^-16, window at most 3, the P1 and P2
  charges) were fitted to networks of the same recipe. One fresh network in 20 already falls
  outside, narrowly, which is the fit showing.
- Task A is local (last two tokens). "Every length" means an arbitrarily long prefix is ignored.
- Fixed slope 24, far above common practice and set by the study team; no LayerNorm; no position
  embedding; width 8; one block; one task with a bar; one recipe; the study team's own task.
- B on fresh seeds is six networks with no bar, and only 6 of 20 trained B networks compute the
  task.
- The exponential's accuracy is assumed (`ExpM`); the operation order is the stated one; the
  forward pass is the study team's own definition, not an existing framework's.
- The checker is a sufficient condition and cannot be complete (Yang et al. 2026).
- teal-sea had the certificate-plus-induction pattern for a trained network first.
- Pre-registration is not independently verifiable: the commits are private.

## Deviations and things written after the freeze

- No file in the freeze list (`scratch/freeze_r8_checker.sha256`) changed after the freeze; the
  list was re-checked before each batch and at the end (all OK).
- Written after the freeze, none in the freeze list, none changes a decision: `tools/r8_jobs.sh`
  (runs the frozen generator and the frozen Lean runner over a job list), `tools/r8_checks.py`
  (numeric checks and the mirror-only items; calls the frozen mirror), `tools/r8_collect.py` (reads
  logs). The study team-check script was written after the A count had been read.
- Before the freeze, the first end-to-end test on the dev network failed in three theorems
  because the generated target lemma for task A was not true by `rfl`; the study team wrote the proof
  into the generator and the freeze followed. Logged in the study's private log (not included) (2026-11-20, 6:57 pm).
- "The rung-7 checker on the same networks" was read with its mirror, not with the rung-7 Lean
  files.
- The A batch took about five hours of wall time because 5 GB reservations queued behind other
  runs; no limit was affected.

## Files

- Registration and amendment: `PREREG_R8.md`. Scope and K1: `SCOPE_R8.md`.
- Checker, soundness: `Lane4/R8Cert.lean`, `Lane4/R8K.lean` (and `R8KA` to `R8KG`, `R8Glue`,
  `R8Defs`, `R8Soft`). Kit cases: `runs/r8-kit/ka` to `kh`.
- Fresh networks: `runs/r8-fresh/{A/u3,B/u5}/s140` to `s159`. Generated files and Lean logs:
  `runs/r8-nets/<tag>/`. Job lists: `scratch/r8jobs/`. Controls 2 to 4: `runs/r8-ctl/`.
- Results: `results/rung8-kernel.json`, `results/rung8-lane-checks.json`,
  `results/rung8-extra.json`, `results/rung8-variants-frozen.json`.
- Private log: `../private log/lane4-2026-11-11.md`.
