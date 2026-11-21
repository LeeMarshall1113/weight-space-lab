# Rung 7 results: kernel-checked all-length correctness for transformers whose weights came from training

Written 2026-11-20, 5:55 am EST; headline, numeric checks and Limits added 6:10 am EST. Registered
design: `PREREG_R7.md` with Amendments 1 to 3. Every number below is read from files named here;
nothing is from memory. `native_decide` is not used anywhere (grep over every generated file: 0).

## Headline

On held-out seeds, the method gives a kernel-checked, all-length correctness theorem for **4 of
the 9 trained networks that pass the screen (4 of 20 trained seeds)**, on a gated one-block
transformer and one carry task, with no proof work per network. On the standard (ungated)
architecture it gives **0 of 18**.

The test-seed figure is higher, 5 of 6 screened networks (the registered bar, 2 of the first 3,
was met with 3 of 3), but the checker's one free constant, the score gap of 12, **was chosen with
those six test networks in view** (Amendment 2 says so). The held-out figure is the one to quote.

## What is proved

**One theorem for all networks** (`Lane4/R7K5.lean`, `sound : Lane4.Cert.Sound`; the statement is
the last definition of `Lane4/R7Cert.lean`): if the computable checker `check (1/1000) N T cert`
returns `true` for a one-block gated transformer `N`, a task `T` given as an automaton and a
certificate, then every network within the additive 1/1000 ball of `N`, in the rounding model of
rung 6a, is within 1/4 of the task target at every position of every input of every length the
model covers. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

**Per trained network**, a generated file `runs/r7-nets/B-u5-s<seed>/Net.lean` (no doctor, no proof
text written for that network; every closed Boolean by `decide +kernel`) proves four theorems,
each with exactly those three axioms:

- `accept`: the checker returns `true` on the skeleton `net` (the trained weights rounded to
  multiples of 1/1024) with the certificate found by `tools/r7_cert.py`.
- `skeleton_ok : Statement net`: the registered statement, whole additive 1/1000 ball.
- `trained_exact_all_lengths`: for the network exactly as trained (`trained`: the float32 weights
  as rationals; no rounding of weights, no perturbation), exact real arithmetic:

      theorem trained_exact_all_lengths (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ)
          (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
          |ANet.out trained (fun x => x) Real.exp Lane4.R7KT.zeroP w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4

- `trained_binary32`: the same bound in IEEE binary32 arithmetic (any round-to-nearest, a float
  exponential within the stated error), at most 65,535 tokens.

The task is statement B of the registration: carry with modulus 3 over 5 tokens (pool case c01),
`target` as registered. The architecture is the gated one of rung 6a: one block, width 8, two
heads (strict and causal mask, fixed slope 24, gate neuron on the keys), ReLU MLP with 12 hidden
units, no LayerNorm.

## Counts (from `results/rung7-kernel.json`, built from each `lean.log`)

| Set | Trained | Pass the frozen screen | Kernel-checked as trained | Rejected by the checker (kernel, `check = false`) |
|---|---|---|---|---|
| B u5, test seeds 100 to 119 | 20 | 6 | 5: 103 (dev), 118, 113, 106, 117 | 1: 108 |
| B u5, reserve seeds 120 to 139 | 20 | 9 | 4: 134, 129, 136, 126 | 5: 125, 133, 137, 131, 139 |
| A u3, test seeds 100 to 119 | 20 | 18 | 0 | 18 |

- **The bar** (Amendment 2, point 3a: at least 2 of the first 3 networks after the dev network,
  in the registered order 118, 113, 106): **3 of 3. Met.**
- **Reserve seeds are reported "after Amendment 3"**, not as "clean": the checker gained its
  magnitude guards after the test-seed prototype results were known (the guards changed no
  decision on any test-seed network and were added before any reserve network existed). The
  reserve rate, 4 of 9 screened networks, is about half the test-seed rate, 5 of 6. The gap
  constant 12 was chosen with the six test-seed networks in view (disclosed in Amendment 2), so
  the reserve figure is the one to quote for a fresh network.
- **Why networks are rejected.** All 6 rejected B networks: one head's content score varies too
  much across candidate keys for the fixed slope 24 to guarantee a score gap of 12 per position
  (spreads 10.7 to 15.9 against 10.78 allowed). A: 16 of 18 for the same reason (spreads 11 to
  27), 2 because plain intervals are too wide (output interval radius over 1/4). A rejected
  network is not proved wrong; the method does not cover it. No checker constant was changed to
  rescue any network.
- **Kernel against prototype:** the kernel's accept or reject equals the Python prototype's on all
  40 files (33 networks, 7 controls).
- **Compile cost per accepted network:** 17.7 to 32.8 s, peak commit 4.29 to 4.38 GB (the import
  alone is 3.9 GB).

## Negative controls (Amendment 2, point 4): 7 of 7 rejected in the kernel

On the dev network B u5 seed 103 unless said: radius 16/1000; radius 4/1000; task A's automaton;
embedding rows 1 and 2 swapped; read-out negated; B u5 seed 100 (a trained network that fails the
task); seed 103 with both candidate sets replaced by seed 118's second head. Each file
`runs/r7-nets/ctl-*/Net.lean` proves `check ... = false`, standard axioms.

## Numeric checks on the nine accepted networks (searches, not proofs)

`tools/r7_checks.py`, fixed before the run, one job under a 3 GB reservation (peak commit 0.25 GB);
`results/rung7-lane-checks.json`, `logs/r7-lane-checks.log`. Ranges over the nine networks:

| Check | Worst deviation from the target (tolerance 0.25) |
|---|---|
| Trained network, no perturbation, float64, lengths 6 to 65,534 | 0.031 to 0.037 |
| Trained network, no perturbation, float32 in the stated order, 1,000 / 16,000 / 65,534 tokens | 0.031 to 0.037 |
| Skeleton, 80 sampled perturbations inside the 1/1000 ball, float64 | 0.043 to 0.051 |
| Skeleton, 5 sign-corner perturbations at 1/1000, float32, to 65,534 tokens | 0.037 to 0.048 |
| First multiple of the radius at which a sampled perturbation breaks the bound | 16 (seven networks), 32 (two) |

Nothing here contradicts the theorems. For the five test-seed networks the prototype's worst proved
bound is 0.153 to 0.231 (`results/rung7-cert-prototype.json`), 3 to 6 times what sampling finds;
I did not record that figure for the four reserve networks.

## How the soundness theorem was obtained

Six kit cases, statements by the study team, each proved by its first Sonnet doctor
(`runs/r7-kit/<id>/attempts`): transfer lemma kT (1 submission), softmax at gap 12 k1 (3),
interval lemmas k2 (2), automaton lemma k4 (2), head lemma k3 (2), composition k5 (1). About
1.04 million doctor tokens. No retry doctor, no stronger-model step. Plus one team-written module
(`Lane4/R7Glue.lean`, reassembly of the checker's conjuncts, 50 lines).

## Amendments and disclosures that bear on reading the result

- Amendment 2: the by-hand stage 1 was skipped on a size estimate; the certificate checker became
  the route. The gap constant 12 was chosen after seeing the prototype on all six B networks.
- Note to Amendment 2: `decide +kernel` (the kernel evaluates the Boolean; no added axiom) in
  place of the plain `decide` tactic, which cannot evaluate rational comparisons.
- Amendment 3: magnitude guards added to the checker, found by the study team reading the evaluator
  against the kit before the remaining kit cases were cut; without them the soundness theorem was
  not provable as written. No decision on any network changed.
- K-a: the one-theorem form of the per-network check exceeded the 4 GB of the rule (6.1 GB); the
  split form the rule allows is what is used.
- Dead ends: a first reassembly by `rfl` was killed on memory (6.7 GB) and replaced by
  `R7Glue.lean`; an idle check service of the study team blocked its own compile in the scheduler queue
  once.

## Limits

- **The registered "exact-arithmetic evaluation" could not be run as worded.** Amendment 2, point
  4, lists an exact-arithmetic evaluation of the trained network on inputs to 65,534 tokens. An
  exact rational evaluation of these networks does not exist: the softmax uses the exponential,
  whose values are irrational. What was run instead is float64 (the stand-in the study team used in
  rung 6a under the same name) and float32, on sampled inputs and sampled positions. The wording
  in the amendment was mine and was loose; the check as run is weaker than the words.
- The numeric checks sample inputs (the four input patterns of rung 4) and at most 1,000 positions
  per long input; they are not exhaustive at any length.
- The reserve-seed count is "after Amendment 3", not "clean": see Counts.
- One architecture (gated, one block, width 8, slope 24, no LayerNorm), one task, one recipe.
- The checker is a sufficient condition. A rejected network is not shown to be wrong.

## What this is and is not

It is a method that turns a trained one-block gated transformer and a two-line certificate into a
kernel-checked, all-length, whole-ball, binary32 correctness theorem in under a minute, with no
proof work per network, and it worked on 9 trained networks.

It is not a result on the standard architecture: statement A (ungated attention, digit sum mod 5)
is 0 of 18 by this route. The networks are width 8 with no LayerNorm and a fixed slope of 24, the
task is one carry automaton, and the method accepts only networks whose heads pick the latest
candidate key by position; on fresh seeds that was 4 of 9 networks that solve the task.

## Robustness row (added 2026-11-20, 6:41 am EST; not part of the registered rung-7 read, not part of rung 8)

Asked for by the project owner after the rung-7 read: the rung-7 pipeline unchanged (frozen training
script and screen through the wrapper `tools/r7x.py`, frozen checker, same generator) on a second
carry automaton and at width 16. Seeds 200 to 209, never used before. Logs: `logs/r7x-sweep.log`,
`runs/r7-nets/Bc02-u5-s205`, `runs/r7-nets/Bw16-u5-s201`, `runs/r7-nets/Bw16-u5-s209`.

| Variant | Trained | Pass the screen | Kernel-checked as trained | Rejected by the checker (kernel) |
|---|---|---|---|---|
| Carry automaton c02 (modulus 3, other classes and digits), width 8 | 10 | 1 | 0 | 1 (seed 205: score spread 10.6, allowed 10.78 before radii) |
| Carry automaton c01 (the rung-7 task), width 16 | 10 | 2 | 1 (seed 201) | 1 (seed 209: bound 0.257 against 0.25) |

- **Width 16 works once:** seed 201 has all four theorems (accept, skeleton_ok,
  trained_exact_all_lengths, trained_binary32), standard axioms, 71.9 s, with no change to the
  checker or the soundness theorem. So the method is not tied to width 8.
- **The second automaton has no accepted network.** One network learned the task and the checker
  rejected it for the usual reason. This row gives no evidence that the method carries to another
  task; it also does not show that it fails, with one screened network.
- **The training recipe is the bottleneck here**, not the checker: 17 of 20 seeds did not learn
  the task at all (error above 0.9). The recipe was tuned on task c01 at width 8.
- "Second automaton" here means another instance of the same carry family, not another family.
  The pool's other one-block family ("last marked value") needs a short extra lemma to match its
  registered target to the automaton form, which I did not write.
- Memory: the width-16 Lean jobs peaked at 4.85 and 5.07 GB of commit under a 3 GB reservation. Width 16
  needs a 4 GB reservation.
