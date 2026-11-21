# the proofs study, rung 8 pre-registration: the rung-7 theorem for ungated softmax attention, at a ball of 2^-14

Status: REGISTERED 2026-11-20 (EST); the commit that adds this file is the registration.
Scope: `SCOPE_R8.md` (commits 48bc26c, ca37fb1), candidate (a) with (b) folded in. Go given by the
project owner on 2026-11-20 after the K1 read, with seven conditions; each is met in a section below
and named there. Pre-registration is not independently verifiable: the commits are private.
Changes after this point are dated amendments at the bottom, made before the step they affect.

## What had been seen when this was written (condition 1)

Nothing in this file is blind to the 18 A networks of rung 7. Said plainly:

- **The prototype checker (`tools/r8_proto.py`) was tuned in four passes on the 18 screened A u3
  networks of seeds 100 to 119.** They are a tuning set. The three designs that did not work:
  1. First version (window of keys, shared attention, affine forms), on the rung-7 skeleton
     (weights rounded to 1/1024) with the rung-7 ball of 1/1000: the network read by hand, A seed
     110, came out at 0.44 against the tolerance 0.25. Rejected.
  2. The same checker with skeleton and ball at 2^-14 and the rung-7 charges for score rounding and
     softmax arithmetic: 1 of 18 accepted.
  3. With two tighter charges for ungated heads (P1 and P2 below, neither proved): 17 of 18.
  4. With the reference key of an ungated head chosen by nominal score instead of "the newest":
     18 of 18. This is the frozen prototype (`scratch/freeze_r8_k1.sha256`).
- **The ball shrank from 1/1000 to 2^-14 to make A pass.** At the rung-7 ball the frozen prototype
  accepts 1 of the 18. By ball size, A accepted: 1 (2^-10), 9 (2^-11), 16 (2^-12), 18 (2^-13,
  2^-14, 2^-16). The value 2^-14 was picked after seeing that table. It is 16.4 times smaller than
  the rung-7 ball.
- B u5, 15 screened networks of seeds 100 to 139: 15 of 15 at either ball (rung-7 checker: 9).
- Controls and the numeric soundness test of the prototype: `SCOPE_R8.md`, "K1 read".
- The rung-8 screen below was run on the old networks after it was written, as a test of the
  tool (numbers in the Screen section). Its threshold and sampling plan are the frozen screen's;
  only the skeleton step and the radius changed, and they were not adjusted after that run.
- No seed above 139 has been trained for task A or task B with any recipe. Seeds 200 to 209 were
  used for the rung-7 robustness row (carry c02 at width 8, carry c01 at width 16) and are not
  used again.
- No Lean has been written or run for rung 8. The Lean checker does not exist yet.

## Statement

Architecture `Lane4/AGate.lean` as in rung 7, statement A: one block, state width 8, two heads
(masks strict and causal), one relative-position slope per head fixed at 24, a ReLU MLP with 12
hidden units, a scalar read-out, no LayerNorm, no position embedding. **The gate parameters are
the constants g = 0, gb = -1 and are not trained, so every earlier position is a candidate key
of plain softmax attention.** (Inside the ball the gate weights move by at most the radius like
every other weight; the gate stays closed-form "always a candidate".) Softmax in the stated
order; the rung-5 float model (`Rnd`, `ExpM` assumed).

Task A as registered in `PREREG_R7.md`: the sum mod 5 of the digits of the last two tokens (token
t is digit t - 1; BOS counts 0), at every position of an input of any length over tokens 1 to 5.

T is the network with the float32 weights exactly as the optimiser left them. **W14 is T with
every weight rounded to the nearest multiple of 2^-14** (computed from T alone). The ball is the
additive ball of radius 2^-14 around W14; T is in it by construction (distance at most 2^-15).

Theorems wanted per network, each with axioms `propext`, `Classical.choice`, `Quot.sound` only:

- `accept`: the Lean checker returns `true` on W14 at radius 2^-14.
- `skeleton_ok`: every network in the ball, in the rounding model, is within 1/4 of the target at
  every position of every input of every length the model covers (the rung-7 `Statement` with
  1/2^14 in place of 1/1000).
- `trained_exact_all_lengths`: T itself, exact real arithmetic, every length.
- `trained_binary32`: T itself in binary32 (any round-to-nearest, a float exponential within the
  stated error), up to 65,535 tokens.

And once for all networks: `Sound8`, the soundness of the checker, in the shape of rung 7's
`Sound` with the radius a parameter: for every `δ` the checker accepts with, every network within
the additive `δ`-ball satisfies the conclusion above. The statements needed are `δ = 1/2^14`
(A and B) and `δ = 1/1000` (B on its rung-7 skeleton).

**Headline sentence if passed (fixed now).** "N of M gradient-trained one-block softmax
transformers without a gate (fresh seeds) are kernel-checked correct, with the weights exactly as
trained, on modular addition of the last two tokens at every context length in exact arithmetic
and up to 65,535 tokens in binary32 arithmetic, with no proof work per network; each theorem
covers an additive weight ball of radius 2^-14, about 16 times smaller than the ball of rung 7.
No LayerNorm, no position embedding, and a relative-position slope fixed at 24; the task is
local, so the every-length part is robustness to an unboundedly long prefix, not long-range
computation." The ball size, the factor 16 and the limits are part of the sentence wherever it
is used; "standard" is not used without "fixed relative-position slope, no LayerNorm" beside it.

**Novelty wording (condition 4).** Not to be written: "first trained network proved at every
length". teal-sea/lean-checked-network has a kernel-checked all-length theorem for a trained
network (a threshold RNN adder in exact integers, finite certificate plus induction), and that
pattern is theirs as much as ours; it is cited wherever ours is described. What may be claimed,
as "we found no earlier one in the search of 2026-11-20", not as "there is none": an all-length
kernel-checked theorem for a trained network with **softmax attention, in floating-point
arithmetic, with a weight ball**, by a checker with one soundness theorem.

## Route

1. Lean checker `Lane4/R8Cert.lean`, written by the study team from the prototype's design, with a
   Python mirror `tools/r8_cert.py` in exact rationals. The frozen K1 prototype stays as the
   record of what K1 read.
2. Kernel feasibility test (K2 below) on tuning-set networks.
3. Kit cases, statements by the study team, one Sonnet doctor at a time; P1 and P2 first.
4. `Sound8` kernel-checked.
5. **Checker freeze**: sha256 of `Lane4/R8Cert.lean`, `tools/r8_cert.py`, the per-network
   generator and the certificate finder, recorded in the study's private log (not included). The frozen checker is run on the
   tuning set (20 A and 15 B networks) and that count is reported as a tuning-set count.
6. Only then are fresh seeds trained (below). Bar read, controls, numeric checks.

**Changes to the checker before step 5 are allowed and expected** (rung 7 needed its magnitude
guards; the kernel may need cheaper arithmetic, such as rounding the ReLU slope or the attention
weights outward to a dyadic grid; a charge may have to rise to what a doctor can prove). Each is
logged in the study's private log (not included) with the tuning-set count before and after. They can only use the tuning
set, because no fresh network exists until step 6. **Any change to the checker, the generator,
the certificate finder, the screen or the training script after the first fresh seed is trained
forfeits "clean"**: the fresh-seed counts are then reported as "after Amendment n", as in rung 7.

Standard axioms only. `native_decide` banned and counted. Closed Booleans by `decide +kernel`
(Note to Amendment 2 of `PREREG_R7.md`). No proof text written per network.

## Proof obligations known now

- **P1.** In a head where every token is a candidate, the keys that compete are within L + 1
  positions of the query, so their position biases are small and the rounding of a score
  difference is charged 2^-10 where rung 7 proved about 1.0 for keys at any distance.
- **P2.** In such a head the error of the rounded softmax arithmetic against the exact weighted
  average is charged B/2^16 where rung 7 proved B/100 (which also covered the leak to other keys;
  here the leak is modelled by explicit weights and a tail term).
- Also new: rational enclosures of exp; attention weights of two to four window keys from score
  intervals; the tail of older keys below e^-16; affine forms through stored-weight dot products
  with perturbation and rounding; the ReLU relaxation; abstract states that carry a window of the
  last L candidate tokens per head; the composition.

With the rung-7 charges in place of P1 and P2 the prototype accepted 1 of 18 at the small ball,
so the design dies if they fail. My reading of the model (`AHead.bias` uses the difference j - i;
`savg` sums oldest key first, so partial sums grow geometrically toward the query) is that both
hold with room; that reading is not a proof.

## Kill rules

- **K1 (read already, on the tuning set): passed, 18 of 18.** Re-read if a charge has to rise: if
  the checker with the provable charges accepts fewer than 6 of the 18 tuning-set A networks, the
  rung stops there and that is the result.
- **K2, kernel feasibility.** The per-network check of the Lean checker, by `decide +kernel`, in
  split form (one lemma per head and per abstract case or group of cases, at most four files
  compiled one after another), on A u3 seed 110 and on the tuning-set A network with the most
  table rows: at most 600 s in total per network and at most 4.5 GB peak commit per job (the
  limits of the guarded runner `tools/build_lean.py`, as in rung 7's K-a). The study team
  may redesign the checker's arithmetic for cost up to three times (each logged); if the third
  still fails, the rung stops: "the check is not kernel-feasible at this size".
- **K3, soundness (K-b style).** Each kit case: one Sonnet doctor, 30 submissions; on failure one
  fresh Sonnet doctor with the first one's notes; **one stronger-model step in total for the whole rung**,
  only with the project owner's clearance at the time. A case still unproved: if it is P1 or P2 or
  a charge, the charge may be raised to what was proved and K1 re-read; otherwise the rung stops
  and what is proved is reported.
- Usage (condition 7): no new doctor case at or above 60% of the usage budget, hard stop 75%; read and logged
  before each case.

## Training and fresh seeds (condition 2)

`tools/r7.py`, frozen since Amendment 3 of rung 7 and not edited: task A recipe u3, task B recipe
u5, **seeds 140 to 159**, 20 each, called through `tools/r8.py sweep`. The no-cheating line of
`PREREG_R7.md` is binding as written there. Nothing is trained before the checker freeze.
Networks are taken in ascending seed order (rung 7 ordered by non-zero skeleton weights; that
count changes with the grid, so the order here is the seed).

## Screen (condition 3)

The frozen rung-7 screen has three parts: s1, the trained network in float32 to 65,534 tokens;
s2, distance to the skeleton (automatic since Amendment 1); s3, the skeleton under sampled
perturbations at radius 1/1000, worst deviation at most 0.10. s3 tests the 1/1000 ball, which is
no longer the statement for A: on the tuning set two A networks (107, 112) fail s3 only, solve
the task, and are accepted by the prototype at 2^-14.

**Screen 8** (`tools/r8.py screen8`, frozen with this file): **s1 exactly as frozen** (read from
the frozen screen's own output), and **s3'**: the frozen s3 with W14 and radius 2^-14 in place of
the 1/1024 skeleton and 1/1000; same 20 uniform and 20 sign-corner perturbations, same lengths,
same threshold 0.10. Pass = s1 and s3'. The frozen rung-7 screen is still run on every fresh
network and recorded.

- A: screen 8 selects the networks the bar is read on.
- B at ball 2^-14: screen 8. B at ball 1/1000: the frozen rung-7 screen, unchanged.

Screen 8 on the old networks (one reserved run, `logs/r8-screen8-old-A.log`, `-B.log`; peak commit
0.24 GB): A u3 seeds 100 to 119, 20 of 20 pass (the frozen screen passes 18; worst deviation
inside the 2^-14 ball 0.031 to 0.046 against 0.10); B u5 seeds 100 to 139, 15 of 40 pass, the
same 15 as the frozen screen, and the other 25 fail s1. So the tuning set for the rest of this
rung is 20 A networks and 15 B networks.

## Bar and counts (condition 2)

- **Bar.** Of the first three A u3 networks, in ascending seed order from 140, that pass screen 8:
  **at least 2 have all four theorems kernel-checked**. Met: rung 8 passes. One of three: a
  showcase theorem, not the rung's result. If fewer than three of the 20 pass screen 8, seeds 160
  to 179 are trained and this is said.
- **Count on 20 fresh seeds (A).** Trained; pass s1; pass screen 8; accepted in the kernel;
  rejected in the kernel (`check = false`), with the reason from the mirror for each.
- **B on fresh seeds, new checker, both balls.** Seeds 140 to 159, recipe u5: (i) W14 at radius
  2^-14, among networks passing screen 8; (ii) the rung-7 skeleton (1/1024) at radius 1/1000,
  among networks passing the frozen rung-7 screen. Beside (ii), the rung-7 checker on the same
  networks, for comparison. These are counts, with no bar.
- A rejected network is reported as rejected. **The checker is not adjusted to rescue any
  network.** A rejection is "not covered", not "wrong".
- The kernel's decision must equal the mirror's on every file; a disagreement is reported and
  the kernel's decision stands.
- The tuning-set count with the frozen checker is reported beside the fresh count and labelled.

## Controls (condition 5; fixed now, each must be rejected)

In the kernel (`check = false` by `decide +kernel`), on the dev network A u3 seed 110, W14,
radius 2^-14 unless said:
1. task B's automaton in place of task A's;
2. embedding rows 1 and 2 swapped;
3. read-out weights negated;
4. read-out bias raised by 1/2;
5. radius 16 times larger (1/1024);
6. radius 64 times larger (1/256);
7. **every fresh network of seeds 140 to 159, A or B, that fails s1** (does not compute the task
   in float32): W14 at 2^-14, and for B also its rung-7 skeleton at 1/1000;
8. the first five, by seed, of the 25 task-failing B u5 networks of seeds 100 to 139, both balls;
   the other twenty in the mirror only.

Controls 5 and 6 are rejections the theorem does not need (a larger ball could be true); they
test that the radius enters the check. If the tuning set is a guide no fresh A network will fail
s1 (0 of 20 did), so control 7 will mostly be B networks; that is said in the report.
An accepted control voids the result until explained.

## Numeric checks on every accepted network (searches, not proofs)

T unperturbed in float64 and in float32 to 65,534 tokens; W14 under sampled perturbations inside
the 2^-14 ball; the multiple of the radius at which sampling breaks the bound; and the numeric
test of the checker's intervals against forward passes (as in `tools/r8_k1.py`): any violation
is reported at the top of the result.

## What would make the result weak, written down now

- The ball: 2^-14, chosen on the tuning set, 16 times smaller than rung 7's. The headline for T
  as trained does not depend on it; the robustness claim does.
- The checker's design and four constants (window tail e^-16, window at most 3, the P1 and P2
  charges) were fitted to 18 networks of the same recipe. Only the fresh seeds measure anything.
- Task A is local (last two tokens). Every length means an arbitrarily long prefix is ignored.
- Fixed slope 24, far above common practice and set by the study team; no LayerNorm; no position
  embedding; width 8; one block; one task; one recipe; the study team's own task.
- exp accuracy assumed; stated operation order; the study team's own forward pass.
- The checker is a sufficient condition and cannot be complete (Yang et al. 2026).
- teal-sea had the certificate-plus-induction pattern for a trained network first.

## Odds, as judgement (not a measurement)

Soundness inside K3: 50%. Kernel feasibility inside K2: 70%. Bar on fresh seeds given both: 85%.
Overall about 30%.

## Reservations (condition 6)

Every Lean, training, screening and prototype run under a scheduler reservation, however short; one Lean
job at a time; 4 GB reservations for per-network files and wide files, 3 GB for small ones.

## Frozen files

sha256 list in `scratch/freeze_r8.sha256`: this file, `tools/r8.py`, `tools/r8_lease.sh`,
`tools/r7.py`, `tools/r6net.py`, `tools/r4_checks.py`, `tools/r5_checks.py`, `tools/r4pool.py`,
`pool/rung4_pool.json`, `Lane4/AGate.lean`, `tools/r8_proto.py`, `tools/r8_k1.py`. Its own
sha256 is in the study's private log (not included) entry for the registration. (The list holds this file's hash, so the
list is written after this file and is not itself named inside a hash.)

## Amendment 1 (2026-11-20 1:02 PM EST): the limits of K2 are raised, after seeing the result

Written before any doctor has been started and before any fresh seed exists. Decided by the
project owner (message of about 1:05 pm by its clock) on the study team's question. The text above the
line "## Amendment 1" is unchanged; its hash in `scratch/freeze_r8.sha256` no longer matches the
whole file, and the new hash is in the study's private log (not included).

**What was measured under K2 as registered** (4 GB reservations, one Lean job at a time; the kernel's
decision equalled the mirror's every time; private log entry of 12:30 to 12:59 pm):

| Network | Form | Time | Peak commit | Against 600 s / 4.5 GB |
|---|---|---|---|---|
| A u3 seed 110 (dev; 6 states, 30 cases) | one lemma per state, one file | 26.0 s | 4.35 GB | met |
| A u3 seed 116 (largest; 156 states, 780 cases) | one lemma per state, one file | 585.7 s | 4.83 GB | time met, memory NOT met |
| A u3 seed 116 | one lemma per case, one file | stopped at 600.8 s | 5.41 GB | neither met |
| A u3 seed 116 | four files (not run) | about 620 s by estimate | under 4.5 GB by estimate | time not met |

So K2 as registered was **not met** for the largest tuning-set network, although the kernel did
accept it. The two alternative forms are recorded as failed (the per-case form measured, the
four-file form by estimate: about 12 s of import per extra file on top of 586 s).

**The change.** K2 now reads: the per-network check, one file, one lemma per head and one per
abstract state, **at most 900 s and at most 6 GB peak commit, under a 5 GB reservation**
(`tools/lean_lease5.sh`, runner `tools/build_net.py`). The 600 s and 4.5 GB were the defaults
of the rung-7 runner, not a bound that any claim rests on. **This is a limit raised after seeing
the result** (586 s, 4.83 GB on A u3 seed 116) and is to be reported as such wherever K2 is
mentioned. The cost redesign allowed by the registered K2 is not used.

**The far side, fixed now.** A fresh-seed network whose check exceeds the amended limits is
reported as "not checked within limits", counts as NOT accepted for the bar and in every count,
and the limits are not raised a second time. The same holds for B networks at either ball
(the largest tuning-set B network has 1,120 cases, so some may fall outside).

**Conditions from the project owner.** One Lean job at a time; before each 5 GB job the scheduler's
free-to-reservation and the commit charge (at most 75%) are checked.

**Also recorded here, because they change the checker text against the K1 prototype** (all
before the checker freeze, all on the tuning set; details in the study's private log (not included)):
- Design pass 1 of the mirror: the attention weights are the only symbols; the ReLU slope is
  rounded down to a multiple of 2^-20; P1 charge 2^-8 (prototype 2^-10); softmax-arithmetic
  charge B/2^13 for every head (prototype B/2^16 ungated, B/100 gated). Tuning set with that
  design: A 20 of 20, B 15 of 15 at 2^-14, B 15 of 15 at 1/1000.
- Two guards the prototype lacked: the reference-key guard (score radius of the newest key +
  that of the reference key + slack + radius times the rank of the reference key, at most 1),
  and the certificate's window length between 1 and 3.
- K2 on seed 116 was measured on the checker text before the last term of that guard was
  added; it is re-measured on the final text under the amended limits and the study's private log (not included) has the
  figure.
