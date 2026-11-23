# Rung 9-LN-M result: bar met (3 of 3); 19 of 20 fresh networks proved on a task the checker never saw

Written 2026-11-22 (Sunday, 8:00 pm EST). Registered in `PREREG_R9M.md`, a commit at
1:50 pm EST, before any network of this task was trained. (That file's first line says "about
3:25 pm": a guessed time, wrong; the file is in the freeze list and was not edited, and the copy in this
repository carries a note on that line. The commit time is the true one.)

## What was tested

The rung 9-LN15 model, checker, soundness theorem, ten proof modules, mirror, generator, runner,
training recipe and screen, **all frozen and unchanged**, on a new task: **the output is the
larger of the digits of the current and the previous token** (five tokens as digits 0 to 4).
Ball 2^-15 around the weights rounded to 2^-14. No tuning set, no doctor tokens, no proof change.
The freeze list (37 files) verified after all kernel work.

Rung 9-LN15 was post hoc: its radius and design were chosen on its own task's tuning networks.
Nothing here was chosen after seeing a network of this task.

## Counts, seeds 800 to 819

| | count |
|---|---|
| trained | 20 |
| pass the screen | **20** |
| **bar: first three screened (800, 801, 802) with all five theorems** | **3 of 3** (needed 2) |
| kernel-accepted, all five theorems | **19** |
| kernel-rejected at a case | 1 (805) |

Each accepted network has `accept`, `skeleton_ok`, `binary32`, `trained_exact_all_lengths` and
`trained_binary32`, with the axioms `propext`, `Classical.choice`, `Quot.sound`, no
`native_decide`, no `sorry`. The kernel's decision equals the mirror's on all 27 objects (20
networks, 7 controls). Kernel cost: 155-case networks 319 to 413 s in two files, at most 4.85 GB;
one 30-case network 82 s; the two 780-case networks (803, 816) four files each, the largest file
696 s and 5.06 GB. The four-file rule held.

Network 805 passes the screen and computes the task; the checker's bound is too wide at one case
(output 0.06 ± 0.19 where 0.25 is allowed in total with the centre's error). A failure of the
enclosure, not of the network.

## Controls (each must be kernel-rejected): 7 of 7

On network 800: task A's automaton in place of this task's; embedding rows 1 and 2 swapped;
read-out negated; read-out bias + 1/2; LN2 gains negated; radius 16 times; radius 64 times. All
seven kernel-rejected (11 to 16 s each).

## Sampled checks on the 19 accepted networks (searches, not proofs)

Trained network, inputs up to 65,534 tokens: worst deviation 0.045 in float32 and in float64.
Sampled perturbations inside the ball: worst 0.051. They first break the 1/4 bound at 8 times the
radius (one network, 807), 32 times (4), 64 times (8), 128 times (5), 256 times (1). Numeric
interval test against the mirror's table: 0 violations in 82,189 positions, smallest slack 0.0009.

## What was seen beforehand, and what was not frozen

- Rung 9-LN15 itself, and the scope probe on a sibling task ("equals the previous token"):
  9 of 10 accepted by the mirror. That probe is why I expected this to pass; it used no network
  of this task.
- A plumbing dry run on one probe network, kernel-checked before the first network of this task.
- The wrapper `tools/r9m.py` that passes the task into the frozen tools was written for this rung
  and frozen with the registration. No fix to it was needed.
- One process slip: a run-control script in the freeze list was edited to widen a
  process-matching pattern, the freeze check failed, and the edit was reverted within the minute; no job
  of this rung ran with the edited file.

## What weakens the result

- **The target is stated in Lean as the task automaton run on the prefix, not as a closed
  form**, so that `task.target = target` holds by `rfl` and no proof text was added. A reader
  checks one fold: the state after i − 1 tokens is the digit of token i − 1 (0 at the start), and
  the output is the larger of it and the current digit.
- The task is local, like task A: the frozen checker's windows hold at most four keys. This
  confirms the LayerNorm result on a second local task; it says nothing about long-range tasks
  (that is rung 10).
- The ball is still only the distance to the rounding grid: no robustness margin beyond rounding.
- Five tokens, one block, width 8, the study team's own recipe; the exponential and the square root are
  assumed in the binary32 statement.
- 19 of 20, not 20 of 20.

## What it changes

The LayerNorm result no longer rests on a post-hoc rung alone. Honest wording for a write-up:
"The checker and theorem were developed on one task, where 13 of 19 fresh networks were proved
after a registered attempt at a larger radius had failed. They were then frozen and run on a
second task with everything registered beforehand: 19 of 20 fresh networks proved, bar met 3 of 3."
It is toy scale, with local tasks.

## Files

`PREREG_R9M.md`, `scratch/freeze_r9m.sha256`; `tools/r9m.py`; `runs/r9m-fresh/` (networks and
screens); `runs/r9m-ctl/`; `runs/r9ln15-nets/m800` to `m819` and `mc_*` (Lean files, logs,
`kernel.json`); `logs/r9m-*.log`; numericchecks in `results/rung9ln15-lanechecks.json` under seeds
800 to 819.
