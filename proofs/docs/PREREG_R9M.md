# Rung 9-LN-M: registration (prospective LayerNorm rung on a new task)

> **Note on this copy.** The registered original (a commit in the private study repository, 1:50 pm EST on
> 2026-11-22, before any network of this task was trained) gave "about 3:25 pm EST" as the time written; that time was a
> guess and is wrong, and the original was not edited because it is in the freeze list. This copy differs from the
> original only by removing internal run-management text (a decision id, a probability estimate, a level label,
> memory-reservation script names). The hashes in `freeze_r9m.sha256` are of the originals, so they do not match
> this copy; no number, rule or date in the registration changed.

Written 2026-11-22 (Sunday). Registered on the project owner's decision to run the prospective rung
on the reserved task M alongside rung 10. **Committed before any network of task M is trained or
seen.** If any change to the checker, the theorem or a proof turns out to be
needed, the rung stops and is reported: that would end "frozen".

## Why

Rung 9-LN15's radius and checker design were chosen on its own task's tuning networks after a
registered attempt failed. This rung runs the same frozen objects on a task they were never fitted
to, with everything fixed first, so that its counts carry no post-hoc caveat.

## What has been seen beforehand (all of it)

- Rung 9-LN15 itself (task A): 18 tuning networks, 20 fresh networks, 7 controls.
- The scope probe on a sibling task E ("current token equals the previous one", seeds 700 to 709,
  `SCOPE_CLEAN.md`): 10 of 10 pass the screen, 9 of 10 accepted by the frozen mirror. **Mirror
  only, no kernel.**
- One plumbing dry run: Lean files generated for probe network E-703 through the wrapper below
  (text inspected; to be kernel-checked as a dry run before the first M network, see "Order").
- **Of task M: nothing.** No network trained, no target evaluated on a network.

## Task M

Five tokens are the digits 0 to 4 (token t is digit t − 1). **The output at position i is the
larger of the digits of tokens i and i − 1**; before position 1 the digit counts 0. It is local
(the frozen checker's windows hold at most four keys) and it is not a modular sum.

In Lean the task is the automaton `{ init := 0, step := fun _ t => t - 1, out := fun s t =>
max s (t - 1) }` and `target w i` is written as that automaton run on the first i − 1 tokens, so
`task.target w i = target w i` holds by `rfl` (as rung 7's task B). A reader checks the target by
reading one fold, not a closed form; I chose this so that no proof text is added.

## Frozen

Everything in `scratch/freeze_r9ln15_s3.sha256` (model, checker, definitions, the ten proof
modules, glue, mirror, generator, runner, recipe and screen), unchanged, and in
`scratch/freeze_r9m.sha256` additionally: this file, `tools/r9m.py` (the wrapper that passes the
task into the frozen tools at run time without editing them), a run-control script,
`tools/ln15_checks.py`, and the frozen helpers the wrapper reaches into (`make_r7_net.py`,
`make_r8_net.py`, `make_r7_cases.py`, `r7_cert.py`, `r7.py`). Recipe `n1`. **Ball 2^-15 around
the weights rounded to 2^-14.** The theorem is `Lane4.LNC.SoundLN`, which takes the task as an
argument.

A bug in the wrapper or the reservation script that does not touch any of the frozen rung 9-LN15 files
may be fixed; each fix is logged in the study's private log (not included) and named in the result.

## Seeds, bar, kill rules

**Seeds 800 to 819**, trained and screened in ascending order; all twenty are run, not only the
first three.

- **Kill (training):** fewer than 10 of 20 pass the screen.
- **Bar:** of the first three that pass the screen, **at least two** are kernel-accepted with all
  five theorems (`accept`, `skeleton_ok`, `binary32`, `trained_exact_all_lengths`,
  `trained_binary32`), standard axioms only, no `native_decide`, no `sorry`.
- **Kernel rule, as before:** at most four files per network, each within 900 s and 6 GB. A
  network over the rule counts as not accepted. Not softened if it bites.
- A disagreement between the kernel and the mirror on any network is reported and that network
  counts as not accepted.
- **Headline count:** kernel-accepted among screened, of the twenty.

## Controls (each must be kernel-rejected), on the first kernel-accepted fresh network

Task A's automaton in place of M's; embedding rows 1 and 2 swapped; read-out negated; read-out
bias + 1/2; LN2 gains negated; radius 16 times; radius 64 times. A control rejected by the mirror
before any certificate exists has no kernel file and is reported as such.

## Numericchecks (searches, not proofs) on the accepted networks

`tools/ln15_checks.py` with the task passed in: float32 and float64 to 65,534 tokens, sampled
perturbations inside the ball, the multiple of the radius at which they break, the interval test.

## Order

1. This file and the freeze list are committed.
2. Train and screen seeds 800 to 819 (Python).
3. Generate the per-network files (mirror decisions are known at this point and are reported as
   mirror decisions).
4. Lean, one job at a time, about 5 GB: first the
   dry-run file of probe network E-703 (a plumbing check on a network already seen; if it fails
   for a reason in the wrapper's text, that is fixed and logged before any M file is checked),
   then the M networks in ascending order, then the controls.

## What it would and would not show

If the bar is met: the LayerNorm result holds prospectively on a second task, with counts that
were not tuned. It stays a toy-scale result: five tokens, one block, local task, the study team's own recipe,
exponential and square root assumed in the binary32 statement, and a ball that is only the
distance to the rounding grid. If the bar fails, rung 9-LN15 stays as it is, post hoc, and the
write-up says that a prospective attempt on a second task failed.
