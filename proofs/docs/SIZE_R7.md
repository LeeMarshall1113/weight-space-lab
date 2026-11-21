# Rung 7: proof size estimate for the stage 1 networks (2026-11-19, before any stage 1 doctor)

Asked by the project owner: can a by-hand proof of the stage 1 network fit the doctor's reach and the 600 s check limit?
Scripts: `scratch/r7_mech.py`, `scratch/r7_size.py` (numpy float64 on the skeleton W; estimates, not proofs).
Networks: B = `runs/r7-stage0/B/u5/s103`, A = `runs/r7-stage0/A/u3/s110`. Both are test-seed networks chosen by the
registered rule; nothing here feeds back into training or selection.

## What the trained networks do

| | B (u5 seed 103) | A (u3 seed 110) |
|---|---|---|
| head 0 (strict) | nearest earlier token that is not token 3; BOS is a candidate | previous token |
| head 1 (causal) | the query token itself (every non-BOS token is a candidate) | the query token itself |
| gate margin against the 1/1000 ball | 46x and 61x the first-order slack | constant gate, 255x |
| content score spread vs slope 24 per position | at most 4.8 | at most 0.35 |
| output is a function of | (query token, token picked by head 0): 25 cases | same: 30 cases |
| worst error of that 25/30-row table | 0.033 | 0.034 |
| table vs real network (hard selection idealised) | differs by under 1e-8 | under 1e-9 |
| hidden units in use | 11 of 12 | 12 of 12 |

So the trained network is a finite table plus an attention leak of about e^-18. The mathematics is the rung-6a argument.
What is new is the arithmetic: dense width-8 vectors through 11 or 12 hidden units, for every row of the table.

## Size against rung 6a

| | largest 6a proof (i18) | B | A |
|---|---|---|---|
| table rows | under 10 | 25 | 30 |
| dot-product bounds a proof must establish | about 60 | 590 | 726 |
| closing arithmetic calls (`norm_num`, `linarith`, ...) | 240 | at least 1,200 (centre and radius per bound) | at least 1,450 |
| proof lines | 2,080 (613k doctor tokens) | about 6,000 to 10,000 at the 6a rate | more |
| Lean check time | 56 s (6a range 14 to 165 s) | 300 to 700 s at 0.25 to 0.6 s per call, with heavier rationals (denominators 1024) | more |

Plain interval propagation (each weight ±1/1000, no use of ReLU signs) gives a worst error bound of 0.098 for B, well
inside the statement's 1/4. For A the same crude method gives 0.38 on its worst row, so A needs a tighter argument
(ReLU signs or cancellation), which is more text per row.

## Read

- A by-hand proof in the rung-6a style does not fit: about three to five times the most text any Sonnet doctor has
  produced in one case, and at or over the 600 s limit for a single file. I put a by-hand pass for B under 10%.
- The bound itself is easy for B (0.098 against 0.25). The obstacle is volume, not mathematics. That is the case the
  certificate checker is for: a computable interval evaluator over rationals (or integers scaled by 1024), one
  soundness theorem for the one-block gated architecture proved once, and then each network is a table of 25 rows
  checked by kernel evaluation (`decide`, never `native_decide`). 590 dot products of 8 terms is small for the kernel.
- B is the better first target for the checker (crude intervals already close). A needs sign-aware intervals.
- Open risk for the checker: whether `decide` evaluates rational or scaled-integer arithmetic of this size in the
  kernel inside the time limit. The first Lean job after the gate (`scratch/R7KTSpec.lean`) tests exactly that on
  the closeness predicate.
