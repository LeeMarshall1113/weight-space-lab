# Weight-space lab

Personal work. Views are my own.

Private pre-release copy (not yet public). Maintainer: `LeeMarshall1113`.

This is a living, correctable lab notebook, not a finished publication. **Please try to
break it** (see `CONTRIBUTING.md`). Corrections are logged in `CHANGELOG.md` with credit,
and claims that do not survive are downgraded in the table below, not quietly edited.

A lab-style repository of experiments on **LLMs writing, reading and editing neural-network
weights**, with pre-registrations, negative results kept, and where possible machine-checked
proofs. Each result lives in its own folder with its own README, pre-registration and
instructions to check it. Only `proofs/` is included so far; the other folders are slots
that will be filled as results are cleared for release.

## Known weaknesses (read first)

These are the weak points we know of; each is repeated, with detail, in `proofs/README.md`
("Limits"). If you find another, that is exactly what we want to hear.

1. **The headline contrast is not like-for-like.** The fragility numbers use an absolute
   weight change (zeros included); the rung-4 ball is relative with zeros held fixed. The
   rung-2 networks have not been tested under the relative ball, so "exact proofs are
   fragile, ours are not" is not established; only that exact-tie constructions break under
   additive noise.
2. **The theorem is about a tailored model.** Hard attention with ties averaged (not
   softmax), hand-written weights, width at most 15, and a *rounding model* (not IEEE:
   no overflow, underflow, subnormals, fused multiply-add or reordered sums), valid only up
   to 65,535 tokens. We have not shown a Lean witness that the rounding hypothesis is
   satisfiable for a positive unit roundoff.
3. **Counting tasks are excluded** (parity, Dyck, sort), where a ball must shrink like 1/n.
4. **No practical advantage over a plain verified program:** the control arm solved every
   task with proofs about a tenth as long. The two arms prove different statements.
5. **Tasks were chosen knowing which mechanism works**, with a lemma kit and a worked
   example supplied; the result is about proof automation as much as about transformers.
6. **The statements are only as good as `Spec.lean`, `Final.lean` and `Lane4/RSeq.lean`**,
   which we wrote; the kernel checks proofs against them, not against intent.
7. **Novelty is a search over abstracts**, not a literature review; "not found" is weaker
   than "does not exist".
8. **Small samples:** 11 of 12, 12 of 12, 10 of 10; one model family; the one miss is an
   agent crash, counted as a failure.

## Index of results

Status words: **confirmed** (the pre-registered claim was met and, for `proofs/`, re-checked
from this folder), **negative** (the pre-registered test was not met or a kill criterion
triggered), **in progress**. "Not yet included" rows say what the lab's own notes report;
they have not been independently re-checked.

| Claim | Status | Where to look | How to check |
|---|---|---|---|
| 11 of 12 LLM-written hard-attention transformers kernel-checked correct at every input length for every relative weight change within 0.5%, under a rounding model up to 65,535 tokens (non-counting tasks only; a plain verified program does the same tasks with proofs about a tenth as long) | confirmed | `proofs/` (rung 4), `proofs/docs/RESULTS_R4.md` | `python tools/check.py runs/rung4-test/net/c14` inside `proofs/`; or `tools/recheck_all.py`. See `proofs/VERIFY.md` |
| 12 of 12 LLM-written ReLU networks proved within tolerance of an exact spec for every weight and bias within 1/1000 (absolute) | confirmed | `proofs/` (rung 3), `proofs/docs/RESULTS_R3.md` | same checker, `runs/rung3-test/` |
| 10 of 10 LLM-written hard-attention transformers proved correct at every input length, exact arithmetic, written weights only | confirmed | `proofs/` (rung 2), `proofs/docs/RESULTS_R2.md` | same checker, `runs/rung2-test/` |
| All ten rung-2 networks break when one weight moves by an absolute 1/1000 (8 of 10 at 1e-6); a proved sort network fails in float32 from length 300 | confirmed (measurement; the perturbation is absolute, see limits in `proofs/README.md`) | `proofs/results/r3-transformers.json`, `rung2-float-probe.json` | `proofs/tools/r3_transformers.py`, `float_probe.py` |
| Softmax attention and IEEE binary32 semantics (rung 5) | in progress, not included | | |
| Injecting a new skill into a pretrained network without gradients (lane 1) | mixed per lab notes: positive on small nets, not shown at the prose rung; not yet included | slot `injection/` | |
| Detecting planted behaviours from weights (lane 2) | negative per lab notes (kill criterion met for a zero-shot doctor); not yet included | slot `detection/` | |
| Reading and repairing small RNNs and transformers from weights (lane 3) | mixed per lab notes (works on compiler-built nets, not on trained ones); not yet included | slot `reading/` | |
| Self-improvement levers (data, recipe, weights) (lane 5) | in progress; not yet included | slot `self-improvement/` | |
| A typed-decision method: reproduction and gate (lane 6) | negative per lab notes (gate not met, shelved); not yet included | slot `typed-decisions/` | |
| The doctor harness: an agent loop that edits weights under a forward-pass budget | tool; not yet included | slot `harness/` | |

## Repository layout

```
proofs/            Lean proofs, checker, pools, pre-registrations, per-case results   (included)
injection/ detection/ reading/ self-improvement/ typed-decisions/ harness/             (empty slots)
LICENSE            Apache-2.0 (code, Lean files, scripts)
NOTICE, CITATION.cff
CONTRIBUTING.md, CHANGELOG.md, .github/ISSUE_TEMPLATE/   (how to report; corrections log)
```

## Licence

Code, Lean files and scripts: Apache-2.0 (`LICENSE`, `NOTICE`). Text and documents
(READMEs, `docs/`, any write-up): CC-BY-4.0. Third-party models and datasets
are not redistributed here; each folder will say what it needs and under what licence.

## Status of this copy

This repository is private while the write-up is being checked. A DOI will be assigned
when it is archived (placeholder in `CITATION.cff`).
