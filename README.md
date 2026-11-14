# Weight-space lab

Private pre-release copy (not published). Owner handle: `LeeMarshall1113`. Display name:
[placeholder, to be filled in by the owner].

A lab-style repository of experiments on **LLMs writing, reading and editing neural-network
weights**, with pre-registrations, negative results kept, and where possible machine-checked
proofs. Each result lives in its own folder with its own README, pre-registration and
instructions to check it. Only `proofs/` is included so far; the other folders are slots
that will be filled as results are cleared for release.

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
```

## Licence

Code, Lean files and scripts: Apache-2.0 (`LICENSE`, `NOTICE`). **Proposed, for the owner to
confirm:** the text and documents (READMEs, `docs/`, any paper) under CC-BY-4.0. Until the
owner confirms, treat documents as all rights reserved. Third-party models and datasets
are not redistributed here; each folder will say what it needs and under what licence.

## Status of this copy

Nothing has been pushed anywhere; there is no remote. A DOI will be assigned when the
repository is archived (placeholder in `CITATION.cff`).
