# proofs/: kernel-checked transformers: proofs, checker and data

Status: private pre-release copy, flagship folder of the weight-space lab repository. Not yet published. Nothing here has been peer reviewed. All commands below run inside this folder (`proofs/`).

This repository holds the Lean 4 proofs, the checker, the specification pools, the
pre-registrations and the per-case results behind a study of LLM-written networks with
Lean-kernel-checked correctness proofs ("rungs" 2, 3 and 4 below; rung 1 is background).
Every claim below is copied from the results files in `docs/` (`RESULTS*.md`), which state
the same limits.

## Claims (exact wording)

**Rung 4 (main result).** 11 of 12 written transformers kernel-checked correct at every
length for every weight setting within 0.5% (relative), and under a modelled rounded
forward pass up to 65,535 positions; non-counting tasks only. Written and proved by LLM
agents (Sonnet family), one fresh agent per case. Plain-code control: 12 of 12, with
proofs about a tenth the length (median 54 against 559 lines).

The theorem for each network (`Spec.lean` `Statement`, `Final.lean` `final`): for every
rounding function `fl` with `Rounding u fl`, `0 ≤ u ≤ 2^-24`, every relative perturbation
of every weight by at most 1/200, every input whose length satisfies
`u·(length+1) ≤ 1/256`, and every position: `|output − target| ≤ 1/4`. With `u = 0` this is
exact arithmetic at **every input length**; with `u = 2^-24` it covers up to 65,535 input
tokens.

**Rung 3.** 12 of 12 ReLU networks (Sonnet) proved to stay within a stated tolerance of an
exact specification for every weight and bias within 1/1000 (absolute, zeros included) on
the whole input box. Control 12 of 12.

**Rung 2.** 10 of 10 hard-attention transformers (3 parity, 3 Dyck, 2 sort, 2 addition)
proved correct at every input length in exact arithmetic about the written weights only.
Control 10 of 10.

**Fragility measurement (from rung 3, "Part B").** For all 10 rung-2 transformers, moving a
single weight by an absolute 1/1000 makes the network wrong at some length of at most 20;
8 of 10 still break at 1e-6 (the two addition networks at 1e-4, not 1e-5). The proved
sort network `s00` gives wrong outputs in float32 from length 300 and is correct in float64.

## Limits (read before citing)

1. **Non-counting tasks only** at rung 4. Parity, Dyck and sort are excluded: they need a
   ball that shrinks like 1/n (analysis, not proved), and no agent was run on them.
2. **The ball is relative; zeros stay exactly zero.** Weaker than rung 3's absolute ball;
   it does not cover additive noise or pruning. The rung-2 fragility test perturbs
   absolutely (zeros included), so the fragility numbers and the rung-4 ball are **not
   like-for-like**.
3. **The rounding statement is about a model, not IEEE arithmetic.** Not modelled:
   overflow, underflow, subnormals, fused multiply-add, reordered or vectorised sums,
   softmax. A real float32 run is linked to the theorem only by numeric checks that found
   no failure. The rounded statement is length-bounded (65,535 tokens).
4. Hard attention with ties averaged, not softmax. Hand-written weights, not trained.
   Width at most 15. One model family, one radius, one tolerance, 12 cases.
5. **The transformers add nothing practical over a verified program**: the plain-code
   control solved every case with much shorter proofs. The two arms prove different
   statements.
6. **Tasks were chosen knowing which mechanism works**; the tasks were easy for the model
   with the supplied lemma kit and worked example (11 of 12 at a median of 2 submissions).
7. **The one rung-4 miss (`i03`) is an agent crash** (API output-limit error, no
   submission), counted as a fail. A rerun died the same way and is not counted.
8. **Novelty rests on a web search over abstracts** (`docs/NOVELTY.md`); "not found" is
   weaker than "does not exist". Related work is not summarised in this README.
9. The theorems are only as good as the files `Spec.lean`, `Final.lean` and
   `Lane4/RSeq.lean`, which the authors wrote; the kernel does not check them against
   intent.

## Layout

```
lean-toolchain, lakefile.toml, lake-manifest.json   Lean 4 + Mathlib pin
Lane4/                 frameworks: Basic, Seq (rung 2), Robust (rung 3), RSeq (rung 4); Export*.lean.txt templates
tools/check.py         the checker (one command checks one case)
tools/recheck_all.py   re-check every case folder under runs/
tools/*                case builders, pools, draws, export and numeric-check scripts, result collectors
pool/                  specification pools and the seeded draws
examples/, prompts/    worked examples and the agent prompt files
runs/rungN-test|dev/{net,prog,twin}/<id>/
                       case.json, Spec.lean, Final.lean, Solution.lean, TASK.md,
                       attempts/NN.json + NN.lean (every submission with the checker's verdict),
                       net.json (exported network), r3_checks.json / r4_checks.json
results/               per-case result JSONs (the sources of the paper's tables)
docs/                  PREREG*.md (pre-registrations, with dated amendments), RESULTS*.md, NOVELTY.md
smoke/                 negative controls (wrong weight, sorry, native_decide, banned token) for the checker
VERIFY.md              what was re-run from this folder, with times
```

`runs/rung4-test/net/i03` has no `Solution.lean` (no submission); `runs/rung4-test/net-rerun/i03`
is the untouched rerun (also no submission). Rung 1 is included only as
`runs/rung1-test/{net,prog}`; its trained-twin arm is summarised in `results/twins-test.json`
but its model files are not included. Rung 0 and rung 5 are not part of this release.

## Setup

Tested versions: Lean `leanprover/lean4:v4.35.0-rc3` (file `lean-toolchain`), Mathlib
`v4.35.0-rc3` = commit `c55e6e786f49471c72fbddbec5415808896aec1e` (see `lake-manifest.json`
for all dependency commits). Python 3.10 or newer; numpy only for the numeric scripts.
The checker's memory guard (a kill if one Lean process passes 4.5 GB) works on Windows
only; on other systems the guard is inactive. In the recorded re-check (`VERIFY.md`) one Lean process peaked at 2.8 GB working set
at most; plan for 4 to 8 GB free.

```bash
elan toolchain install leanprover/lean4:v4.35.0-rc3
lake update            # fetches Mathlib at the pinned revision
lake exe cache get     # downloads Mathlib's prebuilt .olean files (large); or `lake build Mathlib`
```

The checker does not call `lake`. It needs a folder `P` containing
`.lake/packages/*/.lake/build/lib/lean` (the result of the two commands above, with `P` the
repository root), and the `lean` executable:

```bash
export LANE4_LEAN=$(elan which lean)        # path of the toolchain's lean
export LANE4_MATHLIB_PROJECT=$PWD           # default; set it if Mathlib lives elsewhere
```

## Reproduction

Check one proof (builds `build/Lane4/*.olean` the first time, a few minutes):

```bash
python tools/check.py runs/rung4-test/net/c14
```

A pass prints `PASS  c14  kernel-checked` and the axioms of the final theorems, which must
be a subset of `propext`, `Classical.choice`, `Quot.sound`. Any `sorry`, error, time-out
(600 s), memory kill, banned token (`native_decide`, `axiom`, `sorry`, macros, ...) or other
axiom prints FAIL with the reason. Read `runs/rung4-test/net/c14/Spec.lean` and
`Final.lean` for the statement and `Lane4/RSeq.lean` for the definitions it rests on (the
trusted base is those files plus the Lean kernel).

Re-check everything (every case folder with a `Solution.lean`; see `VERIFY.md` for time):

```bash
python tools/recheck_all.py --out results/recheck.json
```

Negative controls (these should FAIL or PASS as their folder names say):

```bash
for d in smoke/s*/; do python tools/check.py $d | head -1; done
```

Numeric checks (numpy, no Lean needed except for export, which re-runs the framework on the
passing solution): `tools/export_r4.py` then `tools/r4_checks.py` for rung 4; `tools/export_nets.py`
and `tools/r3_transformers.py`, `tools/float_probe.py` for the fragility tables;
`tools/collect*.py` assemble `results/*.json`. These scripts read `runs/` and write next to
it; run them on a copy. Their memory needs are not measured.

## What was changed for release

- Local absolute paths and the machine's user name were replaced by `<repo>` and `<home>`
  in `attempts/*.json` (the checker's recorded `lean_output`), `TASK.md` and the text
  results. Only text in the recorded Lean output changed, not any `pass` verdict.
- `tools/check.py` was edited: the two hard-coded machine paths became the environment
  variables above, a non-Windows kill path was added, and the unreleased rung-5 modules
  were removed from its module table.
- Scheduling, memory-reservation and run-log references in `docs/` were generalised
  ("compute scheduler", "memory reservation", "run log (not released)"). The scientific
  content of the pre-registrations and results files is unchanged. The unfinished rung-5
  section of the novelty note was dropped.
- Not included: agent transcripts, internal run logs, per-case scratch folders, generated
  `_Full.lean` / `_Export.lean` files, copies of framework files inside case folders (the
  checker uses `Lane4/`; the copies were byte-identical to it), service and scheduling
  scripts, trained-model files of the twin arms.
- Git history: this repository starts fresh. The pre-registration commit ids quoted in
  `docs/PREREG_R4.md` (5fdefc9, f905339), `RESULTS_R2.md` (6fdeeca) and rung 1 (6cd7ebd)
  refer to the authors' private development repository, where they are timestamped before
  the runs they precede; they cannot be checked from this copy. The frozen-file hashes in
  `docs/freeze_r4.sha256` can.

## Licence and citation

Code, Lean files and scripts: Apache-2.0 (`../LICENSE`). Proposed, for the owner to confirm: text and documents (this README, `docs/`) under CC-BY-4.0. Citation: see `../CITATION.cff` (owner handle `LeeMarshall1113`; display name, repository name and DOI are placeholders).
