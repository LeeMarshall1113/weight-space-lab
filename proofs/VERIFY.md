# VERIFY: what was re-run from this folder

Date: 2026-11-13. Machine: a shared Windows 11 desktop (31 GB RAM), checks run one Lean
process at a time under a 5 GB memory reservation. Lean `leanprover/lean4:v4.35.0-rc3`;
Mathlib `v4.35.0-rc3`, commit `c55e6e786f49471c72fbddbec5415808896aec1e`.

## What "from this folder" means, and one caveat

Everything compiled and checked here is the content of this folder: the framework files in
`Lane4/`, and each case's `Spec.lean`, `Solution.lean`, `Final.lean`, with the checker
`tools/check.py`. The framework `.olean` files were rebuilt from source (`build/` was
deleted first; `check.py` rebuilds `Basic`, `Seq`, `Robust`, `RSeq` as needed).

**Caveat:** Mathlib itself was not re-downloaded or rebuilt for this test. The checker was
pointed (`LANE4_MATHLIB_PROJECT`) at an existing local Mathlib build whose
`lake-manifest.json` is the one in this folder (Mathlib commit above). A reader on a clean
machine runs `lake update && lake exe cache get` first (README, "Setup"); that step was not
exercised here. The test used a copy of this tree; the verdict does not depend on paths.

## Results

1. **Full re-check, flat layout (before the folder was moved into `proofs/`):**
   every case folder under `runs/rung{2,3,4}-test/{net,prog}/` that has a `Solution.lean`:
   **67 of 67 passed**, wall time **1,278 s (21 minutes)**, peak working set of any one
   Lean process **2.8 GB** (limit 4.5 GB). Rows: `results/recheck-flat-layout.json`,
   `results/recheck-flat-layout.log`. Per arm (passed / checked, total Lean seconds):

   | | net | prog (control) |
   |---|---|---|
   | rung 2 | 10 / 10, 127 s | 10 / 10, 118 s |
   | rung 3 | 12 / 12, 484 s | 12 / 12, 134 s |
   | rung 4 | 11 / 11, 242 s | 12 / 12, 124 s |

   The rung-4 net arm has 12 cases but 11 have a `Solution.lean`: `i03` has none (the
   agent crashed before submitting; counted as a fail in the paper).
2. **Final-layout re-run (after moving into `proofs/`, `build/` deleted, oleans rebuilt):**
   a sample, **19 of 19 passed** in 333 s: rung 2 net and prog `a00`, `p05`, `s01`;
   rung 3 net and prog `p001`, `p119`, `p281`; rung 4 net `c14`, `f24`, `i09` and prog
   `c14`, `f24`, `i03`, `i09`. Rows: `results/recheck-sample-final-layout.json`.
3. **Axioms:** every passing check reports the final theorems' axioms as a subset of
   `propext`, `Classical.choice`, `Quot.sound` (some use only `propext`, `Quot.sound`). The
   checker refuses any other axiom. `native_decide_attempted` is false in all 67 rows and
   the checker bans `native_decide` and `ofReduceBool` in a solution.
4. **Negative controls** (`smoke/`, rung-0/1 era cases through the same checker), observed:
   `s1_xor_simp` PASS, `s1b_xor_decide` FAIL (Lean errors), `s2_xor_wrong` FAIL (Lean
   errors), `s3_sorry` FAIL (banned token `sorry`), `s4_native` FAIL (banned token
   `native_decide`), `s5_max_real` PASS, `s6_prog` PASS, `s7_prog_cheat` FAIL (program part
   uses `max`), `s8_twin` PASS. Which outcome each case was designed to give is not
   written down in the case folders; the observed ones are listed as they are.

## What this does not show

- It re-checks that the recorded solutions are accepted by the Lean kernel against the
  recorded statements. It does not check that the statements say what the paper says;
  that is for a reader (README, "Reproduction").
- Times here are shorter than those recorded in the original attempt logs (for example
  134 s for rung-4 `c07` there, at most 29 s here); the logs were taken on a busier machine.
- The numeric scripts (`tools/r4_checks.py` etc.) and the export step were not re-run.
- Rung 1 and `runs/*-dev` folders were not re-checked.
- Not tested on Linux or macOS; the memory guard in `tools/check.py` works on Windows only.
