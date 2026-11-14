# Contributing: please try to break this

Personal work. Views are my own.

This repository is a living lab notebook. We would rather be corrected than cited. Nothing
here has been peer reviewed, and the checks are only as good as the statements they check.

## What we want

- **A broken or too-weak theorem statement:** a `Spec.lean`, `Final.lean` or
  `Lane4/RSeq.lean` that does not say what the README says it says, is vacuous, or can be
  satisfied by a degenerate network.
- **Missed prior work:** anything that already does this, or part of it, that we did not
  cite or compare to. Links to the specific result are the most useful.
- **Counterexamples:** an input, length, perturbation or rounding function that violates a
  claim as we state it.
- **Failed reproductions:** a case that does not re-check on your machine (give the OS,
  Lean and Mathlib versions, command, and output).
- **Better framings:** a clearer or more honest way to state a claim, a fairer comparison
  (for example a relative-ball test of the rung-2 networks), or a better control.

## How to report

Open an issue using one of the templates in `.github/ISSUE_TEMPLATE/`:

- **Error in a claim**
- **Prior work**
- **Reproduction failed**

Pull requests are welcome for fixes, but an issue first is fine and usually better.

## What happens to a report

- Every accepted correction is logged in `CHANGELOG.md` with credit to the reporter (or
  anonymously, if you ask).
- A claim that does not survive is **downgraded in the index table** in `README.md` (for
  example from "confirmed" to "narrowed" or "retracted"), with a pointer to the changelog
  entry. We do not quietly edit it away.
- Negative and mixed results stay in the repository, labelled as such.
- Disagreements are answered in the issue, in public.

## Licence of contributions

Code and Lean files are Apache-2.0 (see `LICENSE`); by contributing you agree your
contribution is under the same terms. Text is proposed CC-BY-4.0 (see `README.md`).
