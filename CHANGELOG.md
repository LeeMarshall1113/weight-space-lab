# Changelog

Corrections, downgrades and additions, newest first. Reporters are credited unless they
ask otherwise. A claim that is narrowed or retracted is also downgraded in the index table
in `README.md`; it is not silently edited.

## v0.2 (2026-11-15, first public version)

- `proofs/` synced to the technical report version 0.9 (`proofs/REPORT.md`): rung 5 (softmax and a
  binary32 model), the rung-4 rounding witness and kit lemmas, Lean witnesses for three cells
  of the perturbation 2x2 (version 2), rung 6b (collision bound, memberships) and rung 6c
  (token-blind class), the open conjectures (statements only), the matching pre-registrations
  and results files, tools and data. Rung 6a (registered, parked) is not included.
- `reading/`: three finished units, all negatives or boundaries (compiled versus trained
  transformers; a decay curve that could not be built, with its correction; kernel-checked
  weight-ball certificates for tiny trained ReLU nets and where they stop), with the bridge
  Lean files.
- Checker: module table extended; `tools/recheck_release.py` and `reading/bridge/recheck_bridge.py`
  re-check every Lean file; results in `proofs/VERIFY.md`.
- Known weaknesses block rewritten to match the report; the "fragile versus robust"
  framing of v0.1 is withdrawn (see the report's 2x2 section).
- No external corrections yet.

## v0.1 (private, never released)

- First private pre-release copy: `proofs/` (rungs 2 to 4), re-checked from this
  folder (`proofs/VERIFY.md`: 67 of 67 recorded solutions pass). Other folders are empty
  slots.
- No external corrections yet.
