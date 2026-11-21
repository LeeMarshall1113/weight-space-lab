# Lean version check for the rung 6a/7/8 proofs (2026-11-21)

**Verdict: we are on Lean `v4.35.0-rc3` with Mathlib `v4.35.0-rc3` (commit c55e6e78...), which is past
the kernel soundness fixes in v4.32.1 (2026-07-22) and v4.32.2 (2026-07-28), and past the v4.34.0
kernel-focused release (2026-09-14). We are not on an affected version for those.** Two caveats: it is a
release candidate, and I did not find a published list of the October 2026 reports, so I cannot say
whether any is fixed after rc3.

What the notes say (release-note pages found by search today; the linked issues were not opened):
- v4.32.1: a kernel bug exploitable by a malicious meta program running in the same process
  (issue 14484, fix PR 14498). Not about `decide` or Nat acceleration.
- v4.32.2: nested inductive types with phantom parameters bypassed the type checker (issue 14576,
  PR 14577); exploitable even with the comparator tool; the nanoda external checker was not affected.
- v4.34.0: three soundness issues fixed, including a union-find cache in `is_def_eq` (14806), a
  reference-count overflow (14838), `is_prop` requiring a sort (14807); GMP 6.3.0 or newer required
  (14833) because older GMP can give unsound results in corner cases; kernel Nat numerals capped at
  128 MB (14849).
- v4.35.0 release-candidate notes: `lake check` and `lake comparator`, external checkers shipped in
  the toolchain (lean4lean, nanoda, others), `Lean.reduceBool` and `Lean.reduceNat` removed, and a
  fix for objects shared between threads (15288, for non-default checkers); I could not confirm which
  rc this entered.

Relevance to us: our files use `decide +kernel` over Nat and Rat arithmetic and no `native_decide`.
Nat acceleration and `decide` are in the changed area of v4.34.0 (GMP, numeral cap), which our
version includes. Every accepted file compiled under this version, so the numeral cap did not
stop any proof.

Not done: we have not run an external checker (nanoda, lean4lean) or `lake comparator` over our
proofs; that is the natural extra evidence, and `lake comparator` appears to be in the 4.35 line.
Cost of re-pinning to 4.35.0 final or 4.36: Mathlib must match, which means a rebuild of Mathlib (hours,
several GB) and a repeat of the full recheck (about 4 hours at 5 GB), plus checking that statements
and hashes still elaborate (the freeze lists are over source text, so they stay valid). I have not
re-pinned anything.
