"""Build the rung-6b proof cases (PREREG_R6.md): runs/r6b/kColl, m05, m10, m29.

    python tools/make_r6b_cases.py

Every case imports the unchanged module `Seq`; the text of Lane4/Collision.lean (from
`namespace Lane4.Coll` on) is the first part of each Spec.lean, so tools/check.py is not
touched. Existing case folders are left alone.
"""
import json, os, shutil

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = lambda *p: os.path.join(HERE, *p)
read = lambda p: open(p, encoding="utf-8").read()
SUBMIT = 'python <repo>/tools/submit.py "<repo>/runs/r6b/%s"'

coll = read(R("Lane4", "Collision.lean"))
COLL = coll[coll.index("namespace Lane4.Coll"):]

RULES = """
## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep helper files inside the `scratch/` sub-folder. Do not touch anything
  outside this folder.
- Write `Solution.lean` with your file-writing tool, as UTF-8, with no `import` line.
- To check, run exactly:

      %s

  It prints PASS or FAIL with Lean's output. You have **12 submissions**; stop at the
  first PASS. A check can take up to 10 minutes and may also wait in a queue. Wait for
  it. Never resubmit while one is pending. You may submit a partial file to see Lean's
  errors for your part; it will FAIL at `Final.lean`.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. Short Python for arithmetic is fine.
- Banned in `Solution.lean` (rejected without running Lean, still costs a submission):
  `sorry`, `admit`, `axiom`, `native_decide`, `macro`, `syntax`, `notation`, `elab`,
  `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`, anything in the `Lean.`
  namespace.
- Standard axioms only. Each check is limited to 600 s and 4.5 GB.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.
- **If the statement is false as written, say so in your reply with the counterexample
  instead of spending submissions.** That would be a useful result.

## When you finish

Reply with PASS or FAIL, the number of submissions used, and three or four sentences on
how you proved it and what went wrong. If you give up, say why and what is left.
"""

TASK_COLL = """# Task: prove a short lower-bound theorem about weight perturbations (Lean 4)

Prove the two statements `Lane4.Coll.CollisionBound` and `Lane4.Coll.CollisionBound'`
defined in `Spec.lean`. Read `Spec.lean` (all definitions), `Final.lean`, and in
`Seq.lean` only the definitions of `TNet` and `TNet.out` (you do not need to unfold the
network evaluator: the class `CountChannel` gives you the outputs).

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll`):

- `theorem collision_bound' : CollisionBound'`
- `theorem collision_bound : CollisionBound`

The checker builds one file from `import Lane4.Seq` (which imports Mathlib), then
`Spec.lean`, then your `Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).** Take the decoder `D` from
`CountChannel`. Let `w₁ = replicate (L-1) s ++ [o]` (count `L-1`) and
`w₂ = replicate L s` (count `L`), both valid, of length `L`. Let `d₂ = -τ` and
`d₁ = (1 - τ*L)/(L-1)`. Then `|d₁| ≤ τ` (this is where `1 ≤ τ*(2L-1)` and `τ ≤ 1` are
used), `|d₂| = τ ≤ 1`, and `(1 + d₁)*(L-1) = (1 + d₂)*L`. The class gives networks `N₁`,
`N₂` with `netRel |dᵢ| N Nᵢ` and outputs `D (L+1) ((1+dᵢ)*kᵢ/(L+1))`, which are equal.
The counts `L-1` and `L` have different parities, so `Correct` cannot hold for both.
You need a monotonicity lemma: `netRel a N N' → a ≤ b → netRel b N N'` (through
`List.Forall₂.imp` at each level; `qRel a x y → a ≤ b → qRel b x y` since `|x| ≥ 0`).
The hypothesis `T.par < 2` is what makes the two parities contradict (`omega` after
`List.countP` rewrites). `scratch/PREVIOUS.lean` is a previous attempt at the statement WITHOUT that
hypothesis: everything in it compiled except the last parity step; you may reuse it.
`CollisionBound` follows from `CollisionBound'` by contradiction (`OnBall` says every
network in the ball is correct). Useful: `List.countP_replicate`, `List.countP_append`,
`List.length_replicate`, `List.mem_replicate`, `Nat.even_add_one`, `omega`.
""" + RULES % (SUBMIT % "kColl2")

TASK_MEM = """# Task: prove that a written transformer has a "count channel" (Lean 4)

`Spec.lean` defines a small hard-attention transformer `net` (two blocks) and the
statement `Membership : Prop := task.CountChannel net`. Prove it.

`net` is the network of `EXAMPLE.lean`, which is a COMPLETE, kernel-checked proof that
this same network computes the parity of the number of counted tokens (file given for
reference: its lemmas about the initial state, the first block and the second block's
scores are what you need to adapt; it is not imported, copy what you use).

**What the statement says.** There is one function `D : ℕ → ℚ → ℚ` such that for every
rational `d` with `|d| ≤ 1` there is a network `N'` inside the relative ball of radius
`|d|` around `net` (every weight `a` replaced by `b` with `|b - a| ≤ |d| * |a|`, so zeros
stay zero) whose output at the last position, on every valid input `w`, equals
`D (w.length + 1) ((1 + d) * k / (w.length + 1))` with `k = w.countP task.inS`.

**What to write.** `Solution.lean`, containing inside `namespace Lane4.Case` (with
`open Lane4.Seq Lane4.Coll`): `theorem membership : Membership`, plus helpers.
The checker builds one file from `import Lane4.Seq`, then `Spec.lean`, then your
`Solution.lean`, then `Final.lean`.

**The intended argument (you may do it differently).**
- `N'` := `net` with the single nonzero entry of the first block's value matrix (the `1`
  in `hd1.V`, row 1, column 0) replaced by `1 + d`. Define it as a function of `d`.
  `netRel |d| net N'`: every other entry is unchanged (`|a - a| = 0 ≤ |d| * |a|`), and
  for the changed entry `|(1 + d) - 1| = |d| ≤ |d| * |1|`. Unfold the lists; `simp` with
  the definitions and `List.Forall₂` constructors, or `decide`-free explicit terms.
- Block 1 has a zero score matrix, so every position is selected (`sel_all`) and slot 1
  becomes `z = (1 + d) * k / n` at every position (the example proves this with `d = 0`).
- Block 2's score from the last position to position `j` is `a * z * j - b * j^2 / n`
  for the constants `a`, `b` of this network; it does not read the token slots. Its
  value reads `(-1)^j`. So the output is `c * avg S (fun j => (-1)^j)` where `S` is the
  set of maximisers of that score over `j < n`.
- You do NOT need to find the maximiser. Define `D n z` as exactly that expression:
  `c * avg ((List.range n).filter (fun j => decide (∀ k ∈ List.range n, f n z k ≤ f n z j))) (fun j => (-1)^j)`
  with `f n z j := a * z * j - b * j^2 / n`, and show `Head.sel` of the second head is
  that filtered list (`List.filter_congr` after rewriting each score). This is the main
  difference from the example, which proves the maximiser is `j = k`.
- The state lists are long; follow the example's way of stating the state after block 1
  as `[flag, z, 0] ++ pos j n` and computing `qdot`/`matVec` on it by `simp`/`norm_num`.
""" + RULES

FINAL_COLL = """namespace Lane4Final
theorem final : Lane4.Coll.CollisionBound ∧ Lane4.Coll.CollisionBound' :=
  ⟨Lane4.Case.collision_bound, Lane4.Case.collision_bound'⟩
end Lane4Final
#print axioms Lane4Final.final
"""
FINAL_MEM = """namespace Lane4Final
theorem final : Lane4.Coll.Task.CountChannel Lane4.Case.task Lane4.Case.net := Lane4.Case.membership
end Lane4Final
#print axioms Lane4Final.final
"""
TASKS = {"05": ("4", "fun t => t == 1 || t == 3 || t == 4", "0"), "10": ("3", "fun t => t == 1 || t == 2", "0"),
         "29": ("4", "fun t => t == 2 || t == 3", "1")}


def put(d, name, text):
    open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(text)


def mk(cid, spec, final, task, extra=()):
    d = R("runs", "r6b", cid)
    if os.path.exists(d):
        print("exists, left alone:", cid)
        return
    os.makedirs(os.path.join(d, "scratch"))
    put(d, "Spec.lean", spec)
    put(d, "Final.lean", final)
    put(d, "TASK.md", task)
    for f in ("Seq.lean", "Basic.lean"):
        shutil.copy(R("Lane4", f), os.path.join(d, f))
    for name, text in extra:
        put(d, name, text)
    json.dump({"id": cid, "arm": "kit", "rung": "6b", "import": "Seq", "final_theorems": ["Lane4Final.final"],
               "max_attempts": 12, "lean_timeout": 600}, open(os.path.join(d, "case.json"), "w"))
    print("built", cid)


if __name__ == "__main__":
    mk("kColl2", COLL + "\n", FINAL_COLL, TASK_COLL)
    for p, (V, inS, par) in TASKS.items():
        sol = read(R("runs", "rung2-test", "net", "p" + p, "Solution.lean"))
        i = sol.index("def net : TNet")
        j = sol.index("\n\n", i)
        defs = sol[sol.index("open Lane4.Seq") + len("open Lane4.Seq"):j]
        spec = (COLL + "\n\nnamespace Lane4.Case\nopen Lane4.Seq Lane4.Coll\n" + defs +
                "\n\ndef task : Task := { V := %s, inS := %s, par := %s }\n\n" % (V, inS, par) +
                "def Membership : Prop := task.CountChannel net\n\nend Lane4.Case\n")
        ex = ("/- EXAMPLE (reference only, not imported): the kernel-checked rung-2 proof that this same network\n"
              "computes the parity task. Its Spec was:\n\n" + read(R("runs", "rung2-test", "net", "p" + p, "Spec.lean")) +
              "\n-/\n\n" + sol)
        mk("m" + p, spec, FINAL_MEM, TASK_MEM % (SUBMIT % ("m" + p)), [("EXAMPLE.lean", ex)])
