"""Build rung-2 doctor-facing case folders (PREREG_R2.md).

    python tools/make_seq_cases.py dev|test net|prog
    python tools/make_seq_cases.py spec <family> <json-params>     # print Spec.lean only

Folders: runs/rung2-<split>/<arm>/<id>/ with TASK.md, Spec.lean, Final.lean, case.json,
Basic.lean and Seq.lean (read-only copies), EXAMPLE.lean and an empty scratch/ folder.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = "python"
SUBMIT = HERE.replace("\\", "/") + "/tools/submit.py"

# program part of a prog-arm solution: no library counting, summing, slicing or sorting,
# and no use of the spec's own definitions
PROG_BANNED = (r"(?<![\w])(countP|count|sum|take|drop|filter|filterMap|mergeSort|insertionSort|sort|"
               r"Good|IsRank|digit|carryOut|Statement|StatementProg|toFinset|Multiset|Finset)(?![\w])")


def valid(V):
    return "def Valid (w : List ℕ) : Prop := w ≠ [] ∧ ∀ t ∈ w, 1 ≤ t ∧ t ≤ %d" % V


def spec_parts(c):
    """(lean definitions, statement for net, statement for prog, prog type, plain-text description)"""
    fam, V = c["family"], c["V"]
    if fam == "parity":
        cond = " || ".join("t == %d" % t for t in c["S"])
        defs = ["def inS (t : ℕ) : Bool := %s" % cond,
                "def Good (w : List ℕ) : Prop := (w.countP inS) % 2 = " + str(c["target"])]
        text = ("Tokens are 1..%d. The input is ACCEPTED exactly when the number of tokens that lie in "
                "{%s} is %s." % (V, ", ".join(map(str, c["S"])), "odd" if c["target"] else "even"))
    elif fam == "dyck":
        chain = "".join("if t = %d then %s else " % (t + 1, "(%d)" % x if x < 0 else str(x))
                        for t, x in enumerate(c["wt"]))
        defs = ["def wt (t : ℕ) : ℤ := %s0" % chain,
                "def Good (w : List ℕ) : Prop :=",
                "  (∀ k, k ≤ w.length → 0 ≤ ((w.take k).map wt).sum) ∧ (w.map wt).sum = 0"]
        text = ("Tokens are 1..%d with weights %s. The input is ACCEPTED exactly when every prefix "
                "has weight sum ≥ 0 and the whole input has weight sum 0 (a bracket-balance check)."
                % (V, ", ".join("%d ↦ %+d" % (t + 1, x) for t, x in enumerate(c["wt"]))))
    elif fam == "sort":
        defs = ["def IsRank (w : List ℕ) (i t : ℕ) : Prop :=",
                "  w.countP (fun s => decide (s < t)) < i ∧ i ≤ w.countP (fun s => decide (s ≤ t))"]
        text = ("Tokens are 1..%d. The output at position i (1 ≤ i ≤ length) must be the i-th smallest "
                "token of the input, i.e. the input sorted in non-decreasing order. `IsRank w i t` says "
                "that t is that token." % V)
    else:
        b = c["base"]
        defs = ["def dA (t : ℕ) : ℕ := (t - 1) / %d" % b,
                "def dC (t : ℕ) : ℕ := (t - 1) %% %d" % b,
                "def carryOut (p : List ℕ) : ℕ := p.foldl (fun c t => (dA t + dC t + c) / %d) 0" % b,
                "def digit (w : List ℕ) (i : ℕ) : ℕ :=",
                "  (dA (w.getD (i - 1) 0) + dC (w.getD (i - 1) 0) + carryOut (w.take (i - 1))) %% %d" % b]
        text = ("Addition in base %d, least significant digit first. Tokens are 1..%d; token t stands "
                "for the digit pair (a, c) with a = (t-1) / %d and c = (t-1) mod %d. The output at "
                "position i (1 ≤ i ≤ length) must be the i-th digit of the sum: (a_i + c_i + carry "
                "into position i) mod %d, with the schoolbook carry. The final carry-out is not "
                "output." % (b, V, b, b, b))
    if fam in ("parity", "dyck"):
        net = ["def Statement (N : TNet) : Prop :=",
               "  ∀ w : List ℕ, Valid w → (0 < N.out w w.length ↔ Good w)"]
        prog = ["def StatementProg (f : List ℕ → Bool) : Prop :=",
                "  ∀ w : List ℕ, Valid w → (f w = true ↔ Good w)"]
        ptype = "List ℕ → Bool"
    elif fam == "sort":
        net = ["def Statement (N : TNet) : Prop :=",
               "  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length →",
               "    ∃ t : ℕ, N.out w i = (t : ℚ) ∧ IsRank w i t"]
        prog = ["def StatementProg (f : List ℕ → List ℕ) : Prop :=",
                "  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → IsRank w i ((f w).getD (i - 1) 0)"]
        ptype = "List ℕ → List ℕ"
    else:
        net = ["def Statement (N : TNet) : Prop :=",
               "  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → N.out w i = ((digit w i : ℕ) : ℚ)"]
        prog = ["def StatementProg (f : List ℕ → List ℕ) : Prop :=",
                "  ∀ w : List ℕ, Valid w → ∀ i, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = digit w i"]
        ptype = "List ℕ → List ℕ"
    return defs, net, prog, ptype, text


def spec_lean(c, arm):
    defs, net, prog, _, _ = spec_parts(c)
    out = ["namespace Lane4.Case", "open Lane4.Seq", "", valid(c["V"]), ""] + defs + [""]
    out += (net if arm == "net" else prog) + ["", "end Lane4.Case", ""]
    return "\n".join(out)


COMMON = """
## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Seq`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Seq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      {py} {submit} "{casedir}"

  It prints PASS or FAIL with Lean's output. You have **{cap} submissions**; the episode
  ends at the first PASS. A check can take up to 10 minutes and may also wait in a queue.
  Wait for it. Never resubmit while one is pending, and do not report until your last
  submission has returned.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. You may run short Python (standard library or numpy) to test
  ideas before you submit.
- Banned in `Solution.lean` (the checker rejects the file without running Lean, and it
  still costs a submission): `sorry`, `admit`, `axiom`, `native_decide`, `macro`,
  `syntax`, `notation`, `elab`, `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`,
  anything in the `Lean.` namespace.
- The proof must be accepted by Lean's kernel using only the standard axioms, and it must
  hold for input lists of EVERY length. Testing finitely many lengths proves nothing here.
- Each check is limited to 600 s and 4.5 GB of memory.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
"""

TASK_NET = """# Task: write a transformer's weights and prove it correct for every input length

Write the weights of a small hard-attention transformer, in the fixed architecture of
`Seq.lean`, that solves the task below, and a Lean 4 proof that it is correct for input
sequences of every length.

**Task.** {text}

The exact statement to prove is `Statement` in `Spec.lean`.

**Architecture (fixed; read `Seq.lean` for the definitions).** Weights are exact
rationals. A BOS token (token 0) is put at position 0, so your input occupies positions
1..length. Each position starts with its token's embedding row followed by eight position
features `[1, i, i², 1/(i+1), (-1)^i, n, 1/n, i/n]` (n = number of positions, BOS
included). Attention is average-hard: the positions with the highest score share the
weight equally. Masks: all, causal (j ≤ i), strict (j < i). Each block is heads plus a
one-hidden-layer ReLU MLP, both residual. Limits: at most 4 blocks, 4 heads per block,
state width (embedding width + 8) at most 24, MLP hidden width at most 32.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.Seq`):

- `def net : TNet` with {V} real tokens, so `{V1}` embedding rows (row 0 is BOS).
- `theorem net_correct : Statement net`.
""" + COMMON

TASK_PROG = """# Task: write a one-pass program and prove it correct for every input length

Write a plain Lean 4 function that solves the task below in a single left-to-right pass,
and a Lean 4 proof that it is correct for input lists of every length.

**Task.** {text}

The exact statement to prove is `StatementProg` in `Spec.lean`.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def prog : {ptype}`. The program part of the file (everything above a line that reads
  exactly `-- PROOF`) must do its work with `List.foldl` and an explicit step function
  ({passes}). It must not use library counting, summing, slicing, filtering or sorting
  (`countP`, `count`, `sum`, `take`, `drop`, `filter`, `mergeSort`, `sort`, ...) and must
  not mention the spec's own definitions. Helper `def`s are allowed above the marker.
- Then the line `-- PROOF`, and below it only lemmas and
  `theorem prog_correct : StatementProg prog`.
""" + COMMON

FINAL_NET = """namespace Lane4Final
theorem shape : Lane4.Seq.TNet.shapeOK Lane4.Case.net {V} = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_correct
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
"""
FINAL_PROG = """namespace Lane4Final
theorem final : Lane4.Case.StatementProg Lane4.Case.prog := Lane4.Case.prog_correct
end Lane4Final
#print axioms Lane4Final.final
"""


def build(split, arm, cap=12):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung2_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw2.json")))
    made = 0
    for cid in draw["rung2_" + split]:
        c = pool[cid]
        d = os.path.join(HERE, "runs", "rung2-" + split, arm, cid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        _, _, _, ptype, text = spec_parts(c)
        fmt = dict(text=text, V=c["V"], V1=c["V"] + 1, ptype=ptype, py=PY, submit=SUBMIT,
                   casedir=d.replace("\\", "/"), cap=cap,
                   passes="two passes are allowed for this task" if c["family"] == "sort" else "one pass")
        os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
        files = {"TASK.md": (TASK_NET if arm == "net" else TASK_PROG).format(**fmt),
                 "Spec.lean": spec_lean(c, arm),
                 "Final.lean": FINAL_NET.format(V=c["V"]) if arm == "net" else FINAL_PROG,
                 "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_seq_%s.lean" % arm),
                                      encoding="utf-8").read()}
        for name, txt in files.items():
            open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
        meta = {"id": cid, "arm": arm, "rung": 2, "split": split, "family": c["family"], "import": "Seq",
                "final_theorems": ["Lane4Final.final", "Lane4Final.shape"] if arm == "net" else ["Lane4Final.final"],
                "max_attempts": cap, "lean_timeout": 600}
        if arm == "prog":
            meta["prog_banned"] = PROG_BANNED
        json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
        for f in ("Basic.lean", "Seq.lean"):
            shutil.copyfile(os.path.join(HERE, "Lane4", f), os.path.join(d, f))
        made += 1
    print("built %d rung2 %s/%s cases" % (made, split, arm))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1] == "spec":
        c = json.loads(sys.argv[3]); c["family"] = sys.argv[2]
        print(spec_lean(c, "net")); print(spec_lean(c, "prog"))
    else:
        build(sys.argv[1], sys.argv[2])
