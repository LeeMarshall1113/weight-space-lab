"""Build doctor-facing case folders.

    python tools/make_cases.py rung0
    python tools/make_cases.py rung1 dev|test net|prog
    (twin cases are written by tools/train_twin.py)

Folders: runs/<rung>/<arm>/<id>/ with TASK.md, Spec.lean, Final.lean,
case.json, Basic.lean (read-only copy) and EXAMPLE.lean.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = "python"
SUBMIT = HERE.replace("\\", "/") + "/tools/submit.py"

COMMON = """
## Rules

- Write exactly one file in this folder: `Solution.lean`. Do not edit any other file here
  and do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.Basic`, then `Spec.lean`, then your `Solution.lean`, then `Final.lean`.
  Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.
- Write `Solution.lean` with your file-writing tool, as UTF-8 (it contains characters such as
  `ℝ` and `≤`); do not patch it with shell one-liners.
- To check, run exactly:

      {py} {submit} "{casedir}"

  It prints PASS or FAIL with Lean's output. You have **{cap} submissions**; the
  episode ends at the first PASS. A submission can take a few minutes (it may
  also sit in a queue; just wait, never resubmit while one is pending).
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start
  other agents, or kill processes. You may run short Python (standard library or
  numpy) to test numbers before you submit.
- Banned in `Solution.lean` (the checker rejects the file without running Lean, and it
  still costs a submission): `sorry`, `admit`, `axiom`, `native_decide`, `macro`,
  `syntax`, `notation`, `elab`, `instance`, `opaque`, `unsafe`, `import`, `#eval`,
  anything in the `Lean.` namespace.
- The proof must be accepted by Lean's kernel using only the standard axioms.
- Each check is limited to 600 s and 4.5 GB of memory. Very long generated proofs
  (thousands of lines) run out of memory; keep the proof compact.
- Lean 4 with Mathlib (the real numbers and `Mathlib.Tactic` are imported; see `Basic.lean`).
  `set_option maxHeartbeats N in` before a theorem is allowed.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
"""

TASK_NET = """# Task: write a ReLU network and prove it correct

Write the weights of a small ReLU multi-layer perceptron that computes this function
exactly, and a Lean 4 proof that it does so at every real point of the box.

**Function** ({n} input{s}):

    spec({args}) = {text}

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** {box}

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def net : Lane4.Net`: rational weights. Hidden layers apply ReLU, the output layer
  is affine. At most 6 hidden layers, each at most 32 units wide, {n} input{s}, 1 output.
- `theorem net_correct : Statement net`, where `Statement` is in `Spec.lean`.
""" + COMMON

TASK_PROG = """# Task: write a branching program and prove it correct

Write a Lean 4 function that computes this function exactly using only `if … then … else`,
comparisons (`≤`, `<`) and arithmetic, and a Lean 4 proof that it equals the spec at every
real point of the box.

**Function** ({n} input{s}):

    spec({args}) = {text}

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** {box}

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `noncomputable def prog ({largs} : ℝ) : ℝ`. The program part of the file (everything
  above a line that reads exactly `-- PROOF`) must not use `max`, `min`, `abs`, `|…|`,
  `relu`, `⊔`, `⊓` or `spec`. Helper `def`s are allowed above the marker.
- Then the line `-- PROOF`, and below it only lemmas and
  `theorem prog_correct : StatementProg prog`, where `StatementProg` is in `Spec.lean`.
""" + COMMON

TASK_R0 = """# Task: write a ReLU network for a boolean function and prove it correct

Write the weights of a small ReLU multi-layer perceptron that computes the boolean function
in `Spec.lean` on all 16 inputs (bits are fed as the rationals 0 and 1; the output must be
exactly 1 or 0), and a Lean 4 proof of that.

**Function:** 4 bits b0 b1 b2 b3; idx = 8*b0 + 4*b1 + 2*b2 + b3; the output is 1 exactly
when idx is in {true_idx}.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def net : Lane4.Net`: rational weights, at most 6 hidden layers, each at most 32 wide,
  4 inputs, 1 output.
- `theorem net_correct : Statement net`. The domain is finite, so a case split on the four
  bits followed by `simp`/`norm_num` is the expected proof shape (`decide` does not work:
  rational arithmetic does not reduce in the kernel).
""" + COMMON

FINAL_NET = """namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.net {n} 1 = true := by decide
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


def qtxt(v):
    return "(%s)" % v if str(v).startswith("-") else str(v)


def box_hyps(box):
    return " → ".join("%s ≤ x%d → x%d ≤ %s" % (qtxt(lo), i, i, hi) for i, (lo, hi) in enumerate(box))


def spec_lean(s, arm):
    n = s["n_in"]
    args = " ".join("x%d" % i for i in range(n))
    out = ["namespace Lane4.Case", "",
           "noncomputable def spec (%s : ℝ) : ℝ :=\n  %s" % (args, s["text"]), ""]
    if arm == "net":
        out += ["def Statement (N : Lane4.Net) : Prop :=",
                "  ∀ %s : ℝ, %s →" % (args, box_hyps(s["box"])),
                "    N.eval [%s] = [spec %s]" % (", ".join(args.split()), args)]
    else:
        out += ["def StatementProg (f : %sℝ) : Prop :=" % ("ℝ → " * n),
                "  ∀ %s : ℝ, %s →" % (args, box_hyps(s["box"])),
                "    f %s = spec %s" % (args, args)]
    out += ["", "end Lane4.Case", ""]
    return "\n".join(out)


def write_case(d, files, meta):
    os.makedirs(d, exist_ok=True)
    for name, txt in files.items():
        open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
    json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
    shutil.copyfile(os.path.join(HERE, "Lane4", "Basic.lean"), os.path.join(d, "Basic.lean"))


def example(arm):
    return open(os.path.join(HERE, "examples", "EXAMPLE_%s.lean" % arm), encoding="utf-8").read()


def build_rung1(split, arm, cap=12):
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw.json")))
    made = []
    for sid in draw["rung1_" + split]:
        s = pool[sid]
        n = s["n_in"]
        d = os.path.join(HERE, "runs", "rung1-" + split, arm, sid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        fmt = dict(n=n, s="" if n == 1 else "s", args=", ".join("x%d" % i for i in range(n)),
                   largs=" ".join("x%d" % i for i in range(n)), text=s["text"],
                   box=", ".join("%s ≤ x%d ≤ %s" % (lo, i, hi) for i, (lo, hi) in enumerate(s["box"])),
                   py=PY, submit=SUBMIT, casedir=d.replace("\\", "/"), cap=cap)
        task = (TASK_NET if arm == "net" else TASK_PROG).format(**fmt)
        final = FINAL_NET.format(n=n) if arm == "net" else FINAL_PROG
        fins = ["Lane4Final.final", "Lane4Final.shape"] if arm == "net" else ["Lane4Final.final"]
        write_case(d, {"TASK.md": task, "Spec.lean": spec_lean(s, arm), "Final.lean": final,
                       "EXAMPLE.lean": example(arm)},
                   {"id": sid, "arm": arm, "rung": 1, "split": split, "final_theorems": fins,
                    "max_attempts": cap, "lean_timeout": 600})
        made.append(sid)
    print("built %d %s/%s cases" % (len(made), split, arm))


def build_rung0(cap=12):
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung0_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw.json")))
    for sid in draw["rung0"]:
        tt = pool[sid]["truth_table"]
        idx = [i for i, v in enumerate(tt) if v]
        d = os.path.join(HERE, "runs", "rung0", "net", sid)
        spec = "\n".join([
            "namespace Lane4.Case", "",
            "def bit (b : Bool) : ℚ := if b then 1 else 0", "",
            "def idx (b0 b1 b2 b3 : Bool) : Nat :=",
            "  8 * b0.toNat + 4 * b1.toNat + 2 * b2.toNat + b3.toNat", "",
            "def spec (b0 b1 b2 b3 : Bool) : ℚ :=",
            "  if %s.contains (idx b0 b1 b2 b3) then 1 else 0" % json.dumps(idx), "",
            "def Statement (N : Lane4.Net) : Prop :=",
            "  ∀ b0 b1 b2 b3 : Bool, N.eval [bit b0, bit b1, bit b2, bit b3] = [spec b0 b1 b2 b3]", "",
            "end Lane4.Case", ""])
        task = TASK_R0.format(true_idx="{" + ", ".join(map(str, idx)) + "}", py=PY, submit=SUBMIT,
                              casedir=d.replace("\\", "/"), cap=cap)
        write_case(d, {"TASK.md": task, "Spec.lean": spec, "Final.lean": FINAL_NET.format(n=4),
                       "EXAMPLE.lean": example("rung0")},
                   {"id": sid, "arm": "net", "rung": 0, "final_theorems": ["Lane4Final.final", "Lane4Final.shape"],
                    "max_attempts": cap, "lean_timeout": 600})
    print("built rung0 cases", draw["rung0"])


if __name__ == "__main__":
    if sys.argv[1] == "rung0":
        build_rung0()
    else:
        build_rung1(sys.argv[2], sys.argv[3])
