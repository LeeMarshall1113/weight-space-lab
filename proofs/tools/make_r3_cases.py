"""Build rung-3 doctor-facing case folders (PREREG_R3.md).

    python tools/make_r3_cases.py dev|test net|prog

net  : weight-ball statement, imports Lane4.Robust, tau = 1/1000, delta per case.
prog : the rung-1 verified-code control (exact equality), unchanged templates.
(twin cases are written by tools/r3_twins.py after the net arm.)

Folders: runs/rung3-<split>/<arm>/<id>/ with TASK.md, Spec.lean, Final.lean, case.json,
Basic.lean, Robust.lean (read-only copies), EXAMPLE.lean and an empty scratch/.
"""
import itertools, json, math, os, shutil, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP
import make_cases as MC

HERE = MC.HERE
TAU = "1/1000"

TASK_ROBUST = """# Task: write a ReLU network and prove it stays correct when its weights move

Write the weights of a small ReLU multi-layer perceptron for the function below, and a
Lean 4 proof that **every** network whose weights and biases are each within {tau} of
yours stays within {delta} of the function at every real point of the box.

**Function** ({n} input{s}):

    spec({args}) = {text}

(`max a b`, `min a b` and `|a|` have their usual meaning.)

**Box:** {box}

**Weight tolerance:** {tau} per weight and per bias. This includes the weights you write
as 0: every unit sees every unit of the layer below with a weight of size up to {tau}.

**Output tolerance:** {delta}.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def net : Lane4.Net`: rational weights. Hidden layers apply ReLU, the output layer
  is affine. At most 6 hidden layers, each at most 32 units wide, {n} input{s}, 1 output.
- `theorem net_robust : StatementRobust net`, where `StatementRobust` is in `Spec.lean`
  and the perturbed forward pass `Net.evalP` is in `Robust.lean`.

Advice: the error grows with every layer and with large weights, so a shallow network
with small weights is easier to prove. Your network does not have to equal the function
exactly; it has to stay within the output tolerance under every allowed perturbation.
""" + MC.COMMON.replace(
    "from\n  `import Lane4.Basic`, then", "from\n  `import Lane4.Robust` (which imports Lane4.Basic), then").replace(
    "Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.",
    "Read `Basic.lean`, `Robust.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.\n"
    "- Helper files (Python scripts, notes) go only in the `scratch/` sub-folder of this folder.")

FINAL_ROBUST = """namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.net {n} 1 = true := by decide
theorem final : Lane4.Case.StatementRobust Lane4.Case.net := Lane4.Case.net_robust
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
"""

assert "import Lane4.Robust" in TASK_ROBUST and "scratch/" in TASK_ROBUST


def spec_range(e, box, n_grid=20000):
    """Exact spec values at the box corners and on a grid of at least n_grid points."""
    n = len(box)
    k = max(2, math.ceil(n_grid ** (1.0 / n)))
    axes = [[F(lo) + (F(hi) - F(lo)) * F(i, k - 1) for i in range(k)] for lo, hi in box]
    vals = [SP.ev(e, list(x)) for x in itertools.product(*axes)]   # corners are grid points
    return min(vals), max(vals)


def delta_for(e, box):
    lo, hi = spec_range(e, box)
    d = max((hi - lo) / 20, F(1, 5))
    return F(math.ceil(d * 100), 100), lo, hi


def spec_robust(s, delta):
    n = s["n_in"]
    args = " ".join("x%d" % i for i in range(n))
    return "\n".join([
        "namespace Lane4.Case", "",
        "noncomputable def spec (%s : ℝ) : ℝ :=\n  %s" % (args, s["text"]), "",
        "def StatementRobust (N : Lane4.Net) : Prop :=",
        "  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (%s) dW db →" % TAU,
        "    ∀ %s : ℝ, %s →" % (args, MC.box_hyps(s["box"])),
        "      ∃ y : ℝ, N.evalP dW db [%s] = [y] ∧ |y - spec %s| ≤ (%s)" % (", ".join(args.split()), args, SP.q(delta)),
        "", "end Lane4.Case", ""])


def build(split, arm, cap=12):
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw3.json")))
    made = []
    for sid in draw["rung3_" + split]:
        s = pool[sid]
        n = s["n_in"]
        d = os.path.join(HERE, "runs", "rung3-" + split, arm, sid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        e = SP.from_json(s["expr"])
        delta, lo, hi = delta_for(e, [tuple(b) for b in s["box"]])
        fmt = dict(n=n, s="" if n == 1 else "s", args=", ".join("x%d" % i for i in range(n)),
                   largs=" ".join("x%d" % i for i in range(n)), text=s["text"],
                   box=", ".join("%s ≤ x%d ≤ %s" % (lo_, i, hi_) for i, (lo_, hi_) in enumerate(s["box"])),
                   py=MC.PY, submit=MC.SUBMIT, casedir=d.replace("\\", "/"), cap=cap,
                   tau=TAU, delta=SP.q(delta))
        meta = {"id": sid, "arm": arm, "rung": 3, "split": split, "max_attempts": cap, "lean_timeout": 600,
                "tau": TAU, "delta": SP.q(delta), "spec_min": SP.q(lo), "spec_max": SP.q(hi)}
        if arm == "net":
            files = {"TASK.md": TASK_ROBUST.format(**fmt), "Spec.lean": spec_robust(s, delta),
                     "Final.lean": FINAL_ROBUST.format(n=n),
                     "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_robust.lean"), encoding="utf-8").read()}
            meta.update({"import": "Robust", "final_theorems": ["Lane4Final.final", "Lane4Final.shape"]})
        else:
            files = {"TASK.md": MC.TASK_PROG.format(**fmt).replace(
                         "Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.",
                         "Read `Basic.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first.\n"
                         "- Helper files (Python scripts, notes) go only in the `scratch/` sub-folder of this folder."),
                     "Spec.lean": MC.spec_lean(s, "prog"), "Final.lean": MC.FINAL_PROG,
                     "EXAMPLE.lean": MC.example("prog")}
            meta.update({"final_theorems": ["Lane4Final.final"]})
        MC.write_case(d, files, meta)
        if arm == "net":
            shutil.copyfile(os.path.join(HERE, "Lane4", "Robust.lean"), os.path.join(d, "Robust.lean"))
        os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
        made.append(sid)
    print("built %d rung3 %s/%s cases" % (len(made), split, arm))


if __name__ == "__main__":
    build(sys.argv[1], sys.argv[2])
