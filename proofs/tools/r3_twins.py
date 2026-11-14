"""Rung-3 trained twins (PREREG_R3.md, twin arm). numpy, CPU, 2 threads.

    python tools/r3_twins.py dev|test

For each spec whose robust-net arm passed: train the rung-1 trainer (unchanged) at the
passing net's hidden widths, seeds 0, 1, 2; round to multiples of 1/1024; measure the
exact error on 20,000 rational box points. The twin's tolerance is the case delta, fixed
before training. Seed 0 is "eligible" if its sampled error is at most delta/2; eligible
twins get a doctor case (the same weight-ball statement around the twin's weights), the
first 6 in draw order only. Writes results/r3-twins-<split>.json.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "2")
import json, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import specpool as SP
import make_cases as MC
import make_r3_cases as M3
import train_twin as TT

HERE = SP.HERE
TASK = """# Task: prove that a given ReLU network stays close to a target when its weights move

`Spec.lean` contains a ReLU multi-layer perceptron `twin` with fixed rational weights (it
was trained, not designed) and a target function `spec`. Prove in Lean 4 that **every**
network whose weights and biases are each within {tau} of `twin`'s stays within {delta} of
the target at every real point of the box.

**Target** ({n} input{s}):

    spec({args}) = {text}

**Box:** {box}

**Weight tolerance:** {tau} per weight and per bias (including weights that are 0).

**Output tolerance:** {delta}.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `theorem twin_robust : StatementRobustTwin`, where `StatementRobustTwin` is in
  `Spec.lean` and the perturbed forward pass `Net.evalP` is in `Robust.lean`. You do not
  write any weights; the network is given and must not be changed.
""" + M3.TASK_ROBUST.split("exactly; it has to stay within the output tolerance under every allowed perturbation.\n")[1]

FINAL = """namespace Lane4Final
theorem shape : Lane4.Net.shapeOK Lane4.Case.twin {n} 1 = true := by decide
theorem final : Lane4.Case.StatementRobustTwin := Lane4.Case.twin_robust
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
"""


def main(split, cap=12):
    pool = {s["id"]: s for s in json.load(open(os.path.join(HERE, "pool", "rung1_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw3.json")))
    out_path = os.path.join(HERE, "results", "r3-twins-%s.json" % split)
    results = json.load(open(out_path)) if os.path.exists(out_path) else {}
    n_cases = sum(1 for r in results.values() if r.get("doctor_case"))
    for sid in draw["rung3_" + split]:
        net_dir = os.path.join(HERE, "runs", "rung3-" + split, "net", sid)
        if sid in results or not os.path.exists(os.path.join(net_dir, "net.json")):
            continue
        s = pool[sid]
        e = SP.from_json(s["expr"])
        box = [tuple(b) for b in s["box"]]
        meta = json.load(open(os.path.join(net_dir, "case.json")))
        delta = F(meta["delta"])
        widths = [len(L["b"]) for L in json.load(open(os.path.join(net_dir, "net.json")))["hidden"]]
        rec = {"widths": widths, "delta": meta["delta"], "seeds": {}}
        for seed in (0, 1, 2):
            Ws, bs = TT.train(e, box, widths, seed)
            Wq, bq = TT.rationalise(Ws, bs)
            worst, n_eq = TT.exact_error(e, box, Wq, bq, seed)
            rec["seeds"][seed] = {"max_exact_err": float(worst), "eligible": bool(worst <= delta / 2)}
            if seed == 0:
                rec["eligible"] = bool(worst <= delta / 2)
                rec["doctor_case"] = bool(rec["eligible"] and n_cases < 6)
                if rec["doctor_case"]:
                    n_cases += 1
                    n = s["n_in"]
                    args = " ".join("x%d" % i for i in range(n))
                    d = os.path.join(HERE, "runs", "rung3-" + split, "twin", sid)
                    spec = "\n".join([
                        "namespace Lane4.Case", "",
                        "noncomputable def spec (%s : ℝ) : ℝ :=\n  %s" % (args, s["text"]), "",
                        TT.net_lean(Wq, bq), "",
                        "def StatementRobustTwin : Prop :=",
                        "  ∀ (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ), Lane4.Within (%s) dW db →" % M3.TAU,
                        "    ∀ %s : ℝ, %s →" % (args, MC.box_hyps(s["box"])),
                        "      ∃ y : ℝ, twin.evalP dW db [%s] = [y] ∧ |y - spec %s| ≤ (%s)" % (
                            ", ".join(args.split()), args, meta["delta"]),
                        "", "end Lane4.Case", ""])
                    fmt = dict(n=n, s="" if n == 1 else "s", args=", ".join(args.split()), text=s["text"],
                               box=", ".join("%s ≤ x%d ≤ %s" % (lo, i, hi) for i, (lo, hi) in enumerate(s["box"])),
                               tau=M3.TAU, delta=meta["delta"], py=MC.PY, submit=MC.SUBMIT,
                               casedir=d.replace("\\", "/"), cap=cap)
                    MC.write_case(d, {"TASK.md": TASK.format(**fmt), "Spec.lean": spec, "Final.lean": FINAL.format(n=n),
                                      "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_robust.lean"), encoding="utf-8").read()},
                                  {"id": sid, "arm": "twin", "rung": 3, "split": split, "import": "Robust",
                                   "final_theorems": ["Lane4Final.final", "Lane4Final.shape"], "max_attempts": cap,
                                   "lean_timeout": 600, "tau": M3.TAU, "delta": meta["delta"], "widths": widths})
                    import shutil
                    shutil.copyfile(os.path.join(HERE, "Lane4", "Robust.lean"), os.path.join(d, "Robust.lean"))
                    os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
                    json.dump({"hidden": [{"W": [[TT.qlit(x) for x in r] for r in W], "b": [TT.qlit(x) for x in b]} for W, b in zip(Wq[:-1], bq[:-1])],
                               "out": {"W": [[TT.qlit(x) for x in r] for r in Wq[-1]], "b": [TT.qlit(x) for x in bq[-1]]}},
                              open(os.path.join(d, "net.json"), "w"))
        results[sid] = rec
        json.dump(results, open(out_path, "w"), indent=1)
        print(sid, widths, "delta", meta["delta"], {k: round(v["max_exact_err"], 4) for k, v in rec["seeds"].items()},
              "eligible" if rec["eligible"] else "NOT eligible", "(doctor case)" if rec["doctor_case"] else "", flush=True)


if __name__ == "__main__":
    main(sys.argv[1])
