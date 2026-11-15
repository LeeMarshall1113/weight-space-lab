"""Train the A6 discreteness variants on the 20 T-random programs.
    python xf/make_disc.py anneal|sparse|both
Writes xf/cases_trained_<v>/<id>/ and xf/cases_trained_<v>.json."""
import json, shutil, sys, warnings
from multiprocessing import Pool
from pathlib import Path
import numpy as np
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); warnings.filterwarnings("ignore")
from xf import model  # noqa: E402
from xf.gen import random_program  # noqa: E402
OPTS = {"anneal": dict(anneal=True, t_end=0.2), "sparse": dict(l1=1e-3), "both": dict(anneal=True, l1=1e-3, t_end=0.2)}

def build(a):
    m, v = a
    prog, _, _ = random_program(m["prog_seed"])
    tries = []
    for t in range(2):
        w, loss = model.train(prog, m["vocab"], m["classes"], steps=2000, seed=m["prog_seed"] % 9973 + 1000 * t, **OPTS[v])
        acc = model.seq_accuracy(w, prog, m["vocab"], m["classes"], 2, 4)
        tries.append(acc)
        if acc >= 0.99:
            d = HERE / f"cases_trained_{v}" / m["case_id"]; d.mkdir(parents=True, exist_ok=True)
            np.savez(d / "weights.npz", **w)
            src = HERE / "cases" / m["case_id"]
            shutil.copy(src / "program.txt", d / "program.txt"); shutil.copy(src / "meta.json", d / "meta.json")
            return {**m, "variant": v, "tries": tries, "ok": True}
    return {**m, "variant": v, "tries": tries, "ok": False}

if __name__ == "__main__":
    v = sys.argv[1]
    man = json.loads((HERE / "cases_xf_20261111_n20.json").read_text())["cases"]
    with Pool(4) as p:
        res = p.map(build, [(m, v) for m in man])
    (HERE / f"cases_trained_{v}.json").write_text(json.dumps({"variant": v, "cases": [r for r in res if r["ok"]],
                                                           "gate_failures": [r for r in res if not r["ok"]]}, indent=1))
    print(v, sum(r["ok"] for r in res), "/", len(res), "passed gate")
