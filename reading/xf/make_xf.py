"""Build the T-random transformer case set (PREREG_XF.md).

    python xf/make_xf.py --n 28 --seed 20261111
Each case: a random acceptable RASP program (xf.gen), a 2-layer d=64 4-head transformer
trained on it (2000 AdamW steps), kept if exact-sequence accuracy >= 0.99 on 1000 held-out
inputs (lengths 4-8). Writes xf/cases/<id>/ and xf/cases_xf_<seed>.json.
"""
import argparse
import hashlib
import json
import sys
import warnings
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
warnings.filterwarnings("ignore")
from xf import gen, model  # noqa: E402

CASES = HERE / "cases"


def build(job):
    i, (prog_seed, src, info) = job
    from xf.gen import random_program
    prog, src, _ = random_program(prog_seed)
    w, loss = model.train(prog, info["vocab"], info["out_values"], steps=2000, seed=prog_seed % 9973)
    acc = model.seq_accuracy(w, prog, info["vocab"], info["out_values"], 2, 4)
    cid = hashlib.sha1(f"xf-{prog_seed}".encode()).hexdigest()[:8]
    meta = {"case_id": cid, "index": i, "prog_seed": prog_seed, "template": info["template"],
            "vocab": info["vocab"], "classes": info["out_values"], "n_layers": 2, "n_heads": 4,
            "d": 64, "train_loss": loss, "seq_acc": acc, "ok": acc >= 0.99}
    if meta["ok"]:
        d = CASES / cid
        d.mkdir(parents=True, exist_ok=True)
        np.savez(d / "weights.npz", **w)
        (d / "program.txt").write_text(src)
        (d / "meta.json").write_text(json.dumps(meta, indent=1))
    return meta


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=28)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--procs", type=int, default=4)
    a = ap.parse_args()
    progs = gen.draw(a.n, a.seed)
    jobs = list(enumerate([(info["seed"], src, info) for _, src, info in progs]))
    with Pool(a.procs) as p:
        metas = p.map(build, jobs)
    ok = [m for m in metas if m["ok"]]
    (HERE / f"cases_xf_{a.seed}.json").write_text(json.dumps({"seed": a.seed, "cases": ok,
                                                             "rejected": [m for m in metas if not m["ok"]]}, indent=1))
    print(f"{len(ok)}/{len(metas)} kept")
