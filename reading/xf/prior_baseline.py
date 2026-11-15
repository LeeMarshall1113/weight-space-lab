"""Prior baseline (PREREG_XF A1): draw programs from the generating pool, keep those that
agree with the case's 20 IO-20 examples, and report the expected functional match of a
uniformly chosen survivor (weighted by draw frequency). Knows the generator: an upper bound
for a prior-only guesser.

    python xf/prior_baseline.py trained|tracr --draws 200000
Writes results/xf_prior_<set>.jsonl
"""
import argparse
import json
import sys
import time
import warnings
from collections import Counter
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent), str(HERE.parent.parent / "shared" / "harness")]
warnings.filterwarnings("ignore")
from xf import rasp as R  # noqa: E402
from xf.gen import random_program, sample_inputs  # noqa: E402
from xf.task import XFTask  # noqa: E402

DRAWS = 200_000


def run(args):
    case_id, kind, draws = args
    t = XFTask(case_id, "IO-20", kind)
    rng = np.random.default_rng(int(t.meta["prog_seed"]) + 17)  # same 20 examples as IO-20
    ex = sample_inputs(rng, t.vocab, 20)
    ex_y = [t._pred(x) for x in ex]
    V = len(t.vocab)
    src_rng = np.random.default_rng(31337)
    counts, progs = Counter(), {}
    t0 = time.time()
    for _ in range(draws):
        p, src, info = random_program(int(src_rng.integers(0, 10**9)), vocab_size=V)
        try:
            if all(R.evaluate(p, x) == y for x, y in zip(ex, ex_y)):
                counts[src] += 1
                progs[src] = p
        except Exception:
            pass
    xs = sample_inputs(np.random.default_rng(424242), t.vocab, 1000)
    net = [t._pred(x) for x in xs]
    tot = sum(counts.values())
    exp_func = 0.0
    for src, c in counts.items():
        seq = np.mean([R.evaluate(progs[src], x) == n for x, n in zip(xs, net)])
        exp_func += (c / tot) * float(seq >= 0.99)
    return {"case_id": case_id, "kind": kind, "draws": draws, "survivors": tot,
            "distinct": len(counts), "expected_functional": exp_func if tot else 0.0,
            "sec": time.time() - t0}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("set", choices=["trained", "tracr"])
    ap.add_argument("--draws", type=int, default=DRAWS)
    ap.add_argument("--n", type=int, default=20)
    a = ap.parse_args()
    man = HERE / ("cases_xf_20261111_n20.json" if a.set == "trained" else "cases_tracr_20261112.json")
    ids = [c["case_id"] for c in json.loads(man.read_text())["cases"]][: a.n]
    with Pool(4) as p:
        res = p.map(run, [(i, a.set, a.draws) for i in ids])
    out = HERE.parent / "results" / f"xf_prior_{a.set}.jsonl"
    with open(out, "w") as f:
        for r in res:
            f.write(json.dumps(r) + "\n")
    print("expected functional:", round(sum(r["expected_functional"] for r in res), 2), "/", len(res))
