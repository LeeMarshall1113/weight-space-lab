"""A6 ladder, CPU columns for n >= 12 (Lean per-input already stopped at n = 10).

    python bridge/ladder.py --n 12
mod3: width from {32, 48, 64} by the dev rule (>= 3/4 of seeds 0-3 exact), then test seeds 100-107:
exact quantized accuracy and exact rational IBP at tau = 1/1000 (one pass; the radius bisection is
skipped at n >= 12 because it is CPU-infeasible). Majority at the same width: test seeds, IBP at 1/1000,
and the region-tree leaf count. Files: nets L{n}_*.json / LMAJ{n}_*.json, results/bridge_ladder_n{n}.jsonl.
"""
import argparse
import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import train as T  # noqa: E402
import stage2 as S  # noqa: E402
import region as R  # noqa: E402


def exact_acc(L):
    return int(sum((v > 0) == (y > 0) for v, y in zip(T.exact_logits(L), T.Y)))


def run(n, out):
    def log(r):
        out.write(json.dumps(r) + "\n"); out.flush(); print(r, flush=True)

    R.set_task(n, "mod3")
    w_ok = None
    for w in (32, 48, 64):
        ok = 0
        for s in range(4):
            t0 = time.time()
            L = T.quantize(S.train_n(n, w, s))
            a = exact_acc(L)
            ok += a == len(T.X)
            log({"n": n, "task": "mod3", "stage": "dev", "w": w, "seed": s, "quant_acc": a, "N": len(T.X),
                 "sec": round(time.time() - t0, 1)})
        if ok >= 3:
            w_ok = w
            break
    log({"n": n, "chosen_w": w_ok})
    if w_ok is None:
        log({"n": n, "stop": "training: no width reached 3/4 dev seeds exact"})
        return
    for task, pref in (("mod3", "L"), ("maj", "LMAJ")):
        R.set_task(n, task)
        f, _ = R.label_fn(task, n)
        for s in range(100, 108):
            t0 = time.time()
            L = T.quantize(S.train_n(n, w_ok, s))
            a = exact_acc(L)
            rec = {"n": n, "task": task, "stage": "test", "w": w_ok, "seed": s, "quant_acc": a, "N": len(T.X)}
            if a == len(T.X):
                rec["ibp_cert_1e-3"] = min(T.ibp_margins(L, F(1, 1000))) > 0
                if task == "maj":
                    st = {"evals": 0, "leaves": 0}
                    tr = R.build(L, F(1, 1000), f, [], n, st)
                    rec["region_leaves"] = R.leaves(tr) if tr else None
                    rec["region_evals"] = st["evals"]
            rec["sec"] = round(time.time() - t0, 1)
            (T.NETS / f"{pref}{n}_w{w_ok}_s{s}.json").write_text(json.dumps({"q": T.Q, "layers": L, "rec": rec}))
            log(rec)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=12)
    a = ap.parse_args()
    with open(T.OUT / f"bridge_ladder_n{a.n}.jsonl", "w") as f:
        run(a.n, f)
