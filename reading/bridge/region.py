"""A6(c) region certificates: branch and bound over the Boolean cube with interval inputs AND
interval weights (exact rationals), then a Lean file for Bridge/Region.lean.

    python bridge/region.py tree <net> --n 10 --task mod3|maj      # build + report tree size
    python bridge/region.py export <net> --n 10 --task mod3|maj    # Lean file (per-subtree lemmas)
    python bridge/region.py train_maj --n 10 --w 32                # majority companion nets, seeds 100-107
"""
import argparse
import json
import re
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import train as T  # noqa: E402

LEAF_CHUNK = 1  # one region per kernel lemma (32 hit 7 GB at n=10, w=32)


def label_fn(task, n):
    if task == "mod3":
        return lambda p: p % 3 == 0, "(fun p : ℕ => p % 3 == 0)"
    h = n // 2
    return (lambda p: p >= h), f"(fun p : ℕ => decide ({h} ≤ p))"


def ibp_box(layers, tau, lo, hi):
    """Output interval for inputs in [lo, hi] and every weight within tau (exact)."""
    Q = T.Q
    for k, (W, b) in enumerate(layers):
        nlo, nhi = [], []
        for row, bi in zip(W, b):
            L = F(bi, Q) - tau
            U = F(bi, Q) + tau
            for wij, l, u in zip(row, lo, hi):
                a, c = F(wij, Q) - tau, F(wij, Q) + tau
                cs = (a * l, a * u, c * l, c * u)
                L += min(cs)
                U += max(cs)
            nlo.append(L)
            nhi.append(U)
        if k < len(layers) - 1:
            nlo = [max(v, F(0)) for v in nlo]
            nhi = [max(v, F(0)) for v in nhi]
        lo, hi = nlo, nhi
    return lo[0], hi[0]


def build(layers, tau, f, pre, k, stats):
    p = sum(pre)
    const = all(f(p + c) == f(p) for c in range(k + 1))
    if const:
        stats["evals"] += 1
        lo = [F(v) for v in pre] + [F(0)] * k
        hi = [F(v) for v in pre] + [F(1)] * k
        L, U = ibp_box(layers, tau, lo, hi)
        if (f(p) and L > 0) or (not f(p) and U < 0):
            stats["leaves"] += 1
            return "L"
    if k == 0:
        return None
    t0 = build(layers, tau, f, pre + [0], k - 1, stats)
    if t0 is None:
        return None
    t1 = build(layers, tau, f, pre + [1], k - 1, stats)
    if t1 is None:
        return None
    return ("S", t0, t1)


def leaves(t):
    return 1 if t == "L" else leaves(t[1]) + leaves(t[2])


def lean_tree(t):
    return "RTree.leaf" if t == "L" else f"(RTree.split {lean_tree(t[1])} {lean_tree(t[2])})"


def export(name, layers, t, n, task, tau="1/1000"):
    f, flean = label_fn(task, n)
    ident = re.sub(r"\W", "_", name) + f"_{task}"
    tn, td = tau.split("/")
    tq = f"({tn}/{td} : ℚ)"
    Q = T.Q
    q = lambda k: f"({k}/{Q} : ℚ)" if k >= 0 else f"(-{-k}/{Q} : ℚ)"
    lay = lambda W, b: "⟨[" + ", ".join("[" + ", ".join(q(v) for v in r) + "]" for r in W) + "], [" + \
        ", ".join(q(v) for v in b) + "]⟩"
    lines = [f"import Bridge.Region\nopen Lane4 Bridge\n",
             f"def net_{ident} : Net :=\n  {{ hidden := [{', '.join(lay(W, b) for W, b in layers[:-1])}],\n"
             f"    out := {lay(*layers[-1])} }}\n",
             f"def f_{ident} : ℕ → Bool := {flean}\n"]
    counter = [0]

    def emit(node, pre, k):
        """Return the name of a lemma proving checkT net τ f pre k node = true."""
        counter[0] += 1
        nm = f"t{counter[0]}_{ident}"
        lit = "[" + ", ".join(map(str, pre)) + "]"
        stmt = f"checkT net_{ident} {tq} f_{ident} {lit} {k} {lean_tree(node)} = true"
        if node == "L" or leaves(node) <= LEAF_CHUNK:
            lines.append(f"theorem {nm} : {stmt} := by decide +kernel\n")
        else:
            a = emit(node[1], pre + [0], k - 1)
            b = emit(node[2], pre + [1], k - 1)
            lines.append(f"theorem {nm} : {stmt} :=\n  checkT_split _ _ _ _ _ _ _ {a} {b}\n")
        return nm

    root = emit(t, [], n)
    lines.append(f"theorem cert_{ident} : SpecG {n} net_{ident} {tq} f_{ident} :=\n"
                 f"  certT {n} net_{ident} {tq} f_{ident} _ {root}\n")
    lines.append(f"#print axioms cert_{ident}\n")
    out = HERE / "lean" / "Bridge" / "Nets" / f"R_{ident}.lean"
    out.write_text("\n".join(lines), encoding="utf-8")
    return out


def set_task(n, task):
    import itertools
    T.X = np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.float64)
    s = T.X.sum(1)
    T.Y = np.where(s % 3 == 0, 1.0, -1.0) if task == "mod3" else np.where(s >= n // 2, 1.0, -1.0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["tree", "export", "train_maj"])
    ap.add_argument("net", nargs="?")
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--w", type=int, default=32)
    ap.add_argument("--task", default="mod3")
    a = ap.parse_args()
    if a.cmd == "train_maj":
        import stage2 as S
        set_task(a.n, "maj")
        S.set_task = lambda n: None  # keep the majority labels
        with open(T.OUT / f"bridge_maj_test_n{a.n}.jsonl", "w") as fo:
            for s in range(100, 108):
                r = S.one_n(a.n, a.w, s, test=False)
                src = T.NETS / f"N{a.n}_w{a.w}_s{s}.json"
                src.rename(T.NETS / f"MAJ{a.n}_w{a.w}_s{s}.json")
                fo.write(json.dumps(r) + "\n"); fo.flush()
                print(r, flush=True)
        return
    d = json.loads((T.NETS / f"{a.net}.json").read_text())
    f, _ = label_fn(a.task, a.n)
    t0 = time.time()
    stats = {"evals": 0, "leaves": 0}
    t = build(d["layers"], F(1, 1000), f, [], a.n, stats)
    rec = {"net": a.net, "task": a.task, "n": a.n, "certified": t is not None,
           "leaves": leaves(t) if t else None, "ibp_evals": stats["evals"], "sec": round(time.time() - t0, 1),
           "per_input_leaves": 2 ** a.n}
    print(json.dumps(rec), flush=True)
    if a.cmd == "export" and t is not None:
        print(export(a.net, d["layers"], t, a.n, a.task))


if __name__ == "__main__":
    main()
