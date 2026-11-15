"""S2b exporter: Lean certificate for the float64 trained weights read as exact dyadic rationals
(bridge/nets/ORDF_w16_s<seed>.json). Same statement and framework as export_lean.py --split.

    python bridge/export_lean_frac.py ORDF_w16_s100 [--tau 1/1000] [--n 6]
"""
import argparse
import json
import re
from pathlib import Path

from export_lean import bool_vecs

HERE = Path(__file__).resolve().parent


def q(p):
    n, d = p
    return f"({n}/{d} : ℚ)" if n >= 0 else f"(-{-n}/{d} : ℚ)"


def layer(W, b):
    rows = ", ".join("[" + ", ".join(q(v) for v in r) + "]" for r in W)
    return f"⟨[{rows}], [{', '.join(q(v) for v in b)}]⟩"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("--tau", default="1/1000")
    ap.add_argument("--n", type=int, default=6)
    a = ap.parse_args()
    L = json.loads((HERE / "nets" / f"{a.name}.json").read_text())["frac"]
    ident = re.sub(r"\W", "_", a.name)
    tn, td = a.tau.split("/")
    tau = f"({tn}/{td} : ℚ)"
    vecs = bool_vecs(a.n)
    lit = lambda v: "[" + ", ".join(map(str, v)) + "]"
    lemmas = "\n".join(f"theorem c{i}_{ident} : checkOneF net_{ident} {tau} {lit(v)} = true := by decide +kernel"
                       for i, v in enumerate(vecs))
    names = ", ".join(f"c{i}_{ident}" for i in range(len(vecs)))
    src = f"""import Bridge.IBP
open Lane4 Bridge

def net_{ident} : Net :=
  {{ hidden := [{", ".join(layer(W, b) for W, b in L[:-1])}],
    out := {layer(*L[-1])} }}

{lemmas}

theorem all_{ident} : checkNF {a.n} net_{ident} {tau} = true := by
  rw [checkNF, show boolVecs {a.n} = [{", ".join(lit(v) for v in vecs)}] from rfl]
  simp only [List.all_cons, List.all_nil, {names}, Bool.and_self]

theorem cert_{ident} : SpecN {a.n} net_{ident} {tau} :=
  certF {a.n} net_{ident} {tau} all_{ident}

#print axioms cert_{ident}
"""
    out = HERE / "lean" / "Bridge" / "Nets" / f"{ident}.lean"
    out.write_text(src, encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
