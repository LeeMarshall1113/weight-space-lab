"""Write a Lean certificate file for one quantized net (bridge/nets/<name>.json).

    python bridge/export_lean.py <name> [--tau 1/1000] [--n 6]
-> bridge/lean/Bridge/Nets/<Name>.lean containing the net and
   theorem cert_<name> : Bridge.SpecN n net τ := Bridge.cert n net τ (by decide)
"""
import argparse
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def q(k, Q):
    return f"({k}/{Q} : ℚ)" if k >= 0 else f"(-{-k}/{Q} : ℚ)"


def layer(W, b, Q):
    rows = ", ".join("[" + ", ".join(q(v, Q) for v in r) + "]" for r in W)
    return f"⟨[{rows}], [{', '.join(q(v, Q) for v in b)}]⟩"


def bool_vecs(n):
    """Same order as Bridge.boolVecs: map (cons 0) ++ map (cons 1)."""
    if n == 0:
        return [[]]
    prev = bool_vecs(n - 1)
    return [[0] + v for v in prev] + [[1] + v for v in prev]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("name")
    ap.add_argument("--tau", default="1/1000")
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--tactic", default="decide +kernel")
    ap.add_argument("--split", action="store_true")
    a = ap.parse_args()
    d = json.loads((HERE / "nets" / f"{a.name}.json").read_text())
    Q, L = d["q"], d["layers"]
    ident = re.sub(r"\W", "_", a.name)
    tn, td = a.tau.split("/")
    src = f"""import Bridge.IBP
open Lane4 Bridge

def net_{ident} : Net :=
  {{ hidden := [{", ".join(layer(W, b, Q) for W, b in L[:-1])}],
    out := {layer(*L[-1], Q)} }}

theorem cert_{ident} : SpecN {a.n} net_{ident} ({tn}/{td} : ℚ) :=
  certF {a.n} net_{ident} ({tn}/{td} : ℚ) (by {a.tactic})
"""
    if a.split:
        # one kernel-checked lemma per input (the kernel cache is per declaration), then assemble
        vecs = bool_vecs(a.n)
        lit = lambda v: "[" + ", ".join(map(str, v)) + "]"
        tau = f"({tn}/{td} : ℚ)"
        lemmas = "\n".join(f"theorem c{i}_{ident} : checkOneF net_{ident} {tau} {lit(v)} = true := by {a.tactic}"
                           for i, v in enumerate(vecs))
        names = ", ".join(f"c{i}_{ident}" for i in range(len(vecs)))
        src = src[:src.index("theorem cert_")] + lemmas + f"""

set_option maxRecDepth 100000 in
theorem all_{ident} : checkNF {a.n} net_{ident} {tau} = true := by
  rw [checkNF, show boolVecs {a.n} = [{", ".join(lit(v) for v in vecs)}] from rfl]
  simp only [List.all_cons, List.all_nil, {names}, Bool.and_self]

theorem cert_{ident} : SpecN {a.n} net_{ident} {tau} :=
  certF {a.n} net_{ident} {tau} all_{ident}

#print axioms cert_{ident}
"""
    out = HERE / "lean" / "Bridge" / "Nets" / f"{ident}.lean"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(src, encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
