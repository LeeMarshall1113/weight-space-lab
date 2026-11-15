"""SCOPE_R6C.md, hand stage: evaluate the proposed SYNTACTIC class on the ten proved rung-2 networks.

tokenBlind(net): let T = embedding coordinates whose value differs between two real tokens
(BOS row ignored). The network reads T only through heads with a zero score matrix and
mask `all` (a global uniform average), and only through their value matrices:
  every head:  no nonzero score entry A[p][q] with p in T or q in T;
               a nonzero value entry V[r][c] with c in T only if A = 0 and mask = all;
  every MLP:   no nonzero W1[h][c] with c in T;      read-out: outW[c] = 0 for c in T.
Pure Python on the exported exact weights; no Lean, no numpy.
"""
import glob, json, os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
import collect2_lib as CL

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def token_blind(net):
    E = net["embed"]
    de = len(E[0])
    T = {c for c in range(de) if len({E[t][c] for t in range(1, len(E))}) > 1}
    why = []
    for b, B in enumerate(net["blocks"]):
        for h, hd in enumerate(B["heads"]):
            A, V = hd["A"], hd["V"]
            if any(A[p][q] != 0 and (p in T or q in T) for p in range(len(A)) for q in range(len(A[p]))):
                why.append("block %d head %d: score reads a token coordinate" % (b + 1, h + 1))
            reads = any(V[r][c] != 0 for r in range(len(V)) for c in T)
            uniform = hd["mask"] == "all" and all(v == 0 for r in A for v in r)
            if reads and not uniform:
                why.append("block %d head %d: value reads a token coordinate, head is not a global uniform average (mask %s)" % (b + 1, h + 1, hd["mask"]))
        if any(B["W1"][k][c] != 0 for k in range(len(B["W1"])) for c in T if c < len(B["W1"][k])):
            why.append("block %d: MLP reads a token coordinate" % (b + 1))
    if any(net["outW"][c] != 0 for c in T):
        why.append("read-out reads a token coordinate")
    return sorted(T), why


res = {}
for d in sorted(glob.glob(os.path.join(HERE, "runs", "rung2-test", "net", "*"))):
    p = os.path.join(d, "net.json")
    if os.path.exists(p):
        T, why = token_blind(CL.load_net(p))
        res[os.path.basename(d)] = {"token_coordinates": T, "token_blind": not why, "why_not": why}
        print(os.path.basename(d), "T =", T, "MEMBER" if not why else "not a member: " + "; ".join(why))
json.dump(res, open(os.path.join(HERE, "results", "r6c-token-blind.json"), "w"), indent=1)
