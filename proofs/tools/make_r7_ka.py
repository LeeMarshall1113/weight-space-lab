"""Rung 7, kill rule K-a: Lean test files for kernel evaluation of the certificate checker
(PREREG_R7.md Amendment 2, point 5). No proof content: only `decide` on closed Boolean terms.

    python tools/make_r7_ka.py <task A|B> <recipe> <seed> [outdir]
        -> <outdir>/R7KA1_<tag>.lean  small pieces (rational arithmetic, one gate, one head)
           <outdir>/R7KA2_<tag>.lean  the whole check, one theorem
           <outdir>/R7KA3_<tag>.lean  the closeness predicate of the transfer lemma (W against T)

Needs build/Lane4/R7Cert.olean (compile scratch/R7Cert.lean to it first).
The certificate is the one tools/r7_cert.py finds (candidate sets), with the state list closed here
by the same rule; the Lean checker recomputes everything, so this file is only a hint.
"""
import json, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(HERE, "tools"))
import r7_cert as RC


def q(v):
    f = F(v)
    s = str(f.numerator) if f.denominator == 1 else "%d/%d" % (f.numerator, f.denominator)
    return "(%s)" % s if f < 0 else s


L = lambda v: "[" + ", ".join(q(x) for x in v) + "]"
M = lambda m: "[" + ",\n      ".join(L(r) for r in m) + "]"
MASK = {"all": "Mask.all", "causal": "Mask.causal", "strict": "Mask.strict"}


def rows(m, n):
    """W1 may be stored flat; return it as a list of rows of length n."""
    flat = [v for r in m for v in (r if isinstance(r, list) else [r])]
    return [flat[i:i + n] for i in range(0, len(flat), n)]


def lean_net(name, net):
    """Heads and blocks as separate definitions (<name>H<k>, <name>B<b>), structure-instance notation."""
    d = len(net["embed"][0])
    out, bnames = [], []
    for bi, B in enumerate(net["blocks"]):
        hn = []
        for k, h in enumerate(B["heads"]):
            hn.append("%sH%d" % (name, k) if bi == 0 else "%sB%dH%d" % (name, bi, k))
            out.append("def %s : AHead :=\n  { A := %s,\n    V := %s,\n    mask := %s, m := %s, g := %s, gb := %s }\n"
                       % (hn[-1], M(h["A"]), M(h["V"]), MASK[h["mask"]], q(h["m"]), L(h["g"]), q(h["gb"])))
        bnames.append("%sB%d" % (name, bi))
        out.append("def %s : ABlock :=\n  { heads := [%s],\n    W1 := %s,\n    b1 := %s,\n    W2 := %s,\n    b2 := %s }\n"
                   % (bnames[-1], ", ".join(hn), M(rows(B["W1"], d)), L(B["b1"]), M(B["W2"]), L(B["b2"])))
    out.append("def %s : ANet :=\n  { embed := %s,\n    blocks := [%s],\n    outW := %s, outB := %s }\n"
               % (name, M(net["embed"]), ", ".join(bnames), L(net["outW"]), q(net["outB"])))
    return "\n".join(out)


TASKS = {
    "B": ("def task : Task :=\n  { ntok := 5, init := 0,\n"
          "    step := fun s t => if [0, 1, 2, 0, 0].getD (t - 1) 0 = 2 then s else [0, 1, 2, 0, 0].getD (t - 1) 0,\n"
          "    out := fun s t => ([2, 0, 2, 2, 0].getD (t - 1) 0 + s) % 3 }\n"),
    "A": ("def task : Task :=\n  { ntok := 5, init := 0,\n    step := fun _ t => t - 1,\n"
          "    out := fun s t => ((t - 1) + s) % 5 }\n"),
}


def certificate(net, tname):
    ok, why, info = RC.check(net, tname, verbose=False)
    ntok = len(net["embed"])
    heads = net["blocks"][0]["heads"]
    if ok:
        cands = [[t in c for t in range(ntok)] for c in info["cands"]]
    else:   # candidate sets by gate centre sign, as the script does before any rejection
        cands = []
        for h in heads:
            cands.append([sum(F(a) * F(x) for a, x in zip(h["g"], net["embed"][t])) + F(h["gb"]) < 0
                          for t in range(ntok)])
    s0, step, _ = RC.task_dfa(tname)
    init = (s0, tuple(0 if c[0] else None for c in cands))
    seen, todo = [init], [init]
    while todo:
        s, picks = todo.pop()
        for t in range(1, ntok):
            nxt = (step(s, t), tuple(t if c[t] else p for c, p in zip(cands, picks)))
            if nxt not in seen:
                seen.append(nxt); todo.append(nxt)
    return ok, why, cands, seen


def lean_cert(cands, states):
    b = lambda x: "true" if x else "false"
    o = lambda p: "none" if p is None else "some %d" % p
    cs = ",\n      ".join("[" + ", ".join(b(x) for x in c) + "]" for c in cands)
    ss = ",\n      ".join("(%d, [%s])" % (s, ", ".join(o(p) for p in pk)) for s, pk in states)
    return "def cert : Cert :=\n  { cands := [%s],\n    states := [%s] }\n" % (cs, ss)


HEAD = ("import Lane4.R7Cert\nnamespace Lane4.KA\nopen Lane4.Seq (Mask)\nopen Lane4.AGate Lane4.Cert\n"
        "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n")


def main():
    tname, recipe, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else os.path.join(HERE, "scratch")
    d = os.path.join(HERE, "runs", "r7-stage0", tname, recipe, "s%d" % seed)
    W, T = json.load(open(os.path.join(d, "W.json"))), json.load(open(os.path.join(d, "T.json")))
    ok, why, cands, states = certificate(W, tname)
    tag = "%s_%s_s%d" % (tname, recipe, seed)
    body = HEAD + lean_net("net", W) + "\n" + TASKS[tname] + "\n" + lean_cert(cands, states) + "\n"
    emb = "(net.embed.map (embIV (1 / 1000)))"
    h0 = "netH0"
    ka1 = body + "\n".join([
        "-- 1. rational arithmetic, plain decide and kernel decide",
        "example : (1 / 3 : ℚ) + 1 / 6 ≤ 1 / 2 := by decide",
        "example : (1 / 3 : ℚ) + 1 / 6 ≤ 1 / 2 := by decide +kernel",
        "-- 2. shape",
        "example : net.shapeOK 5 = true := by decide",
        "example : net.shapeOK 5 = true := by decide +kernel",
        "-- 3. one gate",
        "example : gateDec (1 / 1000) %s (%s.getD 0 []) = some %s := by decide +kernel" % (h0, emb, "true" if cands[0][0] else "false"),
        "-- 4. one head",
        "theorem head0 : headOK (1 / 1000) %s %s (cert.cands.getD 0 []) = true := by decide +kernel" % (emb, h0),
        "#print axioms head0",
        "end Lane4.KA", ""])
    ka2 = body + "\n".join([
        "/-- prototype says: %s (%s) -/" % ("accept" if ok else "reject", why),
        "theorem accept : check (1 / 1000) net task cert = %s := by decide +kernel" % ("true" if ok else "false"),
        "#print axioms accept",
        "end Lane4.KA", ""])
    spec = open(os.path.join(HERE, "scratch", "R7KTSpec.lean"), encoding="utf-8").read()
    spec = spec[:spec.index("end Lane4.Case") + len("end Lane4.Case")]
    ka3 = (spec + "\n\nnamespace Lane4.Case\nopen Lane4.AGate\nopen Lane4.Seq (Mask)\n"
           "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n"
           + lean_net("nW", W) + "\n" + lean_net("nT", T) + "\n" + "\n".join([
               "theorem same : sameShape nW nT = true := by decide +kernel",
               "theorem near : nearNet (1 / 1000) nW nT = true := by decide +kernel",
               "theorem notNear : nearNet (1 / 100000) nW nT = false := by decide +kernel",
               "#print axioms near",
               "end Lane4.Case", ""]))
    for name, txt in (("R7KA1", ka1), ("R7KA2", ka2), ("R7KA3", ka3)):
        p = os.path.join(out, "%s_%s.lean" % (name, tag))
        open(p, "w", encoding="utf-8", newline="\n").write(txt)
        print(p, len(txt))
    print("prototype:", ok, why, "states", len(states), "cands", cands)


if __name__ == "__main__":
    main()
