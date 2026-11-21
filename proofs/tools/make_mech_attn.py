"""Mechanism row (a), PREREG_MECH.md: per-network attention-window theorems.

    python tools/make_mech_attn.py <tag>      runs/mech/<tag>/Net.lean -> runs/mech/<tag>/Attn.lean

Text work only (no numerics): the existing row-(b) file of the network, with the kit case's statements and its
kernel-checked proof (runs/mech-kit/ma/Spec.lean, Solution.lean) included before it, and appended:
  attn_window   Lane4.Case.attn_window8 instantiated at this network, its extracted program and certificate
                (from this file's own `accept`): for every network in the ball, every input, every position
                i >= 1 and every head, a window P of at most L + 1 latest positions outside which the softmax
                weight is at most 3 * tailB of the total;
  attn_eps<k>   3 * tailB <= 2^-21 for head k, by `decide +kernel`;
  attn_L<k>     the certificate's window length of head k.
Does not edit the frozen row-(b) generator or its output.
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
nl = "\n"
KIT = os.path.join(HERE, "runs", "mech-kit", "ma")


def main():
    tag = sys.argv[1]
    d = os.path.join(HERE, "runs", "mech", tag)
    src = open(os.path.join(d, "Net.lean"), encoding="utf-8").read()
    meta = json.load(open(os.path.join(d, "meta.json")))
    assert "theorem accept :" in src, "no accept theorem in " + tag
    dq = re.search(r"theorem accept : check8 \((.*?)\) net task cert = true", src).group(1)
    spec = open(os.path.join(KIT, "Spec.lean"), encoding="utf-8").read()
    sol = open(os.path.join(KIT, "Solution.lean"), encoding="utf-8").read()
    assert "import" not in sol.split("namespace")[0]
    # the statement of AttnWindow8 after its first hypothesis, with this network's constants
    body = spec[spec.index("def AttnWindow8 : Prop :="):spec.index("end Lane4.Case")]
    body = body[body.index("∀ (u η M : ℝ)"):].rstrip()
    for a, b in (("(δ : ℝ)", "(((%s : ℚ)) : ℝ)" % dq), ("tailB δ", "tailB (%s)" % dq), ("T.ntok", "task.ntok"),
                 ("N.blocks", "net.blocks"), ("c.heads", "cert.heads"), ("N.init", "net.init")):
        assert a in body, a
        body = body.replace(a, b)
    nheads = len(re.findall(r"^def hc\d+ : HCert", src, re.M))
    Ls = [int(x) for x in re.findall(r"^def hc\d+ : HCert :=\n  \{ cands := \[.*?\], L := (\d+),", src, re.M)]
    assert len(Ls) == nheads
    first_imp = src.index("\n") + 1
    out = src[:first_imp] + nl + "/- mechanism row (a): statements (lane) and proof (kit case ma, one Sonnet doctor) -/" + nl + \
        spec + nl + sol + nl + src[first_imp:]
    add = ["", "namespace Lane4.Net", "open Lane4.Case Lane4.Cert Lane4.Cert8 Lane4.AGate Lane4.RSoft",
           "open Lane4.Seq (Mask cand tokAt)", "open Lane4.RSeq (Vec)", "",
           "/-- ATTENTION WINDOW for this network (row (a)): in every network of the ball, on every input, at every",
           "position, each head puts all but `3 * tailB` of its softmax weight on a window `P` of at most `L + 1`",
           "of its latest positions. Weights: exact softmax of the scores the network computes. -/",
           "theorem attn_window :", "    " + body.replace(nl, nl + "  ") + " :=",
           "  Lane4.Case.attn_window8 (%s) net task cert accept" % dq, ""]
    for k in range(nheads):
        add.append("theorem attn_eps%d : 3 * tailB (%s) netH%d hc%d ≤ 1 / 2 ^ 21 := by decide +kernel" % (k, dq, k, k))
        add.append("theorem attn_L%d : hc%d.L = %d := by decide +kernel" % (k, k, Ls[k]))
    add += ["", "end Lane4.Net", "#print axioms Lane4.Case.head_tail8", "#print axioms Lane4.Case.attn_window8",
            "#print axioms Lane4.Net.attn_window"] + ["#print axioms Lane4.Net.attn_eps%d" % k for k in range(nheads)] + [""]
    open(os.path.join(d, "Attn.lean"), "w", encoding="utf-8", newline=nl).write(out + nl.join(add))
    meta_a = dict(tag=tag, radius=dq, heads=nheads, window_L=Ls, eps_bound="2^-21")
    json.dump(meta_a, open(os.path.join(d, "attn_meta.json"), "w"), indent=1)
    print(tag, "| heads", nheads, "| window L", Ls)


if __name__ == "__main__":
    main()
