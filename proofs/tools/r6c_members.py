"""Rung 6c: the lane's mechanical membership checks (PREREG_R6C.md, "Membership").

    python tools/r6c_members.py [tactic]      -> runs/r6c/members/Members.lean
                                 (default tactic: decide; others: "decide +kernel", rfl)

One file: import Lane4.Seq; Collision and TokenBlind statement text; for each of the
five networks the exact rung-2 network text (definitions up to `def net`) in its own
namespace and `theorem member : tokenBlind net ntok T = true := by <tactic>`.
No per-network argument: the same tactic for all five. Compile with tools/lean_lease.sh.
"""
import os, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
read = lambda *p: open(os.path.join(HERE, *p), encoding="utf-8").read()
TAC = sys.argv[1] if len(sys.argv) > 1 else "decide"
NETS = {"p05": (4, "[0]"), "p10": (3, "[0]"), "p29": (4, "[0]"), "s00": (2, "[1]"), "s01": (3, "[0, 1]")}


def body(name, ns):
    s = read("Lane4", name)
    return s[s.index("namespace " + ns):]


out = "import Lane4.Seq\n\n" + body("Collision.lean", "Lane4.Coll") + "\n\n" + body("TokenBlind.lean", "Lane4.TB") + "\n\n"
for p, (ntok, T) in NETS.items():
    sol = read("runs", "rung2-test", "net", p, "Solution.lean")
    i = sol.index("def net : TNet")
    j = sol.index("\n\n", i)
    defs = sol[sol.index("open Lane4.Seq") + len("open Lane4.Seq"):j]
    out += ("namespace Lane4.Member.%s\nopen Lane4.Seq Lane4.Coll Lane4.TB\n%s\n\n"
            "theorem member : tokenBlind net %d %s = true := by %s\n\nend Lane4.Member.%s\n\n" % (p, defs, ntok, T, TAC, p))
out += "".join("#print axioms Lane4.Member.%s.member\n" % p for p in NETS)
d = os.path.join(HERE, "runs", "r6c", "members")
os.makedirs(d, exist_ok=True)
open(os.path.join(d, "Members.lean"), "w", encoding="utf-8", newline="\n").write(out)
print("wrote", os.path.join(d, "Members.lean"), "tactic:", TAC)
