"""Split form of the K-a / per-network check: one lemma per head and per abstract state.
usage: python tools/make_r7_split.py <scratch/R7KA2_<tag>.lean>  ->  R7KA4_<tag>.lean beside it"""
import sys, re
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
i = s.index("/-- prototype says")
E = "(net.embed.map (embIV (1 / 1000)))"
n = len(re.findall(r"^\s+\(\d+, \[", s[:i], flags=re.M)) + s[:i].count("states := [(")
nh = len(re.findall(r"^def netH\d+ ", s, flags=re.M))
L = ["theorem hd%d : headOK (1 / 1000) %s netH%d (cert.cands.getD %d []) = true := by decide +kernel" % (k, E, k, k) for k in range(nh)]
L += ["theorem st%d : (List.range task.ntok).all (fun k => caseOK (1 / 1000) net netB0 task cert %s (cert.states.getD %d (0, [])) (k + 1)) = true := by decide +kernel" % (k, E, k) for k in range(n)]
L += ["theorem wts : weightsOK net netB0 = true := by decide +kernel", "#print axioms st0", "end Lane4.KA", ""]
q = p.replace("R7KA2", "R7KA4")
open(q, "w", encoding="utf-8", newline=chr(10)).write(s[:i] + chr(10).join(L))
print(q, "heads", nh, "states", n)
