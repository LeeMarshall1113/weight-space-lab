"""Rung 9-LN15: mechanical port of two proved rung-8 kit modules to the head check `headOKLN`, which is `headOK8`
conjunct for conjunct with four functions renamed (scoreIV -> scoreRel, matIV -> matRel, valBound -> valBoundR,
scoreOK -> scoreOKR). Text substitution only; the result is a DRAFT Solution.lean for the kit case, to be checked
by the kernel through the usual submit path and repaired by a doctor where it does not compile.

    python tools/ln_port.py lb      Lane4/R8KA.lean -> runs/r9ln15-kit/lb/Solution.lean   (ScoreWinLN)
    python tools/ln_port.py lc      Lane4/R8KG.lean -> runs/r9ln15-kit/lc/Solution.lean   (HeadSoundLN)
"""
import os, re, sys
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cid = sys.argv[1]
src, mod = {"lb": ("R8KA.lean", "R8KA"), "lc": ("R8KG.lean", "R8KG")}[cid]
s = open(os.path.join(HERE, "Lane4", src), encoding="utf-8").read()
s = s[s.index("\nset_option"):]                       # the Solution part: after the statement namespace
s = s.replace("namespace Lane4." + mod, "namespace Lane4.Case").replace("end Lane4." + mod, "end Lane4.Case")
s = s.replace("open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2",
              "open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2")
subs = [(r"\bheadOK8\b", "headOKLN"), (r"\bscoreIV\b", "scoreRel"), (r"\bscoreOK\b", "scoreOKR"), (r"\bmatIV\b", "matRel"),
        (r"\bvalBound\b", "valBoundR"), (r"\bdotIV\b", "dotRel"),
        (r"(?<![\w.])score_sound\b", "Lane4.LNKA.score_rel_sound"), (r"(?<![\w.])dot_sound\b", "Lane4.LNKA.dot_rel_sound"),
        (r"\bLane4\.R7K3\.hs_Bf_ge\b", "bfRel_ge"), (r"\bLane4\.R7K3\.hs_Bf_nonneg\b", "bfRel_nonneg"), (r"\bLane4\.R7K3\.hs_Bf\b", "bfRel"),
        (r"\bLane4\.R8KA\.score_win\b", "Lane4.LNKB.score_win_ln"),
        (r"theorem score_win : ScoreWin\b", "theorem score_win_ln : ScoreWinLN"),
        (r"theorem head_sound8 : HeadSound8\b", "theorem head_sound_ln : HeadSoundLN"),
        (r"\bunfold ScoreWin\b", "unfold ScoreWinLN"), (r"\bunfold HeadSound8\b", "unfold HeadSoundLN")]
for a, b in subs:
    s = re.sub(a, b, s)
if cid == "lc":
    extra = '''
/-! ported from Lane4/R7K3.lean (`hs_Bf_nonneg`, `hs_Bf_ge`) for `bfRel` -/

theorem bfRel_nonneg (δ : ℚ) (E : List (List IV)) (cd : List Bool) (r : List ℚ) :
    0 ≤ bfRel δ E cd r :=
  (Lane4.R7K3.hs_foldl_max (fun a : List IV × Bool => qabs (dotRel δ r a.1).1 + (dotRel δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).1

theorem bfRel_ge (δ : ℚ) (E : List (List IV)) (cd : List Bool) (hlen : cd.length = E.length)
    (r : List ℚ) {t : ℕ} (ht : t < E.length) (hcd : cd.getD t false = true) :
    qabs (dotRel δ r (E.getD t [])).1 + (dotRel δ r (E.getD t [])).2 ≤ bfRel δ E cd r := by
  have hmem : (E.getD t [], cd.getD t false) ∈ (List.zip E cd).filter (fun a => a.2) := by
    rw [List.mem_filter]
    exact ⟨Lane4.R7K3.hs_mem_zip E cd hlen t ht, by simpa using hcd⟩
  have key := (Lane4.R7K3.hs_foldl_max (fun a : List IV × Bool => qabs (dotRel δ r a.1).1 + (dotRel δ r a.1).2)
    ((List.zip E cd).filter (fun a => a.2)) 0).2 (E.getD t [], cd.getD t false) hmem
  unfold bfRel
  exact key
'''
    k = s.index("/-! ### list helpers -/")
    s = s[:k] + extra.lstrip("\n") + "\n" + s[k:]
out = os.path.join(HERE, "runs", "r9ln15-kit", cid)
os.makedirs(out, exist_ok=True)
open(os.path.join(out, "Solution.lean"), "w", encoding="utf-8", newline="\n").write(s.lstrip("\n") + "\n")
print(cid, "draft:", len(s.splitlines()), "lines;", "left-over names:",
      sorted(set(re.findall(r"\b(?:headOK8|scoreIV|matIV|dotIV|ScoreWin|HeadSound8|hs_Bf\w*)\b", s))))
