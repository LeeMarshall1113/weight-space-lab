"""Rung 6a, Amendment 1: assemble the per-coordinate kit module from kit case runs/r6-kit/kW
and apply the amendment's edits to the checker map, AGateAll and the case builder.

    python tools/r6_assemble_w.py    -> Lane4/AGateKitW.lean, Lane4/AGateAll.lean; patches
                                        tools/check.py and tools/make_r6a_cases.py (idempotent)
"""
import glob, json, os
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
R = lambda p: open(os.path.join(HERE, p), encoding="utf-8").read()


def W(p, s):
    open(os.path.join(HERE, p), "w", encoding="utf-8", newline="\n").write(s)


def passing(case):
    for p in sorted(glob.glob(os.path.join(HERE, "runs", "r6-kit", case, "attempts", "*.json"))):
        if json.load(open(p, encoding="utf-8")).get("pass"):
            return open(p[:-5] + ".lean", encoding="utf-8").read()
    raise SystemExit("no passing attempt for " + case)


DROP = ("namespace Lane4.Case", "end Lane4.Case", "open Lane4.RSeq (Vec pdot)", "open Lane4.RSoft Lane4.AGate")


def body(text):
    return "\n".join(l for l in text.splitlines() if l.strip() not in DROP).strip() + "\n"


kit = '''/-
the proofs study, rung 6a lemma kit, part 2 (Amendment 1 of PREREG_R6A.md, 2026-11-18): the
per-coordinate form of the stored-weight dot-product bound. Assembled by
tools/r6_assemble_w.py from kit case runs/r6-kit/kW (statements by the study team, proofs by a
Sonnet doctor, checked by the study team's checker). Fixed by the study team; doctors do not edit this
file. What you need is at the END of the file.
-/
import Lane4.AGateKit

namespace Lane4.AGate
open Lane4.RSeq (Vec pdot)
open Lane4.RSoft

''' + body(R("runs/r6-kit/kW/Spec.lean")) + "\n" + body(passing("kW")) + '''
/-! ### What doctors use

`CloseL x xh es Xs` is `Close` with one entry error `es[k]` and one bound `Xs[k]` per
coordinate. `ardot_near_w` (statement `ArdotNearW`) bounds a stored-weight dot product by
`wErr δ r es Xs`, the sum over coordinates of `|a_k| * es[k] + δ * (Xs[k] + es[k])`, plus
the same rounding term as `ardot_near_abs`; the uniform `W`, `X`, `e` only have to bound
all coordinates. Use it when the state is wide and most coordinates are small or exact:
the uniform lemmas charge `len * δ * (X + e)` with the LARGEST `X` and `e`.
`closeL_of_close` turns a uniform `Close` into a `CloseL` with constant lists.
`wErr` unfolds by `simp [wErr]` on explicit lists. -/

end Lane4.AGate
'''
W("Lane4/AGateKitW.lean", kit)

allf = R("Lane4/AGateAll.lean")
if "AGateKitW" not in allf:
    assert allf.count("import Lane4.AGateKit\n") == 1
    W("Lane4/AGateAll.lean", allf.replace("import Lane4.AGateKit\n", "import Lane4.AGateKitW\n"))

c = R("tools/check.py")
old = '"AGateKit": ["AGate"], "AGateAll": ["AGateKit", "Bin32"]}'
new = '"AGateKit": ["AGate"], "AGateKitW": ["AGateKit"],\n        "AGateAll": ["AGateKitW", "Bin32"]}'
if "AGateKitW" not in c:
    assert c.count(old) == 1
    W("tools/check.py", c.replace(old, new))

m = R("tools/make_r6a_cases.py")
if "AGateKitW" not in m:
    edits = [
        ('mods = ("Basic", "Seq", "RSeq", "RSoft", "RSoftKit", "AGate", "AGateKit")',
         'mods = ("Basic", "Seq", "RSeq", "RSoft", "RSoftKit", "AGate", "AGateKit", "AGateKitW")'),
        ("  behind a later one by at least `(m - δ)` per position, up to a small slack).\n",
         "  behind a later one by at least `(m - δ)` per position, up to a small slack).\n"
         "- `AGateKitW.lean` (end of file): `ardot_near_w`, the per-coordinate form: each\n"
         "  coordinate has its own entry error and bound (`CloseL`, `wErr`). Use it when the\n"
         "  state is wide: the uniform lemmas charge `len * δ * (X + e)` with the largest `X`\n"
         "  and `e` and can exceed the 1/4 budget on their own.\n"),
        ("and state values small: every bound scales with them. Read `EXAMPLE.lean` closely.\n",
         "and state values small: every bound scales with them. Read `EXAMPLE.lean` closely.\n"
         "The checker is your only compiler: submit early and in parts (helper lemmas first; a\n"
         "partial file FAILS at `Final.lean` but shows Lean's errors for your part). Stopping\n"
         "with unused submissions counts as a FAIL, the same as using all of them.\n"),
        ("`import Lane4.AGateAll` (AGateKit, AGate,", "`import Lane4.AGateAll` (AGateKitW, AGateKit, AGate,"),
        ("Read `AGate.lean`, `AGateKit.lean`, the end of", "Read `AGate.lean`, `AGateKit.lean`, the end of `AGateKitW.lean`, the end of"),
    ]
    for o, n in edits:
        assert m.count(o) == 1, o
        m = m.replace(o, n)
    W("tools/make_r6a_cases.py", m)
print("assembled AGateKitW.lean (%d lines); AGateAll, check.py, make_r6a_cases.py patched" % kit.count("\n"))
