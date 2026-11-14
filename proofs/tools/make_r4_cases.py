"""Build rung-4 doctor-facing case folders (PREREG_R4.md).

    python tools/make_r4_cases.py dev|test net|prog
    python tools/make_r4_cases.py spec <case-id>          # print both Spec.lean variants

Folders: runs/rung4-<split>/<arm>/<id>/ with TASK.md, Spec.lean, Final.lean, case.json,
Basic.lean, Seq.lean and RSeq.lean (read-only copies), EXAMPLE.lean and an empty scratch/.
"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = "python"
SUBMIT = HERE.replace("\\", "/") + "/tools/submit.py"
TAU = "1 / 200"

# program part of a prog-arm solution: an explicit fold, no library searching or slicing,
# and no use of the spec's own fold or target
PROG_BANNED = (r"(?<![\w])(countP|count|sum|take|drop|filter|filterMap|find\?|findIdx\?|findSome\?|reverse|"
               r"carry|lastv|firstc|prevOcc|target|Statement|StatementProg|toFinset|Multiset|Finset)(?![\w])")


def chain(vals, default="0"):
    return "".join("if t = %d then %d else " % (t + 1, v) for t, v in enumerate(vals)) + default


def spec_parts(c):
    """(lean definitions, plain-text description)"""
    fam, V = c["family"], c["V"]
    if fam == "carry":
        defs = ["def cls (t : ℕ) : ℕ := " + chain(c["cls"]),
                "def dg (t : ℕ) : ℕ := " + chain(c["dg"]),
                "def carry (p : List ℕ) : ℕ := p.foldl (fun c t => if cls t = 2 then c else cls t) 0",
                "def target (w : List ℕ) (i : ℕ) : ℕ :=",
                "  (dg (w.getD (i - 1) 0) + carry (w.take (i - 1))) %% %d" % c["m"]]
        names = {0: "kill", 1: "generate", 2: "propagate"}
        text = ("A carry chain modulo %d. Tokens are 1..%d. Each token has a digit dg and a class: %s. "
                "A carry bit starts at 0 and runs left to right: a generate token sets it to 1, a kill "
                "token sets it to 0, a propagate token leaves it unchanged. The target at position i "
                "(1 ≤ i ≤ length) is (dg(token i) + the carry BEFORE token i is read) mod %d."
                % (c["m"], V, "; ".join("%d: dg %d, %s" % (t + 1, c["dg"][t], names[c["cls"][t]]) for t in range(V)),
                   c["m"]))
    elif fam == "last":
        defs = ["def val (t : ℕ) : ℕ := " + chain(c["val"]),
                "def lastv (p : List ℕ) : ℕ := p.foldl (fun s t => if val t = 0 then s else val t) 0",
                "def target (w : List ℕ) (i : ℕ) : ℕ := lastv (w.take i)"]
        text = ("Tokens are 1..%d. Marked tokens carry a value: %s; the other tokens are unmarked. The "
                "target at position i (1 ≤ i ≤ length) is the value of the LAST marked token among "
                "positions 1..i (position i included), and 0 if there is none."
                % (V, ", ".join("%d ↦ %d" % (t + 1, v) for t, v in enumerate(c["val"]) if v)))
    elif fam == "first":
        defs = ["def code (t : ℕ) : ℕ := " + chain(c["code"]),
                "def cbit (t : ℕ) : ℕ := " + chain(c["c"]),
                "def firstc (p : List ℕ) : ℕ := p.foldl (fun s t => if s = 0 then code t else s) 0",
                "def target (w : List ℕ) (i : ℕ) : ℕ :=",
                "  ((if firstc (w.take i) = 2 then 1 else 0) + cbit (w.getD (i - 1) 0)) % 2"]
        text = ("Tokens are 1..%d. Marked tokens carry a bit a: %s; the other tokens are unmarked. Every "
                "token also has a bit c: %s. Let A_i be the bit a of the FIRST marked token among "
                "positions 1..i (position i included), and 0 if there is none. The target at position i "
                "(1 ≤ i ≤ length) is (A_i + c(token i)) mod 2. (In `Spec.lean`, `code` is 0 for an "
                "unmarked token, 1 for a marked token with a = 0, 2 for a marked token with a = 1.)"
                % (V, ", ".join("%d ↦ %d" % (t + 1, v - 1) for t, v in enumerate(c["code"]) if v),
                   ", ".join("%d ↦ %d" % (t + 1, v) for t, v in enumerate(c["c"]))))
    else:
        defs = ["def h (t : ℕ) : ℕ := " + chain(c["h"]),
                "def prevOcc (w : List ℕ) (i : ℕ) : Option ℕ :=",
                "  (List.range i).reverse.find? (fun j => decide (1 ≤ j) && (tokAt w j == tokAt w i))",
                "def target (w : List ℕ) (i : ℕ) : ℕ :=",
                "  match prevOcc w i with",
                "  | some j => h (tokAt w (j + 1))",
                "  | none => 0"]
        text = ("Tokens are 1..%d, with a table h: %s. For position i (1 ≤ i ≤ length), let j be the "
                "most recent EARLIER position (1 ≤ j < i) holding the same token as position i. The "
                "target at position i is h(token at position j + 1), and 0 if there is no such j. "
                "(Position j + 1 may be position i itself.)"
                % (V, ", ".join("%d ↦ %d" % (t + 1, v) for t, v in enumerate(c["h"]))))
    return defs, text


def spec_lean(c, arm):
    defs, _ = spec_parts(c)
    V = c["V"]
    head = ["namespace Lane4.Case", "open Lane4.RSeq", "open Lane4.Seq (Mask cand tokAt)", ""] + defs + [""]
    if arm == "net":
        st = ["def Statement (N : TNet) : Prop :=",
              "  ∀ (u : ℝ) (fl : ℝ → ℝ), Rounding u fl → 0 ≤ u → u ≤ 1 / 16777216 →",
              "  ∀ p : Pert, p.Within (%s) →" % TAU,
              "  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ %d) → u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 →" % V,
              "  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4"]
    else:
        st = ["def StatementProg (f : List ℕ → List ℕ) : Prop :=",
              "  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ %d) →" % V,
              "  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → (f w).getD (i - 1) 0 = target w i"]
    return "\n".join(head + st + ["", "end Lane4.Case", ""])


COMMON = """
## Rules

- Write exactly one deliverable in this folder: `Solution.lean`. Do not edit any other
  file here. Keep every helper file you create (scripts, notes) inside the `scratch/`
  sub-folder of this folder, and nowhere else. Do not touch anything outside this folder.
- `Solution.lean` has no `import` line. The checker builds one file from
  `import Lane4.RSeq` (which imports Lane4.Seq and Lane4.Basic), then `Spec.lean`, then
  your `Solution.lean`, then `Final.lean`.
  Read `RSeq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first; `Seq.lean` holds the
  mask, candidate-list and token lemmas that `RSeq.lean` reuses.
- Write `Solution.lean` with your file-writing tool, as UTF-8.
- To check, run exactly:

      {py} {submit} "{casedir}"

  It prints PASS or FAIL with Lean's output. You have **{cap} submissions**; the episode
  ends at the first PASS. A check can take up to 10 minutes and may also wait in a queue.
  Wait for it. Never resubmit while one is pending, and do not report until your last
  submission has returned.
- You may NOT run `lean`, `lake`, `elan` or any installer, use the network, start other
  agents, or kill processes. You may run short Python (standard library or numpy) to test
  ideas before you submit.
- Banned in `Solution.lean` (the checker rejects the file without running Lean, and it
  still costs a submission): `sorry`, `admit`, `axiom`, `native_decide`, `macro`,
  `syntax`, `notation`, `elab`, `instance`, `opaque`, `unsafe`, `import`, `#eval`, `#exit`,
  anything in the `Lean.` namespace.
- The proof must be accepted by Lean's kernel using only the standard axioms, and it must
  hold for input lists of EVERY length. Testing finitely many lengths proves nothing here.
- Each check is limited to 600 s and 4.5 GB of memory.
- Lean 4 with Mathlib. `set_option maxHeartbeats N in` before a theorem is allowed.

## When you finish

Reply with: PASS or FAIL, the number of submissions used, and three or four sentences on
how you built it and what went wrong along the way. If you give up, say why.
"""

TASK_NET = """# Task: write a transformer's weights and prove it correct for every length, every nearby weight setting and a rounded forward pass

Write the weights of a small hard-attention transformer, in the fixed architecture of
`RSeq.lean`, that solves the task below, and a Lean 4 proof of `Statement` in `Spec.lean`.

**Task.** {text}

**What the statement says.** For every rounding function `fl` that satisfies the model
`Rounding u fl` with `u ≤ 2^-24`, every relative perturbation of every weight by at most
{tau} (weight `w` becomes `fl (w * (1 + d))`, `|d| ≤ {tau}`), every input `w` whose number
of positions `n = length + 1` satisfies `u * n ≤ 1/256`, and every position `i` in
1..length: the output is within 1/4 of the target. With `u = 0` this is exact arithmetic
at EVERY length; with `u = 2^-24` it is a float32-style forward pass up to 65,535
positions. One proof must cover both, so it has to work from the `Rounding` axioms.

**Architecture (fixed; read `RSeq.lean`).** Written weights are rationals. A BOS token
(token 0) is put at position 0, so your input occupies positions 1..length. Each position
starts with its token's stored embedding row followed by three position features
`[1, fl i, fl n]`. Attention is average-hard: the candidate positions with the highest
(rounded) score share the weight equally. Masks: all, causal (j ≤ i), strict (j < i).
Each block is heads plus a one-hidden-layer ReLU MLP, both residual. Every
multiplication, addition and division is rounded. Limits: at most 4 blocks, 4 heads per
block, state width (embedding width + 3) at most 24, MLP hidden width at most 32.

**Advice.** Under this model a weight written as 0 stays exactly 0, and a sum of exact
zeros is exactly 0; nothing else is exact. Two stored weights written with the same value
are in general NOT equal. A score that must separate positions has to do so with a margin
that the perturbation (relative size {tau}, and it multiplies large position features)
cannot close. Small target values and few layers keep the error bounds easy.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq` and `open Lane4.Seq (Mask cand tokAt)`):

- `def net : TNet` with {V} real tokens, so `{V1}` embedding rows (row 0 is BOS).
- `theorem net_ok : Statement net`.
""" + COMMON

TASK_PROG = """# Task: write a one-pass program and prove it correct for every input length

Write a plain Lean 4 function that solves the task below in a single left-to-right pass,
and a Lean 4 proof that it is correct for input lists of every length.

**Task.** {text}

The function returns the list of targets, one per input position. The exact statement to
prove is `StatementProg` in `Spec.lean`.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case`:

- `def prog : List ℕ → List ℕ`. The program part of the file (everything above a line
  that reads exactly `-- PROOF`) must do its work with `List.foldl` and an explicit step
  function, in one pass. It must not use library searching, counting, slicing or reversing
  (`find?`, `take`, `drop`, `filter`, `reverse`, `count`, `sum`, ...) and must not mention
  the spec's own `carry`, `lastv`, `firstc`, `prevOcc` or `target`. The spec's token
  tables (`cls`, `dg`, `val`, `code`, `cbit`, `h`) may be used. Helper `def`s are allowed
  above the marker.
- Then the line `-- PROOF`, and below it only lemmas and
  `theorem prog_correct : StatementProg prog`.
""" + COMMON.replace(
    "`import Lane4.RSeq` (which imports Lane4.Seq and Lane4.Basic), then `Spec.lean`, then",
    "`import Lane4.RSeq`, then `Spec.lean`, then").replace(
    "Read `RSeq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first; `Seq.lean` holds the\n"
    "  mask, candidate-list and token lemmas that `RSeq.lean` reuses.",
    "Read `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first (`Seq.lean` defines `tokAt`).")

FINAL_NET = """namespace Lane4Final
theorem shape : Lane4.RSeq.TNet.shapeOK Lane4.Case.net {V} = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_ok
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
"""
FINAL_PROG = """namespace Lane4Final
theorem final : Lane4.Case.StatementProg Lane4.Case.prog := Lane4.Case.prog_correct
end Lane4Final
#print axioms Lane4Final.final
"""

assert "Lane4.RSeq`, then `Spec.lean`" in TASK_PROG and "defines `tokAt`" in TASK_PROG


def build(split, arm, cap=12):
    pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
    draw = json.load(open(os.path.join(HERE, "pool", "draw4.json")))
    made = 0
    for cid in draw["rung4_" + split]:
        c = pool[cid]
        d = os.path.join(HERE, "runs", "rung4-" + split, arm, cid)
        if os.path.exists(os.path.join(d, "case.json")):
            continue
        _, text = spec_parts(c)
        fmt = dict(text=text, V=c["V"], V1=c["V"] + 1, py=PY, submit=SUBMIT, tau=TAU.replace(" ", ""),
                   casedir=d.replace("\\", "/"), cap=cap)
        os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
        files = {"TASK.md": (TASK_NET if arm == "net" else TASK_PROG).format(**fmt),
                 "Spec.lean": spec_lean(c, arm),
                 "Final.lean": FINAL_NET.format(V=c["V"]) if arm == "net" else FINAL_PROG,
                 "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_r4_%s.lean" % arm),
                                      encoding="utf-8").read()}
        for name, txt in files.items():
            open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
        meta = {"id": cid, "arm": arm, "rung": 4, "split": split, "family": c["family"], "import": "RSeq",
                "tau": TAU.replace(" ", ""),
                "final_theorems": ["Lane4Final.final", "Lane4Final.shape"] if arm == "net" else ["Lane4Final.final"],
                "max_attempts": cap, "lean_timeout": 600}
        if arm == "prog":
            meta["prog_banned"] = PROG_BANNED
        json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
        for f in ("Basic.lean", "Seq.lean", "RSeq.lean"):
            shutil.copyfile(os.path.join(HERE, "Lane4", f), os.path.join(d, f))
        made += 1
    print("built %d rung4 %s/%s cases" % (made, split, arm))


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1] == "spec":
        pool = {c["id"]: c for c in json.load(open(os.path.join(HERE, "pool", "rung4_pool.json")))}
        print(spec_lean(pool[sys.argv[2]], "net")); print(spec_lean(pool[sys.argv[2]], "prog"))
    else:
        build(sys.argv[1], sys.argv[2])
