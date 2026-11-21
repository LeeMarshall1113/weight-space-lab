"""Rung-7 doctor-facing case folders: prove the ball theorem of a GIVEN skeleton network
(PREREG_R7.md, Route step 4), with the trained network's theorems derived in Final.lean.

    python tools/make_r7_cases.py <A|B> <recipe> <seed> <dev|test>
        from runs/r7-stage0/<task>/<recipe>/s<seed>/{T.json,W.json}
        -> runs/rung7-<split>/<task>-<recipe>-s<seed>/
"""
import json, os, shutil, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r4pool as P
import make_r4_cases as M4
import make_r6a_cases as M6
import r7

HERE = P.HERE


def q(v):
    f = F(v)
    return str(f.numerator) if f.denominator == 1 else "%d/%d" % (f.numerator, f.denominator)


def lean_net(name, net, doc):
    L = lambda v: "[" + ", ".join(q(x) for x in v) + "]"
    M = lambda m: "[" + ",\n      ".join(L(r) for r in m) + "]"
    mask = {"all": "Mask.all", "causal": "Mask.causal", "strict": "Mask.strict"}
    blocks = []
    for B in net["blocks"]:
        heads = ",\n".join("    ⟨%s,\n     %s,\n     %s, %s, %s, %s⟩" % (M(h["A"]), M(h["V"]), mask[h["mask"]], q(h["m"]), L(h["g"]), q(h["gb"]))
                           for h in B["heads"])
        blocks.append("  ⟨[\n%s],\n   %s,\n   %s,\n   %s,\n   %s⟩" % (heads, M(B["W1"]), L(B["b1"]), M(B["W2"]), L(B["b2"])))
    return "/-- %s -/\ndef %s : ANet :=\n ⟨%s,\n  [\n%s],\n  %s, %s⟩\n" % (doc, name, M(net["embed"]), ",\n".join(blocks), L(net["outW"]), q(net["outB"]))


def task_parts(c):
    if c["family"] == "modadd":
        defs = ["/-- Target at position `i`: (digit of token `i` + digit of token `i - 1`) mod 5; token `t` is",
                "digit `t - 1`; before position 1 the digit is 0. -/",
                "def target (w : List ℕ) (i : ℕ) : ℕ :=",
                "  ((w.getD (i - 1) 0 - 1) + (if 2 ≤ i then w.getD (i - 2) 0 - 1 else 0)) % 5"]
        text = ("Tokens 1..5 are the digits 0..4 (token `t` is digit `t - 1`). At every position `i` the output is "
                "(digit of token `i` + digit of token `i - 1`) mod 5; at position 1 the earlier digit counts 0.")
        return defs, text
    return M4.spec_parts(c)


def spec(c, W, T):
    defs, _ = task_parts(c)
    head = ["namespace Lane4.Case", "open Lane4.RSeq (Vec)", "open Lane4.RSoft Lane4.AGate",
            "open Lane4.Seq (Mask cand tokAt)", ""] + defs + ["",
            "def Statement (N : ANet) : Prop :=",
            "  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Rnd u η M fl → ExpM u η ex →",
            "  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →",
            "  ∀ p : APert, p.Within (1 / 1000) →",
            "  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ %d) →" % c["V"],
            "  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →",
            "  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →",
            "  ∀ i : ℕ, 1 ≤ i → i ≤ w.length → |N.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4", ""]
    return "\n".join(head) + "\n" + lean_net("net", W, "The skeleton: the trained weights rounded to multiples of 1/1024. GIVEN; you prove `Statement net`.") + \
        "\n" + lean_net("trained", T, "The network exactly as trained (float32 values as rationals). Used only by Final.lean.") + "\nend Lane4.Case\n"


FINAL_TRAINED = """
namespace Lane4Final
open Lane4.RSoft Lane4.AGate Lane4.Bin32

theorem same : sameShape Lane4.Case.net Lane4.Case.trained = true := by decide
theorem near : nearNet (1 / 1000) Lane4.Case.net Lane4.Case.trained = true := by decide

theorem trained_in_ball : (diffP Lane4.Case.net Lane4.Case.trained).Within (1 / 1000) := by
  have h := diff_within Lane4.Case.net Lane4.Case.trained (1 / 1000) (by norm_num) same near
  have e : (((1 / 1000 : ℚ)) : ℝ) = 1 / 1000 := by norm_num
  rwa [e] at h

/-- The network AS TRAINED, exact real arithmetic, every input length. -/
theorem trained_exact_all_lengths (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ {V}) (i : ℕ)
    (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out Lane4.Case.trained (fun x => x) Real.exp zeroP w i - ((Lane4.Case.target w i : ℕ) : ℝ)|
      ≤ 1 / 4 := by
  rw [← out_shift Lane4.Case.net Lane4.Case.trained same]
  exact exact_all_lengths _ trained_in_ball w hw i h1 h2

/-- The network AS TRAINED, binary32 arithmetic, at most 65,535 input tokens. -/
theorem trained_binary32 (rn fl ex : ℝ → ℝ) (hrn : IsRN rn) (hfl : ∀ x, |x| ≤ maxF → fl x = rn x)
    (hex : ExpM (1 / 2 ^ 24) (1 / 2 ^ 149) ex)
    (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ {V}) (hlen : w.length + 1 ≤ 65536)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    |ANet.out Lane4.Case.trained fl ex zeroP w i - ((Lane4.Case.target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  rw [← out_shift Lane4.Case.net Lane4.Case.trained same]
  exact binary32 rn fl ex hrn hfl hex _ trained_in_ball w hw hlen i h1 h2

end Lane4Final
#print axioms Lane4Final.trained_exact_all_lengths
#print axioms Lane4Final.trained_binary32
"""

TASK = """# Task: prove a GIVEN gated softmax transformer correct for every length under ADDITIVE perturbation of every weight

The network `net` in `Spec.lean` is GIVEN. It came from gradient training: its weights are
multiples of 1/1024, most of them non-zero, and it was not designed to be read. You do
not write or change weights. You write a Lean 4 proof of `Statement net`.

**Task the network solves.** {text}

**What the statement says.** For every rounding function `fl` with `Rnd u η M fl`, every
float exponential `ex` with `ExpM u η ex`, every ADDITIVE perturbation of every weight by
at most 1/1000 (a written weight `w` is used as `asw fl w d = fl (w + d)`, `|d| ≤ 1/1000`,
one `d` per weight, including weights written as 0, gate weights, gate biases and slopes),
and every input whose number of positions `n = length + 1` satisfies `u * n ≤ 1/256`,
`η * n ≤ 1/2^100` and `2^40 * n^2 ≤ M`: at every position `i` in 1..length the output is
within 1/4 of the target. `Final.lean` then derives corollaries (you do not prove them),
among them the same result for the network exactly as trained (`trained` in `Spec.lean`).

**Architecture (fixed; read the header of `AGate.lean`).** A BOS token (token 0) is at
position 0. The state at a position is ONLY the stored embedding row of its token: no
position features. Each head adds a score bias `fl (m' * (j - i))` (slope `m`), has a
gate neuron on the keys (key `j` is a candidate for query `i` iff the mask allows it,
causal `j ≤ i` or strict `j < i`, and `relu (fl (g' · x_j + gb')) = 0` exactly), and
takes a softmax over the candidates; with no candidate its output is 0. One block: two
heads, then a ReLU MLP with 12 hidden units, both residual; a linear read-out.
This network: width 8, {V} real tokens ({V1} embedding rows).{gate_note}

**How such a proof goes.** The network is dense, but the set of IDEAL situations is
finite. With slope 24 each head returns, up to a tiny leak, the value of its nearest
candidate key, so the ideal state after the heads at position `i` depends only on a few
discrete facts ({cases}). So:
1. Work out numerically (a short Python script with `fractions` is fine and expected;
   `net.json` holds the weights, `r6net.py` is the study team's numeric forward pass) what each
   head attends to, the gate value of every token's embedding row, and for every ideal
   case the exact rational state, hidden pre-activations and output. Check your reading
   against `r6net.py` before proving anything.
2. Prove it in Lean as IDEAL value plus ERROR bound, as in `EXAMPLE.lean`:
   - `AGateKit.lean`: `ardot_near_abs`, `ardot_near` (`Close`, `dotQ`), `pdot_near`, `bias_gap`.
   - `AGateKitW.lean` (end of file): `ardot_near_w` with per-coordinate errors and bounds
     (`CloseL`, `wErr`). You will need it: the uniform lemmas are too loose for a dense
     network.
   - `AGate.lean`: `asw_near`, `asw_bound`, `fl_asw`, `relu_fl_zero`, `AHead.mem_cands`,
     `AHead.cands_nodup`.
   - `RSoftKit.lean` (end of file): `soft_near` (a candidate that beats every other
     candidate by a score gap of at least `16 * |j - k|` gets its value returned within
     `B/100 + 1/2^90`), `soft_zeros`.
   - `RSoft.lean`: `Rnd.abs`, `Rnd.near`, `Rnd.bound`, `Rnd.gap`, `mul_near`, `range_const`,
     `range_lin`, `range_quad`, `eta_tiny`, `ndist_cast`.
3. ReLU is 1-Lipschitz (`|relu a - relu b| ≤ |a - b|`), so you never need the sign of a
   hidden unit: carry an error bound through the MLP instead.
4. The content part of each score (`x_i · A' x_j`) is NOT zero here: bound it from the
   finitely many embedding rows, and check that the slope gap (24 minus 1/1000 per
   position) still beats it by `16 * |j - k|`. If it does not for some pair, say so.
5. The study team measured this network numerically: worst deviation {inside:.3f} under
   perturbations of 1/1000 (tolerance 0.25), and it first breaks at {breaks} times that
   radius. So the statement is believed true with room, but worst-case bounds through a
   dense MLP are loose: use per-coordinate bounds everywhere and add up errors per case.
   If your best bound for some case exceeds 1/4, report the case and the numbers.

You may generate Lean text with a script (keep generated files in `scratch/`, then put
the result in `Solution.lean`). Keep each check under the time limit: split the work
into lemmas (one per ideal case, or per layer), avoid one giant `norm_num`.
The checker is your only compiler: submit early and in parts (helper lemmas first; a
partial file FAILS at `Final.lean` but shows Lean's errors for your part). Stopping
with unused submissions counts as a FAIL, the same as using all of them.

**What to define** in `Solution.lean`, inside `namespace Lane4.Case` (with
`open Lane4.RSeq (Vec)`, `open Lane4.RSoft Lane4.AGate` and
`open Lane4.Seq (Mask cand tokAt)`):

- `theorem net_ok : Statement net` (and any helper lemmas). Do NOT define `net`.
""" + M4.COMMON.replace(
    "`import Lane4.RSeq` (which imports Lane4.Seq and Lane4.Basic), then `Spec.lean`, then",
    "`import Lane4.ATransferAll` (ATransfer, AGateKitW, AGateKit, AGate, RSoftKit, RSoft, RSeq, Seq, Basic, and the\n  binary32 file used only by `Final.lean`), then `Spec.lean`, then").replace(
    "Read `RSeq.lean`, `Spec.lean`, `Final.lean` and `EXAMPLE.lean` first; `Seq.lean` holds the\n"
    "  mask, candidate-list and token lemmas that `RSeq.lean` reuses.",
    "Read `AGate.lean`, `AGateKit.lean`, the end of `AGateKitW.lean`, the end of `RSoftKit.lean`, `Spec.lean`, `Final.lean`\n"
    "  and `EXAMPLE.lean` first. Long linter warnings can push errors out of the shown\n"
    "  output; put `set_option linter.unusedVariables false`, `linter.unusedSimpArgs false`\n"
    "  and `linter.deprecated false` at the top of your file.")
assert "ATransferAll" in TASK and "end of `RSoftKit.lean`" in TASK


def build(tname, rname, seed, split, cap=12):
    c = r7.task(tname)
    src = os.path.join(HERE, "runs", "r7-stage0", tname, rname, "s%03d" % seed)
    W, T = json.load(open(os.path.join(src, "W.json"))), json.load(open(os.path.join(src, "T.json")))
    sc = json.load(open(os.path.join(src, "screen.json")))
    assert sc["pass"], "network did not pass the screen"
    cid = "%s-%s-s%03d" % (tname, rname, seed)
    d = os.path.join(HERE, "runs", "rung7-" + split, cid)
    if os.path.exists(os.path.join(d, "case.json")):
        raise SystemExit("exists: " + d)
    os.makedirs(os.path.join(d, "scratch"), exist_ok=True)
    _, text = task_parts(c)
    gate_note = ("\nIn this network the gate parameters are the constants `g = 0`, `gb = -1`: every key is always a\n"
                 "candidate (the gate is open; it only has to be shown to stay 0 under the perturbation)." if tname == "A" else
                 "\nIn this network the gates were trained: find out which tokens each head's gate removes.")
    cases = ("for this task: the token at `i` and the token at `i - 1`, BOS included" if tname == "A" else
             "for this task: the token at `i`, and which token is the nearest candidate of each head, if any")
    fmt = dict(text=text, V=c["V"], V1=c["V"] + 1, py=M4.PY, submit=M4.SUBMIT, casedir=d.replace("\\", "/"), cap=cap,
               gate_note=gate_note, cases=cases, inside=max(sc["W_inside_ball_dev"].values()), breaks=sc["W_breaks_at_multiple"])
    files = {"TASK.md": TASK.format(**fmt), "Spec.lean": spec(c, W, T),
             "Final.lean": M6.final_net(c["V"]) + FINAL_TRAINED.replace("{V}", str(c["V"])),
             "EXAMPLE.lean": open(os.path.join(HERE, "examples", "EXAMPLE_r6a_net.lean"), encoding="utf-8").read()}
    for name, txt in files.items():
        open(os.path.join(d, name), "w", encoding="utf-8", newline="\n").write(txt)
    shutil.copyfile(os.path.join(src, "W.json"), os.path.join(d, "net.json"))
    shutil.copyfile(os.path.join(HERE, "tools", "r6net.py"), os.path.join(d, "r6net.py"))
    meta = {"id": cid, "arm": "net", "rung": 7, "split": split, "task": tname, "family": c["family"], "import": "ATransferAll",
            "delta": "1/1000", "max_attempts": cap, "lean_timeout": 600,
            "final_theorems": ["Lane4Final.final", "Lane4Final.shape", "Lane4Final.exact_all_lengths", "Lane4Final.binary32",
                               "Lane4Final.trained_exact_all_lengths", "Lane4Final.trained_binary32"]}
    json.dump(meta, open(os.path.join(d, "case.json"), "w", encoding="utf-8"), indent=1)
    for f in ("Basic", "Seq", "RSeq", "RSoft", "RSoftKit", "AGate", "AGateKit", "AGateKitW", "ATransfer"):
        shutil.copyfile(os.path.join(HERE, "Lane4", f + ".lean"), os.path.join(d, f + ".lean"))
    print("built", d)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    build(sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4])
