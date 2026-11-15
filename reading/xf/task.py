"""Doctor tasks for the transformer stage (PREREG_XF.md): write a RASP program that
reproduces a trained transformer.

Conditions (kwarg `cond`):
  W         weights.npz + architecture + unlimited black-box queries
  IO-unlim  unlimited black-box queries, no weights
  IO-20     20 fixed input/output examples in the spec, no queries, no weights
Case data lives in reading/xf/cases/<id>/ (program.txt is the secret true program).
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from wsp_harness.core import Task
from xf import model as M
from xf import rasp as R
from xf.gen import sample_inputs

CASES = Path(__file__).resolve().parent / "cases"
CASES_T = Path(__file__).resolve().parent / "cases_tracr"

TRACR_SPEC = """Tracr-compiled transformer (weight names in weights.npz, '__' separates parts):
  input = ["BOS"] + tokens;  row index of each input = its position in INPUT_ORDER below
  x = token_embed__embeddings[ids] + pos_embed__embeddings[0:len]
  for each layer name in LAYERS, in order:
    *attn:  q = x Wq + bq, k = x Wk + bk, v = x Wv + bv   (transformer__<layer>__query__w/b, key, value)
            split q,k,v into NUM_HEADS equal column blocks; per head a = softmax(q_h k_h^T) (no
            scaling, no mask), out_h = a v_h;  x = x + concat_h(out_h) linear__w + linear__b
    *mlp:   x = x + relu(x linear_1__w + linear_1__b) linear_2__w + linear_2__b
  output at token position i (i >= 1, i.e. skipping BOS) = CLASSES[argmax(x[i] @ unembed)]
"""


def np_forward_tracr(w, meta, toks):
    ids = [meta["input_order"].index(t) for t in ["BOS"] + list(toks)]
    x = w["token_embed__embeddings"][ids] + w["pos_embed__embeddings"][: len(ids)]
    H = meta["num_heads"]
    for layer in meta["layers"]:
        p = f"transformer__{layer}"
        if layer.endswith("attn"):
            q = x @ w[p + "__query__w"] + w[p + "__query__b"]
            k = x @ w[p + "__key__w"] + w[p + "__key__b"]
            v = x @ w[p + "__value__w"] + w[p + "__value__b"]
            dk, dv = q.shape[1] // H, v.shape[1] // H
            outs = []
            for h in range(H):
                a = q[:, h * dk:(h + 1) * dk] @ k[:, h * dk:(h + 1) * dk].T
                a = np.exp(a - a.max(1, keepdims=True))
                a /= a.sum(1, keepdims=True)
                outs.append(a @ v[:, h * dv:(h + 1) * dv])
            x = x + np.concatenate(outs, 1) @ w[p + "__linear__w"] + w[p + "__linear__b"]
        else:
            x = x + np.maximum(x @ w[p + "__linear_1__w"] + w[p + "__linear_1__b"], 0) @ w[p + "__linear_2__w"]                 + w[p + "__linear_2__b"]
    return [meta["classes"][i] for i in (x @ w["unembed"])[1:].argmax(1)]


def run_program(src: str):
    import sys
    sys.modules.setdefault("rasp", R)  # the spec tells doctors to `from rasp import *`
    ns = {k: getattr(R, k) for k in R.__all__}
    exec(src, ns)  # noqa: S102 - doctor-written RASP, run in the harness on purpose
    if "out" not in ns:
        raise ValueError("program must define `out`")
    return ns["out"]


class XFTask(Task):
    name = "xf_decompile"

    def __init__(self, case_id: str, cond: str, kind: str = "trained"):
        self.case_id, self.cond, self.kind = case_id, cond, kind
        d = (CASES_T.parent / f"cases_{kind}" if kind.startswith(("tracr", "trained_")) else CASES) / case_id
        self.dir = d
        self.meta = json.loads((d / "meta.json").read_text())
        self.w = dict(np.load(d / "weights.npz"))
        self.vocab, self.classes = self.meta["vocab"], self.meta["classes"]

    def _pred(self, x):
        if self.kind.startswith("tracr"):
            return np_forward_tracr(self.w, self.meta, list(x))
        return M.predict(self.w, list(x), self.vocab, self.classes, self.meta["n_layers"], self.meta["n_heads"])

    def spec(self):
        v = ", ".join(repr(t) for t in self.vocab)
        common = f"""# Task: write a RASP program that reproduces a trained transformer

A small transformer maps a sequence of tokens (vocabulary {{{v}}}, length 4-8) to one output
per position (output values {self.classes}). It was trained with gradient descent on some
unknown RASP-expressible function. Write a RASP program whose output equals the network's
output on every input of length 4-8.

RASP: use only the names in rasp.py in your work directory (they match tracr.rasp):
tokens, indices, Map, SequenceMap, Select, Aggregate, SelectorWidth, Comparison.{{EQ,LT,LEQ,
GT,GEQ,NEQ,TRUE,FALSE}}, numerical, categorical, Full. Select(keys, queries, cmp) selects key
position k for query position q when cmp(key, query); Comparison.LT means key < query.
Categorical Aggregate needs all selected values to agree (else undefined). Test locally:
    from rasp import *; exec(open('program.py').read()); print(evaluate(out, list('{self.vocab[0] * 4}')))

Answer: a file program.py that defines `out` (an SOp). Submit with `submit --answer program.py`.
Scored on exact whole-sequence agreement with the network on 1000 held-out inputs.
"""
        if self.cond == "IO-5":
            return common + f"""
You do NOT get the weights. You may query the network as a black box, but only 5 inputs in
total: `query '[["{self.vocab[0]}", "{self.vocab[-1]}", "{self.vocab[0]}", "{self.vocab[0]}"]]'` (or `query @file.json`); each input costs 1 of 5.
Choose them carefully.
"""
        if self.cond in ("W0", "W5"):
            arch = (TRACR_SPEC + f"""
INPUT_ORDER = {self.meta["input_order"]}
LAYERS = {self.meta["layers"]}
NUM_HEADS = {self.meta["num_heads"]}
CLASSES = {self.meta["classes"]}""") if self.kind.startswith("tracr") else M.SPEC
            return common + f"""
You have the network's weights (weights.npz) and its exact equations:
{arch}
{"You may query the network as a black box, but only 5 inputs in total (each costs 1 of 5): `query '[[...]]'` or `query @file.json`. Choose them to test what you read in the weights. Apart from those 5 queries, the rule below applies." if self.cond == "W5" else "You get NO queries and NO examples."} RULE: you may NOT run the network on token sequences:
no full forward pass on any input, no loop over input strings through the layers. Instead
analyse the weight matrices themselves (embedding and position tables, query-key and
value-output products between embedding/position rows, attention patterns computed from
those rows, what the MLPs do to particular residual directions) and infer the program.
Running the network on inputs voids the run (the harness audits your code).
"""
        if self.cond == "W" and self.kind == "tracr":
            return common + f"""
This network was compiled (not trained): its weights are exact. You have them (weights.npz)
and the exact equations:
{TRACR_SPEC}
INPUT_ORDER = {self.meta["input_order"]}
LAYERS = {self.meta["layers"]}
NUM_HEADS = {self.meta["num_heads"]}
CLASSES = {self.meta["classes"]}
You may also query the network as a black box:
`query '[["{self.vocab[0]}", "{self.vocab[-1]}", "{self.vocab[0]}", "{self.vocab[0]}"]]'` (or `query @file.json`) returns its outputs; the query
budget is effectively unlimited. Use the weights: the point of this condition is to read them.
"""
        if self.cond == "W":
            return common + f"""
You have the network's weights (weights.npz, also weights.txt) and its exact equations:
{M.SPEC}
Token index = position of the token in the vocabulary list above; class index = position of
the value in the output-values list. You may also query the network as a black box:
`query '[["{self.vocab[0]}", "{self.vocab[-1]}", "{self.vocab[0]}", "{self.vocab[0]}"]]'` (or `query @file.json`) returns its outputs; the query
budget is effectively unlimited. Use the weights: the point of this condition is to read them.
"""
        if self.cond == "IO-unlim":
            return common + f"""
You do NOT get the weights. You may query the network as a black box, as much as you like:
`query '[["{self.vocab[0]}", "{self.vocab[-1]}", "{self.vocab[0]}", "{self.vocab[0]}"]]'` (or `query @file.json`) returns its outputs.
"""
        rng = np.random.default_rng(int(self.meta["prog_seed"]) + 17)
        ex = sample_inputs(rng, self.vocab, 20)
        rows = "\n".join(f"  {''.join(x)} -> {self._pred(x)}" for x in ex)
        return common + f"""
You do NOT get the weights and you cannot query the network. Here are 20 input/output pairs
(input written as a string, one token per character; output is a list, one value per position):
{rows}
"""

    def initial_weights(self):
        return self.w

    def weights_text(self, weights, decimals=3):
        if self.cond != "W":
            return "(no weights in this condition)"
        return super().weights_text(weights, decimals)

    def forward(self, weights, queries):
        if self.cond == "IO-20":
            return ["queries are not available in this condition"] * len(queries)
        out = []
        for q in queries:
            q = list(q) if not isinstance(q, str) else list(q)
            if not (4 <= len(q) <= 8) or any(t not in self.vocab for t in q):
                out.append("invalid input (length 4-8, tokens from the vocabulary)")
            else:
                out.append(self._pred(q))
        return out

    def final_score(self, weights, answer):
        rng = np.random.default_rng(424242)
        xs = sample_inputs(rng, self.vocab, 1000)
        net = [self._pred(x) for x in xs]
        true = run_program((self.dir / "program.txt").read_text())
        tru = [R.evaluate(true, x) for x in xs]
        res = {"case_id": self.case_id, "cond": self.cond, "template": self.meta["template"]}
        err = None
        try:
            prog = run_program(answer["program"]) if answer else None
            got = [R.evaluate(prog, x) for x in xs] if prog is not None else None
        except Exception as e:  # malformed program = failure
            got, err = None, repr(e)[:300]
        if got is None:
            return {**res, "seq_agree": 0.0, "tok_agree": 0.0, "functional": False, "error": err,
                    "seq_agree_true": 0.0}
        seq = float(np.mean([g == n for g, n in zip(got, net)]))
        tok = float(np.mean([a == b for g, n in zip(got, net) for a, b in zip(g, n)]))
        return {**res, "seq_agree": seq, "tok_agree": tok, "functional": seq >= 0.99, "error": err,
                "seq_agree_true": float(np.mean([g == t for g, t in zip(got, tru)])),
                "program_lines": len([l for l in answer["program"].splitlines() if l.strip()])}
