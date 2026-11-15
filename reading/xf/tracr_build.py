"""Tracr calibration set (PREREG_XF.md): compile the next 20 acceptable pool programs
(seed 20261112) and save doctor-visible weights + a validated numpy forward description.

Run with the Tracr venv:  .venv-tracr/Scripts/python xf/tracr_build.py
Writes xf/cases_tracr/<id>/{weights.npz, program.txt, meta.json} and xf/cases_tracr_20261112.json.
Residual-dimension labels (which name the program's variables) are NOT saved where the doctor
can see them; only the input order, the output dims and the layer order are.
"""
import hashlib
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from tracr.compiler import compiling  # noqa: E402
from tracr.rasp import rasp as TR  # noqa: E402

from xf import gen  # noqa: E402

OUT = HERE / "cases_tracr"
NAMES = ["tokens", "indices", "Map", "SequenceMap", "Select", "Aggregate", "SelectorWidth",
         "Comparison", "numerical", "categorical", "Full"]


def compile_src(src, vocab):
    ns = {k: getattr(TR, k) for k in NAMES}
    exec(src, ns)
    m = compiling.compile_rasp_to_model(ns["out"], vocab=set(vocab), max_seq_len=8, compiler_bos="BOS")
    return m, ns["out"].label


def np_forward(w, meta, toks):
    """Doctor-facing description, validated against model.apply below."""
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
            hdn = np.maximum(x @ w[p + "__linear_1__w"] + w[p + "__linear_1__b"], 0)
            x = x + hdn @ w[p + "__linear_2__w"] + w[p + "__linear_2__b"]
    logits = x @ w["unembed"]
    return [meta["classes"][i] for i in logits[1:].argmax(1)]


def main():
    OUT.mkdir(exist_ok=True)
    stream = gen.draw(40, 20261112)
    cases, replaced = [], []
    for _, src, info in stream:
        if len(cases) == 20:
            break
        try:
            m, out_name = compile_src(src, info["vocab"])
        except Exception as e:
            replaced.append({"seed": info["seed"], "why": repr(e)[:200]})
            continue
        w = {k.replace("/", "__") + "__" + kk: np.asarray(v, dtype=np.float64)
             for k, d in m.params.items() for kk, v in d.items()}
        labels = [str(l) for l in m.residual_labels]
        enc_out = m.output_encoder.encoding_map  # value -> index
        classes = [v for v, _ in sorted(enc_out.items(), key=lambda kv: kv[1])]
        U = np.zeros((len(labels), len(classes)))
        for j, c in enumerate(classes):
            hit = [i for i, l in enumerate(labels) if l == f"{out_name}:{c}"]
            U[hit[0], j] = 1.0
        w["unembed"] = U
        enc = m.input_encoder.encoding_map
        input_order = [t for t, _ in sorted(enc.items(), key=lambda kv: kv[1])]
        layers = sorted({k.split("/")[1] + "/" + k.split("/")[2] for k in m.params if k.startswith("transformer/")},
                        key=lambda s: (int(s.split("/")[0].split("_")[1]), s.split("/")[1] != "attn"))
        layers = [l.replace("/", "__") for l in layers]
        meta = {"vocab": info["vocab"], "classes": classes, "input_order": input_order,
                "num_heads": int(m.model_config.num_heads), "layers": layers, "template": info["template"],
                "prog_seed": info["seed"], "d_resid": len(labels)}
        # validate the numpy description against tracr on random inputs
        rng = np.random.default_rng(0)
        bad = 0
        for x in gen.sample_inputs(rng, info["vocab"], 60):
            if np_forward(w, meta, x) != m.apply(["BOS"] + x).decoded[1:]:
                bad += 1
        if bad:
            replaced.append({"seed": info["seed"], "why": f"numpy forward mismatch on {bad}/60"})
            continue
        cid = hashlib.sha1(f"tracr-{info['seed']}".encode()).hexdigest()[:8]
        d = OUT / cid
        d.mkdir(exist_ok=True)
        np.savez(d / "weights.npz", **w)
        (d / "program.txt").write_text(src)
        (d / "residual_labels.json").write_text(json.dumps(labels))  # secret, never in work/
        meta["case_id"] = cid
        (d / "meta.json").write_text(json.dumps(meta, indent=1))
        cases.append(meta)
        print(cid, info["template"], len(labels), "dims", len(layers), "layers")
    (HERE / "cases_tracr_20261112.json").write_text(json.dumps({"seed": 20261112, "cases": cases,
                                                                 "replaced": replaced}, indent=1))
    print(len(cases), "cases;", len(replaced), "replaced")


if __name__ == "__main__":
    main()
