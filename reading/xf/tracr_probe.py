"""Probe: compile pool programs with tracr and print the parameter layout."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tracr.rasp import rasp as TR
from tracr.compiler import compiling
from xf import gen

progs = gen.draw(6, 20261112)
for _, src, info in progs:
    ns = {k: getattr(TR, k) for k in ["tokens", "indices", "Map", "SequenceMap", "Select", "Aggregate",
                                       "SelectorWidth", "Comparison", "numerical", "categorical", "Full"]}
    try:
        exec(src, ns)
        m = compiling.compile_rasp_to_model(ns["out"], vocab=set(info["vocab"]), max_seq_len=8, compiler_bos="BOS")
        x = ["BOS"] + info["vocab"][:1] * 2 + info["vocab"][-1:] * 3
        print(info["template"], "OK", m.apply(x).decoded, {k: {kk: v.shape for kk, v in d.items()} for k, d in list(m.params.items())[:4]}, len(m.params))
    except Exception as e:
        print(info["template"], "FAIL", repr(e)[:200])
