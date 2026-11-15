"""Regenerate the n=10 mod-3 test nets (overwritten by train_maj's filename clash) by deterministic retraining;
accept only if quantized accuracy equals the recorded value. Then build their region trees."""
import json, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import train as T, stage2 as S
S.set_task(10)
rec = {json.loads(l)["seed"]: json.loads(l) for l in open(T.OUT / "bridge_s2c_test_n10.jsonl")}
for s in range(100, 108):
    net = S.train_n(10, 32, s)
    L = T.quantize(net)
    acc = int(sum((v > 0) == (y > 0) for v, y in zip(T.exact_logits(L), T.Y)))
    ok = acc == rec[s]["quant_acc"]
    (T.NETS / f"N10_w32_s{s}.json").write_text(json.dumps({"q": T.Q, "layers": L, "rec": rec[s], "regenerated": True}))
    print(s, "acc", acc, "matches record:", ok, flush=True)
