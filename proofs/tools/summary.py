"""Per-arm summary of results/rung1-test.json (written by collect.py).

    python tools/summary.py [results/rung1-test.json]
"""
import glob, json, os, statistics as st, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "results", "rung1-test.json")
rows = json.load(open(path))
for arm in ("net", "prog", "twin"):
    r = [x for x in rows if x["arm"] == arm]
    done = [x for x in r if x["submissions"] > 0]
    p = [x for x in r if x["pass"]]
    kills = 0
    for f in glob.glob(os.path.join(HERE, "runs", "rung1-test", arm, "*", "attempts", "*.json")):
        kills += bool(json.load(open(f, encoding="utf-8")).get("mem_killed"))
    print("%s: cases %d, attempted %d, pass %d" % (arm, len(r), len(done), len(p)))
    if not done:
        continue
    subs = sorted(x["submissions"] for x in done)
    print("  submissions sorted %s  median %s  total %d" % (subs, st.median(subs), sum(subs)))
    print("  lean seconds total %d, median per case %s" % (sum(x["lean_secs"] for x in done),
                                                          st.median(x["lean_secs"] for x in done)))
    print("  timeouts %d, memory kills %d, native_decide attempts %d, banned rejections %d, peak commit %.2f GB" % (
        sum(x["timeouts"] for x in done), kills, sum(x["native_decide_attempts"] for x in done),
        sum(x["banned_rejections"] for x in done), max(x["max_peak_commit_gb"] for x in done)))
    if p:
        ln = sorted(x["solution_lines"] for x in p)
        print("  solution lines of passing cases: median %s, range %d-%d" % (st.median(ln), ln[0], ln[-1]))
    if arm == "net" and p:
        for k in ("hidden_layers", "hidden_units", "nonzero_weights"):
            v = sorted(x[k] for x in p)
            print("  %s: median %s, range %d-%d" % (k, st.median(v), v[0], v[-1]))
        print("  float32 max deviation %.2e, exact mismatches at 10k points %d" % (
            max(x["float32_max_dev"] for x in p), sum(x["exact_mismatches_10k"] for x in p)))
    if arm == "twin":
        print("  failed: %s" % [x["id"] for x in done if not x["pass"]])
        print("  not attempted: %s" % [x["id"] for x in r if x["submissions"] == 0])
