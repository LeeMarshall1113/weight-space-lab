"""Rung-3 results from attempt logs, exports and lane checks.

    python tools/collect3.py      -> results/rung3-test.json + printed table
"""
import glob, json, os, statistics as st
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root = os.path.join(HERE, "runs", "rung3-test")
rows = []
for arm in ("net", "prog", "twin"):
    for d in sorted(glob.glob(os.path.join(root, arm, "*"))):
        r = {"id": os.path.basename(d), "arm": arm, "submissions": 0, "pass": False, "lean_secs": 0.0,
             "native_decide_attempts": 0, "banned_rejections": 0, "timeouts": 0, "mem_kills": 0}
        for p in sorted(glob.glob(os.path.join(d, "attempts", "*.json"))):
            a = json.load(open(p, encoding="utf-8"))
            if a.get("pending"):
                continue
            r["submissions"] += 1
            r["lean_secs"] += a.get("secs", 0) or 0
            r["native_decide_attempts"] += bool(a.get("native_decide_attempted"))
            r["banned_rejections"] += str(a.get("reason", "")).startswith("banned")
            r["timeouts"] += bool(a.get("timed_out")); r["mem_kills"] += bool(a.get("mem_killed"))
            if a.get("pass") and not r["pass"]:
                r["pass"] = True
                r["solution_lines"] = len(open(p[:-5] + ".lean", encoding="utf-8").read().splitlines())
        r["lean_secs"] = round(r["lean_secs"], 1)
        ck = os.path.join(d, "r3_checks.json")
        if os.path.exists(ck):
            c = json.load(open(ck))
            ft = c["finetune"]
            r.update(delta=c["delta"], hidden_widths=c["hidden_widths"], max_abs_weight=c["max_abs_weight"],
                     written_net_max_dev=c["written_net_max_dev"], inside_ball_max_dev=max(c["inside_ball_max_dev"].values()),
                     inside_ball_ok=c["inside_ball_ok"], smallest_violating_multiple=c["smallest_violating_multiple"],
                     float32_max_dev=c["float32_max_dev_from_spec"], finetune_gains=[ft[s]["gain_vs_program"] for s in "012"],
                     finetune_median_gain=c["finetune_median_gain"],
                     finetune_all_inside_ball=all(ft[s]["inside_ball"] for s in "012"),
                     finetune_all_within_delta=all(ft[s]["within_delta"] for s in "012"),
                     unconstrained_gains=[1 - ft[s]["unconstrained"]["mse_finetuned"] / ft[s]["mse_spec_program"] for s in "012"],
                     unconstrained_max_move=max(ft[s]["unconstrained"]["max_weight_move"] for s in "012"),
                     unconstrained_leaves_delta=[ft[s]["unconstrained"]["leaves_delta"] for s in "012"])
        rows.append(r)
json.dump(rows, open(os.path.join(HERE, "results", "rung3-test.json"), "w"), indent=1)
for arm in ("net", "prog", "twin"):
    rs = [r for r in rows if r["arm"] == arm and r["submissions"]]
    if not rs:
        continue
    subs = sorted(r["submissions"] for r in rs)
    print("%s: %d/%d pass | subs %s median %s | lean s median %s | lines %s | nd %d banned %d timeouts %d memkills %d" % (
        arm, sum(r["pass"] for r in rs), len(rs), subs, st.median(subs), st.median(r["lean_secs"] for r in rs),
        sorted(r.get("solution_lines", 0) for r in rs), sum(r["native_decide_attempts"] for r in rs),
        sum(r["banned_rejections"] for r in rs), sum(r["timeouts"] for r in rs), sum(r["mem_kills"] for r in rs)))
print("id    widths        delta  written  in-ball  ratio  breaks@  f32      ft gain (median)  uncon gain  uncon move")
for r in rows:
    if r["arm"] == "net" and "delta" in r:
        print("%-5s %-13s %.2f   %.3f    %.3f    %.2f   %3s      %.1e  %6.1f%%           %5.1f%%      %.3f" % (
            r["id"], r["hidden_widths"], r["delta"], r["written_net_max_dev"], r["inside_ball_max_dev"],
            r["inside_ball_max_dev"] / r["delta"], r["smallest_violating_multiple"], r["float32_max_dev"],
            100 * r["finetune_median_gain"], 100 * st.median(r["unconstrained_gains"]), r["unconstrained_max_move"]))
