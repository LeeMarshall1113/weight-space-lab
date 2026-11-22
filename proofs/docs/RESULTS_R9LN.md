# Rung 9-LN result: stopped at K2 (the enclosure accepts 5 of 18 at the registered ball; the line is 6)

Written 2026-11-21 (Saturday night EST). Registered in `PREREG_R9LN.md`.

**K1 passed (18 of 20 tuning networks compute the task and pass the screen, recipe n1). K2 fired:
after the three registered design changes, the exact-rational prototype accepts 5 of the 18
screened tuning networks at the registered ball 2^-14. The registered line is "fewer than 6". No
Lean was written for this rung, no doctor tokens were spent, no fresh seed was touched. The ball
was not amended and nothing new was registered.**

It is one network short, and the same prototype accepts 13 of 18 at half the radius. That is a
tuning observation, not a result: any rung at a smaller ball is a new registration that must
disclose it was chosen after seeing this table.

## K2 counts by design (18 screened tuning networks, seeds 100 to 119 less 110 and 111)

| design | what changed | accepted at 2^-14 |
|---|---|---|
| 1 | rung-8 absolute rounding charges, interval LayerNorm | 0 |
| 2 (change 1) | relative rounding inside LayerNorm | 0 |
| 3 (change 2) | relative rounding in dot products | 0 |
| 4 (change 3, last) | one symbol per perturbed weight on the value path, LayerNorm linearised with second-order remainders | **5** (102, 104, 115, 116, 118) |

## Radius sweep (numeric interval test on every accepted network: 0 violations in every cell)

| ball radius | design 3 | design 4 |
|---|---|---|
| 2^-14 (registered) | 0 | 5 |
| 2^-15 | 0 | 13 |
| 2^-16 | 0 | 15 |
| 2^-17 | 0 | 15 |
| 2^-18 | 1 | 16 |
| 2^-20 | 10 | 16 |
| 0 (no ball) | 14 | 16 |

Seeds 108 and 109 are rejected at every radius including 0, so their obstacle is rounding and
attention tails, not the ball.

Where the bound goes at 2^-14 under design 4, on the 13 rejections: the ball's first-order
contribution (the symbols) is 0.01 to 0.15; the rest of the radius (rounding, attention tails,
LayerNorm remainders, which also grow with the ball) is 0.16 to 1.06 and is the larger part in
all 13. With no ball at all that rest is still 0.08 to 0.15 on the accepted networks, against a
limit of 1/4 less the network's own error of about 0.03.

## Cost of making each path sound (judgement, not measured)

| path | new proof work beyond the planned LayerNorm rung | kit cases | Sonnet tokens | kernel |
|---|---|---|---|---|
| design 3 (relative rounding constants) | relative-error forms of the rounding lemmas for sums, products, division, square root | +2 | +0.3 to 0.6M | as rung 8 plus square roots |
| design 4 (symbolic tracking) | the above, plus affine forms with a few hundred symbols, exact linear maps on them, linearised LayerNorm with a second-order remainder (the lemma the stronger-model step is reserved for) | +4 to 6 | +1 to 2M, so 3 to 5M in all against the 2 to 3.5M approved | **likely fails K3 as designed** |

The kernel line is the serious one. In the Python prototype a 155-row network takes 1.2 to 1.8 s
with 2 to 4 symbols (radius 0) and 35 to 45 s with about 360 symbols: 25 to 30 times more
arithmetic per row. Rung 8 measured about 1 s per row in the kernel, so 155 rows would be on the
order of an hour against a K3 budget of 4 files of 900 s, and the two 780-row networks would be
far outside it. The symbol count would have to come down by about ten times (merging symbols that
never cancel) before a Lean checker is worth writing. That reduction was not tried.

## Which radius I would register, if an amended rung is wanted

**2^-15 around W14, with design 4.** Reasons: (1) rounding a weight to the 2^-14 grid moves it by
at most 2^-15, so this is the smallest ball around W14 that still contains the trained float32
network itself, which is the property that gives the ball its meaning; (2) 13 of 18 on tuning
networks, enough margin over a bar of 2 of the first 3; (3) nothing else in the registration
changes. A 2^-20 ball would need a finer skeleton grid to contain the trained network and covers
only 8 float32 steps near 1 (float32 spacing near 1 is 2^-23), so it says little more than
"this network, in the rounding model"; I would not register it when 2^-15 works. Design 3 at
2^-20 (10 of 18) is the cheap-proof alternative and is the one I would pick only if the symbol
count cannot be brought down.

I would not register either before the symbol-reduction step is prototyped and one kernel probe
shows a 155-row file inside 900 s. Both are free of doctor tokens.

## What this does and does not show

- It shows that a sound enclosure of LayerNorm on the residual stream is numerically feasible for
  these networks (16 of 18 with no ball, interval test clean), and that the weight ball, not
  LayerNorm itself, is what the registered radius could not carry.
- It does not show any theorem. Everything here is a Python prototype in exact rationals plus a
  sampling test. No Lean exists for the model, the checker or the lemmas.
- The 18 networks are tuning networks and four designs were fitted to them.

## Files

`PREREG_R9LN.md`, `tools/r9ln.py`, `tools/r9ln_proto.py` (design 3), `tools/r9ln_proto4.py`
(design 4), `scratch/r9ln_proto_v1.py`, `scratch/r9ln_proto_v2.py`, `runs/r9ln-tune/`,
`results/rung9ln-proto-*.json`, `results/rung9ln-proto4-*.json`, `logs/r9ln-proto*.log`,
`scratch/freeze_r9ln.sha256`.

## Addendum, 2026-11-22 early morning EST: feasibility step toward a 2^-15 rung

The rung above stays stopped at K2. This addendum is a free feasibility step for a possible NEW,
post-hoc rung; nothing is registered, no soundness Lean was written, no doctor tokens were spent,
no fresh seed was touched.

**1. Fewer symbols** (`tools/r9ln_proto4r.py`; 18 screened tuning networks; interval test on every
accepted network, 0 violations in every cell):

| variant | symbols per accepted network | accepted at 2^-15 | accepted at 2^-14 |
|---|---|---|---|
| design 4 as run before | 339 to 383 | 13 | 5 |
| mode 1: merges that lose nothing | 178 to 197 | 13 | 5 |
| **mode 2: also one symbol per head value** | **40 to 45** | **13** | **5** |
| mode 3: also LN2 gain/bias and attention symbols to the radius | 33 | 1 | 1 |
| mode 4: also W1 to the radius | 25 | 1 | 0 |

Mode 2 accepts exactly the networks design 4 accepts (2^-15: 100 to 105, 107, 112 to 116, 118;
2^-14: 102, 104, 115, 116, 118) with about 8.7 times fewer symbols. Going further loses nearly
everything, so about 42 symbols is the floor for this design.

**2. Kernel timing probe** (`tools/make_ln_probe.py`, files and logs in `scratch/lnprobe/`; a
synthetic workload, not a checker: one `decide +kernel` theorem per row doing the arithmetic
volume of one mode-2 row with 44 symbols, in integers scaled by 2^56; 5 GB reservation, one job at a
time):

| file | time | peak commit | within 900 s / 6 GB |
|---|---|---|---|
| 8 rows, deviations recomputed in every dot product | 126.8 s | 4.41 GB | yes (14.7 s per row) |
| 8 rows, deviations once per row | 36.7 s | 4.41 GB | yes (3.5 s per row) |
| **155 rows, deviations once per row** | **418.8 s** | **4.62 GB** | **yes (2.65 s per row)** |

So a 155-row network's volume fits one file with about half the time to spare. What the probe
leaves out: the head tables, the case enumeration and the exponential enclosures (the whole of
rung 8's roughly 1 s per row), so a real file is more like 570 to 600 s. The two 780-row tuning
networks (113, 114) would need about 2,100 s by the probe and about 2,900 s with the rung-8 part
added: 3 to 4 files, at the edge of a four-file rule. The probe is in fixed point; a checker in
ℚ would be about four times slower (E2) and would not fit, so fixed-point arithmetic becomes part
of what has to be proved sound. The first probe version shows how sensitive the time is to how
the checker is written (a factor of four from one repeated sum).

