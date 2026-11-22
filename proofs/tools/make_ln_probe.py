"""Feasibility step: a kernel TIMING probe, not a checker and not soundness Lean. It writes a Lean file whose
`decide +kernel` theorems do the arithmetic volume of one design-4r table row each, on synthetic numbers:
affine forms as lists of S + 2 integers scaled by 2^56 (centre, radius, S symbol coefficients), and per row

  attention mix     8 coordinates x 4 scaled additions of value forms
  LayerNorm (x2)    mean, 8 centrings, linearised variance (8), six Newton steps for the square root,
                    8 products of two forms (2 scaled additions each), deviations (1-norms) as in the prototype
  W1                12 dot products over 8 forms, the deviations of the inputs computed once per row (the first version recomputed them in every dot product: 14.7 s per row against 3.5), and a ReLU scaling
  W2                8 dot products over 12 forms
  read-out          one dot product over 8 forms

with a floor division of every coefficient after each product, as the prototype's snapping does. One theorem per
row, as rung 8 has one lemma per state.     python tools/make_ln_probe.py <S> <rows> <out.lean>
"""
import sys
S, N, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
T = r"""/- feasibility probe (scratch; synthetic numbers; proves nothing about any network). S = %(S)d symbols, %(N)d rows. -/
import Lane4.R8Cert
set_option maxRecDepth 1000000
namespace LNProbe
abbrev Fm := List Int
def SC : Int := 2 ^ 56
def W : Nat := %(S)d + 2
def zero : Fm := List.replicate W 0
def axpy (a : Int) (x y : Fm) : Fm := List.zipWith (fun xi yi => a * xi + yi) x y
def snap (x : Fm) : Fm := x.map (fun v => v / SC)
def lin (x : Fm) : Int := x.foldl (fun s v => s + (Int.natAbs v : Int)) 0
def addRad (e : Int) : Fm → Fm
  | c :: r :: t => c :: (r + e) :: t
  | o => o
def inp (k j : Nat) : Fm := (List.range W).map fun i => (((k * 31 + j * 17 + i * 7) %% 1001 : Nat) : Int) * 2 ^ 46
def wt (k i j : Nat) : Int := ((((k * 37 + i * 11 + j * 5) %% 2001 : Nat) : Int) - 1000) * 2 ^ 46
def dot (ws : List Int) (xs : List Fm) (dv : Int) : Fm :=
  let s := (List.zip ws xs).foldl (fun acc p => axpy p.1 p.2 acc) zero
  addRad (dv / 2 ^ 15) (snap s)
def devs (xs : List Fm) : Int := xs.foldl (fun t x => t + lin x) 0
def newton (n : Int) : Nat → Int → Int
  | 0, y => y
  | m + 1, y => newton n m ((y + n / (y + 1)) / 2)
def ln (xs : List Fm) : List Fm :=
  let sum := xs.foldl (fun acc x => axpy 1 x acc) zero
  let mean := sum.map (fun v => v / 8)
  let cs := xs.map (fun x => axpy (-1) mean x)
  let v := snap (cs.foldl (fun acc c => axpy (2 * c.headD 0) c acc) zero)
  let dv := cs.foldl (fun t c => t + lin c) 0
  let g0 : Int := SC / 2 + (newton (lin v * SC) 6 SC) %% (2 ^ 54)
  let rinv := addRad (dv / 2 ^ 20) (snap (axpy (-g0) v zero))
  cs.map fun c => addRad ((lin c * lin rinv) / (SC * 2 ^ 20)) (snap (axpy (c.headD 0) rinv (axpy g0 c zero)))
def row (k : Nat) : Bool :=
  let y := (List.range 8).map fun r =>
    snap ((List.range 4).foldl (fun acc j => axpy (wt k r j) (inp (k + 100 * (j + 1)) r) acc) (axpy SC (inp k r) zero))
  let y2 := ln y
  let d2 := devs y2
  let hid := (List.range 12).map fun h =>
    let p := dot ((List.range 8).map (wt (k + 1) h)) y2 d2
    snap (axpy (SC / 2) p zero)
  let dh := devs hid
  let z := (List.zip (List.range 8) y).map fun p =>
    axpy 1 p.2 (dot ((List.range 12).map (wt (k + 2) p.1)) hid dh)
  let zf := ln z
  let o := dot ((List.range 8).map (wt (k + 3) 0)) zf (devs zf)
  decide (lin o < 2 ^ 400)
%(thms)s
end LNProbe
#print axioms LNProbe.r0
"""
thms = "\n".join("theorem r%d : row %d = true := by decide +kernel" % (k, k) for k in range(N))
open(out, "w", encoding="utf-8", newline="\n").write(T % dict(S=S, N=N, thms=thms))
print("wrote", out, "S", S, "rows", N)
