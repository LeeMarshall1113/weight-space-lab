/-
Lane 4 fixed framework. Written by the lane, not by a doctor. Every case file
starts with `import Lane4.Basic`; nothing here may be changed during a run.

A network is a list of hidden affine layers (each followed by ReLU) and one
affine output layer. Weights are exact rationals. Evaluation is defined over
any linearly ordered field `K`; rung 0 uses `K = ℚ`, rung 1 uses `K = ℝ`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace Lane4

variable {K : Type} [Field K] [LinearOrder K]

/-- ReLU. -/
def relu (x : K) : K := max x 0

/-- One affine layer: one row of rational weights and one rational bias per output. -/
structure Layer where
  W : List (List ℚ)
  b : List ℚ

/-- Dot product of a rational weight row with an input vector. -/
def dot (w : List ℚ) (x : List K) : K :=
  (List.zipWith (fun (a : ℚ) (v : K) => (a : K) * v) w x).sum

/-- Affine map `x ↦ W x + b`. -/
def Layer.apply (L : Layer) (x : List K) : List K :=
  List.zipWith (fun (row : List ℚ) (c : ℚ) => dot row x + (c : K)) L.W L.b

/-- A ReLU multi-layer perceptron. -/
structure Net where
  hidden : List Layer
  out : Layer

/-- Forward pass: ReLU after every hidden layer, none after the output layer. -/
def Net.eval (N : Net) (x : List K) : List K :=
  N.out.apply (N.hidden.foldl (fun h L => (L.apply h).map relu) x)

/-! ### Shape check (so that `zipWith` never silently truncates) -/

def Layer.shapeOK (L : Layer) (nin : Nat) : Bool :=
  L.W.length == L.b.length && L.W.all (fun r => r.length == nin)

/-- Width after the hidden layers, or `none` if a layer is malformed or wider than 32. -/
def hiddenWidth : List Layer → Nat → Option Nat
  | [], n => some n
  | L :: Ls, n =>
    if L.shapeOK n && decide (L.b.length ≤ 32) then hiddenWidth Ls L.b.length else none

/-- Well-shaped, at most 6 hidden layers, each at most 32 wide, `nin` inputs, `nout` outputs. -/
def Net.shapeOK (N : Net) (nin nout : Nat) : Bool :=
  decide (N.hidden.length ≤ 6) &&
  match hiddenWidth N.hidden nin with
  | some h => N.out.shapeOK h && N.out.b.length == nout
  | none => false

/-! ### Small lemma kit (available to every doctor) -/

theorem relu_of_nonneg {a : K} (h : 0 ≤ a) : relu a = a := max_eq_left h

theorem relu_of_nonpos {a : K} (h : a ≤ 0) : relu a = 0 := max_eq_right h

section lemmas
variable [IsStrictOrderedRing K]

theorem relu_sub_relu_neg (a : K) : relu a - relu (-a) = a := by
  unfold relu
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem relu_add_relu_neg (a : K) : relu a + relu (-a) = |a| := by
  unfold relu
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring

theorem add_relu_sub (a b : K) : a + relu (b - a) = max a b := by
  unfold relu
  rcases le_total a b with h | h
  · rw [max_eq_left (by linarith), max_eq_right h]; ring
  · rw [max_eq_right (by linarith), max_eq_left h]; ring

theorem sub_relu_sub (a b : K) : a - relu (a - b) = min a b := by
  unfold relu
  rcases le_total a b with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right h]; ring

end lemmas

end Lane4
