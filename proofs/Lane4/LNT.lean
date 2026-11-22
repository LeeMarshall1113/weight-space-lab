/-
Lane 4, rung 9-LN15: the trained network as a point of the ball (after Lane4/R7KT.lean, which does
this for networks without LayerNorm). Definitions and the two STATEMENTS of kit case lj.
Written by the lane. No theorems.
-/
import Lane4.LNCert

namespace Lane4.LNT
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate Lane4.LN Lane4.R7KT
open Lane4.Seq (Mask cand tokAt)

/-- `T - W`, weight by weight, LayerNorm gains and biases included. -/
noncomputable def diffPL (W T : LNNet) : LPert where
  a := diffP W.net T.net
  g1 := dq W.g1 T.g1
  b1 := dq W.b1 T.b1
  g2 := dq W.g2 T.g2
  b2 := dq W.b2 T.b2
  gf := dq W.gf T.gf
  bf := dq W.bf T.bf

/-- The zero perturbation. -/
noncomputable def zeroPL : LPert :=
  ⟨zeroP, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def sameShapeL (W T : LNNet) : Bool :=
  sameShape W.net T.net && W.g1.length == T.g1.length && W.b1.length == T.b1.length &&
  W.g2.length == T.g2.length && W.b2.length == T.b2.length &&
  W.gf.length == T.gf.length && W.bf.length == T.bf.length

def nearNetL (δ : ℚ) (W T : LNNet) : Bool :=
  nearNet δ W.net T.net && nearL δ W.g1 T.g1 && nearL δ W.b1 T.b1 &&
  nearL δ W.g2 T.g2 && nearL δ W.b2 T.b2 && nearL δ W.gf T.gf && nearL δ W.bf T.bf

/-- Statement 1: the skeleton `W` perturbed by `T - W` IS the network `T` with no perturbation:
same output for every rounding function, exponential, square root, input and position. -/
def OutShiftL : Prop :=
  ∀ (W T : LNNet), sameShapeL W T = true → ∀ (fl ex sq : ℝ → ℝ) (w : List ℕ) (i : ℕ),
    LNNet.out W fl ex sq (diffPL W T) w i = LNNet.out T fl ex sq zeroPL w i

/-- Statement 2: same shape and entrywise within `δ` gives a perturbation within `δ`. -/
def DiffWithinL : Prop :=
  ∀ (W T : LNNet) (δ : ℚ), 0 ≤ δ → sameShapeL W T = true → nearNetL δ W T = true →
    (diffPL W T).Within (δ : ℝ)

end Lane4.LNT
