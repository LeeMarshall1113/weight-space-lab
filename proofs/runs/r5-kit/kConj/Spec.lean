namespace Lane4.Conj

/-! ## A. Parity has no length-independent relative weight ball (rung-2 architecture)

Architecture class: `Lane4.Seq.TNet` (hard attention with ties averaged, eight position
features `1, i, i^2, 1/(i+1), (-1)^i, n, 1/n, i/n`, residual ReLU MLP, affine read-out),
within the shape limits of `TNet.shapeOK` (at most 4 blocks, 4 heads, width 24, hidden 32).
Perturbation: relative, every weight `w` replaced by some `w'` with `|w' - w| ≤ τ * |w|`
(so written zeros stay zero). -/

section parity
open Lane4.Seq

def qRel (τ a b : ℚ) : Prop := |b - a| ≤ τ * |a|
def vRel (τ : ℚ) (a b : List ℚ) : Prop := List.Forall₂ (qRel τ) a b
def mRel (τ : ℚ) (A B : List (List ℚ)) : Prop := List.Forall₂ (vRel τ) A B
def hRel (τ : ℚ) (h g : Head) : Prop := mRel τ h.A g.A ∧ mRel τ h.V g.V ∧ h.mask = g.mask
def bRel (τ : ℚ) (B C : Block) : Prop :=
  List.Forall₂ (hRel τ) B.heads C.heads ∧ mRel τ B.W1 C.W1 ∧ vRel τ B.b1 C.b1 ∧
  mRel τ B.W2 C.W2 ∧ vRel τ B.b2 C.b2
/-- `N'` is inside the relative ball of radius `τ` around `N`. -/
def netRel (τ : ℚ) (N N' : TNet) : Prop :=
  mRel τ N.embed N'.embed ∧ List.Forall₂ (bRel τ) N.blocks N'.blocks ∧
  vRel τ N.outW N'.outW ∧ qRel τ N.outB N'.outB

/-- The network decides, by the sign of its output at the last position, whether the
number of tokens equal to 1 is even (tokens are 1 and 2). -/
def ComputesParity (N : TNet) (w : List ℕ) : Prop :=
  0 < N.out w w.length ↔ Even (w.count 1)

/-- Every network in the relative ball of radius `τ` around `N` computes parity on every
input of length 1 to `L`. -/
def ParityOnBall (N : TNet) (τ : ℚ) (L : ℕ) : Prop :=
  ∀ N', netRel τ N N' → ∀ w : List ℕ, (∀ t ∈ w, t = 1 ∨ t = 2) →
    1 ≤ w.length → w.length ≤ L → ComputesParity N' w

/-- CONJECTURE A1. No network in the class has a relative ball of positive radius on
which parity is computed at every length. -/
def ParityNoBall : Prop :=
  ∀ N : TNet, N.shapeOK 2 = true → ∀ τ : ℚ, 0 < τ → ∃ L : ℕ, ¬ ParityOnBall N τ L

/-- CONJECTURE A2 (quantitative; less certain than A1). The radius shrinks at least like
`C / L`, with one constant for the whole class. -/
def ParityRadiusBound : Prop :=
  ∃ C : ℚ, 0 < C ∧ ∀ N : TNet, N.shapeOK 2 = true → ∀ (τ : ℚ) (L : ℕ),
    0 ≤ τ → 1 ≤ L → ParityOnBall N τ L → τ * (L : ℚ) ≤ C

end parity

/-! ## B. No length-independent ABSOLUTE weight ball in the rung-4 architecture

Architecture class: `Lane4.RSeq.TNet` in exact arithmetic (`fl = id`, zero relative
perturbation), position features `1, i, n` in the residual stream, linear read-out.
Perturbation: additive, every weight (zeros included) moved by at most `δ`.
Task: the value of the last marked token (tokens 1 and 2 are marked with values 1 and 2,
token 3 is unmarked), a task for which rung 4 has kernel-checked relative-ball theorems. -/

section absolute
open Lane4.RSeq
open Lane4.Seq (Mask)

def qAbs (δ a b : ℚ) : Prop := |b - a| ≤ δ
def vAbs (δ : ℚ) (a b : List ℚ) : Prop := List.Forall₂ (qAbs δ) a b
def mAbs (δ : ℚ) (A B : List (List ℚ)) : Prop := List.Forall₂ (vAbs δ) A B
def hAbs (δ : ℚ) (h g : Head) : Prop := mAbs δ h.A g.A ∧ mAbs δ h.V g.V ∧ h.mask = g.mask
def bAbs (δ : ℚ) (B C : Block) : Prop :=
  List.Forall₂ (hAbs δ) B.heads C.heads ∧ mAbs δ B.W1 C.W1 ∧ vAbs δ B.b1 C.b1 ∧
  mAbs δ B.W2 C.W2 ∧ vAbs δ B.b2 C.b2
/-- `N'` is inside the absolute ball of radius `δ` around `N`. -/
def netAbs (δ : ℚ) (N N' : TNet) : Prop :=
  mAbs δ N.embed N'.embed ∧ List.Forall₂ (bAbs δ) N.blocks N'.blocks ∧
  vAbs δ N.outW N'.outW ∧ qAbs δ N.outB N'.outB

/-- Value of the last marked token among the first `i` tokens (0 if none). -/
def lastMarked (w : List ℕ) (i : ℕ) : ℕ :=
  (w.take i).foldl (fun s t => if t = 1 then 1 else if t = 2 then 2 else s) 0

/-- The zero relative perturbation. -/
def pert0 : Pert :=
  { E := fun _ _ => 0, A := fun _ _ _ _ => 0, V := fun _ _ _ _ => 0, W1 := fun _ _ _ => 0,
    b1 := fun _ _ => 0, W2 := fun _ _ _ => 0, b2 := fun _ _ => 0, oW := fun _ => 0, oB := 0 }

/-- Every network in the absolute ball of radius `δ` around `N` is within 1/4 of the
target at every position of every input of length at most `L`. -/
def LastOnAbsBall (N : TNet) (δ : ℚ) (L : ℕ) : Prop :=
  ∀ N', netAbs δ N N' → ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) → w.length ≤ L →
    ∀ i, 1 ≤ i → i ≤ w.length →
      |N'.out (fun x => x) pert0 w i - ((lastMarked w i : ℕ) : ℝ)| ≤ 1 / 4

/-- CONJECTURE B1. In this architecture no network has an absolute ball of positive
radius on which the last-marked task is solved at every length. -/
def LastNoAbsBall : Prop :=
  ∀ N : TNet, N.shapeOK 3 = true → ∀ δ : ℚ, 0 < δ → ∃ L : ℕ, ¬ LastOnAbsBall N δ L

end absolute

end Lane4.Conj
