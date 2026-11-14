/-
Lane 4, rung 3 fixed framework: ReLU networks with PERTURBED weights. Written by the lane.

`Net` (rational written weights) is the type of Basic.lean. A perturbation is a pair of
functions
    dW : layer → row → column → ℝ        db : layer → row → ℝ
(layers are numbered 0, 1, ... through the hidden layers; the output layer has index
`N.hidden.length`). `N.evalP dW db x` runs the network over ℝ with weight
`W[l][i][j] + dW l i j` and bias `b[l][i] + db l i`. `Within τ dW db` says every
perturbation entry is at most τ in absolute value. So

    ∀ dW db, Within τ dW db → ...

quantifies over every real weight setting in the closed box of radius τ (per weight and
per bias, including the entries that are written as 0) around the written network.
-/
import Lane4.Basic

namespace Lane4

/-- `Σ_k (w[k] + d (j+k)) * x[k]` : one perturbed row applied to an input vector. -/
noncomputable def dotP : List ℚ → List ℝ → (ℕ → ℝ) → ℕ → ℝ
  | a :: w, v :: x, d, j => ((a : ℝ) + d j) * v + dotP w x d (j + 1)
  | _, _, _, _ => 0

/-- Rows `i, i+1, ...` of one perturbed affine layer. -/
noncomputable def rowsP : List (List ℚ) → List ℚ → (ℕ → ℕ → ℝ) → (ℕ → ℝ) → List ℝ → ℕ → List ℝ
  | r :: W, c :: b, dW, db, x, i =>
    (dotP r x (dW i) 0 + ((c : ℝ) + db i)) :: rowsP W b dW db x (i + 1)
  | _, _, _, _, _, _ => []

/-- The hidden layers `l, l+1, ...` with ReLU after each. -/
noncomputable def hiddenP : List Layer → (ℕ → ℕ → ℕ → ℝ) → (ℕ → ℕ → ℝ) → List ℝ → ℕ → List ℝ
  | L :: Ls, dW, db, x, l =>
    hiddenP Ls dW db ((rowsP L.W L.b (dW l) (db l) x 0).map relu) (l + 1)
  | [], _, _, x, _ => x

/-- Forward pass of the perturbed network over ℝ. -/
noncomputable def Net.evalP (N : Net) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) (x : List ℝ) : List ℝ :=
  rowsP N.out.W N.out.b (dW N.hidden.length) (db N.hidden.length) (hiddenP N.hidden dW db x 0) 0

/-- Every weight and bias perturbation is at most `τ` in absolute value. -/
def Within (τ : ℝ) (dW : ℕ → ℕ → ℕ → ℝ) (db : ℕ → ℕ → ℝ) : Prop :=
  (∀ l i j, |dW l i j| ≤ τ) ∧ (∀ l i, |db l i| ≤ τ)

/-! ### Lemma kit -/

/-- A perturbation times a bounded value is small. -/
theorem pert_abs_mul {d v τ B : ℝ} (hd : |d| ≤ τ) (hv : |v| ≤ B) : |d * v| ≤ τ * B := by
  rw [abs_mul]
  exact mul_le_mul hd hv (abs_nonneg v) (le_trans (abs_nonneg d) hd)

/-- One perturbed product against the unperturbed one. -/
theorem pert_mul {a d v v' τ e B : ℝ} (hd : |d| ≤ τ) (hv : |v' - v| ≤ e) (hB : |v| ≤ B) :
    |(a + d) * v' - a * v| ≤ |a| * e + τ * (B + e) := by
  have h1 : (a + d) * v' - a * v = a * (v' - v) + d * v' := by ring
  have h2 : |a * (v' - v)| ≤ |a| * e := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg a)
  have h3 : |v'| ≤ B + e := by
    have : v' = v + (v' - v) := by ring
    rw [this]
    exact le_trans (abs_add_le _ _) (add_le_add hB hv)
  have h4 : |d * v'| ≤ τ * (B + e) := pert_abs_mul hd h3
  rw [h1]
  exact le_trans (abs_add_le _ _) (add_le_add h2 h4)

/-- ReLU is 1-Lipschitz. -/
theorem relu_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; simp
  · rw [max_eq_right ha, max_eq_left hb, abs_le]
    constructor <;> linarith [abs_nonneg (a - b), le_abs_self (a - b), neg_le_abs (a - b)]
  · rw [max_eq_left ha, max_eq_right hb, abs_le]
    constructor <;> linarith [abs_nonneg (a - b), le_abs_self (a - b), neg_le_abs (a - b)]
  · rw [max_eq_left ha, max_eq_left hb]

/-- ReLU does not increase a perturbation. -/
theorem relu_pert {p q e : ℝ} (h : |p - q| ≤ e) : |relu p - relu q| ≤ e :=
  le_trans (relu_sub_le p q) h

/-- Three-term triangle inequality with bounds. -/
theorem abs_add3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a + b + c| ≤ A + B + C :=
  le_trans (abs_add_le _ _) (add_le_add (le_trans (abs_add_le _ _) (add_le_add ha hb)) hc)

theorem relu_nonneg' (a : ℝ) : 0 ≤ relu a := le_max_right _ _

theorem relu_le_of_le {a B : ℝ} (h : a ≤ B) (hB : 0 ≤ B) : relu a ≤ B := max_le h hB

end Lane4
