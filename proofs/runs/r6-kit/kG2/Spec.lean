namespace Lane4.Case
open Lane4.RSeq (Vec pdot)
open Lane4.RSoft Lane4.AGate

/-- The ideal dot product: written weights (no perturbation, no rounding) times a vector. -/
noncomputable def dotQ (r : List ℚ) (x : List ℝ) : ℝ :=
  (List.zipWith (fun (a : ℚ) (v : ℝ) => (a : ℝ) * v) r x).sum

/-- The ideal dot product of two real vectors. -/
noncomputable def dotR (x y : List ℝ) : ℝ := (List.zipWith (fun (a v : ℝ) => a * v) x y).sum

/-- `x` is within `e` of `xh` entrywise, and `xh` is bounded by `X`. -/
def Close (x xh : List ℝ) (e X : ℝ) : Prop :=
  x.length = xh.length ∧ ∀ k, k < x.length → |x.getD k 0 - xh.getD k 0| ≤ e ∧ |xh.getD k 0| ≤ X

/-- A rounded dot product of additively perturbed stored weights with an approximate
vector is close to the ideal dot product of the written weights with the ideal vector.
`W` bounds the written weights, `X` the ideal entries, `e` the entry error, `δ` the
perturbation. At most 32 terms. -/
def ArdotNear : Prop :=
  ∀ (u η M δ : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  0 ≤ δ → δ ≤ 1 →
  ∀ (r : List ℚ) (x xh : List ℝ) (d : ℕ → ℝ) (W X e : ℝ),
  r.length = x.length → r.length ≤ 32 → Close x xh e X → (∀ k, |d k| ≤ δ) →
  (∀ a ∈ r, |(a : ℝ)| ≤ W) → 0 ≤ W → 0 ≤ X → 0 ≤ e →
  (W + 1) * (X + e + 1) ≤ 2 ^ 20 → 2 ^ 30 ≤ M →
    |ardot fl r x d 0 0 - dotQ r xh|
      ≤ (r.length : ℝ) * (W * e + δ * (X + e)) + (r.length : ℝ) * (W + 1) * (X + e + 1) / 2 ^ 16
        + 1 / 2 ^ 100
    ∧ |ardot fl r x d 0 0| ≤ (r.length : ℝ) * (W + 1) * (X + e + 1) * 2

/-- The same for the rounded dot product of two approximate real vectors (`pdot`). -/
def PdotNear : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ (x xh y yh : List ℝ) (X Y e1 e2 : ℝ),
  x.length = y.length → x.length ≤ 32 → Close x xh e1 X → Close y yh e2 Y →
  0 ≤ X → 0 ≤ Y → 0 ≤ e1 → 0 ≤ e2 →
  (X + e1 + 1) * (Y + e2 + 1) ≤ 2 ^ 20 → 2 ^ 30 ≤ M →
    |pdot fl x y 0 - dotR xh yh|
      ≤ (x.length : ℝ) * (e1 * (Y + e2) + X * e2) + (x.length : ℝ) * (X + e1 + 1) * (Y + e2 + 1) / 2 ^ 16
        + 1 / 2 ^ 100
    ∧ |pdot fl x y 0| ≤ (x.length : ℝ) * (X + e1 + 1) * (Y + e2 + 1) * 2

/-- Position bias: an earlier key `k < j` is behind key `j` by at least `(m - δ)` per
position, up to a rounding slack. `n` bounds all positions. -/
def BiasGap : Prop :=
  ∀ (u η M δ : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  0 ≤ δ → δ ≤ 1 →
  ∀ (h : AHead) (dm : ℝ), |dm| ≤ δ → (1 : ℝ) ≤ (h.m : ℝ) → (h.m : ℝ) ≤ 1024 →
  ∀ (n i j k : ℕ), k < j → j ≤ n → i ≤ n →
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 12 * ((n : ℝ) + 1) ≤ M →
    h.bias fl dm i k + ((h.m : ℝ) - δ) * ((j : ℝ) - (k : ℝ)) - ((h.m : ℝ) + 2) / 32 ≤ h.bias fl dm i j
    ∧ |h.bias fl dm i j| ≤ ((h.m : ℝ) + 2) * ((n : ℝ) + 1)

/-- The sum of the absolute values of a written row. -/
noncomputable def absSum (r : List ℚ) : ℝ := (r.map (fun (a : ℚ) => |(a : ℝ)|)).sum

/-- A sharper form of `ArdotNear`: the entry error `e` is multiplied by the SUM of the
absolute written weights, not by (number of entries) times (largest weight). -/
def ArdotNearAbs : Prop :=
  ∀ (u η M δ : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  0 ≤ δ → δ ≤ 1 →
  ∀ (r : List ℚ) (x xh : List ℝ) (d : ℕ → ℝ) (W X e : ℝ),
  r.length = x.length → r.length ≤ 32 → Close x xh e X → (∀ k, |d k| ≤ δ) →
  (∀ a ∈ r, |(a : ℝ)| ≤ W) → 0 ≤ W → 0 ≤ X → 0 ≤ e →
  (W + 1) * (X + e + 1) ≤ 2 ^ 20 → 2 ^ 30 ≤ M →
    |ardot fl r x d 0 0 - dotQ r xh|
      ≤ absSum r * e + (r.length : ℝ) * δ * (X + e) + (r.length : ℝ) * (W + 1) * (X + e + 1) / 2 ^ 16
        + 1 / 2 ^ 100

end Lane4.Case
