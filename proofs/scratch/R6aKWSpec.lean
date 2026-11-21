import Lane4.AGateAll
namespace Lane4.Case
open Lane4.RSeq (Vec pdot)
open Lane4.RSoft Lane4.AGate

/-- `x` is within `es` of `xh` entry by entry, and `xh` is bounded by `Xs` entry by entry.
The per-coordinate form of `Close`. -/
def CloseL (x xh es Xs : List ℝ) : Prop :=
  x.length = xh.length ∧ es.length = x.length ∧ Xs.length = x.length ∧
  ∀ k, k < x.length →
    |x.getD k 0 - xh.getD k 0| ≤ es.getD k 0 ∧ |xh.getD k 0| ≤ Xs.getD k 0

/-- The per-coordinate error budget of one stored-weight dot product: each term costs
`|a| * e + δ * (X + e)` with that coordinate's own `e` and `X`. -/
noncomputable def wErr (δ : ℝ) : List ℚ → List ℝ → List ℝ → ℝ
  | a :: r, e :: es, X :: Xs => |(a : ℝ)| * e + δ * (X + e) + wErr δ r es Xs
  | _, _, _ => 0

/-- `ArdotNearAbs` with per-coordinate entry errors and bounds. The uniform `W`, `X`, `e`
are used only for the rounding term and the magnitude bound. At most 32 terms. -/
def ArdotNearW : Prop :=
  ∀ (u η M δ : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  0 ≤ δ → δ ≤ 1 →
  ∀ (r : List ℚ) (x xh es Xs : List ℝ) (d : ℕ → ℝ) (W X e : ℝ),
  r.length = x.length → r.length ≤ 32 → CloseL x xh es Xs →
  (∀ k, k < x.length → es.getD k 0 ≤ e ∧ Xs.getD k 0 ≤ X) → (∀ k, |d k| ≤ δ) →
  (∀ a ∈ r, |(a : ℝ)| ≤ W) → 0 ≤ W → 0 ≤ X → 0 ≤ e →
  (W + 1) * (X + e + 1) ≤ 2 ^ 20 → 2 ^ 30 ≤ M →
    |ardot fl r x d 0 0 - dotQ r xh|
      ≤ wErr δ r es Xs + (r.length : ℝ) * (W + 1) * (X + e + 1) / 2 ^ 16 + 1 / 2 ^ 100
    ∧ |ardot fl r x d 0 0| ≤ (r.length : ℝ) * (W + 1) * (X + e + 1) * 2

/-- A uniform `Close` is a `CloseL` with constant lists. -/
def CloseLOfClose : Prop :=
  ∀ (x xh : List ℝ) (e X : ℝ), Close x xh e X →
    CloseL x xh (List.replicate x.length e) (List.replicate x.length X)

end Lane4.Case
#check @Lane4.Case.ArdotNearW
#check @Lane4.Case.CloseLOfClose
