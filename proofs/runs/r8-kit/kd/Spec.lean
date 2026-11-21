namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- SHARED ATTENTION OVER A WINDOW. Pure real analysis: no rounding, no floats.
`c` are the candidate positions, `jr ∈ c` the reference key, `W` a list of other candidates (the
window). For the `i`-th window key the ratio `exp (s k - s jr)` lies in `[lo i, hi i]`; the ratios
of all remaining candidates sum to at most `tl`. Then there are weights `a i`, ONE set for every
value function `f`, each inside the stated interval, non-negative and summing to at most 1, such
that the exact softmax average of `f` is the reference value plus the weighted value differences,
up to `2 * tl * B`. -/
def MixBound : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (s : ℕ → ℝ) (jr : ℕ), jr ∈ c →
  ∀ (W : List ℕ) (lo hi : List ℝ), W.Nodup → (∀ k ∈ W, k ∈ c ∧ k ≠ jr) →
  lo.length = W.length → hi.length = W.length →
  (∀ i, i < W.length → 0 ≤ lo.getD i 0 ∧ lo.getD i 0 ≤ Real.exp (s (W.getD i 0) - s jr) ∧
                        Real.exp (s (W.getD i 0) - s jr) ≤ hi.getD i 0) →
  ∀ tl : ℝ, 0 ≤ tl →
  ((c.filter (fun k => decide (k ≠ jr ∧ k ∉ W))).map (fun k => Real.exp (s k - s jr))).sum ≤ tl →
  ∃ a : ℕ → ℝ,
    (∀ i, i < W.length →
       lo.getD i 0 / (1 + lo.getD i 0 + (hi.sum - hi.getD i 0) + tl) ≤ a i ∧
       a i ≤ hi.getD i 0 / (1 + hi.getD i 0 + (lo.sum - lo.getD i 0))) ∧
    (∀ i, 0 ≤ a i) ∧
    ((List.range W.length).map a).sum ≤ 1 ∧
    ∀ (f : ℕ → ℝ) (B : ℝ), (∀ k ∈ c, |f k| ≤ B) →
      |eavg c s f
        - (f jr + ((List.range W.length).map (fun i => a i * (f (W.getD i 0) - f jr))).sum)|
        ≤ 2 * tl * B

end Lane4.Case
