namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft

/-- Left-to-right rounded summation is close to the exact sum. Range condition: twice the
total magnitude (plus the underflow terms) stays within `M`. -/
def RsumErr : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → 0 ≤ η →
  ∀ (l : List ℝ) (acc : ℝ), u * (l.length : ℝ) ≤ 1 / 256 →
    2 * (|acc| + (l.map (fun a => |a|)).sum) + 2 * (l.length : ℝ) * η ≤ M →
    |rsum fl l acc - (acc + l.sum)|
      ≤ 101 / 100 * u * (l.length : ℝ) * (|acc| + (l.map (fun a => |a|)).sum)
        + 2 * (l.length : ℝ) * η

/-- A geometric sum over the distances to `j` in a duplicate-free list of naturals. -/
def GeomDist : Prop :=
  ∀ (c : List ℕ), c.Nodup → ∀ (j : ℕ) (q : ℝ), 0 ≤ q → q ≤ 1 / 2 →
    ((c.filter (fun k => decide (k ≠ j))).map (fun k => q ^ ndist j k)).sum ≤ 4 * q

end Lane4.Case
