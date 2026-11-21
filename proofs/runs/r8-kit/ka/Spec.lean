namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- SCORES OF CANDIDATE KEYS AGAINST THE CERTIFICATE'S TABLE (contains obligation P1).
A head that passes `headOK8`; `x j` is the state at position `j`, known to lie in row `tok j` of
`E`; the query is at position `i` with a real token. For candidate key positions `j, k ≤ i`
(positions hold candidate tokens), with `sj, sk` the table entries `sAt hc (tok i) (tok j)`,
`sAt hc (tok i) (tok k)` (centre, radius) of their content scores:

* every score is at most `(m + 2) * (n + 1) + 1025` in size;
* FAR: if `k < j`, the score of `k` minus the score of `j` is at most
  `-(m - δ) * (j - k)` plus the difference of the centres, both radii and `sigFar h`;
* NEAR (P1): if both keys are within 4 positions of the query, the score difference is the
  nominal one, `m * (k - j)` plus the difference of the centres, up to `δ * |k - j|`, both radii
  and `1 / 2^8`. -/
def ScoreWin : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOK8 δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 → smallM h.A = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA : ℕ → ℕ → ℝ) (dm : ℝ), (∀ a b, |dA a b| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
  ∀ j k, j ≤ i → k ≤ i →
  hc.cands.getD (tok j) false = true → hc.cands.getD (tok k) false = true →
    |h.score fl dA dm x i j| ≤ ((h.m : ℚ) : ℝ) * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) + 1025
    ∧ (k < j →
        h.score fl dA dm x i k - h.score fl dA dm x i j
          ≤ -((((h.m - δ : ℚ)) : ℝ) * ((j : ℝ) - (k : ℝ)))
            + ((((sAt hc (tok i) (tok k)).1 - (sAt hc (tok i) (tok j)).1 : ℚ)) : ℝ)
            + ((((sAt hc (tok i) (tok k)).2 + (sAt hc (tok i) (tok j)).2 + sigFar h : ℚ)) : ℝ))
    ∧ (i ≤ k + 4 → i ≤ j + 4 →
        |h.score fl dA dm x i k - h.score fl dA dm x i j
            - (((h.m : ℚ) : ℝ) * ((k : ℝ) - (j : ℝ))
               + ((((sAt hc (tok i) (tok k)).1 - (sAt hc (tok i) (tok j)).1 : ℚ)) : ℝ))|
          ≤ ((δ : ℚ) : ℝ) * |(k : ℝ) - (j : ℝ)|
            + ((((sAt hc (tok i) (tok k)).2 + (sAt hc (tok i) (tok j)).2 + 1 / 2 ^ 8 : ℚ)) : ℝ))

end Lane4.Case
