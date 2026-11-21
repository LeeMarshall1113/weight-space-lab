namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.R7K2

/-- THE HEAD LEMMA. A head that passes `headOK` against the interval table `E` of the
embedding rows returns, at every query position `i` of an input of any length:

* if `j` is the latest candidate position of the query (`Latest`), a vector inside
  `headOut ... (some (tok j))`: the head's value at the token of position `j`, widened by
  the softmax error;
* if no position the mask allows holds a candidate token, a vector inside
  `headOut ... none` (all zeros).

`x j` is the state at position `j` (the block's input), known to lie in row `tok j` of `E`;
`n` is the number of positions; the query's token is a real token (not BOS). -/
def HeadSound : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Ctx u η M fl → ExpM u η ex →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (cd : List Bool) (dd : ℕ),
  headOK δ E h cd = true → h.shapeOK dd = true → dd ≤ 24 →
  smallM h.A = true → smallM h.V = true → smallQ h.g = true → smallQ [h.gb] = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ i k, |dA i k| ≤ (δ : ℝ)) → (∀ i k, |dV i k| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
    (∀ j, Latest h.mask cd tok n i j →
       InIVs (h.attn fl ex dA dV dm dg dgb n x i) (headOut δ E h cd (some (tok j))))
    ∧ ((∀ j ∈ cand h.mask n i, cd.getD (tok j) false = false) →
       InIVs (h.attn fl ex dA dV dm dg dgb n x i) (headOut δ E h cd none))
    ∧ (∀ p : Option ℕ, ∀ v ∈ headOut δ E h cd p, 0 ≤ v.2)

end Lane4.Case
