namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- THE HEAD LEMMA OF RUNG 8. A head that passes `headOK8`, under an additive perturbation of at
most `δ`, in the rounding model. `x j` is the state at position `j` (the block's input), known to
lie in row `tok j` of `E`; `n` is the number of positions; the query at position `i` has a real
token. `P` lists the latest candidate positions of the query, newest first (`WinPos`), and holds
every candidate position unless it is as long as a full window. If `headAF` returns forms `o` for
the tokens at `P`, then there are symbol values `e'` in `[-1, 1]` (one per non-reference key) such
that, under EVERY symbol assignment `e` that agrees with `e'` on this head's symbols (numbers
`pre, pre + 1, ...`), the head's output vector is represented by `o`, entry by entry. -/
def HeadSound8 : Prop :=
  ∀ (u η M : ℝ) (fl ex : ℝ → ℝ), Ctx u η M fl → ExpM u η ex →
  ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 / 2 →
  ∀ (h : AHead) (E : List (List IV)) (hc : HCert) (dd : ℕ),
  headOK8 δ E h hc = true → h.shapeOK dd = true → dd ≤ 24 →
  smallM h.A = true → smallM h.V = true → smallQ h.g = true → smallQ [h.gb] = true →
  (∀ row ∈ E, row.length = dd ∧ Bdd 16 row) →
  ∀ (dA dV : ℕ → ℕ → ℝ) (dm : ℝ) (dg : ℕ → ℝ) (dgb : ℝ),
  (∀ a b, |dA a b| ≤ (δ : ℝ)) → (∀ a b, |dV a b| ≤ (δ : ℝ)) → |dm| ≤ (δ : ℝ) →
  (∀ k, |dg k| ≤ (δ : ℝ)) → |dgb| ≤ (δ : ℝ) →
  ∀ (n : ℕ) (x : ℕ → Vec) (tok : ℕ → ℕ),
  u * (n : ℝ) ≤ 1 / 256 → η * (n : ℝ) ≤ 1 / 2 ^ 100 → 2 ^ 40 * (n : ℝ) ^ 2 ≤ M →
  (∀ j, j < n → tok j < E.length ∧ InIVs (x j) (E.getD (tok j) [])) →
  ∀ i, i < n → 1 ≤ tok i →
  ∀ (P : List ℕ) (pre : ℕ), WinPos h.mask hc.cands tok n i P →
  P.length ≤ fullLen h hc (tok i) →
  (P.length < fullLen h hc (tok i) →
     ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true → k ∈ P) →
  ∀ o : List AF, headAF δ h hc dd pre (tok i) (P.map tok) = some o →
    ∃ e' : ℕ → ℝ, (∀ k, |e' k| ≤ 1) ∧
      ∀ e : ℕ → ℝ, (∀ k, k < P.length - 1 → e (pre + k) = e' k) →
        InAFs e (h.attn fl ex dA dV dm dg dgb n x i) o

end Lane4.Case
