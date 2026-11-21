/-
the proofs study, mechanism row (a) for rung 8 (PREREG_MECH.md): attention mass outside the certificate's
window. Statements only; written by the study team. `Real.exp` of the network's own scores: the weights
meant here are the exact softmax of the scores the network computes in the rounding model.
-/
namespace Lane4.Case

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

/-- Head level. Hypotheses as `Lane4.R8KG.HeadSound8` up to the window `P`. Conclusion: the
candidate keys outside `P` carry at most `3 * tailB` of the total (unnormalised) softmax weight. -/
def HeadTail8 : Prop :=
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Ctx u η M fl →
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
  ∀ (P : List ℕ), WinPos h.mask hc.cands tok n i P →
  P.length ≤ fullLen h hc (tok i) →
  (P.length < fullLen h hc (tok i) →
     ∀ k ∈ cand h.mask n i, hc.cands.getD (tok k) false = true → k ∈ P) →
    (((h.cands fl dg dgb n x i).filter (fun k => decide (k ∉ P))).map
        (fun k => Real.exp (h.score fl dA dm x i k))).sum
      ≤ ((3 * tailB δ h hc : ℚ) : ℝ) *
        ((h.cands fl dg dgb n x i).map (fun k => Real.exp (h.score fl dA dm x i k))).sum

/-- Network level. If the rung-8 checker accepts, then in every network of the ball, in the
rounding model, on every input, at every position `i ≥ 1`, every head `a` has a window `P` of at
most `L + 1` of its latest candidate positions outside which the softmax weight is at most
`3 * tailB` of the total. -/
def AttnWindow8 : Prop :=
  ∀ (δ : ℚ) (N : ANet) (T : Task) (c : Cert8), check8 δ N T c = true →
  ∀ (u η M : ℝ) (fl : ℝ → ℝ), Rnd u η M fl →
  0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  ∀ p : APert, p.Within (δ : ℝ) →
  ∀ w : List ℕ, (∀ t ∈ w, 1 ≤ t ∧ t ≤ T.ntok) →
  u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256 → η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100 →
  2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M →
  ∀ (B : ABlock), N.blocks = [B] →
  ∀ (a : ℕ) (h : AHead) (hc : HCert), a < B.heads.length →
  B.heads.getD a h = h → c.heads.getD a hc = hc →
  ∀ i : ℕ, 1 ≤ i → i ≤ w.length →
  ∃ P : List ℕ, WinPos h.mask hc.cands (tokAt w) (w.length + 1) i P ∧ P.length ≤ hc.L + 1 ∧
    (((h.cands fl (p.g 0 a) (p.gb 0 a) (w.length + 1) (N.init fl p w) i).filter
        (fun k => decide (k ∉ P))).map
        (fun k => Real.exp (h.score fl (p.A 0 a) (p.m 0 a) (N.init fl p w) i k))).sum
      ≤ ((3 * tailB δ h hc : ℚ) : ℝ) *
        ((h.cands fl (p.g 0 a) (p.gb 0 a) (w.length + 1) (N.init fl p w) i).map
          (fun k => Real.exp (h.score fl (p.A 0 a) (p.m 0 a) (N.init fl p w) i k))).sum

end Lane4.Case
