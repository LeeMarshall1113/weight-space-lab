/-
PREREG_RNN amendment A1: cluster invariant. Bridge/RNN.lean is unchanged.

The box invariant is checked for an abstract automaton (clusters 0..nC-1, table T, start c0)
whose accepting set is acc ∘ π. `simCheck` verifies that π maps it onto the spec DFA
(π c0 = q0, π (T c a) = δ (π c) a). Together they give the spec statement `RSpec` for the
spec DFA itself: every weight in the τ-ball, every string over the alphabet, every length.
-/
import Bridge.RNN

namespace Bridge
open Lane4

def simCheck (k nC : ℕ) (T : ℕ → ℕ → ℕ) (c0 : ℕ) (π : ℕ → ℕ) (δ : ℕ → ℕ → ℕ) (q0 : ℕ) : Bool :=
  decide (π c0 = q0) &&
  (List.range nC).all (fun c => (List.range k).all (fun a => decide (π (T c a) = δ (π c) a)))

theorem sim_run (k nC : ℕ) (T : ℕ → ℕ → ℕ) (π : ℕ → ℕ) (δ : ℕ → ℕ → ℕ)
    (hT : ∀ c, c < nC → ∀ a, a < k → T c a < nC ∧ π (T c a) = δ (π c) a) :
    ∀ (w : List ℕ), (∀ a ∈ w, a < k) → ∀ c, c < nC → π (runD T c w) = runD δ (π c) w := by
  intro w
  induction w with
  | nil => intro _ c _; rfl
  | cons a w ih =>
    intro hw c hc
    have ha : a < k := hw a (by simp)
    have hw' : ∀ b ∈ w, b < k := fun b hb => hw b (by simp [hb])
    obtain ⟨h1, h2⟩ := hT c hc a ha
    simp only [runD]
    rw [ih hw' (T c a) h1, h2]

theorem certClust (C R : Layer) (k d nC : ℕ) (T : ℕ → ℕ → ℕ) (c0 : ℕ) (π : ℕ → ℕ)
    (δ : ℕ → ℕ → ℕ) (q0 : ℕ) (acc : ℕ → Bool) (τ : ℚ) (B : List (List ℚ × List ℚ))
    (hc : checkR C R k d nC T c0 (fun c => acc (π c)) τ B = true)
    (hs : simCheck k nC T c0 π δ q0 = true) :
    RSpec C R k d δ q0 acc τ := by
  intro dW db dWo dbo hW hb hWo hbo w hw
  have hA := certR C R k d nC T c0 (fun c => acc (π c)) τ B hc dW db dWo dbo hW hb hWo hbo w hw
  -- facts from the two Boolean checks
  have hc' := hc
  unfold checkR at hc'
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨hq0, _⟩, _⟩, hall⟩ := hc'
  have hc0 : c0 < nC := of_decide_eq_true hq0
  unfold simCheck at hs
  rw [Bool.and_eq_true] at hs
  obtain ⟨hπ0, hsall⟩ := hs
  have hT : ∀ c, c < nC → ∀ a, a < k → T c a < nC ∧ π (T c a) = δ (π c) a := by
    intro c hcn a ha
    have h1 := List.all_eq_true.mp hall c (List.mem_range.mpr hcn)
    rw [Bool.and_eq_true] at h1
    have h2 := List.all_eq_true.mp h1.2 a (List.mem_range.mpr ha)
    rw [Bool.and_eq_true] at h2
    have h3 := List.all_eq_true.mp hsall c (List.mem_range.mpr hcn)
    have h4 := List.all_eq_true.mp h3 a (List.mem_range.mpr ha)
    exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h4⟩
  have hsim := sim_run k nC T π δ hT w hw c0 hc0
  rw [of_decide_eq_true hπ0] at hsim
  simp only at hA ⊢
  rw [← hsim]
  exact hA

end Bridge
