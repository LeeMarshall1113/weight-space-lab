namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def zA : List (List ℚ) := [z6, z6, z6, z6, z6, z6]

def head1 : AHead :=
  { A := zA, V := [z6, z6, z6, [1, 0, 0, 0, 0, 0], z6, z6], mask := Mask.strict, m := 24,
    g := [-1, 0, 0, 0, 0, 0], gb := 1 / 2 }

def head2 : AHead :=
  { A := zA, V := [z6, z6, z6, z6, [0, 0, 1, 0, 0, 0], z6], mask := Mask.causal, m := 24,
    g := [-1, 0, 0, 1, 0, 0], gb := 1 / 2 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def blk2 : ABlock :=
  { heads := [head2], W1 := [[0, -1, 0, 0, 1, 0], [0, 1, 0, 0, -1, 0]], b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [[0, 0, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0],
              [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]],
    blocks := [blk1, blk2], outW := [0, 0, 0, 0, 0, 1], outB := 0 }

/-! ### ideal quantities -/

def mkN (t : ℕ) : ℕ := if code t = 0 then 0 else 1
def aN (t : ℕ) : ℕ := if code t = 2 then 1 else 0

def fval (w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if fval w i = 0 then code (tokAt w (i + 1)) else fval w i

theorem fval_ne (w : List ℕ) (n : ℕ) :
    fval w n ≠ 0 ↔ ∃ j, j ≤ n ∧ code (tokAt w j) ≠ 0 := by
  induction n with
  | zero =>
    simp [fval, Lane4.Seq.tokAt_zero, code]
  | succ n ih =>
    simp only [fval]
    by_cases h : fval w n = 0
    · rw [if_pos h]
      constructor
      · intro h2
        exact ⟨n + 1, le_refl _, h2⟩
      · rintro ⟨j, hj, hc⟩
        rcases Nat.lt_or_ge j (n + 1) with h3 | h3
        · exfalso
          have : fval w n ≠ 0 := ih.mpr ⟨j, by omega, hc⟩
          exact this h
        · have : j = n + 1 := by omega
          subst this; exact hc
    · rw [if_neg h]
      constructor
      · intro _
        obtain ⟨j, hj, hc⟩ := ih.mp h
        exact ⟨j, by omega, hc⟩
      · intro _; exact h

theorem fval_stay (w : List ℕ) (n m : ℕ) (h : fval w n ≠ 0) (hm : n ≤ m) :
    fval w m = fval w n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    show (if fval w m = 0 then _ else fval w m) = _
    rw [ih]
    rw [if_neg h]

theorem fval_first (w : List ℕ) (j : ℕ) (hc : code (tokAt w j) ≠ 0) (h0 : fval w (j - 1) = 0)
    (hj : 1 ≤ j) : fval w j = code (tokAt w j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  show (if fval w k = 0 then _ else fval w k) = _
  simp at h0
  rw [if_pos h0]

theorem fval_P (w : List ℕ) (i : ℕ) (h : fval w i ≠ 0) :
    ∃ j, j ≤ i ∧ code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0 := by
  induction i with
  | zero => exact absurd rfl h
  | succ i ih =>
    by_cases h1 : fval w i = 0
    · refine ⟨i + 1, le_refl _, ?_, by simpa using h1⟩
      have : fval w (i + 1) = code (tokAt w (i + 1)) := by
        show (if fval w i = 0 then _ else fval w i) = _
        rw [if_pos h1]
      rw [← this]; exact h
    · obtain ⟨j, hj, a, b⟩ := ih h1
      exact ⟨j, by omega, a, b⟩

theorem P_unique (w : List ℕ) (j j' : ℕ) (hj : code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0)
    (hj' : code (tokAt w j') ≠ 0 ∧ fval w (j' - 1) = 0) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : fval w (j' - 1) ≠ 0 := (fval_ne w _).mpr ⟨j, by omega, hj.1⟩
    exact this hj'.2
  · have : fval w (j - 1) ≠ 0 := (fval_ne w _).mpr ⟨j', by omega, hj'.1⟩
    exact this hj.2

theorem P_val (w : List ℕ) (j i : ℕ) (hj : code (tokAt w j) ≠ 0 ∧ fval w (j - 1) = 0)
    (hji : j ≤ i) : fval w i = code (tokAt w j) := by
  have h1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact absurd (by simp [Lane4.Seq.tokAt_zero, code]) hj.1
    · exact h
  have h2 := fval_first w j hj.1 hj.2 h1
  rw [← h2]
  exact fval_stay w j i (by rw [h2]; exact hj.1) hji

end Lane4.Case
