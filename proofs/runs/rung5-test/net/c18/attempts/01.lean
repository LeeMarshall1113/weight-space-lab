namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.style.longLine false

def z10 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def embRows : List (List ℚ) :=
  [[0, 0, 0, 0, 0, 0, 0],
   [0, 1, 1, 0, 1, 0, 0],
   [1, 0, 0, 1, 2, 0, 0],
   [1, 0, 0, 1, 2, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 1, 0, 1, 2, 0, 0]]

def rowS : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0, 20, 0]
def rowP : List ℚ := [0, -50, 0, 0, 0, 0, 0, 0, 0, 0]
def rowT : List ℚ := [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z10, z10, z10, z10, z10, z10, z10, rowS, z10, rowP],
    V := [z10, z10, z10, z10, z10, rowT, z10, z10, z10, z10],
    mask := Mask.strict }

def blk : Block :=
  { heads := [hd],
    W1 := [[0, 0, 2, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 2, 0, 1, 0, 0, 0, 0]],
    b1 := [-2, -2],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, -2], [0, 0], [0, 0], [0, 0]],
    b2 := z10 }

def net : TNet :=
  { embed := embRows,
    blocks := [blk],
    outW := [0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    outB := 0 }

def embq (t c : ℕ) : ℚ := (embRows.getD t []).getD c 0

noncomputable def ev (fl : ℝ → ℝ) (p : Pert) (t c : ℕ) : ℝ := sw fl (embq t c) (p.E t c)

def gq (t : ℕ) : ℕ := if t = 2 ∨ t = 3 then 1 else 0

theorem tok_le5 (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [ev fl p (tokAt w j) 0, ev fl p (tokAt w j) 1, ev fl p (tokAt w j) 2,
      ev fl p (tokAt w j) 3, ev fl p (tokAt w j) 4, 0, 0, 1, fl (j : ℝ),
      fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h6 := tok_le5 w hw j
  have h3 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨ tokAt w j = 5 := by omega
  rcases h3 with h | h | h | h | h | h <;>
    simp [TNet.init, net, embRows, swRow, pos, ev, embq, h, sw_zero hr, hr.one]


theorem carry_snoc (l : List ℕ) (t : ℕ) :
    carry (l ++ [t]) = if cls t = 2 then carry l else cls t := by
  simp [carry, List.foldl_append]

theorem carry_win (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ m, m ≤ w.length → ∃ j, j < m + 1 ∧ ¬ (tokAt w j = 1 ∨ tokAt w j = 5) ∧
      (∀ k, j < k → k < m + 1 → (tokAt w k = 1 ∨ tokAt w k = 5)) ∧
      gq (tokAt w j) = carry (w.take m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · simp [Lane4.Seq.tokAt_zero]
    · intro k h1 h2; omega
    · simp [Lane4.Seq.tokAt_zero, gq, carry]
  | succ m ih =>
    intro hle
    obtain ⟨j, hj, hnp, hall, hc⟩ := ih (by omega)
    have hm : m < w.length := by omega
    have htk : tokAt w (m + 1) = w[m] := Lane4.Seq.tokAt_succ w m hm
    have htake : w.take (m + 1) = w.take m ++ [w[m]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hm]
      rfl
    have hb := hw _ (List.getElem_mem hm)
    have hcar : carry (w.take (m + 1)) = if cls w[m] = 2 then carry (w.take m) else cls w[m] := by
      rw [htake, carry_snoc]
    by_cases hp : w[m] = 1 ∨ w[m] = 5
    · have h2 : cls w[m] = 2 := by
        rcases hp with h | h <;> simp [cls, h]
      refine ⟨j, by omega, hnp, ?_, ?_⟩
      · intro k hk1 hk2
        by_cases hk : k = m + 1
        · subst hk; rw [htk]; exact hp
        · exact hall k hk1 (by omega)
      · rw [hcar, if_pos h2]; exact hc
    · refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
      · rw [htk]; exact hp
      · intro k hk1 hk2; omega
      · rw [hcar, htk]
        have h4 : w[m] = 2 ∨ w[m] = 3 ∨ w[m] = 4 := by omega
        rcases h4 with h | h | h <;> simp [cls, gq, h]

theorem tok_get (w : List ℕ) (m : ℕ) : w.getD m 0 = tokAt w (m + 1) := by
  simp [tokAt]

