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


structure Env (u η M : ℝ) (fl : ℝ → ℝ) (n : ℕ) : Prop where
  hr : Rnd u η M fl
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη : η ≤ 1 / 2 ^ 149
  hn : u * (n : ℝ) ≤ 1 / 256
  hM : 2 ^ 40 * (n : ℝ) ^ 2 ≤ M
  hn1 : 1 ≤ n

theorem Env.rin {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ 2 ^ 40) : C * (n : ℝ) ≤ M := range_lin E.hM E.hn1 hC0 hC

theorem Env.rc {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {C : ℝ}
    (hC : C ≤ 2 ^ 40) : C ≤ M := range_const E.hM E.hn1 hC

theorem Env.nR {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) : (1 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast E.hn1

/-- rounding error of a small number -/
theorem Env.fs {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x : ℝ} (hx : |x| ≤ 100) :
    |fl x - x| ≤ 1 / 1000 := by
  have h := E.hr.abs E.hu0 hx (E.rc (by norm_num))
  have h1 := eta_tiny E.hη
  have h2 : u * 100 ≤ 1 / 2 ^ 24 * 100 := mul_le_mul_of_nonneg_right E.hu1 (by norm_num)
  have h3 : (1 : ℝ) / 2 ^ 24 * 100 + 1 / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- rounding error of a number of size at most C*n -/
theorem Env.fsn {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ 100) (hx : |x| ≤ C * n) : |fl x - x| ≤ 1 / 2 := by
  have h := E.hr.abs E.hu0 hx (E.rin hC0 (by linarith))
  have h1 := eta_tiny E.hη
  have h2 : u * (C * (n : ℝ)) = C * (u * n) := by ring
  have h3 : C * (u * (n : ℝ)) ≤ C * (1 / 256) := mul_le_mul_of_nonneg_left E.hn hC0
  have h4 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

/-- fl of fl is fl, for small numbers -/
theorem Env.id100 {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x : ℝ} (hx : |x| ≤ 100) :
    fl (fl x) = fl x := E.hr.idem x (le_trans hx (E.rc (by norm_num)))

theorem Env.idn {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) {x C : ℝ} (hC0 : 0 ≤ C)
    (hx : |x| ≤ C * n) (hC : C ≤ 2 ^ 40) : fl (fl x) = fl x :=
  E.hr.idem x (le_trans hx (E.rin hC0 hC))

/-- stored weights -/
theorem Env.swa {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hw : |(w : ℝ)| ≤ 100) :
    |sw fl w d - (w : ℝ)| ≤ 1 / 199 * |(w : ℝ)| + 1 / 10 ^ 40 := by
  have hε : (1 : ℝ) / 200 + u + u * (1 / 200) ≤ 1 / 199 := by
    have := E.hu1
    linarith
  have h200 : (200 : ℝ) ≤ M := E.rc (by norm_num)
  have h := sw_near E.hr E.hu0 w hd (by norm_num) (by linarith) hε
  have := eta_tiny E.hη
  linarith

theorem Env.swfix {u η M : ℝ} {fl : ℝ → ℝ} {n : ℕ} (E : Env u η M fl n) (w : ℚ) {d : ℝ}
    (hd : |d| ≤ 1 / 200) (hw : |(w : ℝ)| ≤ 100) : fl (sw fl w d) = sw fl w d := by
  have h200 : (200 : ℝ) ≤ M := E.rc (by norm_num)
  exact fl_sw E.hr w hd (by norm_num) (by linarith)

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 a5 a6 qi qn b0 b1 b2 b3 b4 b5 b6 qk qn' : ℝ)
    (hI1 : fl (fl (sw fl 20 (dA 7 8) * qk)) = fl (sw fl 20 (dA 7 8) * qk))
    (hI2 : fl (fl (sw fl (-50) (dA 9 1) * b1)) = fl (sw fl (-50) (dA 9 1) * b1)) :
    hd.score fl dA [a0, a1, a2, a3, a4, a5, a6, 1, qi, qn] [b0, b1, b2, b3, b4, b5, b6, 1, qk, qn'] =
      fl (fl (sw fl 20 (dA 7 8) * qk) + fl (qn * fl (sw fl (-50) (dA 9 1) * b1))) := by
  simp [Head.score, hd, z10, rowS, rowP, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ)
    (b0 b1 b2 b3 b4 b5 b6 qk qn : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * b0)) = fl (sw fl 1 (dV 0) * b0)) :
    rdot fl rowT [b0, b1, b2, b3, b4, b5, b6, 1, qk, qn] dV 0 0
      = fl (sw fl 1 (dV 0) * b0) := by
  simp [rowT, rdot, sw_zero hr, hr.zero, hI]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g h i j : ℝ) :
    rdot fl z10 [a, b, c, d, e, f, g, h, i, j] dV 0 0 = 0 := by
  simp [z10, rdot, sw_zero hr, hr.zero]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, 0, 0, savg fl ex (cand Mask.strict (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl rowT (net.init fl p w j) (p.V 0 0 5) 0 0),
         0, 0, 0, 0] := by
  have hV : hd.V = [z10, z10, z10, z10, z10, rowT, z10, z10, z10, z10] := rfl
  have hm : hd.mask = Mask.strict := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.strict (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z10 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw]
    exact zrow_eq hr d _ _ _ _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

end Lane4.Case
