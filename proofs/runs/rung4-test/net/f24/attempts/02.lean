namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

def z8 : List ℚ := [0, 0, 0, 0, 0, 0, 0, 0]

/-- coordinates: 0 u (unmarked flag), 1 a, 2 c, 3 slot A, 4 slot out, 5 one, 6 fl i, 7 fl n -/
def hd : Head :=
  { A := [z8, z8, z8, z8, z8, [0, 0, 0, 0, 0, 0, -1, 0], z8, [-4, 0, 0, 0, 0, 0, 0, 0]],
    V := [z8, z8, z8, [0, 1, 0, 0, 0, 0, 0, 0], z8, z8, z8, z8],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd],
    W1 := [[0, 0, -1, 1, 0, 0, 0, 0], [0, 0, 1, -1, 0, 0, 0, 0]],
    b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [1, 1], [0, 0], [0, 0], [0, 0]],
    b2 := z8 }

def net : TNet :=
  { embed := [[1, 0, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 1, 1, 0, 0],
      [0, 0, 0, 0, 0], [1, 0, 1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 0, 0, 1, 0, 0, 0],
    outB := 0 }

def ut (t : ℕ) : ℚ := if t = 1 ∨ t = 3 ∨ t = 4 then 0 else 1
def at_ (t : ℕ) : ℚ := if t = 3 then 1 else 0
def ct (t : ℕ) : ℚ := ((cbit t : ℕ) : ℚ)

noncomputable def av (fl : ℝ → ℝ) (p : Pert) (w : List ℕ) (j : ℕ) : ℝ :=
  sw fl (at_ (tokAt w j)) (p.E (tokAt w j) 1)

noncomputable def OUT (fl : ℝ → ℝ) (g1 g2 g3 g4 k1 k2 ow c A : ℝ) : ℝ :=
  fl (ow * fl (fl (k1 * relu (fl (fl (g1 * c) + fl (g2 * A))))
    + fl (k2 * relu (fl (fl (g3 * c) + fl (g4 * A))))))

theorem code_cases (t : ℕ) (ht : t ≤ 5) :
    (code t = 0 ∧ at_ t = 0 ∧ ut t = 1) ∨ (code t = 1 ∧ at_ t = 0 ∧ ut t = 0) ∨
    (code t = 2 ∧ at_ t = 1 ∧ ut t = 0) := by
  interval_cases t <;> simp [code, at_, ut]

theorem cbit_le (t : ℕ) : cbit t ≤ 1 := by
  unfold cbit
  split_ifs <;> omega

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem tokAt_eq_getD (w : List ℕ) (i : ℕ) (hi : 1 ≤ i) : tokAt w i = w.getD (i - 1) 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp [tokAt]

/-! ### first marked token -/

theorem firstc_append (l : List ℕ) (t : ℕ) :
    firstc (l ++ [t]) = if firstc l = 0 then code t else firstc l := by
  simp only [firstc, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem take_succ' (w : List ℕ) (i : ℕ) (h : i < w.length) :
    w.take (i + 1) = w.take i ++ [w[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  rfl

theorem first_spec (w : List ℕ) : ∀ i, i ≤ w.length →
    (firstc (w.take i) = 0 ∧ ∀ k, k ≤ i → code (tokAt w k) = 0) ∨
    (∃ j, j ≤ i ∧ code (tokAt w j) ≠ 0 ∧ (∀ k, k < j → code (tokAt w k) = 0) ∧
      firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨by simp [firstc], ?_⟩
    intro k hk
    have : k = 0 := by omega
    subst this
    simp [Lane4.Seq.tokAt_zero, code]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hlt : m < w.length := by omega
    have htk := Lane4.Seq.tokAt_succ w m hlt
    rw [take_succ' w m hlt, firstc_append]
    rcases ih' with ⟨h0, hall⟩ | ⟨j, hj, hmj, hbef, hf⟩
    · rw [if_pos h0]
      by_cases hc : code w[m] = 0
      · left
        refine ⟨hc, ?_⟩
        intro k hk
        by_cases hkm : k = m + 1
        · subst hkm
          rw [htk]
          exact hc
        · exact hall k (by omega)
      · right
        refine ⟨m + 1, le_refl _, ?_, ?_, ?_⟩
        · rw [htk]; exact hc
        · intro k hk
          exact hall k (by omega)
        · rw [htk]
    · have hne : firstc (w.take m) ≠ 0 := by rw [hf]; exact hmj
      rw [if_neg hne]
      right
      exact ⟨j, by omega, hmj, hbef, hf⟩

/-! ### initial state -/

theorem init_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [sw fl (ut (tokAt w j)) (p.E (tokAt w j) 0),
      sw fl (at_ (tokAt w j)) (p.E (tokAt w j) 1),
      sw fl (ct (tokAt w j)) (p.E (tokAt w j) 2), 0, 0, 1, fl (j : ℝ),
      fl (((w.length + 1 : ℕ)) : ℝ)] := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨
      tokAt w j = 4 ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, pos, h, sw_zero hr, ut, at_, ct, cbit]

theorem score_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a0 a1 a2 a3 a4 qi qn b0 b1 b2 b3 b4 qj qn' : ℝ) :
    hd.score fl dA [a0, a1, a2, a3, a4, 1, qi, qn] [b0, b1, b2, b3, b4, 1, qj, qn']
      = fl (fl (sw fl (-1) (dA 5 6) * qj) + fl (qn * fl (sw fl (-4) (dA 7 0) * b0))) := by
  simp [Head.score, hd, z8, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

/-! ### small real-number lemmas -/

theorem swm1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    |sw fl (-1) d + 1| ≤ 3 / 250 := by
  have h := sw_rel hr hu0 (-1) hdd (ε := 3 / 250) (by linarith)
  simp only [Rat.cast_neg, Rat.cast_one, abs_neg, abs_one, mul_one, sub_neg_eq_add] at h
  exact h

theorem sw1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    |sw fl 1 d - 1| ≤ 3 / 250 := by
  have h := sw_rel hr hu0 1 hdd (ε := 3 / 250) (by linarith)
  simp only [Rat.cast_one, abs_one, mul_one] at h
  exact h

theorem swm4 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    |sw fl (-4) d + 4| ≤ 3 / 250 * 4 := by
  have h := sw_rel hr hu0 (-4) hdd (ε := 3 / 250) (by linarith)
  have e1 : (((-4 : ℚ)) : ℝ) = -4 := by norm_num
  rw [e1] at h
  have e2 : |(-4 : ℝ)| = 4 := by norm_num
  rw [e2] at h
  have e3 : sw fl (-4) d + 4 = sw fl (-4) d - (-4) := by ring
  rw [e3]
  exact h

theorem fl_small {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x : ℝ} (hx : |x| ≤ 4) : |fl x - x| ≤ 1 / 1000000 := by
  have := hr.err hu0 hx
  linarith

theorem flA {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x t r : ℝ} (hx : |x - t| ≤ r) (h4 : |x| ≤ 4) :
    |fl x - t| ≤ r + 1 / 1000000 := by
  have h1 := fl_small hr hu0 hu1 h4
  have h2 := abs_sub_le (fl x) x t
  linarith

theorem abs4 {x t r : ℝ} (h : |x - t| ≤ r) (ht : |t| ≤ 1) (hr : r ≤ 2) : |x| ≤ 4 := by
  have := abs_sub_abs_le_abs_sub x t
  linarith

theorem pmul {x y a b : ℝ} (hx : |x - 1| ≤ a) (hy : |y - 1| ≤ b) :
    |x * y - 1| ≤ a + b + a * b := near_mul hx hy

theorem nmul {x y a b : ℝ} (hx : |x + 1| ≤ a) (hy : |y - 1| ≤ b) :
    |x * y - (-1)| ≤ a + b + a * b := by
  have h1 : |-x - 1| ≤ a := by
    have : -x - 1 = -(x + 1) := by ring
    rw [this, abs_neg]
    exact hx
  have h := near_mul h1 hy
  have h2 : -x * y - 1 = -(x * y - (-1)) := by ring
  rw [h2, abs_neg] at h
  exact h

theorem relu_nn (x : ℝ) : 0 ≤ relu x := le_max_right _ _

theorem flN {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) {N : ℝ} (hN0 : 0 ≤ N)
    (hn : u * N ≤ 1 / 256) : N - 1 / 256 ≤ fl N ∧ fl N ≤ N + 1 / 256 := by
  have h := hr.rel N
  rw [abs_of_nonneg hN0] at h
  have := abs_le.mp h
  constructor <;> linarith [this.1, this.2]

theorem posN {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) {n k : ℕ} {N : ℝ}
    (hN : (n : ℝ) = N) (hk : k ≤ n) (hn : u * N ≤ 1 / 256) :
    0 ≤ fl (k : ℝ) ∧ fl (k : ℝ) ≤ N + 1 / 256 := by
  subst hN
  exact hr.pos_le hu0 hk hn

theorem posG {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) {n a b : ℕ} {N : ℝ}
    (hN : (n : ℝ) = N) (hab : a < b) (hbn : b ≤ n) (hn : u * N ≤ 1 / 256) :
    fl (a : ℝ) + 127 / 128 ≤ fl (b : ℝ) := by
  subst hN
  exact hr.pos_gap hu0 hab hbn hn

/-! ### score comparisons -/

theorem cmp_um {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {g h e qk qj qn N : ℝ}
    (hg1 : -(3 / 250) ≤ g + 1) (hg2 : g + 1 ≤ 3 / 250)
    (hh1 : -(3 / 250 * 4) ≤ h + 4) (hh2 : h + 4 ≤ 3 / 250 * 4)
    (he1 : -(3 / 250) ≤ e - 1) (he2 : e - 1 ≤ 3 / 250)
    (hqk0 : 0 ≤ qk) (hqj0 : 0 ≤ qj) (hqjN : qj ≤ N + 1 / 256)
    (hqn1 : N - 1 / 256 ≤ qn) (hqn2 : qn ≤ N + 1 / 256) (hN2 : 2 ≤ N)
    (hn : u * N ≤ 1 / 256) :
    fl (fl (g * qk) + fl (qn * fl (h * e))) < fl (fl (g * qj) + fl (qn * fl (h * 0))) := by
  have hqn0 : 0 ≤ qn := by linarith
  have hR : fl (g * qk) ≤ 0 := by
    have h1 : g * qk ≤ 0 := by nlinarith [mul_nonneg (show (0:ℝ) ≤ -g by linarith) hqk0]
    have := hr.mono _ _ h1
    rwa [hr.zero] at this
  have hHE1 : h * e ≤ -39 / 10 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -(3952 / 1000) - h by linarith)
      (show (0:ℝ) ≤ e by linarith)]
  have hHE2 : -41 / 10 ≤ h * e := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ h + 4048 / 1000 by linarith)
      (show (0:ℝ) ≤ e by linarith)]
  have hP1 := hr.upper hu0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |h * e| ≤ 5)
  have hP2 := hr.lower hu0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |h * e| ≤ 5)
  have hu5 : u * 5 ≤ 1 / 1000 := by linarith
  have hPu : fl (h * e) ≤ -389 / 100 := by linarith
  have hPl : -42 / 10 ≤ fl (h * e) := by linarith
  have hQ1 : qn * fl (h * e) ≤ -389 / 100 * qn := by
    nlinarith [mul_nonneg hqn0 (show (0:ℝ) ≤ -389 / 100 - fl (h * e) by linarith)]
  have hQ2 : -42 / 10 * qn ≤ qn * fl (h * e) := by
    nlinarith [mul_nonneg hqn0 (show (0:ℝ) ≤ fl (h * e) + 42 / 10 by linarith)]
  have hQabs : |qn * fl (h * e)| ≤ 5 * N := abs_le.mpr ⟨by linarith, by linarith⟩
  have hQ := hr.upper hu0 hQabs
  have huN : u * (5 * N) ≤ 5 / 256 := by nlinarith [hn]
  have hQf : fl (qn * fl (h * e)) ≤ -38 / 10 * N := by linarith
  have hS1 : fl (fl (g * qk) + fl (qn * fl (h * e))) ≤ fl (qn * fl (h * e)) := by
    have := hr.mono (fl (g * qk) + fl (qn * fl (h * e))) (fl (qn * fl (h * e))) (by linarith)
    rwa [hr.idem] at this
  have e1 : fl (fl (g * qj) + fl (qn * fl (h * 0))) = fl (g * qj) := by
    simp [hr.zero, hr.idem]
  rw [e1]
  have hgq1 : -(1012 / 1000) * qj ≤ g * qj := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ g + 1012 / 1000 by linarith) hqj0]
  have hgq2 : g * qj ≤ 0 := by nlinarith [mul_nonneg (show (0:ℝ) ≤ -g by linarith) hqj0]
  have hF := hr.lower hu0 (abs_le.mpr ⟨by linarith, by linarith⟩ : |g * qj| ≤ 2 * N)
  have huN2 : u * (2 * N) ≤ 2 / 256 := by nlinarith [hn]
  linarith

theorem cmp_mm {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {g h qk qj qn N : ℝ}
    (hg1 : -(3 / 250) ≤ g + 1) (hg2 : g + 1 ≤ 3 / 250)
    (hgap : qj + 127 / 128 ≤ qk) (hqj0 : 0 ≤ qj) (hqk0 : 0 ≤ qk)
    (hqkN : qk ≤ N + 1 / 256) (hn : u * N ≤ 1 / 256) (hN2 : 2 ≤ N) :
    fl (fl (g * qk) + fl (qn * fl (h * 0))) < fl (fl (g * qj) + fl (qn * fl (h * 0))) := by
  have e1 : ∀ q : ℝ, fl (fl (g * q) + fl (qn * fl (h * 0))) = fl (g * q) := by
    intro q
    simp [hr.zero, hr.idem]
  rw [e1 qk, e1 qj]
  have hk1 : -(2 * N + 2) ≤ g * qk := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ g + 1012 / 1000 by linarith) hqk0]
  have hk2 : g * qk ≤ 2 * N + 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -g by linarith) hqk0]
  have hj1 : -(2 * N + 2) ≤ g * qj := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ g + 1012 / 1000 by linarith) hqj0]
  have hj2 : g * qj ≤ 2 * N + 2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -g by linarith) hqj0]
  have hgg : g * qk ≤ g * qj + g * (127 / 128) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ -g by linarith)
      (show (0:ℝ) ≤ qk - qj - 127 / 128 by linarith)]
  have huB : u * (2 * N + 2) ≤ 1 / 100 := by nlinarith [hn, hu1]
  apply hr.lt_of_gap hu0 (B := 2 * N + 2) (abs_le.mpr ⟨hk1, hk2⟩) (abs_le.mpr ⟨hj1, hj2⟩)
  nlinarith

/-! ### selection -/

theorem sel_first {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) (j : ℕ) (hj : j ≤ i) (hmj : code (tokAt w j) ≠ 0)
    (hbef : ∀ k < j, code (tokAt w k) = 0) :
    hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
  have hj1 : 1 ≤ j := by
    by_contra h
    have h0 : j = 0 := by omega
    subst h0
    apply hmj
    simp [Lane4.Seq.tokAt_zero, code]
  obtain ⟨N, hN⟩ : ∃ N : ℝ, (((w.length + 1 : ℕ)) : ℝ) = N := ⟨_, rfl⟩
  rw [hN] at hn
  have hN2 : (2 : ℝ) ≤ N := by
    rw [← hN]
    have : 2 ≤ w.length + 1 := by omega
    exact_mod_cast this
  have hg := abs_le.mp (swm1 hr hu0 hu1 (hp.A 0 0 5 6))
  have hh := abs_le.mp (swm4 hr hu0 hu1 (hp.A 0 0 7 0))
  have hqn := flN hr (by linarith) hn
  have hqj := posN hr hu0 hN (show j ≤ w.length + 1 by omega) hn
  have hjt : tokAt w j ≤ 5 := tok_le w hw j
  have hutj : ut (tokAt w j) = 0 := by
    rcases code_cases _ hjt with ⟨h0, _, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact absurd h0 hmj
    · exact h
    · exact h
  apply Head.sel_unique
  · rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal]
    exact hj
  · intro k hk hne
    rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
    simp only [init_eq hr p w hw]
    rw [score_eq hr, score_eq hr]
    rw [hN]
    rw [hutj, sw_zero hr]
    have hkt : tokAt w k ≤ 5 := tok_le w hw k
    have hkN : k ≤ w.length + 1 := by omega
    have hqk := posN hr hu0 hN hkN hn
    by_cases hkc : code (tokAt w k) = 0
    · have hutk : ut (tokAt w k) = 1 := by
        rcases code_cases _ hkt with ⟨_, _, h⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
        · exact h
        · omega
        · omega
      rw [hutk]
      have he := abs_le.mp (sw1 hr hu0 hu1 (hp.E (tokAt w k) 0))
      exact cmp_um hr hu0 hu1 hg.1 hg.2 hh.1 hh.2 he.1 he.2 hqk.1 hqj.1 hqj.2 hqn.1 hqn.2
        hN2 hn
    · have hkj : j < k := by
        by_contra hnot
        have : k < j := by omega
        exact hkc (hbef k this)
      have hutk : ut (tokAt w k) = 0 := by
        rcases code_cases _ hkt with ⟨h0, _, _⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
        · exact absurd h0 hkc
        · exact h
        · exact h
      rw [hutk, sw_zero hr]
      exact cmp_mm hr hu0 hu1 hg.1 hg.2 (posG hr hu0 hN hkj hkN hn) hqj.1 hqk.1 hqk.2 hn hN2

/-! ### attention output -/

theorem ravg_of_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (h : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  unfold ravg
  rw [rsum_zeros hr _ (by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact h j hj)]
  simp [hr.zero]

theorem attn_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    hd.attn fl (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i =
      [0, 0, 0, ravg fl (hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i)
          (fun j => fl (sw fl 1 (p.V 0 0 3 1) * av fl p w j)), 0, 0, 0, 0] := by
  simp [Head.attn, hd, z8, attnRows, rdot, init_eq hr p w hw, sw_zero hr, hr.zero, hr.idem,
    ravg_zero hr, av]

theorem attn_val {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256)
    (i : ℕ) (hi : i ≤ w.length) :
    ∃ A : ℝ, hd.attn fl (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
        = [0, 0, 0, A, 0, 0, 0, 0] ∧ fl A = A ∧
      ((firstc (w.take i) = 2 ∧ |A - 1| ≤ 1 / 25) ∨ (firstc (w.take i) ≠ 2 ∧ A = 0)) := by
  refine ⟨ravg fl (hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i)
    (fun j => fl (sw fl 1 (p.V 0 0 3 1) * av fl p w j)), attn_eq hr p w hw i, ?_, ?_⟩
  · unfold ravg
    exact hr.idem _
  · rcases first_spec w i hi with ⟨hf0, hall⟩ | ⟨j, hj, hmj, hbef, hf⟩
    · right
      refine ⟨by rw [hf0]; norm_num, ?_⟩
      apply ravg_of_zero hr
      intro j hjS
      have hjc := ((Head.mem_sel hd fl (p.A 0 0) (w.length + 1) (net.init fl p w) i j).1 hjS).1
      rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hjc
      have h0 := hall j hjc
      have ht : tokAt w j ≤ 5 := tok_le w hw j
      rcases code_cases _ ht with ⟨_, ha, _⟩ | ⟨hc1, _, _⟩ | ⟨hc2, _, _⟩
      · simp [av, ha, sw_zero hr, hr.zero]
      · omega
      · omega
    · have hs := sel_first hr hu0 hu1 p hp w hw hn i hi j hj hmj hbef
      rw [hs, ravg_singleton hr]
      have ht : tokAt w j ≤ 5 := tok_le w hw j
      rcases code_cases _ ht with ⟨h0, _, _⟩ | ⟨hc1, ha, _⟩ | ⟨hc2, ha, _⟩
      · exact absurd h0 hmj
      · right
        refine ⟨by rw [hf, hc1]; norm_num, ?_⟩
        simp [av, ha, sw_zero hr, hr.zero, hr.idem]
      · left
        refine ⟨by rw [hf, hc2], ?_⟩
        have hav : av fl p w j = sw fl 1 (p.E (tokAt w j) 1) := by simp [av, ha]
        have h1 := sw1 hr hu0 hu1 (hp.E (tokAt w j) 1)
        have h2 := sw1 hr hu0 hu1 (hp.V 0 0 3 1)
        rw [← hav] at h1
        have m := pmul h2 h1
        have a := flA hr hu0 hu1 m (abs4 m (by norm_num) (by norm_num))
        show |fl (fl (sw fl 1 (p.V 0 0 3 1) * av fl p w j)) - 1| ≤ 1 / 25
        rw [hr.idem]
        exact le_trans a (by norm_num)

/-! ### output -/

theorem out_eq {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A : ℝ)
    (hA : hd.attn fl (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
        = [0, 0, 0, A, 0, 0, 0, 0])
    (hAi : fl A = A) :
    net.out fl p w i = OUT fl (sw fl (-1) (p.W1 0 0 2)) (sw fl 1 (p.W1 0 0 3))
      (sw fl 1 (p.W1 0 1 2)) (sw fl (-1) (p.W1 0 1 3)) (sw fl 1 (p.W2 0 4 0))
      (sw fl 1 (p.W2 0 4 1)) (sw fl 1 (p.oW 4))
      (sw fl (ct (tokAt w i)) (p.E (tokAt w i) 2)) A := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, hA, init_eq hr p w hw]
  simp [OUT, relu, z8, rdot, raffine, radd, sw_zero hr, hr.zero, hr.idem, hr.one, hAi, fl_sw hr]

/-! ### numerics of the final xor -/

theorem fin1 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {k h ow : ℝ} (hk : |k - 1| ≤ 3 / 250)
    (how : |ow - 1| ≤ 3 / 250) (hh : |h - 1| ≤ 1 / 15) :
    |fl (ow * fl (k * h)) - 1| ≤ 1 / 4 := by
  have m1 := pmul hk hh
  have a1 := flA hr hu0 hu1 m1 (abs4 m1 (by norm_num) (by norm_num))
  have m2 := pmul how a1
  have a2 := flA hr hu0 hu1 m2 (abs4 m2 (by norm_num) (by norm_num))
  exact le_trans a2 (by norm_num)

theorem flup {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {x : ℝ} (h0 : 0 ≤ x) (h4 : x ≤ 4) :
    0 ≤ fl x ∧ fl x ≤ x + 1 / 1000000 := by
  refine ⟨hr.nonneg h0, ?_⟩
  have := hr.upper hu0 (abs_le.mpr ⟨by linarith, h4⟩ : |x| ≤ 4)
  linarith

theorem finF {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {k1 k2 ow H1 H2 : ℝ} (hk1 : |k1 - 1| ≤ 3 / 250)
    (hk2 : |k2 - 1| ≤ 3 / 250) (how : |ow - 1| ≤ 3 / 250)
    (h1 : 0 ≤ H1) (h1' : H1 ≤ 1 / 10) (h2 : 0 ≤ H2) (h2' : H2 ≤ 1 / 10) :
    |fl (ow * fl (fl (k1 * H1) + fl (k2 * H2)))| ≤ 1 / 4 := by
  have k1u := abs_le.mp hk1
  have k2u := abs_le.mp hk2
  have ou := abs_le.mp how
  have t1n : 0 ≤ k1 * H1 := mul_nonneg (by linarith [k1u.1]) h1
  have t1u : k1 * H1 ≤ 253 / 250 * (1 / 10) :=
    mul_le_mul (by linarith [k1u.2]) h1' h1 (by norm_num)
  have t2n : 0 ≤ k2 * H2 := mul_nonneg (by linarith [k2u.1]) h2
  have t2u : k2 * H2 ≤ 253 / 250 * (1 / 10) :=
    mul_le_mul (by linarith [k2u.2]) h2' h2 (by norm_num)
  have f1 := flup hr hu0 hu1 t1n (by linarith)
  have f2 := flup hr hu0 hu1 t2n (by linarith)
  have f3 := flup hr hu0 hu1 (show 0 ≤ fl (k1 * H1) + fl (k2 * H2) by linarith [f1.1, f2.1])
    (by linarith [f1.2, f2.2])
  have pn : 0 ≤ ow * fl (fl (k1 * H1) + fl (k2 * H2)) :=
    mul_nonneg (by linarith [ou.1]) f3.1
  have pu : ow * fl (fl (k1 * H1) + fl (k2 * H2)) ≤ 253 / 250 * (21 / 100) :=
    mul_le_mul (by linarith [ou.2]) (by linarith [f1.2, f2.2, f3.2, t1u, t2u]) f3.1
      (by norm_num)
  have f4 := flup hr hu0 hu1 pn (by linarith)
  exact abs_le.mpr ⟨by linarith [f4.1], by linarith [f4.2]⟩

theorem pre_small {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {X Y : ℝ} (hX : |X + 1| ≤ 1 / 40) (hY : |Y - 1| ≤ 1 / 18) :
    relu (fl (fl X + fl Y)) ≤ 1 / 10 := by
  have hX' : |X - (-1)| ≤ 1 / 40 := by rw [sub_neg_eq_add]; exact hX
  have fX := flA hr hu0 hu1 hX' (abs4 hX' (by norm_num) (by norm_num))
  have fY := flA hr hu0 hu1 hY (abs4 hY (by norm_num) (by norm_num))
  obtain ⟨a1, a2⟩ := abs_le.mp fX
  obtain ⟨b1, b2⟩ := abs_le.mp fY
  have hs : |fl X + fl Y| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum' : |fl X + fl Y - 0| ≤ 1 / 40 + 1 / 1000000 + (1 / 18 + 1 / 1000000) := by
    rw [sub_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have f3 := flA hr hu0 hu1 hsum' hs
  have : fl (fl X + fl Y) ≤ 1 / 10 := by
    have := (abs_le.mp f3).2
    linarith
  exact max_le this (by norm_num)

theorem pre_small' {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {X Y : ℝ} (hX : |X - 1| ≤ 1 / 40) (hY : |Y + 1| ≤ 1 / 18) :
    relu (fl (fl X + fl Y)) ≤ 1 / 10 := by
  have hY' : |Y - (-1)| ≤ 1 / 18 := by rw [sub_neg_eq_add]; exact hY
  have fX := flA hr hu0 hu1 hX (abs4 hX (by norm_num) (by norm_num))
  have fY := flA hr hu0 hu1 hY' (abs4 hY' (by norm_num) (by norm_num))
  obtain ⟨a1, a2⟩ := abs_le.mp fX
  obtain ⟨b1, b2⟩ := abs_le.mp fY
  have hs : |fl X + fl Y| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum' : |fl X + fl Y - 0| ≤ 1 / 40 + 1 / 1000000 + (1 / 18 + 1 / 1000000) := by
    rw [sub_zero]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have f3 := flA hr hu0 hu1 hsum' hs
  have : fl (fl X + fl Y) ≤ 1 / 10 := by
    have := (abs_le.mp f3).2
    linarith
  exact max_le this (by norm_num)

theorem numfin {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216)
    {g1 g2 g3 g4 k1 k2 ow c A : ℝ}
    (hg1 : |g1 + 1| ≤ 3 / 250) (hg2 : |g2 - 1| ≤ 3 / 250) (hg3 : |g3 - 1| ≤ 3 / 250)
    (hg4 : |g4 + 1| ≤ 3 / 250) (hk1 : |k1 - 1| ≤ 3 / 250) (hk2 : |k2 - 1| ≤ 3 / 250)
    (how : |ow - 1| ≤ 3 / 250) (cb ab : ℕ)
    (hc : (cb = 0 ∧ c = 0) ∨ (cb = 1 ∧ |c - 1| ≤ 3 / 250))
    (hA : (ab = 0 ∧ A = 0) ∨ (ab = 1 ∧ |A - 1| ≤ 1 / 25)) :
    |OUT fl g1 g2 g3 g4 k1 k2 ow c A - (((ab + cb) % 2 : ℕ) : ℝ)| ≤ 1 / 4 := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩ <;> rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, hA⟩
  · have e : OUT fl g1 g2 g3 g4 k1 k2 ow 0 0 = 0 := by simp [OUT, hr.zero, relu]
    rw [e]
    norm_num
  · -- c = 0, A near 1
    have m2 := pmul hg2 hA
    have f2 := flA hr hu0 hu1 m2 (abs4 m2 (by norm_num) (by norm_num))
    have m4 := nmul hg4 hA
    have f4 := flA hr hu0 hu1 m4 (abs4 m4 (by norm_num) (by norm_num))
    have hH1 : relu (fl (g2 * A)) = fl (g2 * A) :=
      max_eq_left (by have := (abs_le.mp f2).1; linarith)
    have hH2 : relu (fl (g4 * A)) = 0 :=
      max_eq_right (by have := (abs_le.mp f4).2; linarith)
    have e : OUT fl g1 g2 g3 g4 k1 k2 ow 0 A = fl (ow * fl (k1 * fl (g2 * A))) := by
      simp [OUT, hr.zero, hr.idem, hH1, hH2]
    have ht : (((1 + 0) % 2 : ℕ) : ℝ) = 1 := by norm_num
    rw [e, ht]
    exact fin1 hr hu0 hu1 hk1 how (le_trans f2 (by norm_num))
  · -- c near 1, A = 0
    have m1 := nmul hg1 hc
    have f1 := flA hr hu0 hu1 m1 (abs4 m1 (by norm_num) (by norm_num))
    have m3 := pmul hg3 hc
    have f3 := flA hr hu0 hu1 m3 (abs4 m3 (by norm_num) (by norm_num))
    have hH1 : relu (fl (g1 * c)) = 0 :=
      max_eq_right (by have := (abs_le.mp f1).2; linarith)
    have hH2 : relu (fl (g3 * c)) = fl (g3 * c) :=
      max_eq_left (by have := (abs_le.mp f3).1; linarith)
    have e : OUT fl g1 g2 g3 g4 k1 k2 ow c 0 = fl (ow * fl (k2 * fl (g3 * c))) := by
      simp [OUT, hr.zero, hr.idem, hH1, hH2]
    have ht : (((0 + 1) % 2 : ℕ) : ℝ) = 1 := by norm_num
    rw [e, ht]
    exact fin1 hr hu0 hu1 hk2 how (le_trans f3 (by norm_num))
  · -- both near 1: result 0
    have hx1 : |g1 * c + 1| ≤ 1 / 40 := by
      have := nmul hg1 hc
      rw [sub_neg_eq_add] at this
      exact le_trans this (by norm_num)
    have hx4 : |g4 * A + 1| ≤ 1 / 18 := by
      have := nmul hg4 hA
      rw [sub_neg_eq_add] at this
      exact le_trans this (by norm_num)
    have hx2 : |g2 * A - 1| ≤ 1 / 18 := le_trans (pmul hg2 hA) (by norm_num)
    have hx3 : |g3 * c - 1| ≤ 1 / 40 := le_trans (pmul hg3 hc) (by norm_num)
    have H1 := pre_small hr hu0 hu1 hx1 hx2
    have H2 := pre_small' hr hu0 hu1 hx3 hx4
    have key := finF hr hu0 hu1 hk1 hk2 how (relu_nn _) H1 (relu_nn _) H2
    have ht : (((1 + 1) % 2 : ℕ) : ℝ) = 0 := by norm_num
    rw [ht, sub_zero]
    exact key

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  obtain ⟨A, hA, hAi, hAc⟩ := attn_val hr hu0 hu1 p hp w hw hn i hi
  rw [out_eq hr p w hw i A hA hAi]
  have hcb : cbit (tokAt w i) ≤ 1 := cbit_le _
  have hc : (cbit (tokAt w i) = 0 ∧ sw fl (ct (tokAt w i)) (p.E (tokAt w i) 2) = 0) ∨
      (cbit (tokAt w i) = 1 ∧
        |sw fl (ct (tokAt w i)) (p.E (tokAt w i) 2) - 1| ≤ 3 / 250) := by
    rcases (by omega : cbit (tokAt w i) = 0 ∨ cbit (tokAt w i) = 1) with h | h
    · left
      refine ⟨h, ?_⟩
      have : ct (tokAt w i) = 0 := by simp [ct, h]
      rw [this]
      exact sw_zero hr _
    · right
      refine ⟨h, ?_⟩
      have : ct (tokAt w i) = 1 := by simp [ct, h]
      rw [this]
      exact sw1 hr hu0 hu1 (hp.E _ 2)
  have hg1 := swm1 hr hu0 hu1 (hp.W1 0 0 2)
  have hg2 := sw1 hr hu0 hu1 (hp.W1 0 0 3)
  have hg3 := sw1 hr hu0 hu1 (hp.W1 0 1 2)
  have hg4 := swm1 hr hu0 hu1 (hp.W1 0 1 3)
  have hk1 := sw1 hr hu0 hu1 (hp.W2 0 4 0)
  have hk2 := sw1 hr hu0 hu1 (hp.W2 0 4 1)
  have how := sw1 hr hu0 hu1 (hp.oW 4)
  rcases hAc with ⟨hf2, hA1⟩ | ⟨hf2, hA0⟩
  · have htg : target w i = (1 + cbit (tokAt w i)) % 2 := by
      unfold target
      rw [if_pos hf2, ← tokAt_eq_getD w i hi1]
    rw [htg]
    exact numfin hr hu0 hu1 hg1 hg2 hg3 hg4 hk1 hk2 how (cbit (tokAt w i)) 1 hc
      (Or.inr ⟨rfl, hA1⟩)
  · have htg : target w i = (0 + cbit (tokAt w i)) % 2 := by
      unfold target
      rw [if_neg hf2, ← tokAt_eq_getD w i hi1]
    rw [htg]
    exact numfin hr hu0 hu1 hg1 hg2 hg3 hg4 hk1 hk2 how (cbit (tokAt w i)) 0 hc
      (Or.inl ⟨rfl, hA0⟩)

end Lane4.Case
