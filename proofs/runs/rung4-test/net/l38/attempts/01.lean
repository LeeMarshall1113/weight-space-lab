namespace Lane4.Case
open Lane4.RSeq
open Lane4.Seq (Mask cand tokAt)

/-- State: [v, u, r, 1, fl i, fl n] (width 6). v = value, u = 1 for unmarked tokens, r = result. -/
def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def v2 : List ℚ := [1, 0, 0, 0, 0, 0]

/-- Score of key j: stored(1) * position of j, minus 2 * n for unmarked keys (their `u` slot is 1,
for marked keys it is exactly 0). Causal: the last marked position wins. Value: copy `v` into `r`. -/
def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, 1, 0], z6, [0, -2, 0, 0, 0, 0]],
    V := [z6, z6, v2, z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [2, 0, 0], [3, 0, 0], [1, 0, 0], [0, 1, 0], [1, 0, 0]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

/-! ### Target facts -/

theorem val_le (t : ℕ) : val t ≤ 3 := by
  unfold val
  split_ifs <;> omega

theorem tgt_succ (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    target w (i + 1) = if val (tokAt w (i + 1)) = 0 then target w i else val (tokAt w (i + 1)) := by
  rw [Lane4.Seq.tokAt_succ w i hi]
  have h1 : w.take (i + 1) = w.take i ++ [w[i]] := by
    first
      | exact List.take_succ_eq_append_getElem hi
      | simp [List.take_succ, List.getElem?_eq_getElem hi]
  unfold target lastv
  rw [h1, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

theorem last_marked (w : List ℕ) : ∀ i : ℕ, i ≤ w.length →
    ((∀ j, 1 ≤ j → j ≤ i → val (tokAt w j) = 0) ∧ target w i = 0) ∨
    (∃ j, 1 ≤ j ∧ j ≤ i ∧ val (tokAt w j) ≠ 0 ∧ (∀ k, j < k → k ≤ i → val (tokAt w k) = 0) ∧
      target w i = val (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    refine ⟨fun j h1 h2 => ?_, ?_⟩
    · exfalso
      omega
    · simp [target, lastv]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hrec := tgt_succ w i (by omega)
    by_cases hm : val (tokAt w (i + 1)) = 0
    · rw [if_pos hm] at hrec
      rcases ih' with ⟨h1, h2⟩ | ⟨j, hj1, hj2, hj3, hj4, hj5⟩
      · left
        refine ⟨fun j a b => ?_, by rw [hrec, h2]⟩
        by_cases hj : j = i + 1
        · rw [hj]; exact hm
        · exact h1 j a (by omega)
      · right
        refine ⟨j, hj1, by omega, hj3, fun k a b => ?_, by rw [hrec, hj5]⟩
        by_cases hk : k = i + 1
        · rw [hk]; exact hm
        · exact hj4 k a (by omega)
    · rw [if_neg hm] at hrec
      right
      exact ⟨i + 1, by omega, le_refl _, hm, fun k a b => by omega, hrec⟩

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

/-! ### Embedding -/

theorem init_row {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (j : ℕ)
    (c0 c1 c2 : ℚ) (h : net.embed.getD (tokAt w j) [] = [c0, c1, c2]) :
    net.init fl p w j = [sw fl c0 (p.E (tokAt w j) 0), sw fl c1 (p.E (tokAt w j) 1),
      sw fl c2 (p.E (tokAt w j) 2), 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  simp only [TNet.init]
  rw [h]
  simp [swRow, pos]

theorem sw_nat {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 16777216)
    (c : ℕ) {d : ℝ} (hdd : |d| ≤ 1 / 200) :
    |sw fl (c : ℚ) d - (c : ℝ)| ≤ 3 / 250 * |(c : ℝ)| := by
  have h := sw_rel hr hu0 (c : ℚ) hdd (ε := 3 / 250) (by linarith)
  rw [Rat.cast_natCast] at h
  exact h

theorem init_unm {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (hrow : net.embed.getD (tokAt w j) [] = [0, 1, 0]) :
    ∃ b : ℝ, net.init fl p w j = [0, b, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] ∧
      |b - 1| ≤ 3 / 250 := by
  refine ⟨sw fl 1 (p.E (tokAt w j) 1), ?_, ?_⟩
  · rw [init_row hr p w j 0 1 0 hrow]
    simp only [sw_zero hr]
  · have h := sw_rel hr hu0 1 (hp.E (tokAt w j) 1) (ε := 3 / 250) (by linarith)
    simp only [Rat.cast_one, abs_one, mul_one] at h
    exact h

theorem init_mrk {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ) (j : ℕ)
    (c : ℕ) (hrow : net.embed.getD (tokAt w j) [] = [(c : ℚ), 0, 0]) :
    ∃ a : ℝ, net.init fl p w j = [a, 0, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] ∧
      |a - (c : ℝ)| ≤ 3 / 250 * |(c : ℝ)| := by
  refine ⟨sw fl (c : ℚ) (p.E (tokAt w j) 0), ?_, sw_nat hr hu0 hu1 c (hp.E _ 0)⟩
  rw [init_row hr p w j c 0 0 hrow]
  simp only [sw_zero hr]

theorem init_cases {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    (val (tokAt w j) ≠ 0 ∧ ∃ a : ℝ,
        net.init fl p w j = [a, 0, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] ∧
        |a - (val (tokAt w j) : ℝ)| ≤ 3 / 250 * |(val (tokAt w j) : ℝ)|) ∨
    (val (tokAt w j) = 0 ∧ ∃ b : ℝ,
        net.init fl p w j = [0, b, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] ∧
        |b - 1| ≤ 3 / 250) := by
  have ht := tok_le w hw j
  have hc : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4 ∨
      tokAt w j = 5 := by omega
  rcases hc with h | h | h | h | h | h
  · right
    exact ⟨by rw [h]; decide, init_unm hr hu0 hu1 p hp w j (by rw [h]; simp [net])⟩
  · left
    have hv : val (tokAt w j) = 2 := by rw [h]; decide
    rw [hv]
    exact ⟨by norm_num, init_mrk hr hu0 hu1 p hp w j 2 (by rw [h]; simp [net])⟩
  · left
    have hv : val (tokAt w j) = 3 := by rw [h]; decide
    rw [hv]
    exact ⟨by norm_num, init_mrk hr hu0 hu1 p hp w j 3 (by rw [h]; simp [net])⟩
  · left
    have hv : val (tokAt w j) = 1 := by rw [h]; decide
    rw [hv]
    exact ⟨by norm_num, init_mrk hr hu0 hu1 p hp w j 1 (by rw [h]; simp [net])⟩
  · right
    exact ⟨by rw [h]; decide, init_unm hr hu0 hu1 p hp w j (by rw [h]; simp [net])⟩
  · left
    have hv : val (tokAt w j) = 1 := by rw [h]; decide
    rw [hv]
    exact ⟨by norm_num, init_mrk hr hu0 hu1 p hp w j 1 (by rw [h]; simp [net])⟩

theorem init_any {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) (p : Pert) (hp : p.Within (1 / 200)) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    ∃ a1 b1 : ℝ, net.init fl p w j =
      [a1, b1, 0, 1, fl (j : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
  rcases init_cases hr hu0 hu1 p hp w hw j with ⟨_, a, h, _⟩ | ⟨_, b, h, _⟩
  · exact ⟨a, 0, h⟩
  · exact ⟨0, b, h⟩

/-! ### Scores -/

set_option maxHeartbeats 800000 in
theorem score_m {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a1 b1 qi qn a qj qn' : ℝ) :
    hd.score fl dA [a1, b1, 0, 1, qi, qn] [a, 0, 0, 1, qj, qn'] = fl (sw fl 1 (dA 3 4) * qj) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

set_option maxHeartbeats 800000 in
theorem score_u {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (dA : ℕ → ℕ → ℝ)
    (a1 b1 qi qn b qj qn' : ℝ) :
    hd.score fl dA [a1, b1, 0, 1, qi, qn] [0, b, 0, 1, qj, qn'] =
      fl (fl (sw fl 1 (dA 3 4) * qj) + fl (qn * fl (sw fl (-2) (dA 5 1) * b))) := by
  simp [Head.score, hd, z6, pdot, rmat, rdot, sw_zero hr, hr.zero, hr.idem]

theorem sc_mm {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {n : ℕ} (hn : u * (n : ℝ) ≤ 1 / 256) {S : ℝ}
    (hS : |S - 1| ≤ 3 / 250) {j k : ℕ} (hjk : j < k) (hkn : k ≤ n) :
    fl (S * fl (j : ℝ)) < fl (S * fl (k : ℝ)) := by
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hS0 : 0 ≤ S := by linarith
  have hg := hr.pos_gap hu0 hjk hkn hn
  have hk' := hr.pos_le hu0 hkn hn
  have hj' := hr.pos_le hu0 (show j ≤ n by omega) hn
  apply hr.lt_of_gap hu0 (B := 2 * ((n : ℝ) + 1 / 256))
  · rw [abs_of_nonneg (mul_nonneg hS0 hj'.1)]
    exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
  · rw [abs_of_nonneg (mul_nonneg hS0 hk'.1)]
    exact mul_le_mul (by linarith) hk'.2 hk'.1 (by norm_num)
  · have h1 := mul_le_mul_of_nonneg_left hg hS0
    nlinarith [h1, hn, hu0, hu1, hS1]

theorem sm_pos {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {n : ℕ} (hn : u * (n : ℝ) ≤ 1 / 256) {S : ℝ}
    (hS : |S - 1| ≤ 3 / 250) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    0 < fl (S * fl (j : ℝ)) := by
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hS0 : 0 ≤ S := by linarith
  have hg := hr.pos_gap hu0 (show 0 < j by omega) hjn hn
  simp only [Nat.cast_zero, hr.zero] at hg
  have hj' := hr.pos_le hu0 hjn hn
  have hSq0 : 0 ≤ S * fl (j : ℝ) := mul_nonneg hS0 hj'.1
  have hB : |S * fl (j : ℝ)| ≤ 2 * ((n : ℝ) + 1 / 256) := by
    rw [abs_of_nonneg hSq0]
    exact mul_le_mul (by linarith) hj'.2 hj'.1 (by norm_num)
  have h2 := hr.lower hu0 hB
  have h1 := mul_le_mul_of_nonneg_left hg hS0
  have hun : u * (2 * ((n : ℝ) + 1 / 256)) ≤ 1 / 50 := by nlinarith [hn, hu1, hu0]
  nlinarith [h1, h2, hun]

theorem sc_um {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 16777216) {n : ℕ} (hn2 : 2 ≤ n) (hn : u * (n : ℝ) ≤ 1 / 256)
    {S s2 b : ℝ} (hS : |S - 1| ≤ 3 / 250) (hs2 : |s2 + 2| ≤ 3 / 125)
    (hb : |b - 1| ≤ 3 / 250) {k : ℕ} (hkn : k ≤ n) :
    fl (fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (s2 * b))) ≤ 0 := by
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  obtain ⟨hs1, hs2'⟩ := abs_le.mp hs2
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hqk := hr.pos_le hu0 hkn hn
  have hqn := hr.pos_le hu0 (le_refl n) hn
  have hqn_lo : (n : ℝ) - 1 / 256 ≤ fl (n : ℝ) := by
    have := (abs_le.mp (hr.natCast_near n)).1
    linarith
  have hS0 : 0 ≤ S := by linarith
  have hSq0 : 0 ≤ S * fl (k : ℝ) := mul_nonneg hS0 hqk.1
  have hSqle : S * fl (k : ℝ) ≤ 253 / 250 * ((n : ℝ) + 1 / 256) :=
    mul_le_mul (by linarith) hqk.2 hqk.1 (by norm_num)
  have hXb : |S * fl (k : ℝ)| ≤ 2 * ((n : ℝ) + 1 / 256) := by
    rw [abs_of_nonneg hSq0]
    linarith
  have hX := hr.upper hu0 hXb
  have hsb_hi : s2 * b ≤ -39 / 20 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(s2 + 247 / 125) by linarith)
      (show (0 : ℝ) ≤ b by linarith)]
  have hsb_lo : -41 / 20 ≤ s2 * b := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ s2 + 253 / 125 by linarith)
      (show (0 : ℝ) ≤ b by linarith)]
  have hsb_abs : |s2 * b| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hT := hr.upper hu0 hsb_abs
  have hT' := hr.lower hu0 hsb_abs
  have hu3 : u * 3 ≤ 1 / 1000 := by linarith
  have hTup : fl (s2 * b) ≤ -19 / 10 := by linarith
  have hTlo : -21 / 10 ≤ fl (s2 * b) := by linarith
  have hqn0 : 0 ≤ fl (n : ℝ) := hqn.1
  have hY1 : fl (n : ℝ) * fl (s2 * b) ≤ -19 / 10 * fl (n : ℝ) := by
    nlinarith [mul_nonneg hqn0 (show (0 : ℝ) ≤ -19 / 10 - fl (s2 * b) by linarith)]
  have hY2 : -21 / 10 * fl (n : ℝ) ≤ fl (n : ℝ) * fl (s2 * b) := by
    nlinarith [mul_nonneg hqn0 (show (0 : ℝ) ≤ fl (s2 * b) + 21 / 10 by linarith)]
  have hYb : |fl (n : ℝ) * fl (s2 * b)| ≤ 3 * ((n : ℝ) + 1 / 256) :=
    abs_le.mpr ⟨by linarith [hqn.2], by linarith⟩
  have hY := hr.upper hu0 hYb
  have hun1 : u * (2 * ((n : ℝ) + 1 / 256)) ≤ 1 / 50 := by nlinarith [hn, hu1, hu0]
  have hun2 : u * (3 * ((n : ℝ) + 1 / 256)) ≤ 1 / 50 := by nlinarith [hn, hu1, hu0]
  have hsum : fl (S * fl (k : ℝ)) + fl (fl (n : ℝ) * fl (s2 * b)) ≤ 0 := by
    linarith
  have := hr.mono _ _ hsum
  rwa [hr.zero] at this

/-! ### Zero helpers -/

theorem rdot_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) :
    ∀ (row : List ℚ) (v : Vec) (d : ℕ → ℝ) (j : ℕ) (acc : ℝ),
      (∀ a ∈ row, a = 0) → acc = 0 → rdot fl row v d j acc = 0 := by
  intro row
  induction row with
  | nil =>
    intro v d j acc _ h
    first
      | simpa [rdot] using h
      | (show acc = 0; exact h)
  | cons a t ih =>
    intro v d j acc hz h
    cases v with
    | nil =>
      first
        | simpa [rdot] using h
        | (show acc = 0; exact h)
    | cons x v =>
      have ha : a = 0 := hz a (by simp)
      subst ha
      show rdot fl t v d (j + 1) (fl (acc + fl (sw fl 0 (d j) * x))) = 0
      refine ih v d (j + 1) _ (fun b hb => hz b (List.mem_cons_of_mem _ hb)) ?_
      rw [h, sw_zero hr, zero_mul, hr.zero, zero_add, hr.zero]

theorem rdot_cons0 {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (a : ℚ) (t : List ℚ)
    (ht : ∀ x ∈ t, x = 0) (v : Vec) (d : ℕ → ℝ) : rdot fl (a :: t) (0 :: v) d 0 0 = 0 := by
  show rdot fl t v d (0 + 1) (fl (0 + fl (sw fl a (d 0) * 0))) = 0
  rw [mul_zero, hr.zero, add_zero, hr.zero]
  exact rdot_zero hr t v d _ 0 ht rfl

theorem ravg_zero_of {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (f : ℕ → ℝ)
    (hf : ∀ j ∈ S, f j = 0) : ravg fl S f = 0 := by
  unfold ravg
  have hs : rsum fl (S.map f) 0 = 0 := by
    apply rsum_zeros hr
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact hf j hj
  rw [hs]
  simp [hr.zero]

theorem attnRows_zero {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (S : List ℕ) (x : ℕ → Vec)
    (dV : ℕ → ℕ → ℝ) :
    ∀ (rows : List (List ℚ)) (i : ℕ),
      (∀ r ∈ rows, ∀ j ∈ S, ∀ d : ℕ → ℝ, rdot fl r (x j) d 0 0 = 0) →
      attnRows fl rows dV S x i = rows.map (fun _ => (0 : ℝ)) := by
  intro rows
  induction rows with
  | nil =>
    intro i _
    simp [attnRows]
  | cons r M ih =>
    intro i h
    simp only [attnRows, List.map_cons]
    rw [ravg_zero_of hr S (fun j => rdot fl r (x j) (dV i) 0 0)
        (fun j hj => h r (by simp) j hj (dV i)),
      ih (i + 1) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

theorem hrow_shape (r : List ℚ) (hr : r ∈ hd.V) :
    ∃ a t, r = a :: t ∧ ∀ x ∈ t, x = (0 : ℚ) := by
  have hr' : r ∈ ([z6, z6, v2, z6, z6, z6] : List (List ℚ)) := hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  have h2 : r = z6 ∨ r = v2 := by tauto
  rcases h2 with rfl | rfl
  · exact ⟨0, [0, 0, 0, 0, 0], rfl, by simp⟩
  · exact ⟨1, [0, 0, 0, 0, 0], rfl, by simp⟩

/-! ### Output in closed form -/

set_option maxHeartbeats 800000 in
theorem out_A {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (i j : ℕ)
    (a1 b1 qi qn a qj qn' : ℝ)
    (hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j])
    (hxi : net.init fl p w i = [a1, b1, 0, 1, qi, qn])
    (hxj : net.init fl p w j = [a, 0, 0, 1, qj, qn']) :
    net.out fl p w i = fl (sw fl 1 (p.oW 2) * fl (sw fl 1 (p.V 0 0 2 0) * a)) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  have hV : hd.V = [z6, z6, v2, z6, z6, z6] := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, Head.attn, hsel, hV, attnRows,
    ravg_singleton hr]
  simp only [hxi, hxj]
  simp [z6, v2, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

set_option maxHeartbeats 800000 in
theorem out_B {u : ℝ} {fl : ℝ → ℝ} (hr : Rounding u fl) (p : Pert) (w : List ℕ) (i : ℕ)
    (a1 b1 qi qn : ℝ)
    (hattn : hd.attn fl (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i =
      [0, 0, 0, 0, 0, 0])
    (hxi : net.init fl p w i = [a1, b1, 0, 1, qi, qn]) :
    net.out fl p w i = 0 := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold TNet.out TNet.run
  rw [hb, ho, hc]
  simp only [runFrom, Block.apply, blk, headsApply, hattn, hxi]
  simp [z6, radd, raffine, rdot, sw_zero hr, hr.zero, hr.idem, hr.one, fl_sw hr]

/-! ### Main theorem -/

theorem net_ok : Statement net := by
  intro u fl hr hu0 hu1 p hp w hw hn i hi1 hi
  have hnr : 2 ≤ w.length + 1 := by omega
  obtain ⟨a1, b1, hxi⟩ := init_any hr hu0 hu1 p hp w hw i
  rcases last_marked w i hi with ⟨hz, ht⟩ | ⟨j, hj1, hji, hjm, hlast, ht⟩
  · -- no marked token among positions 1..i
    have hzc : ∀ k ∈ cand Mask.causal (w.length + 1) i,
        ∃ b : ℝ, net.init fl p w k =
          [0, b, 0, 1, fl (k : ℝ), fl ((w.length + 1 : ℕ) : ℝ)] := by
      intro k hk
      rw [Lane4.Seq.mem_cand_causal] at hk
      rcases init_cases hr hu0 hu1 p hp w hw k with ⟨hv, a, ha, _⟩ | ⟨_, b, hb, _⟩
      · exfalso
        apply hv
        by_cases hk0 : k = 0
        · rw [hk0, Lane4.Seq.tokAt_zero]
          decide
        · exact hz k (by omega) hk
      · exact ⟨b, hb⟩
    have hattn : hd.attn fl (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i =
        [0, 0, 0, 0, 0, 0] := by
      unfold Head.attn
      have hrows : ∀ r ∈ hd.V,
          ∀ j ∈ hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i,
          ∀ d : ℕ → ℝ, rdot fl r (net.init fl p w j) d 0 0 = 0 := by
        intro r hr' j hj d
        have hjc : j ∈ cand Mask.causal (w.length + 1) i :=
          ((Head.mem_sel hd fl (p.A 0 0) (w.length + 1) (net.init fl p w) i j).mp hj).1
        obtain ⟨b, hb⟩ := hzc j hjc
        rw [hb]
        obtain ⟨a, t, hat, ht'⟩ := hrow_shape r hr'
        rw [hat]
        exact rdot_cons0 hr a t ht' _ d
      rw [attnRows_zero hr _ (net.init fl p w) (p.V 0 0) hd.V 0 hrows]
      try rfl
    have hout := out_B hr p w i a1 b1 _ _ hattn hxi
    rw [hout, ht]
    norm_num
  · -- the last marked token is at position j
    rcases init_cases hr hu0 hu1 p hp w hw j with ⟨_, a, hxj, ha⟩ | ⟨hv, _⟩
    · have hS : |sw fl 1 (p.A 0 0 3 4) - 1| ≤ 3 / 250 := by
        have h := sw_rel hr hu0 1 (hp.A 0 0 3 4) (ε := 3 / 250) (by linarith)
        simp only [Rat.cast_one, abs_one, mul_one] at h
        exact h
      have hs2 : |sw fl (-2) (p.A 0 0 5 1) + 2| ≤ 3 / 125 := by
        have h := sw_rel hr hu0 (-2) (hp.A 0 0 5 1) (ε := 3 / 250) (by linarith)
        have e1 : (((-2 : ℚ)) : ℝ) = -2 := by norm_num
        have e2 : |(-2 : ℝ)| = 2 := by norm_num
        rw [e1, e2] at h
        rw [abs_le] at h ⊢
        constructor <;> linarith [h.1, h.2]
      have hsel : hd.sel fl (p.A 0 0) (w.length + 1) (net.init fl p w) i = [j] := by
        apply Head.sel_unique
        · show j ∈ cand Mask.causal (w.length + 1) i
          rw [Lane4.Seq.mem_cand_causal]
          exact hji
        · intro k hk hne
          have hk' : k ≤ i := by
            rw [show hd.mask = Mask.causal from rfl, Lane4.Seq.mem_cand_causal] at hk
            exact hk
          rw [hxi, hxj]
          rcases init_cases hr hu0 hu1 p hp w hw k with ⟨hvk, ak, hxk, _⟩ | ⟨hvk, bk, hxk, hbk⟩
          · rw [hxk, score_m hr, score_m hr]
            have hkj : k < j := by
              by_contra hcon
              have hjk : j < k := by omega
              exact hvk (hlast k hjk hk')
            exact sc_mm hr hu0 hu1 hn hS hkj (show j ≤ w.length + 1 by omega)
          · rw [hxk, score_u hr, score_m hr]
            exact lt_of_le_of_lt
              (sc_um hr hu0 hu1 hnr hn hS hs2 hbk (show k ≤ w.length + 1 by omega))
              (sm_pos hr hu0 hu1 hn hS hj1 (show j ≤ w.length + 1 by omega))
      have hout := out_A hr p w i j a1 b1 _ _ a _ _ hsel hxi hxj
      rw [hout, ht]
      have hc3 := val_le (tokAt w j)
      generalize val (tokAt w j) = c at ha hc3 ⊢
      have hS2' := sw_rel hr hu0 1 (hp.V 0 0 2 0) (ε := 3 / 250) (by linarith)
      have hO := sw_rel hr hu0 1 (hp.oW 2) (ε := 3 / 250) (by linarith)
      have h1 := rel_fl hr hu0 (rel_mul hS2' ha (c := 1 / 40) (by norm_num)) (c := 13 / 500)
        (by linarith)
      have h2 := rel_fl hr hu0 (rel_mul hO h1 (c := 1 / 25) (by norm_num)) (c := 21 / 500)
        (by linarith)
      simp only [Rat.cast_one, one_mul] at h2
      have hcr : |(c : ℝ)| ≤ 3 := by
        rw [abs_of_nonneg (Nat.cast_nonneg c)]
        exact_mod_cast hc3
      have := mul_le_mul_of_nonneg_left hcr (show (0 : ℝ) ≤ 21 / 500 by norm_num)
      linarith
    · exact absurd hv hjm

end Lane4.Case
