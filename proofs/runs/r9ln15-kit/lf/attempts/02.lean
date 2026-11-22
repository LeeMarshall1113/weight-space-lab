set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Lane4.Case
open Lane4.RSeq (Vec pdot radd rsum)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.LN Lane4.LNC Lane4.R7K2
open Lane4.LNKD

/-! ### list relations -/

theorem c_inffs_cons {e : ℕ → ℝ} {v : ℝ} {xs : List ℝ} {a : FF} {As : List FF} :
    InFFs e (v :: xs) (a :: As) ↔ InFF e v a ∧ InFFs e xs As := by
  unfold InFFs
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨?_, by simpa using hl, fun k hk => ?_⟩
    · simpa using h 0 (by simp)
    · have := h (k + 1) (by simpa using hk)
      simpa using this
  · rintro ⟨h0, hl, h⟩
    refine ⟨by simpa using hl, fun k hk => ?_⟩
    cases k with
    | zero => simpa using h0
    | succ k => simpa using h k (by simpa using hk)

theorem c_inffs_map (e : ℕ → ℝ) (F : ℝ → ℝ) (G : FF → FF) : ∀ (x : List ℝ) (X : List FF),
    InFFs e x X → (∀ v ∈ x, ∀ a ∈ X, InFF e v a → InFF e (F v) (G a)) →
    InFFs e (x.map F) (X.map G) := by
  intro x
  induction x with
  | nil =>
    intro X hx _
    cases X with
    | nil => exact ⟨by simp, fun k hk => by simp at hk⟩
    | cons a As => exact absurd hx.1 (by simp)
  | cons v xs ih =>
    intro X hx hP
    cases X with
    | nil => exact absurd hx.1 (by simp)
    | cons a As =>
      obtain ⟨ha, hrest⟩ := c_inffs_cons.mp hx
      simp only [List.map_cons]
      refine c_inffs_cons.mpr ⟨hP v (by simp) a (by simp) ha, ih As hrest ?_⟩
      intro v' hv' a' ha' h'
      exact hP v' (by simp [hv']) a' (by simp [ha']) h'

/-! ### forms -/

theorem c_linValI_sub (e : ℕ → ℝ) : ∀ (a b : List ℤ) (k : ℕ), a.length = b.length →
    linValI (List.zipWith (fun x y => x - y) a b) e k = linValI a e k - linValI b e k := by
  intro a
  induction a with
  | nil =>
    intro b k h
    cases b with
    | nil => simp [linValI]
    | cons _ _ => simp at h
  | cons x a ih =>
    intro b k h
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, linValI]
      rw [ih b (k + 1) (by simpa using h)]
      push_cast; ring

theorem c_inff_add (e : ℕ → ℝ) (v w : ℝ) (a b : FF) (hv : InFF e v a) (hw : InFF e w b)
    (hl : a.t.length = b.t.length) : InFF e (v + w) (a.add b) := by
  unfold InFF at hv hw ⊢
  simp only [FF.add]
  rw [linValI_zipWith_add e a.t b.t 0 hl]
  push_cast
  rw [abs_le] at hv hw ⊢
  constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]

theorem c_inff_sub (e : ℕ → ℝ) (v w : ℝ) (a b : FF) (hv : InFF e v a) (hw : InFF e w b)
    (hl : a.t.length = b.t.length) : InFF e (v - w) (a.sub b) := by
  unfold InFF at hv hw ⊢
  simp only [FF.sub]
  rw [c_linValI_sub e a.t b.t 0 hl]
  push_cast
  rw [abs_le] at hv hw ⊢
  constructor <;> linarith [hv.1, hv.2, hw.1, hw.2]

theorem c_wide_gen {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (z f : ℝ)
    (s : FF) (m : ℤ) (hs : InFF e z s) (hf : |f - z| ≤ u * |z| + η)
    (hz : |z| * 2 ^ 56 ≤ (m : ℝ)) : InFF e f (s.wide (chg m)) := by
  have h1 := round_chg hC.u0 hC.u1 hC.h0 hC.h1 z m hz
  unfold InFF at hs ⊢
  simp only [FF.wide]
  push_cast
  have e1 : f * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)
      = (f - z) * 2 ^ 56 + (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) := by ring
  rw [e1]
  have h2 : |(f - z) * 2 ^ 56| = |f - z| * 2 ^ 56 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  have h3 : |f - z| * 2 ^ 56 ≤ (u * |z| + η) * 2 ^ 56 :=
    mul_le_mul_of_nonneg_right hf (by norm_num)
  have h4 := abs_add_le ((f - z) * 2 ^ 56) (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0))
  linarith

theorem c_iabs_add (x y : ℤ) : iabs (x + y) ≤ iabs x + iabs y := by
  rw [iabs_eq', iabs_eq', iabs_eq']; exact abs_add_le x y

theorem c_iabs_sub (x y : ℤ) : iabs (x - y) ≤ iabs x + iabs y := by
  rw [iabs_eq', iabs_eq', iabs_eq']
  calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

theorem c_linI_zip (f : ℤ → ℤ → ℤ) (hf : ∀ x y, iabs (f x y) ≤ iabs x + iabs y) :
    ∀ a b : List ℤ, linI (List.zipWith f a b) ≤ linI a + linI b := by
  intro a
  induction a with
  | nil =>
    intro b
    rw [List.zipWith_nil_left, linI_nil']
    have := linI_nonneg b
    omega
  | cons x a ih =>
    intro b
    cases b with
    | nil =>
      rw [List.zipWith_nil_right, linI_nil']
      have := linI_nonneg (x :: a)
      omega
    | cons y b =>
      rw [List.zipWith_cons_cons, linI_cons, linI_cons, linI_cons]
      have h1 := hf x y
      have h2 := ih b
      omega

theorem c_mag_add (a b : FF) : (a.add b).mag ≤ a.mag + b.mag := by
  have h1 := c_linI_zip (fun x y => x + y) c_iabs_add a.t b.t
  have h2 := c_iabs_add a.c b.c
  show iabs (a.c + b.c) + (linI (List.zipWith (fun x y => x + y) a.t b.t) + (a.r + b.r))
    ≤ (iabs a.c + (linI a.t + a.r)) + (iabs b.c + (linI b.t + b.r))
  omega

theorem c_linI_rep : ∀ n, linI (List.replicate n (0 : ℤ)) = 0
  | 0 => linI_nil'
  | n + 1 => by
    rw [List.replicate_succ, linI_cons, c_linI_rep n]
    simp [iabs]

theorem c_zero_mag (ns : ℕ) : (zeroF ns).mag = 0 := by
  show iabs 0 + (linI (List.replicate ns (0 : ℤ)) + 0) = 0
  rw [c_linI_rep]
  simp [iabs]

theorem c_fold_mag (B : ℤ) : ∀ (X : List FF) (acc : FF), (∀ a ∈ X, a.mag ≤ B) →
    (X.foldl FF.add acc).mag ≤ acc.mag + (X.length : ℤ) * B := by
  intro X
  induction X with
  | nil => intro acc _; simp
  | cons a As ih =>
    intro acc h
    have hf : (a :: As).foldl FF.add acc = As.foldl FF.add (acc.add a) := rfl
    rw [hf]
    have h1 := ih (acc.add a) (fun b hb => h b (by simp [hb]))
    have h2 := c_mag_add acc a
    have h3 := h a (by simp)
    simp only [List.length_cons]
    push_cast
    nlinarith

theorem c_fold_max : ∀ (X : List FF) (acc : ℤ),
    acc ≤ X.foldl (fun m x => max m x.mag) acc ∧
    ∀ a ∈ X, a.mag ≤ X.foldl (fun m x => max m x.mag) acc := by
  intro X
  induction X with
  | nil => intro acc; simp
  | cons a As ih =>
    intro acc
    have hf : (a :: As).foldl (fun m x => max m x.mag) acc
        = As.foldl (fun m x => max m x.mag) (max acc a.mag) := rfl
    rw [hf]
    obtain ⟨h1, h2⟩ := ih (max acc a.mag)
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · rw [h]; exact le_trans (le_max_right _ _) h1
    · exact h2 b h

theorem c_fold_le (B : ℤ) : ∀ (X : List FF) (acc : ℤ), acc ≤ B → (∀ a ∈ X, a.mag ≤ B) →
    X.foldl (fun m x => max m x.mag) acc ≤ B := by
  intro X
  induction X with
  | nil => intro acc h _; simpa using h
  | cons a As ih =>
    intro acc h hX
    have hf : (a :: As).foldl (fun m x => max m x.mag) acc
        = As.foldl (fun m x => max m x.mag) (max acc a.mag) := rfl
    rw [hf]
    exact ih _ (max_le h (hX a (by simp))) (fun b hb => hX b (by simp [hb]))

theorem c_sumform (e : ℕ → ℝ) (ns : ℕ) : ∀ (x : List ℝ) (X : List FF) (acc : FF) (v0 : ℝ),
    InFF e v0 acc → acc.t.length = ns → (∀ a ∈ X, a.t.length = ns) → InFFs e x X →
    InFF e (v0 + sumL x) (X.foldl FF.add acc) ∧ (X.foldl FF.add acc).t.length = ns := by
  intro x
  induction x with
  | nil =>
    intro X acc v0 h0 hl hX hx
    cases X with
    | nil =>
      have h : sumL ([] : List ℝ) = 0 := rfl
      simp only [List.foldl_nil, h, add_zero]
      exact ⟨h0, hl⟩
    | cons a As => exact absurd hx.1 (by simp)
  | cons v xs ih =>
    intro X acc v0 h0 hl hX hx
    cases X with
    | nil => exact absurd hx.1 (by simp)
    | cons a As =>
      obtain ⟨ha, hrest⟩ := c_inffs_cons.mp hx
      have hat : a.t.length = ns := hX a (by simp)
      have hadd := c_inff_add e v0 v acc a h0 ha (by rw [hl, hat])
      have hlen : (acc.add a).t.length = ns := by
        simp [FF.add, List.length_zipWith, hl, hat]
      have := ih As (acc.add a) (v0 + v) hadd hlen (fun b hb => hX b (by simp [hb])) hrest
      have e1 : v0 + sumL (v :: xs) = (v0 + v) + sumL xs := by
        have : sumL (v :: xs) = v + sumL xs := rfl
        rw [this]; ring
      have hf : (a :: As).foldl FF.add acc = As.foldl FF.add (acc.add a) := rfl
      rw [e1, hf]
      exact this

theorem c_vals (e : ℕ → ℝ) (he : Sym e) (mx : ℤ) : ∀ (x : List ℝ) (X : List FF), InFFs e x X →
    (∀ a ∈ X, a.mag ≤ mx) → ∀ v ∈ x, |v| * 2 ^ 56 ≤ (mx : ℝ) := by
  intro x
  induction x with
  | nil => intro X _ _ v hv; simp at hv
  | cons v0 xs ih =>
    intro X hx hm v hv
    cases X with
    | nil => exact absurd hx.1 (by simp)
    | cons a As =>
      obtain ⟨ha, hrest⟩ := c_inffs_cons.mp hx
      rcases List.mem_cons.mp hv with h | h
      · rw [h]
        have := (box_sound e v0 a he ha).2.2
        have h2 : (a.mag : ℝ) ≤ mx := by exact_mod_cast hm a (by simp)
        linarith
      · exact ih As hrest (fun b hb => hm b (by simp [hb])) v h

theorem c_abs_sum : ∀ l : List ℝ, |sumL l| ≤ sumAbsL l
  | [] => by simp [sumL, sumAbsL]
  | a :: l => by
    have ih := c_abs_sum l
    have e1 : sumL (a :: l) = a + sumL l := rfl
    have e2 : sumAbsL (a :: l) = |a| + sumAbsL l := rfl
    rw [e1, e2]
    exact le_trans (abs_add_le _ _) (by linarith)

/-! ### the mean -/

theorem c_mean_arith (u η N m : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2 ^ 149) (hN : 1 ≤ N) (hm : 0 ≤ m) :
    (1 + u) * (2 * u * N * m + 2 * η * 2 ^ 56) + u * m + η * 2 ^ 56
      ≤ N * ((9 / 10) * (m / 2 ^ 22) + 1 / 10) := by
  have hNm : 0 ≤ N * m := mul_nonneg (by linarith) hm
  have hmN : m ≤ N * m := by nlinarith
  have h1 : u * (N * m) ≤ (1 / 2 ^ 24) * (N * m) := mul_le_mul_of_nonneg_right hu hNm
  have h2 : u * m ≤ (1 / 2 ^ 24) * m := mul_le_mul_of_nonneg_right hu hm
  have h3 : η * 2 ^ 56 ≤ 1 / 2 ^ 93 := by
    calc η * 2 ^ 56 ≤ (1 / 2 ^ 149) * 2 ^ 56 := mul_le_mul_of_nonneg_right hη (by norm_num)
      _ = 1 / 2 ^ 93 := by norm_num
  have h3' : 0 ≤ η * 2 ^ 56 := mul_nonneg hη0 (by norm_num)
  have h4 : u * (u * (N * m)) ≤ (1 / 2 ^ 24) * ((1 / 2 ^ 24) * (N * m)) :=
    mul_le_mul hu h1 (mul_nonneg hu0 hNm) (by norm_num)
  have hu1 : u ≤ 1 := le_trans hu (by norm_num)
  have h5 : u * (η * 2 ^ 56) ≤ 1 * (1 / 2 ^ 93) := mul_le_mul hu1 h3 h3' zero_le_one
  nlinarith [h1, h2, h3, h4, h5, hmN]

theorem c_mean_err {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (x : List ℝ)
    (hn1 : 1 ≤ x.length) (hn32 : x.length ≤ 32) (m : ℝ) (hm0 : 0 ≤ m) (hm16 : m ≤ 16 * 2 ^ 56)
    (hmx : ∀ v ∈ x, |v| ≤ m / 2 ^ 56) :
    |fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)| * 2 ^ 56
      ≤ (x.length : ℝ) * ((9 / 10) * (m / 2 ^ 22) + 1 / 10) := by
  have hN1 : (1 : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast hn1
  have hN32 : (x.length : ℝ) ≤ 32 := by exact_mod_cast hn32
  have hv30 : ∀ v ∈ x, |v| ≤ 2 ^ 30 := by
    intro v hv
    have h1 := hmx v hv
    have h2 : m / 2 ^ 56 ≤ 16 := by rw [div_le_iff₀ (by norm_num)]; linarith
    have : (16 : ℝ) ≤ 2 ^ 30 := by norm_num
    linarith
  have hR := Lane4.LNKA.rsum_rel u η M fl hC x hn32 hv30
  have hsA : sumAbsL x ≤ m / 2 ^ 56 * (x.length : ℝ) :=
    Lane4.LNKA.la_sumAbsL_le (m / 2 ^ 56) x hmx
  have hσ : |sumL x| ≤ sumAbsL x := c_abs_sum x
  generalize (x.length : ℝ) = N at hR hsA hN1 hN32 ⊢
  generalize rsum fl x 0 = r at hR ⊢
  generalize sumL x = σ at hR hσ ⊢
  generalize sumAbsL x = sA at hR hsA hσ
  have hu0 := hC.u0
  have hu := hC.u1
  have hη0 := hC.h0
  have hη := hC.h1
  have hNpos : 0 < N := by linarith
  have hS : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hsAS : sA * 2 ^ 56 ≤ N * m := by
    have h1 := mul_le_mul_of_nonneg_right hsA hS.le
    have e1 : m / 2 ^ 56 * N * 2 ^ 56 = N * m := by
      have : (2 : ℝ) ^ 56 ≠ 0 := by norm_num
      field_simp
    linarith
  have hd1 : |r / N - σ / N| * 2 ^ 56 ≤ 2 * u * N * m + 2 * η * 2 ^ 56 := by
    have e1 : r / N - σ / N = (r - σ) / N := by ring
    rw [e1, abs_div, abs_of_pos hNpos]
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    have h1 : |r - σ| * 2 ^ 56 ≤ (2 * N * u * sA + 2 * N * η) * 2 ^ 56 :=
      mul_le_mul_of_nonneg_right hR hS.le
    have h2 : u * (sA * 2 ^ 56) ≤ u * (N * m) := mul_le_mul_of_nonneg_left hsAS hu0
    have h3 := mul_le_mul_of_nonneg_left h2 hNpos.le
    nlinarith [h1, h3]
  have hσN : |σ / N| * 2 ^ 56 ≤ m := by
    rw [abs_div, abs_of_pos hNpos, div_mul_eq_mul_div, div_le_iff₀ hNpos]
    have := mul_le_mul_of_nonneg_right hσ hS.le
    nlinarith [this, hsAS]
  have hB1 : 0 ≤ 2 * u * N * m + 2 * η * 2 ^ 56 := by
    have h1 : 0 ≤ u * N * m := mul_nonneg (mul_nonneg hu0 hNpos.le) hm0
    have h2 : 0 ≤ η * 2 ^ 56 := mul_nonneg hη0 hS.le
    linarith
  have hq1 : |r / N| ≤ |σ / N| + |r / N - σ / N| := by
    have h := abs_add_le (σ / N) (r / N - σ / N)
    have e : σ / N + (r / N - σ / N) = r / N := by ring
    rw [e] at h
    exact h
  have hqS : |r / N| * 2 ^ 56 ≤ m + (2 * u * N * m + 2 * η * 2 ^ 56) := by
    have := mul_le_mul_of_nonneg_right hq1 hS.le
    linarith
  have hu1 : u ≤ 1 := le_trans hu (by norm_num)
  have hqM : |r / N| ≤ M := by
    have hu32 : u * N ≤ 32 := by
      calc u * N ≤ 1 * N := mul_le_mul_of_nonneg_right hu1 hNpos.le
        _ ≤ 32 := by linarith
    have h1 : u * N * m ≤ 32 * m := mul_le_mul_of_nonneg_right hu32 hm0
    have h2 : η * 2 ^ 56 ≤ 1 / 2 ^ 93 := by
      calc η * 2 ^ 56 ≤ (1 / 2 ^ 149) * 2 ^ 56 := mul_le_mul_of_nonneg_right hη (by norm_num)
        _ = 1 / 2 ^ 93 := by norm_num
    have h3 : |r / N| * 2 ^ 56 ≤ 2000 * 2 ^ 56 := by nlinarith
    have h4 : |r / N| ≤ 2000 := le_of_mul_le_mul_right h3 hS
    have := hC.M1
    have : (2000 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  have hf := hC.rnd.err (r / N) hqM
  have hT := abs_add_le (fl (r / N) - r / N) (r / N - σ / N)
  have e2 : fl (r / N) - r / N + (r / N - σ / N) = fl (r / N) - σ / N := by ring
  rw [e2] at hT
  have hT2 := mul_le_mul_of_nonneg_right hT hS.le
  have h6 := mul_le_mul_of_nonneg_right hf hS.le
  have h7 : u * (|r / N| * 2 ^ 56) ≤ u * (m + (2 * u * N * m + 2 * η * 2 ^ 56)) :=
    mul_le_mul_of_nonneg_left hqS hu0
  have hfin := c_mean_arith u η N m hu0 hu hη0 hη hN1 hm0
  nlinarith [hT2, h6, h7, hfin, hd1]

theorem c_floor_abs (a n : ℤ) (hn : 0 < n) : |((a / n : ℤ) : ℝ)| ≤ |(a : ℝ)| / n + 1 := by
  have h := floor_facts a n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : |(a : ℝ) / n| = |(a : ℝ)| / n := by rw [abs_div, abs_of_pos hn']
  have h1 := le_abs_self ((a : ℝ) / n)
  have h2 := neg_abs_le ((a : ℝ) / n)
  rw [e] at h1 h2
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem c_linI_div (n : ℤ) (hn : 0 < n) : ∀ t : List ℤ,
    ((linI (t.map (fun x => x / n)) : ℤ) : ℝ) ≤ (linI t : ℝ) / n + (t.length : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro t
  induction t with
  | nil => simp [linI_nil']
  | cons x l ih =>
    rw [List.map_cons, linI_cons, linI_cons]
    push_cast
    rw [iabs_cast, iabs_cast]
    have h1 := c_floor_abs x n hn
    simp only [List.length_cons]
    push_cast
    have e : ((|(x : ℝ)| + (linI l : ℝ)) / n) = |(x : ℝ)| / n + (linI l : ℝ) / n := by ring
    rw [e]
    linarith

theorem c_mean_core {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (he : Sym e)
    (ns : ℕ) (x : List ℝ) (hn1 : 1 ≤ x.length) (hn32 : x.length ≤ 32)
    (s : FF) (hs : InFF e (sumL x) s) (hslen : s.t.length = ns) (mxI : ℤ) (hm0 : 0 ≤ mxI)
    (hm16 : mxI ≤ 16 * SC) (hmx : ∀ v ∈ x, |v| * 2 ^ 56 ≤ (mxI : ℝ)) :
    InFF e (fl (rsum fl x 0 / (x.length : ℝ)))
      ⟨s.c / (x.length : ℤ), s.t.map (fun t => t / (x.length : ℤ)),
        cdiv s.r (x.length : ℤ) + ((ns : ℤ) + 1) + (x.length : ℤ) * chg mxI⟩ := by
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hnZ : (0 : ℤ) < (x.length : ℤ) := by omega
  have hN1 : (1 : ℝ) ≤ (x.length : ℝ) := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < (x.length : ℝ) := by linarith
  have hS : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hm0' : 0 ≤ (mxI : ℝ) := by exact_mod_cast hm0
  have hm16' : (mxI : ℝ) ≤ 16 * 2 ^ 56 := by
    have : (mxI : ℝ) ≤ ((16 * SC : ℤ) : ℝ) := by exact_mod_cast hm16
    rw [Int.cast_mul, hSC] at this
    simpa using this
  have hmx' : ∀ v ∈ x, |v| ≤ (mxI : ℝ) / 2 ^ 56 := fun v hv => by
    rw [le_div_iff₀ (by norm_num)]; exact hmx v hv
  have herr := c_mean_err hC x hn1 hn32 (mxI : ℝ) hm0' hm16' hmx'
  have hchg := chg_facts mxI hm0
  have hfs := floor_facts s.c (x.length : ℤ) hnZ
  have hcd := cdiv_facts s.r (x.length : ℤ) hnZ
  have hlin := map_floor_err e he 1 (x.length : ℤ) hnZ s.t 0
  simp only [one_mul, Int.cast_one] at hlin
  push_cast at hfs hcd hlin
  rw [hslen] at hlin
  unfold InFF at hs ⊢
  show |fl (rsum fl x 0 / (x.length : ℝ)) * 2 ^ 56
      - (((s.c / (x.length : ℤ) : ℤ) : ℝ) + linValI (s.t.map (fun t => t / (x.length : ℤ))) e 0)|
    ≤ ((cdiv s.r (x.length : ℤ) + ((ns : ℤ) + 1) + (x.length : ℤ) * chg mxI : ℤ) : ℝ)
  push_cast
  have hb : |(sumL x / (x.length : ℝ)) * 2 ^ 56
      - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ))|
      ≤ (s.r : ℝ) / (x.length : ℝ) := by
    have e1 : (sumL x / (x.length : ℝ)) * 2 ^ 56
        - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ))
        = (sumL x * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) / (x.length : ℝ) := by
      field_simp
    rw [e1, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right hs hNpos.le
  have herr2 : |(fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)) * 2 ^ 56|
      ≤ (x.length : ℝ) * ((chg mxI : ℤ) : ℝ) := by
    rw [abs_mul, abs_of_pos hS]
    refine le_trans herr ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hchg.1, hchg.2]) hNpos.le
  have hC1 : |(s.c : ℝ) / (x.length : ℝ) - ((s.c / (x.length : ℤ) : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hfs.1, hfs.2]
  have key : fl (rsum fl x 0 / (x.length : ℝ)) * 2 ^ 56
      - (((s.c / (x.length : ℤ) : ℤ) : ℝ) + linValI (s.t.map (fun t => t / (x.length : ℤ))) e 0)
      = (fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)) * 2 ^ 56
        + ((sumL x / (x.length : ℝ)) * 2 ^ 56
          - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ)))
        + ((s.c : ℝ) / (x.length : ℝ) - ((s.c / (x.length : ℤ) : ℤ) : ℝ))
        + (1 / (x.length : ℝ) * linValI s.t e 0
          - linValI (s.t.map (fun t => t / (x.length : ℤ))) e 0) := by
    ring
  rw [key]
  have t1 := abs_add_le ((fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)) * 2 ^ 56
        + ((sumL x / (x.length : ℝ)) * 2 ^ 56
          - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ)))
        + ((s.c : ℝ) / (x.length : ℝ) - ((s.c / (x.length : ℤ) : ℤ) : ℝ)))
      (1 / (x.length : ℝ) * linValI s.t e 0
          - linValI (s.t.map (fun t => t / (x.length : ℤ))) e 0)
  have t2 := abs_add_le ((fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)) * 2 ^ 56
        + ((sumL x / (x.length : ℝ)) * 2 ^ 56
          - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ))))
      ((s.c : ℝ) / (x.length : ℝ) - ((s.c / (x.length : ℤ) : ℤ) : ℝ))
  have t3 := abs_add_le ((fl (rsum fl x 0 / (x.length : ℝ)) - sumL x / (x.length : ℝ)) * 2 ^ 56)
      ((sumL x / (x.length : ℝ)) * 2 ^ 56
          - ((s.c : ℝ) / (x.length : ℝ) + linValI s.t e 0 / (x.length : ℝ)))
  linarith [hcd.1]

theorem c_mean_mag (ns : ℕ) (hns : ns ≤ 1024) (n : ℕ) (hn1 : 1 ≤ n) (hn32 : n ≤ 32)
    (s : FF) (hslen : s.t.length = ns) (hsmag : (s.mag : ℝ) ≤ (n : ℝ) * (16 * 2 ^ 56))
    (mxI : ℤ) (hm0 : 0 ≤ mxI) (hm16 : mxI ≤ 16 * SC) :
    ((FF.mag ⟨s.c / (n : ℤ), s.t.map (fun t => t / (n : ℤ)),
        cdiv s.r (n : ℤ) + ((ns : ℤ) + 1) + (n : ℤ) * chg mxI⟩ : ℤ) : ℝ) ≤ 17 * 2 ^ 56 := by
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hnZ : (0 : ℤ) < (n : ℤ) := by omega
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hN32 : (n : ℝ) ≤ 32 := by exact_mod_cast hn32
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hns' : (ns : ℝ) ≤ 1024 := by exact_mod_cast hns
  have hm0' : 0 ≤ (mxI : ℝ) := by exact_mod_cast hm0
  have hm16' : (mxI : ℝ) ≤ 16 * 2 ^ 56 := by
    have : (mxI : ℝ) ≤ ((16 * SC : ℤ) : ℝ) := by exact_mod_cast hm16
    rw [Int.cast_mul, hSC] at this
    simpa using this
  have L1 := c_floor_abs s.c (n : ℤ) hnZ
  have L2 := c_linI_div (n : ℤ) hnZ s.t
  have L3 := cdiv_facts s.r (n : ℤ) hnZ
  have hch : ((chg mxI : ℤ) : ℝ) ≤ (mxI : ℝ) / 2 ^ 22 + 1 := by
    have h := floor_facts mxI (2 ^ 22) (by norm_num)
    have e : ((2 ^ 22 : ℤ) : ℝ) = 2 ^ 22 := by norm_num
    rw [e] at h
    have e2 : chg mxI = mxI / 2 ^ 22 + 1 := rfl
    rw [e2]
    push_cast
    linarith [h.1]
  push_cast at L1 L2 L3
  rw [hslen] at L2
  have e0 : ((FF.mag ⟨s.c / (n : ℤ), s.t.map (fun t => t / (n : ℤ)),
        cdiv s.r (n : ℤ) + ((ns : ℤ) + 1) + (n : ℤ) * chg mxI⟩ : ℤ) : ℝ)
      = |((s.c / (n : ℤ) : ℤ) : ℝ)| + ((linI (s.t.map (fun t => t / (n : ℤ))) : ℤ) : ℝ)
        + (((cdiv s.r (n : ℤ) : ℤ) : ℝ) + ((ns : ℝ) + 1) + (n : ℝ) * ((chg mxI : ℤ) : ℝ)) := by
    unfold FF.mag FF.dev
    push_cast
    rw [iabs_cast]
    ring
  have e1 : (s.mag : ℝ) = |(s.c : ℝ)| + ((linI s.t : ℤ) : ℝ) + (s.r : ℝ) := by
    unfold FF.mag FF.dev
    push_cast
    rw [iabs_cast]
    ring
  rw [e0]
  have hmg : (|(s.c : ℝ)| + ((linI s.t : ℤ) : ℝ) + (s.r : ℝ)) / (n : ℝ) ≤ 16 * 2 ^ 56 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hnch : (n : ℝ) * ((chg mxI : ℤ) : ℝ) ≤ 32 * (16 * 2 ^ 34 + 1) := by
    have h1 : ((chg mxI : ℤ) : ℝ) ≤ 16 * 2 ^ 34 + 1 := by
      have : (mxI : ℝ) / 2 ^ 22 ≤ 16 * 2 ^ 34 := by
        rw [div_le_iff₀ (by norm_num)]; linarith
      linarith
    have h2 : (0 : ℝ) ≤ ((chg mxI : ℤ) : ℝ) := by
      have := chg_facts mxI hm0
      linarith [this.2]
    calc (n : ℝ) * ((chg mxI : ℤ) : ℝ) ≤ (n : ℝ) * (16 * 2 ^ 34 + 1) :=
          mul_le_mul_of_nonneg_left h1 hNpos.le
      _ ≤ 32 * (16 * 2 ^ 34 + 1) := mul_le_mul_of_nonneg_right hN32 (by norm_num)
  have hsplit : (|(s.c : ℝ)| + ((linI s.t : ℤ) : ℝ) + (s.r : ℝ)) / (n : ℝ)
      = |(s.c : ℝ)| / (n : ℝ) + (linI s.t : ℝ) / (n : ℝ) + (s.r : ℝ) / (n : ℝ) := by ring
  nlinarith [L1, L2, L3.2, hmg, hnch, hsplit]

/-! ### centring -/

theorem c_cent_entry {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (e : ℕ → ℝ) (he : Sym e)
    (v mf : ℝ) (a mean : FF) (hv : InFF e v a) (hm : InFF e mf mean)
    (hl : a.t.length = mean.t.length) (hav : |v| ≤ 16) (hmf : |mf| ≤ 17) :
    InFF e (fl (v - mf)) ((a.sub mean).wide (chg (a.mag + mean.mag))) := by
  have hz := c_inff_sub e v mf a mean hv hm hl
  have hzM : |v - mf| ≤ M := by
    have h1 := hC.M1
    have h2 : |v - mf| ≤ |v| + |mf| := by
      calc |v - mf| = |v + -mf| := by rw [sub_eq_add_neg]
        _ ≤ |v| + |-mf| := abs_add_le _ _
        _ = |v| + |mf| := by rw [abs_neg]
    have : (33 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith
  have hf := hC.rnd.err (v - mf) hzM
  have hb1 := (box_sound e v a he hv).2.2
  have hb2 := (box_sound e mf mean he hm).2.2
  have hzb : |v - mf| * 2 ^ 56 ≤ ((a.mag + mean.mag : ℤ) : ℝ) := by
    have h2 : |v - mf| ≤ |v| + |mf| := by
      calc |v - mf| = |v + -mf| := by rw [sub_eq_add_neg]
        _ ≤ |v| + |-mf| := abs_add_le _ _
        _ = |v| + |mf| := by rw [abs_neg]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 2 ^ 56)]
  exact c_wide_gen hC e (v - mf) _ _ _ hz hf hzb

theorem cent_sound : CentSound := by
  intro u η M fl hC ns x X e he hns hn1 hn32 hx hsh
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hXl : X.length = x.length := hx.1.symm
  have hlen : ∀ a ∈ X, a.t.length = ns := fun a ha => (hsh a ha).1
  have hmag : ∀ a ∈ X, a.mag ≤ 16 * SC := fun a ha => (hsh a ha).2
  obtain ⟨mxI, hmxI⟩ : ∃ m : ℤ, m = X.foldl (fun m (x : FF) => max m x.mag) 0 := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : FF, s = X.foldl FF.add (zeroF ns) := ⟨_, rfl⟩
  have hmean : meanF ns X = ⟨s.c / (x.length : ℤ), s.t.map (fun t => t / (x.length : ℤ)),
      cdiv s.r (x.length : ℤ) + ((ns : ℤ) + 1) + (x.length : ℤ) * chg mxI⟩ := by
    rw [hsd, hmxI]
    simp only [meanF, hXl]
  obtain ⟨hmax1, hmax2⟩ := c_fold_max X 0
  rw [← hmxI] at hmax1 hmax2
  have hm16 : mxI ≤ 16 * SC := by
    rw [hmxI]; exact c_fold_le (16 * SC) X 0 (by unfold SC; norm_num) hmag
  have hmx := c_vals e he mxI x X hx hmax2
  have hz0 : InFF e 0 (zeroF ns) := by
    show |(0 : ℝ) * 2 ^ 56 - (((0 : ℤ) : ℝ) + linValI (List.replicate ns (0 : ℤ)) e 0)|
      ≤ ((0 : ℤ) : ℝ)
    rw [linValI_replicate]
    simp
  have hzlen : (zeroF ns).t.length = ns := by simp [zeroF]
  obtain ⟨hs, hslen⟩ := c_sumform e ns x X (zeroF ns) 0 hz0 hzlen hlen hx
  rw [← hsd, zero_add] at hs
  rw [← hsd] at hslen
  have hsmagZ : s.mag ≤ (x.length : ℤ) * (16 * SC) := by
    have := c_fold_mag (16 * SC) X (zeroF ns) hmag
    rw [c_zero_mag, ← hsd, hXl] at this
    omega
  have hsmag : (s.mag : ℝ) ≤ (x.length : ℝ) * (16 * 2 ^ 56) := by
    have : (s.mag : ℝ) ≤ (((x.length : ℤ) * (16 * SC) : ℤ) : ℝ) := by exact_mod_cast hsmagZ
    rw [Int.cast_mul, Int.cast_mul, hSC] at this
    simpa using this
  have hmeanIn : InFF e (fl (rsum fl x 0 / (x.length : ℝ))) (meanF ns X) := by
    rw [hmean]
    exact c_mean_core hC e he ns x hn1 hn32 s hs hslen mxI hmax1 hm16 hmx
  have hmeanLen : (meanF ns X).t.length = ns := by
    rw [hmean]
    show (s.t.map (fun t => t / (x.length : ℤ))).length = ns
    rw [List.length_map]; exact hslen
  have hmeanMag : ((meanF ns X).mag : ℝ) ≤ 17 * 2 ^ 56 := by
    rw [hmean]
    exact c_mean_mag ns hns x.length hn1 hn32 s hslen hsmag mxI hmax1 hm16
  have hmeanMagZ : (meanF ns X).mag ≤ 17 * SC := by
    have : ((meanF ns X).mag : ℝ) ≤ ((17 * SC : ℤ) : ℝ) := by
      rw [Int.cast_mul, hSC]; simpa using hmeanMag
    exact_mod_cast this
  have hmf : |fl (rsum fl x 0 / (x.length : ℝ))| ≤ 17 := by
    have := (box_sound e _ _ he hmeanIn).2.2
    have h2 : |fl (rsum fl x 0 / (x.length : ℝ))| * 2 ^ 56 ≤ 17 * 2 ^ 56 := le_trans this hmeanMag
    exact le_of_mul_le_mul_right h2 (by norm_num)
  have hcentF : centF (meanF ns X) X
      = X.map (fun a => (a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))) := rfl
  have hcentL : lnCentre fl x
      = x.map (fun v => fl (v - fl (rsum fl x 0 / (x.length : ℝ)))) := rfl
  refine ⟨?_, ?_⟩
  · rw [hcentF, hcentL]
    apply c_inffs_map e _ _ x X hx
    intro v _ a ha hva
    have hb := (box_sound e v a he hva).2.2
    have hmg : (a.mag : ℝ) ≤ 16 * 2 ^ 56 := by
      have : (a.mag : ℝ) ≤ ((16 * SC : ℤ) : ℝ) := by exact_mod_cast hmag a ha
      rw [Int.cast_mul, hSC] at this
      simpa using this
    have hav : |v| ≤ 16 := by
      have : |v| * 2 ^ 56 ≤ 16 * 2 ^ 56 := le_trans hb hmg
      exact le_of_mul_le_mul_right this (by norm_num)
    exact c_cent_entry hC e he v _ a _ hva hmeanIn (by rw [hlen a ha, hmeanLen]) hav hmf
  · intro c hc
    rw [hcentF] at hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    have hat := hlen a ha
    have hmg : (a.mag : ℝ) ≤ 16 * 2 ^ 56 := by
      have : (a.mag : ℝ) ≤ ((16 * SC : ℤ) : ℝ) := by exact_mod_cast hmag a ha
      rw [Int.cast_mul, hSC] at this
      simpa using this
    refine ⟨?_, ?_⟩
    · show (List.zipWith (fun x y => x - y) a.t (meanF ns X).t).length = ns
      rw [List.length_zipWith, hat, hmeanLen]; simp
    · have h1 := c_linI_zip (fun x y => x - y) c_iabs_sub a.t (meanF ns X).t
      have h2 := c_iabs_sub a.c (meanF ns X).c
      have ha' : a.mag = iabs a.c + (linI a.t + a.r) := rfl
      have hm' : (meanF ns X).mag = iabs (meanF ns X).c + (linI (meanF ns X).t + (meanF ns X).r) := rfl
      show ((a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))).mag ≤ 64 * SC
      have hint : ((a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))).mag
          ≤ a.mag + (meanF ns X).mag + chg (a.mag + (meanF ns X).mag) := by
        show iabs (a.c - (meanF ns X).c) + (linI (List.zipWith (fun x y => x - y) a.t (meanF ns X).t)
            + (a.r + (meanF ns X).r + chg (a.mag + (meanF ns X).mag)))
          ≤ a.mag + (meanF ns X).mag + chg (a.mag + (meanF ns X).mag)
        omega
      have hchg : ((chg (a.mag + (meanF ns X).mag) : ℤ) : ℝ)
          ≤ ((a.mag + (meanF ns X).mag : ℤ) : ℝ) / 2 ^ 22 + 1 := by
        have h := floor_facts (a.mag + (meanF ns X).mag) (2 ^ 22) (by norm_num)
        have e : ((2 ^ 22 : ℤ) : ℝ) = 2 ^ 22 := by norm_num
        rw [e] at h
        have e2 : chg (a.mag + (meanF ns X).mag) = (a.mag + (meanF ns X).mag) / 2 ^ 22 + 1 := rfl
        rw [e2]
        push_cast at h ⊢
        linarith [h.1]
      have hcast : (((a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))).mag : ℝ)
          ≤ (a.mag : ℝ) + ((meanF ns X).mag : ℝ) + ((chg (a.mag + (meanF ns X).mag) : ℤ) : ℝ) := by
        exact_mod_cast hint
      push_cast at hchg
      have h33 : ((a.mag : ℝ) + ((meanF ns X).mag : ℝ)) / 2 ^ 22 ≤ 33 * 2 ^ 34 := by
        rw [div_le_iff₀ (by norm_num)]; linarith
      have hreal : (((a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))).mag : ℝ)
          ≤ 64 * 2 ^ 56 := by linarith
      have : (((a.sub (meanF ns X)).wide (chg (a.mag + (meanF ns X).mag))).mag : ℝ)
          ≤ ((64 * SC : ℤ) : ℝ) := by
        rw [Int.cast_mul, hSC]; simpa using hreal
      exact_mod_cast this

end Lane4.Case
