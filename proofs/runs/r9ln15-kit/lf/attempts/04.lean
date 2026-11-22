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


/-! ### variance: the form -/

theorem c_wide_add (e : ℕ → ℝ) (z f : ℝ) (s : FF) (R : ℤ) (hs : InFF e z s)
    (hf : |f - z| * 2 ^ 56 ≤ (R : ℝ)) : InFF e f (s.wide R) := by
  unfold InFF at hs ⊢
  simp only [FF.wide]
  push_cast
  have e1 : f * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)
      = (f - z) * 2 ^ 56 + (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0)) := by ring
  rw [e1]
  have h2 : |(f - z) * 2 ^ 56| = |f - z| * 2 ^ 56 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 56)]
  have h4 := abs_add_le ((f - z) * 2 ^ 56) (z * 2 ^ 56 - ((s.c : ℝ) + linValI s.t e 0))
  linarith

theorem v_foldl (l : List ℤ) : ∀ s : ℤ, l.foldl (fun s v => s + v) s = s + l.sum := by
  induction l with
  | nil => intro s; simp
  | cons a l ih => intro s; simp [List.foldl, ih]; ring

theorem v_sumI (l : List ℤ) : sumI l = l.sum := by
  unfold sumI; rw [v_foldl]; simp

theorem v_sumI_cons (a : ℤ) (l : List ℤ) : sumI (a :: l) = a + sumI l := by
  rw [v_sumI, v_sumI]; simp

theorem v_linValI_lin (e : ℕ → ℝ) (w : ℤ) : ∀ (a b : List ℤ) (k : ℕ), a.length = b.length →
    linValI (List.zipWith (fun x y => w * x + y) a b) e k = (w : ℝ) * linValI a e k + linValI b e k := by
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

theorem v_lcT_len (ns : ℕ) : ∀ (w : List ℤ) (C : List FF), (∀ a ∈ C, a.t.length = ns) →
    (lcT ns w C).length = ns := by
  intro w
  induction w with
  | nil =>
    intro C _
    show (List.replicate ns (0 : ℤ)).length = ns
    simp
  | cons w0 ws ih =>
    intro C h
    cases C with
    | nil =>
      show (List.replicate ns (0 : ℤ)).length = ns
      simp
    | cons x xs =>
      have hx := h x (by simp)
      have h2 := ih xs (fun a ha => h a (by simp [ha]))
      show (List.zipWith (fun a b => w0 * a + b) x.t (lcT ns ws xs)).length = ns
      rw [List.length_zipWith, hx, h2]
      simp

theorem v_sumform (e : ℕ → ℝ) (he : Sym e) (ns : ℕ) : ∀ (c : List ℝ) (C : List FF),
    InFFs e c C → (∀ a ∈ C, a.t.length = ns) →
    ∃ E : ℝ, sumL (c.map (fun v => v * v)) * 2 ^ 112
        = ((sumI (C.map (fun a => a.c * a.c)) : ℤ) : ℝ)
          + linValI (lcT ns (C.map (fun a => 2 * a.c)) C) e 0 + E
      ∧ |E| ≤ ((sumI (C.map (fun a => 2 * iabs a.c * a.r + a.dev * a.dev)) : ℤ) : ℝ) := by
  intro c
  induction c with
  | nil =>
    intro C hx hl
    cases C with
    | nil =>
      refine ⟨0, ?_, ?_⟩
      · have h1 : sumL (([] : List ℝ).map (fun v => v * v)) = 0 := rfl
        have h2 : sumI (([] : List FF).map (fun a => a.c * a.c)) = 0 := rfl
        have h3 : lcT ns (([] : List FF).map (fun a => 2 * a.c)) [] = List.replicate ns 0 := rfl
        rw [h1, h2, h3, linValI_replicate]
        simp
      · have h2 : sumI (([] : List FF).map (fun a => 2 * iabs a.c * a.r + a.dev * a.dev)) = 0 := rfl
        rw [h2]
        simp
    | cons a As => exact absurd hx.1 (by simp)
  | cons v cs ih =>
    intro C hx hl
    cases C with
    | nil => exact absurd hx.1 (by simp)
    | cons a As =>
      obtain ⟨ha, hrest⟩ := c_inffs_cons.mp hx
      obtain ⟨E', hE', hb'⟩ := ih As hrest (fun b hb => hl b (by simp [hb]))
      have hat : a.t.length = ns := hl a (by simp)
      have hlenT : (lcT ns (As.map (fun a => 2 * a.c)) As).length = ns :=
        v_lcT_len ns _ As (fun b hb => hl b (by simp [hb]))
      have hlc : lcT ns ((a :: As).map (fun a => 2 * a.c)) (a :: As)
          = List.zipWith (fun x y => (2 * a.c) * x + y) a.t
              (lcT ns (As.map (fun a => 2 * a.c)) As) := rfl
      have hval := v_linValI_lin e (2 * a.c) a.t (lcT ns (As.map (fun a => 2 * a.c)) As) 0
        (by rw [hat, hlenT])
      have hd := inff_dev e v a he ha
      have hρ : |v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)| ≤ (a.r : ℝ) := ha
      have e1 : sumL ((v :: cs).map (fun v => v * v))
          = v * v + sumL (cs.map (fun v => v * v)) := rfl
      have hk : sumI ((a :: As).map (fun a => a.c * a.c))
          = a.c * a.c + sumI (As.map (fun a => a.c * a.c)) := by
        rw [List.map_cons, v_sumI_cons]
      have hg : sumI ((a :: As).map (fun a => 2 * iabs a.c * a.r + a.dev * a.dev))
          = (2 * iabs a.c * a.r + a.dev * a.dev)
            + sumI (As.map (fun a => 2 * iabs a.c * a.r + a.dev * a.dev)) := by
        rw [List.map_cons, v_sumI_cons]
      refine ⟨E' + (2 * (a.c : ℝ) * (v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0))
          + (v * 2 ^ 56 - (a.c : ℝ)) ^ 2), ?_, ?_⟩
      · rw [e1, hk, hlc, hval]
        push_cast
        linear_combination hE'
      · rw [hg]
        push_cast
        rw [iabs_cast]
        have h2 : |2 * (a.c : ℝ) * (v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0))|
            ≤ 2 * |(a.c : ℝ)| * (a.r : ℝ) := by
          rw [abs_mul, abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left hρ (by positivity)
        have h3 : (v * 2 ^ 56 - (a.c : ℝ)) ^ 2 ≤ (a.dev : ℝ) * (a.dev : ℝ) := by
          have h := abs_le.mp hd
          nlinarith [mul_nonneg (sub_nonneg.2 h.2) (by linarith [h.1] : (0 : ℝ) ≤ (a.dev : ℝ) + (v * 2 ^ 56 - (a.c : ℝ)))]
        have h4 : |(v * 2 ^ 56 - (a.c : ℝ)) ^ 2| = (v * 2 ^ 56 - (a.c : ℝ)) ^ 2 := abs_of_nonneg (sq_nonneg _)
        have t1 := abs_add_le E' (2 * (a.c : ℝ) * (v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0))
          + (v * 2 ^ 56 - (a.c : ℝ)) ^ 2)
        have t2 := abs_add_le (2 * (a.c : ℝ) * (v * 2 ^ 56 - ((a.c : ℝ) + linValI a.t e 0)))
          ((v * 2 ^ 56 - (a.c : ℝ)) ^ 2)
        linarith

theorem v_form_core (e : ℕ → ℝ) (he : Sym e) (ns : ℕ) (Q N : ℝ) (D K G : ℤ) (T : List ℤ) (E : ℝ)
    (hNpos : 0 < N) (hD : 0 < D) (hDc : (D : ℝ) = N * 2 ^ 56) (hTlen : T.length = ns)
    (hE : Q * 2 ^ 112 = (K : ℝ) + linValI T e 0 + E) (hEb : |E| ≤ (G : ℝ)) :
    InFF e (Q / N + 1 / 100000) ⟨K / D + EPSI, T.map (fun x => x / D), cdiv G D + ((ns : ℤ) + 3)⟩ := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hfs := floor_facts K D hD
  have hcd := cdiv_facts G D hD
  have hlin := map_floor_err e he 1 D hD T 0
  simp only [one_mul, Int.cast_one] at hlin
  rw [hTlen] at hlin
  have hep : ((EPSI : ℤ) : ℝ) ≤ 2 ^ 56 / 100000 ∧ 2 ^ 56 / 100000 < ((EPSI : ℤ) : ℝ) + 1 := by
    have h := floor_facts SC 100000 (by norm_num)
    have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
    rw [hSC] at h
    have e2 : ((100000 : ℤ) : ℝ) = 100000 := by norm_num
    rw [e2] at h
    exact h
  have hQ : Q / N * 2 ^ 56 = (K : ℝ) / D + linValI T e 0 / D + E / D := by
    have h1 : Q / N * 2 ^ 56 = (Q * 2 ^ 112) / (D : ℝ) := by
      rw [hDc]
      have : N ≠ 0 := hNpos.ne'
      first | (field_simp; ring) | field_simp
    rw [h1, hE]; ring
  unfold InFF
  show |(Q / N + 1 / 100000) * 2 ^ 56
      - (((K / D + EPSI : ℤ) : ℝ) + linValI (T.map (fun x => x / D)) e 0)|
    ≤ ((cdiv G D + ((ns : ℤ) + 3) : ℤ) : ℝ)
  push_cast
  have hC1 : |(K : ℝ) / D - ((K / D : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hfs.1, hfs.2]
  have hC2 : |(2 : ℝ) ^ 56 / 100000 - ((EPSI : ℤ) : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hep.1, hep.2]
  have hC3 : |E / (D : ℝ)| ≤ ((cdiv G D : ℤ) : ℝ) := by
    rw [abs_div, abs_of_pos hDpos]
    exact le_trans (div_le_div_of_nonneg_right hEb hDpos.le) hcd.1
  have key : (Q / N + 1 / 100000) * 2 ^ 56
      - (((K / D : ℤ) : ℝ) + ((EPSI : ℤ) : ℝ) + linValI (T.map (fun x => x / D)) e 0)
      = ((K : ℝ) / D - ((K / D : ℤ) : ℝ))
        + (1 / (D : ℝ) * linValI T e 0 - linValI (T.map (fun x => x / D)) e 0)
        + E / (D : ℝ) + ((2 : ℝ) ^ 56 / 100000 - ((EPSI : ℤ) : ℝ)) := by
    linear_combination hQ
  rw [key]
  have t1 := abs_add_le (((K : ℝ) / D - ((K / D : ℤ) : ℝ))
        + (1 / (D : ℝ) * linValI T e 0 - linValI (T.map (fun x => x / D)) e 0)
        + E / (D : ℝ)) ((2 : ℝ) ^ 56 / 100000 - ((EPSI : ℤ) : ℝ))
  have t2 := abs_add_le (((K : ℝ) / D - ((K / D : ℤ) : ℝ))
        + (1 / (D : ℝ) * linValI T e 0 - linValI (T.map (fun x => x / D)) e 0))
        (E / (D : ℝ))
  have t3 := abs_add_le ((K : ℝ) / D - ((K / D : ℤ) : ℝ))
        (1 / (D : ℝ) * linValI T e 0 - linValI (T.map (fun x => x / D)) e 0)
  linarith

theorem v_form (e : ℕ → ℝ) (he : Sym e) (ns : ℕ) (c : List ℝ) (C : List FF) (hn1 : 1 ≤ c.length)
    (hx : InFFs e c C) (hl : ∀ a ∈ C, a.t.length = ns) :
    InFF e (sumL (c.map (fun v => v * v)) / (c.length : ℝ) + 1 / 100000)
      (varF ns (c.length : ℤ) C) := by
  obtain ⟨E, hE, hEb⟩ := v_sumform e he ns c C hx hl
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hNpos : (0 : ℝ) < (c.length : ℝ) := by exact_mod_cast (by omega : 0 < c.length)
  have hD : (0 : ℤ) < (c.length : ℤ) * SC := mul_pos (by omega) (by unfold SC; norm_num)
  have hDc : (((c.length : ℤ) * SC : ℤ) : ℝ) = (c.length : ℝ) * 2 ^ 56 := by
    rw [Int.cast_mul, hSC]; simp
  exact v_form_core e he ns _ (c.length : ℝ) ((c.length : ℤ) * SC) _ _ _ _ hNpos hD hDc
    (v_lcT_len ns _ C hl) hE hEb

/-! ### variance: rounding -/

theorem v_sq {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (v : ℝ) (hv : |v| ≤ 64) :
    |fl (v * v) - v * v| ≤ u * (v * v) + η ∧ 0 ≤ v * v ∧ v * v ≤ 4096 := by
  have hv0 : 0 ≤ v * v := mul_self_nonneg v
  have hv2 : v * v ≤ 4096 := by
    have h := abs_mul_abs_self v
    have : |v| * |v| ≤ 64 * 64 := mul_le_mul hv hv (abs_nonneg v) (by norm_num)
    linarith
  refine ⟨?_, hv0, hv2⟩
  have herr := hC.rnd.err (v * v) (by
    rw [abs_of_nonneg hv0]; have := hC.M1; have : (4096 : ℝ) ≤ 2 ^ 40 := by norm_num
    linarith)
  rw [abs_of_nonneg hv0] at herr
  exact herr

theorem v_sum_err {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) : ∀ c : List ℝ, (∀ v ∈ c, |v| ≤ 64) →
    |sumL (c.map (fun v => fl (v * v))) - sumL (c.map (fun v => v * v))|
        ≤ u * sumL (c.map (fun v => v * v)) + η * (c.length : ℝ)
    ∧ sumAbsL (c.map (fun v => fl (v * v)))
        ≤ (1 + u) * sumL (c.map (fun v => v * v)) + η * (c.length : ℝ)
    ∧ 0 ≤ sumL (c.map (fun v => v * v))
    ∧ sumL (c.map (fun v => v * v)) ≤ 4096 * (c.length : ℝ) := by
  intro c
  induction c with
  | nil => intro _; simp [sumL, sumAbsL]
  | cons v cs ih =>
    intro h
    obtain ⟨i1, i2, i3, i4⟩ := ih (fun w hw => h w (by simp [hw]))
    obtain ⟨herr, hv0, hv2⟩ := v_sq hC v (h v (by simp))
    have e1 : sumL ((v :: cs).map (fun v => fl (v * v)))
        = fl (v * v) + sumL (cs.map (fun v => fl (v * v))) := rfl
    have e2 : sumL ((v :: cs).map (fun v => v * v)) = v * v + sumL (cs.map (fun v => v * v)) := rfl
    have e3 : sumAbsL ((v :: cs).map (fun v => fl (v * v)))
        = |fl (v * v)| + sumAbsL (cs.map (fun v => fl (v * v))) := rfl
    have hl : ((v :: cs).length : ℝ) = (cs.length : ℝ) + 1 := by simp
    rw [e1, e2, e3, hl]
    have hp : |fl (v * v)| ≤ v * v + (u * (v * v) + η) := by
      have h' := abs_le.mp herr
      rw [abs_le]; constructor <;> linarith [h'.1, h'.2, hv0]
    have e4 : fl (v * v) + sumL (cs.map (fun v => fl (v * v)))
        - (v * v + sumL (cs.map (fun v => v * v)))
        = (fl (v * v) - v * v) + (sumL (cs.map (fun v => fl (v * v)))
          - sumL (cs.map (fun v => v * v))) := by ring
    have t := abs_add_le (fl (v * v) - v * v) (sumL (cs.map (fun v => fl (v * v)))
          - sumL (cs.map (fun v => v * v)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e4]; nlinarith [t, herr, i1]
    · nlinarith [hp, i2]
    · linarith
    · linarith

theorem v_arith {u η : ℝ} {fl : ℝ → ℝ} (N A r : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hN1 : 1 ≤ N) (hN32 : N ≤ 32) (hA : 0 ≤ A)
    (hA4 : A ≤ 4096)
    (hFL : ∀ x : ℝ, |x| ≤ 2 ^ 20 → |fl x - x| ≤ u * |x| + η)
    (hr : |r - A * N| ≤ u * (A * N) + N * η + 2 * N * u * ((1 + u) * (A * N) + N * η) + 2 * N * η) :
    |fl (fl (r / N) + fl (1 / 100000)) - (A + 1 / 100000)| * 2 ^ 56
      ≤ (N + 3) * ((9 / 10) * ((A + 1 / 100000) * 2 ^ 56 / 2 ^ 22) + 1 / 10) := by
  have hNpos : 0 < N := by linarith
  have hS : (0 : ℝ) < 2 ^ 56 := by norm_num
  have hT1 : 0 ≤ A * N := mul_nonneg hA hNpos.le
  have hNη : 0 ≤ N * η := mul_nonneg hNpos.le hη0
  have s1 : |r - A * N| ≤ N * ((2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) * A + 6 * η) := by
    refine le_trans hr ?_
    have a : u * (A * N) ≤ (1 / 2 ^ 24) * (A * N) := mul_le_mul_of_nonneg_right hu hT1
    have b : u * (u * (A * N)) ≤ (1 / 2 ^ 24) * ((1 / 2 ^ 24) * (A * N)) :=
      mul_le_mul hu a (mul_nonneg hu0 hT1) (by norm_num)
    have c : N * (u * (A * N)) ≤ N * ((1 / 2 ^ 24) * (A * N)) := mul_le_mul_of_nonneg_left a hNpos.le
    have d : N * (u * (u * (A * N))) ≤ N * ((1 / 2 ^ 24) * ((1 / 2 ^ 24) * (A * N))) :=
      mul_le_mul_of_nonneg_left b hNpos.le
    have f : u * η ≤ (1 / 2 ^ 24) * η := mul_le_mul_of_nonneg_right hu hη0
    have g' : N * (N * (u * η)) ≤ N * (N * ((1 / 2 ^ 24) * η)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left f hNpos.le) hNpos.le
    have h32 : N * (N * ((1 / 2 ^ 24) * η)) ≤ N * η := by
      have h1 : N * (1 / 2 ^ 24) ≤ 1 := by linarith
      calc N * (N * ((1 / 2 ^ 24) * η)) = (N * (1 / 2 ^ 24)) * (N * η) := by ring
        _ ≤ 1 * (N * η) := mul_le_mul_of_nonneg_right h1 hNη
        _ = N * η := one_mul _
    nlinarith [a, c, d, g', h32, hT1, hNη]
  have hb' : (2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) ≤ 1 / 2 ^ 17 := by linarith
  have hb0 : 0 ≤ (2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) := by
    have : 0 ≤ (2 * N + 1) := by linarith
    positivity
  have s2 : |r / N - A| ≤ (2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) * A + 6 * η := by
    have e1 : r / N - A = (r - A * N) / N := by field_simp
    rw [e1, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith [s1]
  have hbA : (2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) * A ≤ 1 / 2 ^ 17 * 4096 :=
    mul_le_mul hb' hA4 hA (by norm_num)
  have s3 : |r / N| ≤ A + ((2 * N + 1) * (1 / 2 ^ 24) * (1 + 1 / 2 ^ 24) * A + 6 * η) := by
    have h := abs_add_le A (r / N - A)
    have e : A + (r / N - A) = r / N := by ring
    rw [e, abs_of_nonneg hA] at h
    linarith [s2]
  have hq20 : |r / N| ≤ 2 ^ 20 := by
    have : (4096 : ℝ) + 1 / 2 ^ 17 * 4096 + 6 * (1 / 2 ^ 149) ≤ 2 ^ 20 := by norm_num
    linarith
  have hf1 := hFL (r / N) hq20
  have hf1' : |fl (r / N) - r / N| ≤ (1 / 2 ^ 24) * |r / N| + η :=
    le_trans hf1 (by have := mul_le_mul_of_nonneg_right hu (abs_nonneg (r / N)); linarith)
  have hg := hFL (1 / 100000) (by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100000)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100000)] at hg
  have hg' : |fl (1 / 100000) - 1 / 100000| ≤ (1 / 2 ^ 24) * (1 / 100000) + η :=
    le_trans hg (by have := mul_le_mul_of_nonneg_right hu (by norm_num : (0 : ℝ) ≤ 1 / 100000); linarith)
  have hfb : |fl (r / N)| ≤ 5000 := by
    have h := abs_add_le (fl (r / N) - r / N) (r / N)
    have e : fl (r / N) - r / N + r / N = fl (r / N) := by ring
    rw [e] at h
    have h5 : (1 / 2 ^ 24 : ℝ) * (4096 + 1 / 2 ^ 17 * 4096 + 6 * (1 / 2 ^ 149)) ≤ 1 := by norm_num
    have h6 : (1 / 2 ^ 24 : ℝ) * |r / N| ≤ (1 / 2 ^ 24 : ℝ) * (4096 + 1 / 2 ^ 17 * 4096 + 6 * (1 / 2 ^ 149)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    linarith
  have hgb : |fl (1 / 100000)| ≤ 1 := by
    have h := abs_add_le (fl (1 / 100000) - 1 / 100000) (1 / 100000)
    have e : fl (1 / 100000) - 1 / 100000 + 1 / 100000 = fl (1 / 100000) := by ring
    rw [e, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100000)] at h
    have : (1 / 2 ^ 24 : ℝ) * (1 / 100000) + 1 / 2 ^ 149 + 1 / 100000 ≤ 1 := by norm_num
    linarith
  have hsum : |fl (r / N) + fl (1 / 100000)| ≤ 2 ^ 20 := by
    have h := abs_add_le (fl (r / N)) (fl (1 / 100000))
    have : (5001 : ℝ) ≤ 2 ^ 20 := by norm_num
    linarith
  have hvh := hFL (fl (r / N) + fl (1 / 100000)) hsum
  have hvh' : |fl (fl (r / N) + fl (1 / 100000)) - (fl (r / N) + fl (1 / 100000))|
      ≤ (1 / 2 ^ 24) * |fl (r / N) + fl (1 / 100000)| + η :=
    le_trans hvh (by have := mul_le_mul_of_nonneg_right hu (abs_nonneg (fl (r / N) + fl (1 / 100000))); linarith)
  have t1 : |fl (fl (r / N) + fl (1 / 100000)) - (A + 1 / 100000)|
      ≤ |fl (fl (r / N) + fl (1 / 100000)) - (fl (r / N) + fl (1 / 100000))|
        + |fl (r / N) - A| + |fl (1 / 100000) - 1 / 100000| := by
    have e : fl (fl (r / N) + fl (1 / 100000)) - (A + 1 / 100000)
        = (fl (fl (r / N) + fl (1 / 100000)) - (fl (r / N) + fl (1 / 100000)))
          + (fl (r / N) - A) + (fl (1 / 100000) - 1 / 100000) := by ring
    rw [e]
    have h1 := abs_add_le ((fl (fl (r / N) + fl (1 / 100000)) - (fl (r / N) + fl (1 / 100000)))
          + (fl (r / N) - A)) (fl (1 / 100000) - 1 / 100000)
    have h2 := abs_add_le (fl (fl (r / N) + fl (1 / 100000)) - (fl (r / N) + fl (1 / 100000)))
          (fl (r / N) - A)
    linarith
  have t2 : |fl (r / N) - A| ≤ |fl (r / N) - r / N| + |r / N - A| := by
    have e : fl (r / N) - A = (fl (r / N) - r / N) + (r / N - A) := by ring
    rw [e]; exact abs_add_le _ _
  have t3 : |fl (r / N) + fl (1 / 100000)|
      ≤ (A + 1 / 100000) + |fl (r / N) - A| + |fl (1 / 100000) - 1 / 100000| := by
    have e : fl (r / N) + fl (1 / 100000)
        = (A + 1 / 100000) + (fl (r / N) - A) + (fl (1 / 100000) - 1 / 100000) := by ring
    rw [e]
    have h1 := abs_add_le ((A + 1 / 100000) + (fl (r / N) - A)) (fl (1 / 100000) - 1 / 100000)
    have h2 := abs_add_le (A + 1 / 100000) (fl (r / N) - A)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A + 1 / 100000)] at h2
    linarith
  nlinarith [t1, t2, t3, hf1', hg', hvh', s2, s3, hT1, hNη]

theorem v_round {u η M : ℝ} {fl : ℝ → ℝ} (hC : Ctx u η M fl) (c : List ℝ) (hn1 : 1 ≤ c.length)
    (hn32 : c.length ≤ 32) (hc : ∀ v ∈ c, |v| ≤ 64) :
    |fl (fl (rsum fl (c.map (fun v => fl (v * v))) 0 / (c.length : ℝ)) + fl (1 / 100000))
      - (sumL (c.map (fun v => v * v)) / (c.length : ℝ) + 1 / 100000)| * 2 ^ 56
      ≤ ((c.length : ℝ) + 3) * ((9 / 10) * ((sumL (c.map (fun v => v * v)) / (c.length : ℝ)
          + 1 / 100000) * 2 ^ 56 / 2 ^ 22) + 1 / 10) := by
  obtain ⟨i1, i2, i3, i4⟩ := v_sum_err hC c hc
  have hN1 : (1 : ℝ) ≤ (c.length : ℝ) := by exact_mod_cast hn1
  have hN32 : (c.length : ℝ) ≤ 32 := by exact_mod_cast hn32
  have hNpos : (0 : ℝ) < (c.length : ℝ) := by linarith
  have hu0 := hC.u0
  have hu := hC.u1
  have hη0 := hC.h0
  have hη := hC.h1
  have hu1 : u ≤ 1 := le_trans hu (by norm_num)
  have hp30 : ∀ p ∈ c.map (fun v => fl (v * v)), |p| ≤ 2 ^ 30 := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨herr, hv0, hv2⟩ := v_sq hC v (hc v hv)
    have h1 : u * (v * v) ≤ 1 * 4096 := mul_le_mul hu1 hv2 hv0 zero_le_one
    have h2 : η ≤ 1 := le_trans hη (by norm_num)
    have h3 := abs_le.mp herr
    have : (4096 : ℝ) + 4096 + 1 ≤ 2 ^ 30 := by norm_num
    rw [abs_le]
    constructor <;> nlinarith [h3.1, h3.2, hv0, hv2]
  have hR := Lane4.LNKA.rsum_rel u η M fl hC (c.map (fun v => fl (v * v)))
    (by simpa using hn32) hp30
  simp only [List.length_map] at hR
  have hAN : sumL (c.map (fun v => v * v)) / (c.length : ℝ) * (c.length : ℝ)
      = sumL (c.map (fun v => v * v)) := by field_simp
  have hmul : 2 * (c.length : ℝ) * u * sumAbsL (c.map (fun v => fl (v * v)))
      ≤ 2 * (c.length : ℝ) * u * ((1 + u) * sumL (c.map (fun v => v * v)) + η * (c.length : ℝ)) :=
    mul_le_mul_of_nonneg_left i2 (mul_nonneg (mul_nonneg (by norm_num) hNpos.le) hu0)
  have hr : |rsum fl (c.map (fun v => fl (v * v))) 0
        - sumL (c.map (fun v => v * v)) / (c.length : ℝ) * (c.length : ℝ)|
      ≤ u * (sumL (c.map (fun v => v * v)) / (c.length : ℝ) * (c.length : ℝ))
        + (c.length : ℝ) * η
        + 2 * (c.length : ℝ) * u * ((1 + u) * (sumL (c.map (fun v => v * v)) / (c.length : ℝ)
            * (c.length : ℝ)) + (c.length : ℝ) * η)
        + 2 * (c.length : ℝ) * η := by
    rw [hAN]
    have t := abs_add_le (rsum fl (c.map (fun v => fl (v * v))) 0 - sumL (c.map (fun v => fl (v * v))))
      (sumL (c.map (fun v => fl (v * v))) - sumL (c.map (fun v => v * v)))
    have e : rsum fl (c.map (fun v => fl (v * v))) 0 - sumL (c.map (fun v => fl (v * v)))
        + (sumL (c.map (fun v => fl (v * v))) - sumL (c.map (fun v => v * v)))
        = rsum fl (c.map (fun v => fl (v * v))) 0 - sumL (c.map (fun v => v * v)) := by ring
    rw [e] at t
    nlinarith [t, hR, i1, hmul]
  have hA4 : sumL (c.map (fun v => v * v)) / (c.length : ℝ) ≤ 4096 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hA0 : 0 ≤ sumL (c.map (fun v => v * v)) / (c.length : ℝ) := div_nonneg i3 hNpos.le
  have hFL : ∀ x : ℝ, |x| ≤ 2 ^ 20 → |fl x - x| ≤ u * |x| + η := by
    intro x hx
    apply hC.rnd.err
    have := hC.M1
    have : (2 : ℝ) ^ 20 ≤ 2 ^ 40 := by norm_num
    linarith
  exact v_arith (c.length : ℝ) _ _ hu0 hu hη0 hη hN1 hN32 hA0 hA4 hFL hr

theorem var_sound : VarSound := by
  intro u η M fl hC ns c C e he hn1 hn32 hx hsh
  have hSC : ((SC : ℤ) : ℝ) = 2 ^ 56 := by unfold SC; norm_num
  have hXl : C.length = c.length := hx.1.symm
  have hlen : ∀ a ∈ C, a.t.length = ns := fun a ha => (hsh a ha).1
  have hvals := c_vals e he (64 * SC) c C hx (fun a ha => (hsh a ha).2)
  have hc : ∀ v ∈ c, |v| ≤ 64 := by
    intro v hv
    have h1 := hvals v hv
    have : ((64 * SC : ℤ) : ℝ) = 64 * 2 ^ 56 := by rw [Int.cast_mul, hSC]; norm_num
    rw [this] at h1
    exact le_of_mul_le_mul_right h1 (by norm_num)
  have hNpos : (0 : ℝ) < (c.length : ℝ) := by exact_mod_cast (by omega : 0 < c.length)
  have hform := v_form e he ns c C hn1 hx hlen
  have hbox := (box_sound e _ _ he hform).2.2
  obtain ⟨i1, i2, i3, i4⟩ := v_sum_err hC c hc
  have hround := v_round hC c hn1 hn32 hc
  have hvarW : varW ns C = (varF ns (c.length : ℤ) C).wide
      (((c.length : ℤ) + 3) * chg (varF ns (c.length : ℤ) C).mag) := by
    simp only [varW, hXl]
  rw [hvarW]
  refine ⟨?_, ?_⟩
  · apply c_wide_add e _ _ _ _ hform
    have hm0 : 0 ≤ (varF ns (c.length : ℤ) C).mag := by
      have : (0 : ℝ) ≤ (((varF ns (c.length : ℤ) C).mag : ℤ) : ℝ) :=
        le_trans (by positivity) hbox
      exact_mod_cast this
    have hch := chg_facts _ hm0
    have hV0 : 0 ≤ sumL (c.map (fun v => v * v)) / (c.length : ℝ) + 1 / 100000 := by
      have := div_nonneg i3 hNpos.le
      linarith
    rw [abs_of_nonneg hV0] at hbox
    push_cast
    refine le_trans hround ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith [hch.1, hch.2]
  · show (List.map (fun x => x / ((c.length : ℤ) * SC))
        (lcT ns (C.map (fun a => 2 * a.c)) C)).length = ns
    rw [List.length_map]
    exact v_lcT_len ns _ C hlen

end Lane4.Case
