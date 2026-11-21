set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Lane4.Case
open Lane4.RSeq (Vec pdot)
open Lane4.RSoft Lane4.AGate

theorem close_len {x xh : List ℝ} {e X : ℝ} (h : Close x xh e X) : x.length = xh.length := by
  unfold Close at h
  exact h.1

theorem close_cons {a b : ℝ} {x y : List ℝ} {e X : ℝ} (h : Close (a :: x) (b :: y) e X) :
    |a - b| ≤ e ∧ |b| ≤ X ∧ Close x y e X := by
  unfold Close at h
  obtain ⟨hl, hk⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hk 0 (by simp)
    simpa using this.1
  · have := hk 0 (by simp)
    simpa using this.2
  · simpa using hl
  · intro k hk'
    have := hk (k + 1) (by simp only [List.length_cons]; omega)
    simpa using this

theorem ar_step {u η M δ : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hM : 1073741824 ≤ M) (a : ℚ) (v vh d : ℝ) (W X e T acc s E A : ℝ)
    (hd : |d| ≤ δ) (ha : |(a : ℝ)| ≤ W) (hW : 0 ≤ W) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hTd : T = (W + 1) * (X + e + 1)) (hT : T ≤ 1048576)
    (hv : |v - vh| ≤ e) (hvh : |vh| ≤ X)
    (hE : |acc - s| ≤ E) (hA : |acc| ≤ A) (hAT : A + 3 / 2 * T ≤ 48 * T) :
    |fl (acc + fl (asw fl a d * v)) - (s + (a : ℝ) * vh)|
        ≤ E + (W * e + δ * (X + e) + T / 65536 + η * 2097152)
    ∧ |fl (acc + fl (asw fl a d * v))| ≤ A + 3 / 2 * T := by
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  have hWT : W + 1 ≤ T := by
    rw [hTd]; linarith [mul_nonneg (by linarith : (0:ℝ) ≤ W + 1) (add_nonneg hX he)]
  have hT1 : 1 ≤ T := by linarith
  have hXe : X + e + 1 ≤ T := by
    rw [hTd]; linarith [mul_nonneg hW (by linarith : (0:ℝ) ≤ X + e + 1)]
  have hY : X + e ≤ 1048576 := by linarith
  have hVY : (W + 1) * (X + e) = T - (W + 1) := by rw [hTd]; ring
  have hTM : T ≤ M := by linarith
  have hWM : |(a : ℝ)| + δ ≤ M := by linarith
  have hα := asw_near h hu0 a hd hWM
  have hSb := asw_bound h hu0 a hd hWM
  have hu1 : u * (|(a : ℝ)| + δ) ≤ u * (W + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have hα' : |asw fl a d - (a : ℝ)| ≤ δ + (u * (W + 1) + η) := by linarith
  have hSb' : |asw fl a d| ≤ (W + 1) + (u * (W + 1) + η) := by linarith
  have huW : 0 ≤ u * (W + 1) := mul_nonneg hu0 (by linarith)
  have hα0 : 0 ≤ δ + (u * (W + 1) + η) := by linarith
  have hvb : |v| ≤ X + e := by
    have := abs_sub_abs_le_abs_sub v vh
    linarith
  have hmul := mul_near hα' hv
  have hp1 : (δ + (u * (W + 1) + η)) * |vh| ≤ (δ + (u * (W + 1) + η)) * X :=
    mul_le_mul_of_nonneg_left hvh hα0
  have hp2 : e * |(a : ℝ)| ≤ e * W := mul_le_mul_of_nonneg_left ha he
  have hq1 : u * ((W + 1) * (X + e)) ≤ u * T :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have hq2 : η * (X + e) ≤ η * 1048576 := mul_le_mul_of_nonneg_left hY hη0
  have huT : u * T ≤ T / 16777216 := by
    have := mul_le_mul_of_nonneg_right hu hT0
    linarith
  have hep : |asw fl a d * v - (a : ℝ) * vh|
      ≤ W * e + δ * (X + e) + u * T + η * 1048576 := by
    linarith [hmul, hp1, hp2, hq1, hq2]
  have hSv : |asw fl a d * v| ≤ T := by
    rw [abs_mul]
    have h1 := mul_le_mul hSb' hvb (abs_nonneg v) (by linarith)
    linarith [h1, hq1, hq2, hVY, huT, hT]
  have hfp := h.near hu0 hep hSv hTM
  have hfb := h.bound hu0 hSv hTM
  have hx1 : |acc + fl (asw fl a d * v) - (s + (a : ℝ) * vh)|
      ≤ E + ((W * e + δ * (X + e) + u * T + η * 1048576) + (u * T + η)) := by
    have := abs_add_le (acc - s) (fl (asw fl a d * v) - (a : ℝ) * vh)
    have h3 : acc - s + (fl (asw fl a d * v) - (a : ℝ) * vh)
        = acc + fl (asw fl a d * v) - (s + (a : ℝ) * vh) := by ring
    rw [h3] at this
    linarith
  have hx2 : |acc + fl (asw fl a d * v)| ≤ A + (T + (u * T + η)) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hB' : A + (T + (u * T + η)) ≤ 48 * T := by linarith
  have hBM : A + (T + (u * T + η)) ≤ M := by linarith
  have hfin := h.near hu0 hx1 hx2 hBM
  have hfin2 := h.bound hu0 hx2 hBM
  have hub : u * (A + (T + (u * T + η))) ≤ u * (48 * T) :=
    mul_le_mul_of_nonneg_left hB' hu0
  have hub2 : u * (48 * T) ≤ (1 / 16777216) * (48 * T) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  constructor
  · linarith [hfin, hub, hub2, huT, hη0, hT0]
  · linarith [hfin2, hub, hub2, huT, hη0, hT0, hT1]

theorem ardot_aux {u η M δ : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hM : 1073741824 ≤ M) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ δ)
    (W X e T : ℝ) (hW : 0 ≤ W) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hTd : T = (W + 1) * (X + e + 1)) (hT : T ≤ 1048576) :
    ∀ (r : List ℚ) (x xh : List ℝ) (j : ℕ) (acc s E A : ℝ), r.length = x.length →
      Close x xh e X → (∀ a ∈ r, |(a : ℝ)| ≤ W) → |acc - s| ≤ E → |acc| ≤ A →
      A + (r.length : ℝ) * (3 / 2 * T) ≤ 48 * T →
      (|ardot fl r x d j acc - (s + dotQ r xh)| ≤
          E + (r.length : ℝ) * (W * e + δ * (X + e) + T / 65536 + η * 2097152)
        ∧ |ardot fl r x d j acc| ≤ A + (r.length : ℝ) * (3 / 2 * T)) := by
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  intro r
  induction r with
  | nil =>
    intro x xh j acc s E A hl hC ha hE hA hAT
    have h1 : ardot fl [] x d j acc = acc := by cases x <;> rfl
    have h2 : dotQ [] xh = 0 := by simp [dotQ]
    rw [h1, h2]
    simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨hE, hA⟩
  | cons a0 r' ih =>
    intro x xh j acc s E A hl hC ha hE hA hAT
    cases x with
    | nil => simp at hl
    | cons v x' =>
      have hlen := close_len hC
      cases xh with
      | nil => simp at hlen
      | cons vh xh' =>
        obtain ⟨hv, hvh, hC'⟩ := close_cons hC
        have hl' : r'.length = x'.length := by simpa using hl
        have hℓ0 : (0 : ℝ) ≤ (r'.length : ℝ) * (3 / 2 * T) :=
          mul_nonneg (Nat.cast_nonneg _) (by linarith)
        have hAT1 := hAT
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hAT1
        have hAT2 : A + 3 / 2 * T ≤ 48 * T := by linarith
        obtain ⟨s1, s2⟩ := ar_step h hu0 hu hη0 hη hδ0 hδ1 hM a0 v vh (d j) W X e T acc s E A
          (hd j) (ha a0 (by simp)) hW hX he hTd hT hv hvh hE hA hAT2
        have ih' := ih x' xh' (j + 1) (fl (acc + fl (asw fl a0 (d j) * v)))
          (s + (a0 : ℝ) * vh) (E + (W * e + δ * (X + e) + T / 65536 + η * 2097152))
          (A + 3 / 2 * T) hl' hC' (fun b hb => ha b (by simp [hb])) s1 s2 (by linarith)
        have e1 : ardot fl (a0 :: r') (v :: x') d j acc
            = ardot fl r' x' d (j + 1) (fl (acc + fl (asw fl a0 (d j) * v))) := by
          first | rfl | simp [ardot]
        have e2 : dotQ (a0 :: r') (vh :: xh') = (a0 : ℝ) * vh + dotQ r' xh' := by
          simp [dotQ]
        rw [e1, e2]
        obtain ⟨i1, i2⟩ := ih'
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        constructor
        · have : s + ((a0 : ℝ) * vh + dotQ r' xh') = s + (a0 : ℝ) * vh + dotQ r' xh' := by ring
          rw [this]; linarith
        · linarith

theorem ardot_near : ArdotNear := by
  intro u η M δ fl hr hu0 hu hη0 hη hδ0 hδ1 r x xh d W X e hl hl32 hC hd ha hW hX he hT hM
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have h30 : (2 : ℝ) ^ 30 = 1073741824 := by norm_num
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  rw [h30] at hM
  rw [h20] at hT
  obtain ⟨T, hTd⟩ : ∃ T, T = (W + 1) * (X + e + 1) := ⟨_, rfl⟩
  rw [← hTd] at hT
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  have hℓ : (r.length : ℝ) ≤ 32 := by exact_mod_cast hl32
  have hℓ0 : (0 : ℝ) ≤ r.length := Nat.cast_nonneg _
  have key := ardot_aux hr hu0 hu hη0 hη' hδ0 hδ1 hM d hd W X e T hW hX he hTd hT r x xh 0
    0 0 0 0 hl hC ha (by simp) (by simp)
    (by have := mul_le_mul_of_nonneg_right hℓ (by linarith : 0 ≤ 3 / 2 * T); linarith)
  obtain ⟨k1, k2⟩ := key
  simp only [zero_add] at k1 k2
  have hηb : η * 2097152 ≤ 1 / 2 ^ 149 * 2097152 := mul_le_mul_of_nonneg_right hη (by norm_num)
  have hη2 : (r.length : ℝ) * (η * 2097152) ≤ 32 * (1 / 2 ^ 149 * 2097152) :=
    mul_le_mul hℓ hηb (mul_nonneg hη0 (by norm_num)) (by norm_num)
  have hη3 : (32 : ℝ) * (1 / 2 ^ 149 * 2097152) ≤ 1 / 1267650600228229401496703205376 := by
    norm_num
  have e2 : (r.length : ℝ) * (W + 1) * (X + e + 1) / 65536 = (r.length : ℝ) * (T / 65536) := by
    rw [hTd]; ring
  have e3 : (r.length : ℝ) * (W + 1) * (X + e + 1) * 2 = (r.length : ℝ) * T * 2 := by
    rw [hTd]; ring
  have hlT : 0 ≤ (r.length : ℝ) * T := mul_nonneg hℓ0 hT0
  rw [h16, h100, e2, e3]
  constructor
  · linarith [k1, hη2, hη3]
  · linarith [k2, hlT]

theorem pd_step {u η M : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000)
    (hM : 1073741824 ≤ M) (a ah b bh : ℝ) (X Y e1 e2 T acc s E A : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hTd : T = (X + e1 + 1) * (Y + e2 + 1)) (hT : T ≤ 1048576)
    (ha : |a - ah| ≤ e1) (hah : |ah| ≤ X) (hb : |b - bh| ≤ e2) (hbh : |bh| ≤ Y)
    (hE : |acc - s| ≤ E) (hA : |acc| ≤ A) (hAT : A + 3 / 2 * T ≤ 48 * T) :
    |fl (acc + fl (a * b)) - (s + ah * bh)|
        ≤ E + (e1 * (Y + e2) + X * e2 + T / 65536 + η * 2097152)
    ∧ |fl (acc + fl (a * b))| ≤ A + 3 / 2 * T := by
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  have hT1 : 1 ≤ T := by
    rw [hTd]
    linarith [mul_nonneg (add_nonneg hX he1) (add_nonneg hY he2)]
  have hTM : T ≤ M := by linarith
  have hab : |a| ≤ X + e1 := by
    have := abs_sub_abs_le_abs_sub a ah
    linarith
  have hbb : |b| ≤ Y + e2 := by
    have := abs_sub_abs_le_abs_sub b bh
    linarith
  have hmul := mul_near ha hb
  have hp1 : e1 * |bh| ≤ e1 * Y := mul_le_mul_of_nonneg_left hbh he1
  have hp2 : e2 * |ah| ≤ e2 * X := mul_le_mul_of_nonneg_left hah he2
  have huT : u * T ≤ T / 16777216 := by
    have := mul_le_mul_of_nonneg_right hu hT0
    linarith
  have hep : |a * b - ah * bh| ≤ e1 * (Y + e2) + X * e2 := by
    linarith [hmul, hp1, hp2]
  have hSv : |a * b| ≤ T := by
    rw [abs_mul]
    have h1 := mul_le_mul hab hbb (abs_nonneg b) (by linarith)
    linarith [h1, hTd, hX, hY, he1, he2]
  have hfp := h.near hu0 hep hSv hTM
  have hfb := h.bound hu0 hSv hTM
  have hx1 : |acc + fl (a * b) - (s + ah * bh)|
      ≤ E + ((e1 * (Y + e2) + X * e2) + (u * T + η)) := by
    have := abs_add_le (acc - s) (fl (a * b) - ah * bh)
    have h3 : acc - s + (fl (a * b) - ah * bh) = acc + fl (a * b) - (s + ah * bh) := by ring
    rw [h3] at this
    linarith
  have hx2 : |acc + fl (a * b)| ≤ A + (T + (u * T + η)) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hB' : A + (T + (u * T + η)) ≤ 48 * T := by linarith
  have hBM : A + (T + (u * T + η)) ≤ M := by linarith
  have hfin := h.near hu0 hx1 hx2 hBM
  have hfin2 := h.bound hu0 hx2 hBM
  have hub : u * (A + (T + (u * T + η))) ≤ u * (48 * T) :=
    mul_le_mul_of_nonneg_left hB' hu0
  have hub2 : u * (48 * T) ≤ (1 / 16777216) * (48 * T) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  constructor
  · linarith [hfin, hub, hub2, huT, hη0, hT0]
  · linarith [hfin2, hub, hub2, huT, hη0, hT0, hT1]

theorem pdot_aux {u η M : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000)
    (hM : 1073741824 ≤ M) (X Y e1 e2 T : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hTd : T = (X + e1 + 1) * (Y + e2 + 1)) (hT : T ≤ 1048576) :
    ∀ (x y xh yh : List ℝ) (acc s E A : ℝ), x.length = y.length →
      Close x xh e1 X → Close y yh e2 Y → |acc - s| ≤ E → |acc| ≤ A →
      A + (x.length : ℝ) * (3 / 2 * T) ≤ 48 * T →
      (|pdot fl x y acc - (s + dotR xh yh)| ≤
          E + (x.length : ℝ) * (e1 * (Y + e2) + X * e2 + T / 65536 + η * 2097152)
        ∧ |pdot fl x y acc| ≤ A + (x.length : ℝ) * (3 / 2 * T)) := by
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  intro x
  induction x with
  | nil =>
    intro y xh yh acc s E A hl hC1 hC2 hE hA hAT
    have h1 : pdot fl [] y acc = acc := by cases y <;> rfl
    have h2 : dotR xh yh = 0 := by
      cases xh with
      | nil => simp [dotR]
      | cons b t =>
        have := close_len hC1
        simp at this
    rw [h1, h2]
    simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨hE, hA⟩
  | cons a0 x' ih =>
    intro y xh yh acc s E A hl hC1 hC2 hE hA hAT
    cases y with
    | nil => simp at hl
    | cons b0 y' =>
      have hlen1 := close_len hC1
      have hlen2 := close_len hC2
      cases xh with
      | nil => simp at hlen1
      | cons ah xh' =>
        cases yh with
        | nil => simp at hlen2
        | cons bh yh' =>
          obtain ⟨ha, hah, hC1'⟩ := close_cons hC1
          obtain ⟨hb, hbh, hC2'⟩ := close_cons hC2
          have hl' : x'.length = y'.length := by simpa using hl
          have hℓ0 : (0 : ℝ) ≤ (x'.length : ℝ) * (3 / 2 * T) :=
            mul_nonneg (Nat.cast_nonneg _) (by linarith)
          have hAT1 := hAT
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hAT1
          have hAT2 : A + 3 / 2 * T ≤ 48 * T := by linarith
          obtain ⟨s1, s2⟩ := pd_step h hu0 hu hη0 hη hM a0 ah b0 bh X Y e1 e2 T acc s E A
            hX hY he1 he2 hTd hT ha hah hb hbh hE hA hAT2
          have ih' := ih y' xh' yh' (fl (acc + fl (a0 * b0))) (s + ah * bh)
            (E + (e1 * (Y + e2) + X * e2 + T / 65536 + η * 2097152))
            (A + 3 / 2 * T) hl' hC1' hC2' s1 s2 (by linarith)
          have e1' : pdot fl (a0 :: x') (b0 :: y') acc
              = pdot fl x' y' (fl (acc + fl (a0 * b0))) := by
            first | rfl | simp [pdot]
          have e2' : dotR (ah :: xh') (bh :: yh') = ah * bh + dotR xh' yh' := by
            simp [dotR]
          rw [e1', e2']
          obtain ⟨i1, i2⟩ := ih'
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          constructor
          · have : s + (ah * bh + dotR xh' yh') = s + ah * bh + dotR xh' yh' := by ring
            rw [this]; linarith
          · linarith

theorem pdot_near : PdotNear := by
  intro u η M fl hr hu0 hu hη0 hη x xh y yh X Y e1 e2 hl hl32 hC1 hC2 hX hY he1 he2 hT hM
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have h30 : (2 : ℝ) ^ 30 = 1073741824 := by norm_num
  have h20 : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 = 1 / 1267650600228229401496703205376 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  rw [h30] at hM
  rw [h20] at hT
  obtain ⟨T, hTd⟩ : ∃ T, T = (X + e1 + 1) * (Y + e2 + 1) := ⟨_, rfl⟩
  rw [← hTd] at hT
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  have hℓ : (x.length : ℝ) ≤ 32 := by exact_mod_cast hl32
  have hℓ0 : (0 : ℝ) ≤ x.length := Nat.cast_nonneg _
  have key := pdot_aux hr hu0 hu hη0 hη' hM X Y e1 e2 T hX hY he1 he2 hTd hT x y xh yh
    0 0 0 0 hl hC1 hC2 (by simp) (by simp)
    (by have := mul_le_mul_of_nonneg_right hℓ (by linarith : 0 ≤ 3 / 2 * T); linarith)
  obtain ⟨k1, k2⟩ := key
  simp only [zero_add] at k1 k2
  have hηb : η * 2097152 ≤ 1 / 2 ^ 149 * 2097152 := mul_le_mul_of_nonneg_right hη (by norm_num)
  have hη2 : (x.length : ℝ) * (η * 2097152) ≤ 32 * (1 / 2 ^ 149 * 2097152) :=
    mul_le_mul hℓ hηb (mul_nonneg hη0 (by norm_num)) (by norm_num)
  have hη3 : (32 : ℝ) * (1 / 2 ^ 149 * 2097152) ≤ 1 / 1267650600228229401496703205376 := by
    norm_num
  have e2' : (x.length : ℝ) * (X + e1 + 1) * (Y + e2 + 1) / 65536
      = (x.length : ℝ) * (T / 65536) := by
    rw [hTd]; ring
  have e3 : (x.length : ℝ) * (X + e1 + 1) * (Y + e2 + 1) * 2 = (x.length : ℝ) * T * 2 := by
    rw [hTd]; ring
  have hlT : 0 ≤ (x.length : ℝ) * T := mul_nonneg hℓ0 hT0
  rw [h16, h100, e2', e3]
  constructor
  · linarith [k1, hη2, hη3]
  · linarith [k2, hlT]

theorem bias_gap : BiasGap := by
  intro u η M δ fl hr hu0 hu hη0 hη hδ0 hδ1 h dm hdm hm1 hm2 n i j k hkj hjn hin hun hηn hM
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkj' : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
  have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hkn : (k : ℝ) ≤ n := by linarith
  have hM' : 4096 * ((n : ℝ) + 1) ≤ M := by
    have : (2 : ℝ) ^ 12 * ((n : ℝ) + 1) = 4096 * ((n : ℝ) + 1) := by norm_num
    linarith
  have hmM : (h.m : ℝ) + 1 ≤ M := by linarith
  have habs : |(h.m : ℝ)| = (h.m : ℝ) := abs_of_nonneg (by linarith)
  have hS := asw_near hr hu0 h.m hdm (by rw [habs]; linarith)
  have hSb := asw_bound hr hu0 h.m hdm (by rw [habs]; linarith)
  rw [habs] at hS hSb
  have hbias : ∀ t : ℕ, h.bias fl dm i t = fl (asw fl h.m dm * ((t : ℝ) - (i : ℝ))) := by
    intro t
    simp [AHead.bias]
  rw [hbias k, hbias j]
  generalize asw fl h.m dm = S at hS hSb ⊢
  have hu1 : u * ((h.m : ℝ) + δ) ≤ u * ((h.m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have hu2 : u * ((h.m : ℝ) + 1) ≤ (1 / 16777216) * ((h.m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hu (by linarith)
  have hS1 : (h.m : ℝ) - δ - u * ((h.m : ℝ) + 1) - η ≤ S := by
    have := (abs_le.mp hS).1
    linarith
  have hS2 : |S| ≤ (h.m : ℝ) + 2 := by linarith
  have hki : |(k : ℝ) - (i : ℝ)| ≤ n := by
    rw [abs_le]; constructor <;> linarith
  have hji : |(j : ℝ) - (i : ℝ)| ≤ n := by
    rw [abs_le]; constructor <;> linarith
  have hm2' : (0 : ℝ) ≤ (h.m : ℝ) + 2 := by linarith
  have ha : |S * ((k : ℝ) - (i : ℝ))| ≤ ((h.m : ℝ) + 2) * n := by
    rw [abs_mul]; exact mul_le_mul hS2 hki (abs_nonneg _) hm2'
  have hb : |S * ((j : ℝ) - (i : ℝ))| ≤ ((h.m : ℝ) + 2) * n := by
    rw [abs_mul]; exact mul_le_mul hS2 hji (abs_nonneg _) hm2'
  have hBM : ((h.m : ℝ) + 2) * n ≤ M := by
    have := mul_le_mul_of_nonneg_right (by linarith : (h.m : ℝ) + 2 ≤ 1026) hn0
    linarith
  have hgap := hr.gap hu0 ha hb hBM
  have hbound := hr.bound hu0 hb hBM
  have hba : S * ((j : ℝ) - (i : ℝ)) - S * ((k : ℝ) - (i : ℝ)) = S * ((j : ℝ) - (k : ℝ)) := by
    ring
  have hjk0 : (0 : ℝ) ≤ (j : ℝ) - (k : ℝ) := by linarith
  have hjkn : (j : ℝ) - (k : ℝ) ≤ n := by linarith
  have P1 : ((h.m : ℝ) - δ - u * ((h.m : ℝ) + 1) - η) * ((j : ℝ) - (k : ℝ))
      ≤ S * ((j : ℝ) - (k : ℝ)) := mul_le_mul_of_nonneg_right hS1 hjk0
  have hnn : 0 ≤ u * ((h.m : ℝ) + 1) + η := by
    have := mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ (h.m : ℝ) + 1)
    linarith
  have P2 : (u * ((h.m : ℝ) + 1) + η) * ((j : ℝ) - (k : ℝ))
      ≤ (u * ((h.m : ℝ) + 1) + η) * n := mul_le_mul_of_nonneg_left hjkn hnn
  have P3 : ((h.m : ℝ) + 1) * (u * n) ≤ ((h.m : ℝ) + 1) * (1 / 256) :=
    mul_le_mul_of_nonneg_left hun (by linarith)
  have P4 : ((h.m : ℝ) + 2) * (u * n) ≤ ((h.m : ℝ) + 2) * (1 / 256) :=
    mul_le_mul_of_nonneg_left hun hm2'
  have hηn' : η * n ≤ 1 / 2 ^ 100 := hηn
  have h100 : (1 : ℝ) / 2 ^ 100 ≤ 1 / 1000000000000 := by norm_num
  constructor
  · linarith [hgap, hba, P1, P2, P3, P4, hηn', h100, hη', hη0]
  · linarith [hbound, P4, hη', hη0]

end Lane4.Case
