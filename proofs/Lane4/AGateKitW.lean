/-
Lane 4, rung 6a lemma kit, part 2 (Amendment 1 of PREREG_R6A.md, 2026-11-18): the
per-coordinate form of the stored-weight dot-product bound. Assembled by
tools/r6_assemble_w.py from kit case runs/r6-kit/kW (statements by the lane, proofs by a
Sonnet doctor, checked by the lane's checker). Fixed by the lane; doctors do not edit this
file. What you need is at the END of the file.
-/
import Lane4.AGateKit

namespace Lane4.AGate
open Lane4.RSeq (Vec pdot)
open Lane4.RSoft

/-- `x` is within `es` of `xh` entry by entry, and `xh` is bounded by `Xs` entry by entry.
The per-coordinate form of `Close`. -/
def CloseL (x xh es Xs : List ℝ) : Prop :=
  x.length = xh.length ∧ es.length = x.length ∧ Xs.length = x.length ∧
  ∀ k, k < x.length →
    |x.getD k 0 - xh.getD k 0| ≤ es.getD k 0 ∧ |xh.getD k 0| ≤ Xs.getD k 0

/-- The per-coordinate error budget of one stored-weight dot product: each term costs
`|a| * e + δ * (X + e)` with that coordinate's own `e` and `X`. -/
noncomputable def wErr (δ : ℝ) : List ℚ → List ℝ → List ℝ → ℝ
  | a :: r, e :: es, X :: Xs => |(a : ℝ)| * e + δ * (X + e) + wErr δ r es Xs
  | _, _, _ => 0

/-- `ArdotNearAbs` with per-coordinate entry errors and bounds. The uniform `W`, `X`, `e`
are used only for the rounding term and the magnitude bound. At most 32 terms. -/
def ArdotNearW : Prop :=
  ∀ (u η M δ : ℝ) (fl : ℝ → ℝ), Rnd u η M fl → 0 ≤ u → u ≤ 1 / 2 ^ 24 → 0 ≤ η → η ≤ 1 / 2 ^ 149 →
  0 ≤ δ → δ ≤ 1 →
  ∀ (r : List ℚ) (x xh es Xs : List ℝ) (d : ℕ → ℝ) (W X e : ℝ),
  r.length = x.length → r.length ≤ 32 → CloseL x xh es Xs →
  (∀ k, k < x.length → es.getD k 0 ≤ e ∧ Xs.getD k 0 ≤ X) → (∀ k, |d k| ≤ δ) →
  (∀ a ∈ r, |(a : ℝ)| ≤ W) → 0 ≤ W → 0 ≤ X → 0 ≤ e →
  (W + 1) * (X + e + 1) ≤ 2 ^ 20 → 2 ^ 30 ≤ M →
    |ardot fl r x d 0 0 - dotQ r xh|
      ≤ wErr δ r es Xs + (r.length : ℝ) * (W + 1) * (X + e + 1) / 2 ^ 16 + 1 / 2 ^ 100
    ∧ |ardot fl r x d 0 0| ≤ (r.length : ℝ) * (W + 1) * (X + e + 1) * 2

/-- A uniform `Close` is a `CloseL` with constant lists. -/
def CloseLOfClose : Prop :=
  ∀ (x xh : List ℝ) (e X : ℝ), Close x xh e X →
    CloseL x xh (List.replicate x.length e) (List.replicate x.length X)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


theorem closeL_cons {a b e0 X0 : ℝ} {x y es Xs : List ℝ}
    (h : CloseL (a :: x) (b :: y) (e0 :: es) (X0 :: Xs)) :
    |a - b| ≤ e0 ∧ |b| ≤ X0 ∧ CloseL x y es Xs := by
  unfold CloseL at h
  obtain ⟨hl, hle, hlX, hk⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := hk 0 (by simp)
    simpa using this.1
  · have := hk 0 (by simp)
    simpa using this.2
  · unfold CloseL
    refine ⟨by simpa using hl, by simpa using hle, by simpa using hlX, ?_⟩
    intro k hk'
    have := hk (k + 1) (by simp only [List.length_cons]; omega)
    simpa using this

theorem ar_step2 {u η M δ : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hM : 1073741824 ≤ M) (a : ℚ) (v vh d : ℝ) (W X e e' X' T acc s E A : ℝ)
    (hd : |d| ≤ δ) (ha : |(a : ℝ)| ≤ W) (hW : 0 ≤ W) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hTd : T = (W + 1) * (X + e + 1)) (hT : T ≤ 1048576)
    (hv : |v - vh| ≤ e') (hvh : |vh| ≤ X') (hee : e' ≤ e) (hXX : X' ≤ X)
    (hE : |acc - s| ≤ E) (hA : |acc| ≤ A) (hAT : A + 3 / 2 * T ≤ 48 * T) :
    |fl (acc + fl (asw fl a d * v)) - (s + (a : ℝ) * vh)|
        ≤ E + (|(a : ℝ)| * e' + δ * (X' + e') + T / 65536 + η * 2097152)
    ∧ |fl (acc + fl (asw fl a d * v))| ≤ A + 3 / 2 * T := by
  have he' : 0 ≤ e' := le_trans (abs_nonneg _) hv
  have hX' : 0 ≤ X' := le_trans (abs_nonneg _) hvh
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
  have hp1 : (δ + (u * (W + 1) + η)) * |vh| ≤ (δ + (u * (W + 1) + η)) * X' :=
    mul_le_mul_of_nonneg_left hvh hα0
  have hp2 : e' * |(a : ℝ)| ≤ e' * W := mul_le_mul_of_nonneg_left ha he'
  have hqq : 0 ≤ u * (W + 1) + η := by linarith
  have hq0 : (u * (W + 1) + η) * (X' + e') ≤ (u * (W + 1) + η) * (X + e) :=
    mul_le_mul_of_nonneg_left (by linarith) hqq
  have hq1 : u * ((W + 1) * (X + e)) ≤ u * T :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have hq2 : η * (X + e) ≤ η * 1048576 := mul_le_mul_of_nonneg_left hY hη0
  have huT : u * T ≤ T / 16777216 := by
    have := mul_le_mul_of_nonneg_right hu hT0
    linarith
  have hep : |asw fl a d * v - (a : ℝ) * vh|
      ≤ |(a : ℝ)| * e' + δ * (X' + e') + u * T + η * 1048576 := by
    have hbig : |asw fl a d * v - (a : ℝ) * vh|
        ≤ (δ + (u * (W + 1) + η)) * |vh| + e' * |(a : ℝ)| + (δ + (u * (W + 1) + η)) * e' := by
      simpa using hmul
    have hz : |asw fl a d * v - (a : ℝ) * vh|
        ≤ |(a : ℝ)| * e' + δ * (X' + e') + (u * (W + 1) + η) * (X' + e') := by
      nlinarith [hbig, hp1]
    nlinarith [hz, hq0, hq1, hq2]
  have hSv : |asw fl a d * v| ≤ T := by
    rw [abs_mul]
    have h1 := mul_le_mul hSb' hvb (abs_nonneg v) (by linarith)
    linarith [h1, hq1, hq2, hVY, huT, hT]
  have hfp := h.near hu0 hep hSv hTM
  have hfb := h.bound hu0 hSv hTM
  have hx1 : |acc + fl (asw fl a d * v) - (s + (a : ℝ) * vh)|
      ≤ E + ((|(a : ℝ)| * e' + δ * (X' + e') + u * T + η * 1048576) + (u * T + η)) := by
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

theorem ardot_auxL {u η M δ : ℝ} {fl : ℝ → ℝ} (h : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 16777216) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 1000000000000) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hM : 1073741824 ≤ M) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ δ)
    (W X e T : ℝ) (hW : 0 ≤ W) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hTd : T = (W + 1) * (X + e + 1)) (hT : T ≤ 1048576) :
    ∀ (r : List ℚ) (x xh es Xs : List ℝ) (j : ℕ) (acc s E A : ℝ), r.length = x.length →
      CloseL x xh es Xs → (∀ k, k < x.length → es.getD k 0 ≤ e ∧ Xs.getD k 0 ≤ X) →
      (∀ a ∈ r, |(a : ℝ)| ≤ W) → |acc - s| ≤ E → |acc| ≤ A →
      A + (r.length : ℝ) * (3 / 2 * T) ≤ 48 * T →
      (|ardot fl r x d j acc - (s + dotQ r xh)| ≤
          E + wErr δ r es Xs + (r.length : ℝ) * (T / 65536 + η * 2097152)
        ∧ |ardot fl r x d j acc| ≤ A + (r.length : ℝ) * (3 / 2 * T)) := by
  have hT0 : 0 ≤ T := by rw [hTd]; exact mul_nonneg (by linarith) (by linarith)
  intro r
  induction r with
  | nil =>
    intro x xh es Xs j acc s E A hl hC hb ha hE hA hAT
    have h1 : ardot fl [] x d j acc = acc := by cases x <;> rfl
    have h2 : dotQ [] xh = 0 := by simp [dotQ]
    have h3 : wErr δ [] es Xs = 0 := by simp [wErr]
    rw [h1, h2, h3]
    simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨by linarith, by linarith⟩
  | cons a0 r' ih =>
    intro x xh es Xs j acc s E A hl hC hb ha hE hA hAT
    have hC0 := hC
    obtain ⟨hlen, hles, hlXs, _⟩ := hC0
    cases x with
    | nil => simp at hl
    | cons v x' =>
      cases xh with
      | nil => simp at hlen
      | cons vh xh' =>
        cases es with
        | nil => simp at hles
        | cons e0 es' =>
          cases Xs with
          | nil => simp at hlXs
          | cons X0 Xs' =>
            obtain ⟨hv, hvh, hC'⟩ := closeL_cons hC
            have hb0 := hb 0 (by simp)
            simp only [List.getD_cons_zero] at hb0
            have hl' : r'.length = x'.length := by simpa using hl
            have hb' : ∀ k, k < x'.length → es'.getD k 0 ≤ e ∧ Xs'.getD k 0 ≤ X := by
              intro k hk
              have := hb (k + 1) (by simp only [List.length_cons]; omega)
              simpa using this
            have hℓ0 : (0 : ℝ) ≤ (r'.length : ℝ) * (3 / 2 * T) :=
              mul_nonneg (Nat.cast_nonneg _) (by linarith)
            have hAT1 := hAT
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hAT1
            have hAT2 : A + 3 / 2 * T ≤ 48 * T := by linarith
            obtain ⟨s1, s2⟩ := ar_step2 h hu0 hu hη0 hη hδ0 hδ1 hM a0 v vh (d j) W X e e0 X0 T
              acc s E A (hd j) (ha a0 (by simp)) hW hX he hTd hT hv hvh hb0.1 hb0.2 hE hA hAT2
            have ih' := ih x' xh' es' Xs' (j + 1) (fl (acc + fl (asw fl a0 (d j) * v)))
              (s + (a0 : ℝ) * vh)
              (E + (|(a0 : ℝ)| * e0 + δ * (X0 + e0) + T / 65536 + η * 2097152))
              (A + 3 / 2 * T) hl' hC' hb' (fun b hb => ha b (by simp [hb])) s1 s2 (by linarith)
            have e1 : ardot fl (a0 :: r') (v :: x') d j acc
                = ardot fl r' x' d (j + 1) (fl (acc + fl (asw fl a0 (d j) * v))) := by
              first | rfl | simp [ardot]
            have e2 : dotQ (a0 :: r') (vh :: xh') = (a0 : ℝ) * vh + dotQ r' xh' := by
              simp [dotQ]
            have hab : wErr δ (a0 :: r') (e0 :: es') (X0 :: Xs')
                = |(a0 : ℝ)| * e0 + δ * (X0 + e0) + wErr δ r' es' Xs' := by
              simp [wErr]
            rw [e1, e2, hab]
            obtain ⟨i1, i2⟩ := ih'
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            constructor
            · have : s + ((a0 : ℝ) * vh + dotQ r' xh') = s + (a0 : ℝ) * vh + dotQ r' xh' := by ring
              rw [this]; linarith
            · linarith

theorem ardot_near_w : ArdotNearW := by
  intro u η M δ fl hr hu0 hu hη0 hη hδ0 hδ1 r x xh es Xs d W X e hl hl32 hC hb hd ha hW hX he hT hM
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
  have key := ardot_auxL hr hu0 hu hη0 hη' hδ0 hδ1 hM d hd W X e T hW hX he hTd hT r x xh es Xs 0
    0 0 0 0 hl hC hb ha (by simp) (by simp)
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
  · have : (r.length : ℝ) * (T / 65536 + η * 2097152)
        = (r.length : ℝ) * (T / 65536) + (r.length : ℝ) * (η * 2097152) := by ring
    linarith [k1, hη2, hη3]
  · linarith [k2, hlT]

theorem closeL_of_close : CloseLOfClose := by
  intro x xh e X h
  obtain ⟨hl, hk⟩ := h
  refine ⟨hl, by simp, by simp, ?_⟩
  intro k hk'
  have := hk k hk'
  have e1 : (List.replicate x.length e).getD k 0 = e := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hk']
  have e2 : (List.replicate x.length X).getD k 0 = X := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hk']
  rw [e1, e2]
  exact this

/-! ### What doctors use

`CloseL x xh es Xs` is `Close` with one entry error `es[k]` and one bound `Xs[k]` per
coordinate. `ardot_near_w` (statement `ArdotNearW`) bounds a stored-weight dot product by
`wErr δ r es Xs`, the sum over coordinates of `|a_k| * es[k] + δ * (Xs[k] + es[k])`, plus
the same rounding term as `ardot_near_abs`; the uniform `W`, `X`, `e` only have to bound
all coordinates. Use it when the state is wide and most coordinates are small or exact:
the uniform lemmas charge `len * δ * (X + e)` with the LARGEST `X` and `e`.
`closeL_of_close` turns a uniform `Close` into a `CloseL` with constant lists.
`wErr` unfolds by `simp [wErr]` on explicit lists. -/

end Lane4.AGate
