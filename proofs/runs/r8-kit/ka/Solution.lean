set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace Lane4.Case
open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

theorem k_getD_map {α β : Type} (f : α → β) (d : α) (d' : β) :
    ∀ (l : List α) (k : ℕ), k < l.length → (l.map f).getD k d' = f (l.getD k d)
  | [], k, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, k + 1, h => by
      simp only [List.map_cons, List.getD_cons_succ]
      exact k_getD_map f d d' l k (by simpa using h)

theorem k_sAt {δ : ℚ} {h : AHead} {E : List (List IV)} {hc : HCert}
    (hS : hc.S = E.map (fun xq => E.map (fun xt => scoreIV δ h xq xt)))
    {q t : ℕ} (hq : q < E.length) (ht : t < E.length) :
    sAt hc q t = scoreIV δ h (E.getD q []) (E.getD t []) := by
  unfold sAt
  rw [hS, k_getD_map (fun xq => E.map (fun xt => scoreIV δ h xq xt)) [] [] E q hq]
  exact k_getD_map (fun xt => scoreIV δ h (E.getD q []) xt) [] (0, 0) E t ht

theorem k_open {δ : ℚ} {E : List (List IV)} {h : AHead} {hc : HCert}
    (hok : headOK8 δ E h hc = true) :
    1 ≤ h.m ∧ h.m ≤ 1024 ∧ hc.cands.length = E.length ∧
    hc.S = E.map (fun xq => E.map (fun xt => scoreIV δ h xq xt)) ∧
    (∀ tq, 1 ≤ tq → tq < E.length → ∀ t, t < E.length → hc.cands.getD t false = true →
       scoreOK δ h (E.getD tq []) (E.getD t []) = true) := by
  unfold headOK8 at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hm1⟩, hm2⟩, hlen⟩, -⟩, hS⟩, -⟩, -⟩, -⟩, hs⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  refine ⟨hm1, hm2, hlen, hS, ?_⟩
  intro tq h1 htq t ht hcd
  have a1 := List.all_eq_true.mp hs (E.getD tq []) (Lane4.R7K3.hs_mem_drop E tq h1 htq)
  have a2 := List.all_eq_true.mp a1 (E.getD t [], hc.cands.getD t false)
    (Lane4.R7K3.hs_mem_zip E hc.cands hlen t ht)
  exact Lane4.R7K3.hs_or2 a2 hcd

theorem k_S {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ^ 40 ≤ M) {m dm : ℝ}
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1024) (hdm : |dm| ≤ 1 / 2) :
    |fl (m + dm) - (m + dm)| ≤ u * 1025 + η ∧ |fl (m + dm)| ≤ m + 1 := by
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  rw [h40] at hM
  obtain ⟨d1, d2⟩ := abs_le.mp hdm
  have hx : |m + dm| ≤ 1025 := by rw [abs_le]; constructor <;> linarith
  have h1 := hr.abs hu0 hx (by linarith)
  refine ⟨h1, ?_⟩
  have h2 : |fl (m + dm)| ≤ |m + dm| + |fl (m + dm) - (m + dm)| := by
    have := abs_add_le (m + dm) (fl (m + dm) - (m + dm))
    have e : m + dm + (fl (m + dm) - (m + dm)) = fl (m + dm) := by ring
    rw [e] at this
    linarith
  have h3 : |m + dm| ≤ m + 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hu1025 : u * 1025 ≤ 1025 / 16777216 := by linarith
  linarith

theorem k_size {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) {S m n d c : ℝ}
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1024) (hS : |S| ≤ m + 1) (hn1 : 1 ≤ n) (hd : |d| ≤ n)
    (hc : |c| ≤ 1024) (hM : 2 ^ 40 * n ^ 2 ≤ M) :
    |fl (fl (S * d) + c)| ≤ (m + 2) * (n + 1) + 1025 := by
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  rw [h40] at hM
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hn21 : 1 ≤ n ^ 2 := by nlinarith
  have hMn : 4000 * n + 2000 ≤ M := by nlinarith [sq_nonneg n]
  have hQ : |S * d| ≤ (m + 1) * n := by
    rw [abs_mul]; exact mul_le_mul hS hd (abs_nonneg _) (by linarith)
  have hQ' : (m + 1) * n ≤ 1025 * n :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  rw [show (m + 2) * (n + 1) + 1025 = (m + 1) * n + n + m + 1027 by ring]
  generalize (m + 1) * n = Q at hQ hQ' ⊢
  have hQ0 : 0 ≤ Q := le_trans (abs_nonneg _) hQ
  have e1 := hr.err (S * d) (le_trans hQ (by linarith))
  have hw0 : 0 ≤ u * Q := mul_nonneg hu0 hQ0
  have hw : u * Q ≤ n / 1000 := by
    have := mul_le_mul hu hQ' hQ0 (by norm_num)
    linarith
  have hSd : u * |S * d| ≤ u * Q := mul_le_mul_of_nonneg_left hQ hu0
  have ha : |fl (S * d)| ≤ Q + u * Q + η := by
    have := abs_add_le (S * d) (fl (S * d) - S * d)
    have e : S * d + (fl (S * d) - S * d) = fl (S * d) := by ring
    rw [e] at this
    linarith
  have hy : |fl (S * d) + c| ≤ Q + u * Q + η + 1024 := le_trans (abs_add_le _ _) (by linarith)
  have e2 := hr.err (fl (S * d) + c) (le_trans hy (by linarith))
  have hfl : |fl (fl (S * d) + c)| ≤ |fl (S * d) + c| + (u * |fl (S * d) + c| + η) := by
    have := abs_add_le (fl (S * d) + c) (fl (fl (S * d) + c) - (fl (S * d) + c))
    have e : fl (S * d) + c + (fl (fl (S * d) + c) - (fl (S * d) + c)) = fl (fl (S * d) + c) := by
      ring
    rw [e] at this
    linarith
  have hu2 : u * |fl (S * d) + c| ≤ u * (Q + u * Q + η + 1024) := mul_le_mul_of_nonneg_left hy hu0
  have hu3 : u * (u * Q) ≤ u * Q := mul_le_of_le_one_left hw0 (by linarith)
  have hu4 : u * η ≤ η := mul_le_of_le_one_left hη0 (by linarith)
  have hu5 : u * (Q + u * Q + η + 1024) = u * Q + u * (u * Q) + u * η + 1024 * u := by ring
  linarith

theorem k_near_core {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hM : 2 ^ 40 ≤ M)
    {S m dm δ dj dk cj ck cj' ck' rj rk : ℝ}
    (hS1 : |S - (m + dm)| ≤ u * 1025 + η) (hS2 : |S| ≤ m + 1) (hm1 : 1 ≤ m) (hm2 : m ≤ 1024)
    (hdj : |dj| ≤ 4) (hdk : |dk| ≤ 4) (hkj : |dk - dj| ≤ 4)
    (hcj : |cj| ≤ 1024) (hck : |ck| ≤ 1024) (hdm : |dm| ≤ δ)
    (hcj' : |cj - cj'| ≤ rj) (hck' : |ck - ck'| ≤ rk) :
    |fl (fl (S * dk) + ck) - fl (fl (S * dj) + cj) - (m * (dk - dj) + (ck' - cj'))|
      ≤ δ * |dk - dj| + (rk + rj + 1 / 2 ^ 8) := by
  have h24 : (2 : ℝ) ^ 24 = 16777216 := by norm_num
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have h8 : (2 : ℝ) ^ 8 = 256 := by norm_num
  have hη' : η ≤ 1 / 1000000000000 := le_trans hη (by norm_num)
  rw [h24] at hu
  rw [h40] at hM
  rw [h8]
  have hS3 : |S| ≤ 1025 := by linarith
  have one : ∀ (d c : ℝ), |d| ≤ 4 → |c| ≤ 1024 →
      |fl (fl (S * d) + c) - (S * d + c)| ≤ u * 4100 + η + (u * 5125 + η) := by
    intro d c hd hc
    have hSd : |S * d| ≤ 4100 := by
      rw [abs_mul]
      calc |S| * |d| ≤ 1025 * 4 := mul_le_mul hS3 hd (abs_nonneg _) (by norm_num)
        _ = 4100 := by norm_num
    have e1 := hr.abs hu0 hSd (by linarith)
    have ha : |fl (S * d)| ≤ 4101 := by
      have := abs_add_le (S * d) (fl (S * d) - S * d)
      have e : S * d + (fl (S * d) - S * d) = fl (S * d) := by ring
      rw [e] at this
      have hu41 : u * 4100 ≤ 4100 / 16777216 := by linarith
      linarith
    have hy : |fl (S * d) + c| ≤ 5125 := le_trans (abs_add_le _ _) (by linarith)
    have e2 := hr.abs hu0 hy (by linarith)
    have e3 : |fl (fl (S * d) + c) - (S * d + c)|
        ≤ |fl (fl (S * d) + c) - (fl (S * d) + c)| + |fl (S * d) - S * d| := by
      have := abs_add_le (fl (fl (S * d) + c) - (fl (S * d) + c)) (fl (S * d) - S * d)
      have e : fl (fl (S * d) + c) - (fl (S * d) + c) + (fl (S * d) - S * d)
          = fl (fl (S * d) + c) - (S * d + c) := by ring
      rw [e] at this
      exact this
    linarith
  have A := one dk ck hdk hck
  have B := one dj cj hdj hcj
  have P : |(S - (m + dm)) * (dk - dj)| ≤ (u * 1025 + η) * 4 := by
    rw [abs_mul]; exact mul_le_mul hS1 hkj (abs_nonneg _) (by linarith)
  have Q : |dm * (dk - dj)| ≤ δ * |dk - dj| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hdm (abs_nonneg _)
  obtain ⟨A1, A2⟩ := abs_le.mp A
  obtain ⟨B1, B2⟩ := abs_le.mp B
  obtain ⟨P1, P2⟩ := abs_le.mp P
  obtain ⟨Q1, Q2⟩ := abs_le.mp Q
  obtain ⟨c1, c2⟩ := abs_le.mp hcj'
  obtain ⟨c3, c4⟩ := abs_le.mp hck'
  rw [abs_le]
  constructor <;> linarith

theorem k_score_eq (h : AHead) (fl : ℝ → ℝ) (dA : ℕ → ℕ → ℝ) (dm : ℝ) (x : ℕ → Vec) (i t : ℕ) :
    h.score fl dA dm x i t
      = fl (fl (asw fl h.m dm * ((t : ℝ) - (i : ℝ))) + pdot fl (x i) (armat fl h.A (x t) dA 0) 0) := by
  simp [AHead.score, AHead.bias]

theorem score_win : ScoreWin := by
  intro u η M fl C δ hδ0 hδ1 h E hc dd hok hshape hdd hsA hrows dA dm hdA hdm n x tok hun hηn hM
    hx i hin hti j k hji hki hcj hck
  obtain ⟨hm1, hm2, hlen, hS, hsc⟩ := k_open hok
  have hjn : j < n := lt_of_le_of_lt hji hin
  have hkn : k < n := lt_of_le_of_lt hki hin
  have hm1R : (1 : ℝ) ≤ (h.m : ℝ) := by exact_mod_cast hm1
  have hm2R : (h.m : ℝ) ≤ 1024 := by exact_mod_cast hm2
  have hδ0R : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ0
  have hδhalf : (δ : ℝ) ≤ 1 / 2 := zhalf δ hδ1
  have hδ1R : (δ : ℝ) ≤ 1 := by linarith
  have hdmh : |dm| ≤ 1 / 2 := le_trans hdm hδhalf
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  obtain ⟨hM12, -, -, hMS⟩ := Lane4.R7K3.hs_Sb hn1 hM hm1R hm2R
  have hM1 : (2 : ℝ) ^ 40 ≤ M := C.M1
  obtain ⟨hS1, hS2⟩ := k_S C.rnd C.u0 C.u1 C.h0 C.h1 hM1 hm1R hm2R hdmh
  have hSdef : asw fl h.m dm = fl ((h.m : ℝ) + dm) := rfl
  have hS1' : |asw fl h.m dm - ((h.m : ℝ) + dm)| ≤ u * 1025 + η := by rw [hSdef]; exact hS1
  have hS2' : |asw fl h.m dm| ≤ (h.m : ℝ) + 1 := by rw [hSdef]; exact hS2
  have content : ∀ t, t < n → hc.cands.getD (tok t) false = true →
      InIV (pdot fl (x i) (armat fl h.A (x t) dA 0) 0) (sAt hc (tok i) (tok t)) ∧
      0 ≤ (sAt hc (tok i) (tok t)).2 ∧
      |pdot fl (x i) (armat fl h.A (x t) dA 0) 0| ≤ 1024 := by
    intro t ht hcd
    obtain ⟨hqi, hxi⟩ := hx i hin
    obtain ⟨hqt, hxt⟩ := hx t ht
    have rq := hrows _ (zgetD_mem' [] E _ hqi)
    have rt := hrows _ (zgetD_mem' [] E _ hqt)
    obtain ⟨sA1, sA2, -, -, -⟩ := Lane4.R7K3.hs_shape hshape
    have lq : (x i).length = dd := by rw [zinIVs_len hxi]; exact rq.1
    have lt' : (x t).length = dd := by rw [zinIVs_len hxt]; exact rt.1
    rw [k_sAt hS hqi hqt]
    exact score_sound u η M fl C δ hδ0 hδ1 h (x i) (x t) _ _ dA hdA
      (fun r hr => by rw [sA2 r hr, lt']) (by omega) (by rw [sA1, lq]) (by omega) hsA hxi
      rq.2 hxt rt.2 (hsc (tok i) hti hqi (tok t) hqt hcd)
  have pack : ∀ t, t < n → hc.cands.getD (tok t) false = true →
      |h.bias fl dm i t| ≤ ((h.m : ℝ) + 2) * ((n : ℝ) + 1) ∧
      |h.score fl dA dm x i t - (h.bias fl dm i t + pdot fl (x i) (armat fl h.A (x t) dA 0) 0)|
        ≤ ((h.m : ℝ) + 2) / 256 + 1 / 4096 := by
    intro t ht hct
    obtain ⟨-, -, kc3⟩ := content t ht hct
    have hb := Lane4.R7K3.hs_bias_abs C.rnd C.u0 C.u1 C.h0 C.h1 hδ0R hδ1R h dm hdm hm1R hm2R
      n i t ht.le hin.le hun hηn hM12
    exact ⟨hb, Lane4.R7K3.hs_round_sum C.rnd C.u0 C.u1 C.h0 C.h1 (m := (h.m : ℝ)) (n := (n : ℝ))
      (by linarith) (by linarith) (Nat.cast_nonneg n) hb kc3 hun hMS⟩
  have hjiR : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
  have hkiR : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hki
  have hinR : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin.le
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, -, cj3⟩ := content j hjn hcj
    rw [k_score_eq]
    have hd : |((j : ℝ) - (i : ℝ))| ≤ (n : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    have := k_size C.rnd C.u0 C.u1 C.h0 C.h1 (S := asw fl h.m dm) (m := (h.m : ℝ)) (n := (n : ℝ))
      hm1R hm2R hS2' hn1R hd cj3 hM
    linarith
  · intro hkj
    obtain ⟨kc1, kc2, kc3⟩ := content k hkn hck
    obtain ⟨jc1, jc2, jc3⟩ := content j hjn hcj
    have hbg := bias_gap u η M (δ : ℝ) fl C.rnd C.u0 C.u1 C.h0 C.h1 hδ0R hδ1R h dm hdm hm1R hm2R
      n i j k hkj hjn.le hin.le hun hηn hM12
    obtain ⟨-, pj⟩ := pack j hjn hcj
    obtain ⟨-, pk⟩ := pack k hkn hck
    obtain ⟨b1, b2⟩ := hbg
    unfold InIV at kc1 jc1
    obtain ⟨k1, k2⟩ := abs_le.mp kc1
    obtain ⟨j1, j2⟩ := abs_le.mp jc1
    obtain ⟨a1, a2⟩ := abs_le.mp pj
    obtain ⟨e1, e2⟩ := abs_le.mp pk
    unfold sigFar
    push_cast
    linarith
  · intro hk4 hj4
    obtain ⟨kc1, kc2, kc3⟩ := content k hkn hck
    obtain ⟨jc1, jc2, jc3⟩ := content j hjn hcj
    have hk4R : (i : ℝ) ≤ (k : ℝ) + 4 := by exact_mod_cast hk4
    have hj4R : (i : ℝ) ≤ (j : ℝ) + 4 := by exact_mod_cast hj4
    have hdj : |(j : ℝ) - (i : ℝ)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
    have hdk : |(k : ℝ) - (i : ℝ)| ≤ 4 := by rw [abs_le]; constructor <;> linarith
    have hkj' : |((k : ℝ) - (i : ℝ)) - ((j : ℝ) - (i : ℝ))| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith
    unfold InIV at kc1 jc1
    have key := k_near_core C.rnd C.u0 C.u1 C.h0 C.h1 hM1 (S := asw fl h.m dm)
      (m := (h.m : ℝ)) (dm := dm) (δ := (δ : ℝ)) (dj := (j : ℝ) - (i : ℝ))
      (dk := (k : ℝ) - (i : ℝ))
      (cj := pdot fl (x i) (armat fl h.A (x j) dA 0) 0)
      (ck := pdot fl (x i) (armat fl h.A (x k) dA 0) 0)
      (cj' := (((sAt hc (tok i) (tok j)).1 : ℚ) : ℝ))
      (ck' := (((sAt hc (tok i) (tok k)).1 : ℚ) : ℝ))
      (rj := (((sAt hc (tok i) (tok j)).2 : ℚ) : ℝ))
      (rk := (((sAt hc (tok i) (tok k)).2 : ℚ) : ℝ))
      hS1' hS2' hm1R hm2R hdj hdk hkj' jc3 kc3 hdm jc1 kc1
    have hab : |((k : ℝ) - (i : ℝ)) - ((j : ℝ) - (i : ℝ))| = |(k : ℝ) - (j : ℝ)| := by
      rw [show ((k : ℝ) - (i : ℝ)) - ((j : ℝ) - (i : ℝ)) = (k : ℝ) - (j : ℝ) by ring]
    rw [hab] at key
    obtain ⟨K1, K2⟩ := abs_le.mp key
    rw [k_score_eq h fl dA dm x i k, k_score_eq h fl dA dm x i j]
    push_cast
    rw [abs_le]
    constructor <;> linarith

end Lane4.Case
