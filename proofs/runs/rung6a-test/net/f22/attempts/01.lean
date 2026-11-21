namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network.  State [mk, f, a, c, A, y]. -/

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def zrows : List (List ℚ) := [z6, z6, z6, z6, z6, z6]

def head1 : AHead :=
  { A := zrows, V := [z6, [1, 0, 0, 0, 0, 0], z6, z6, z6, z6], mask := Mask.strict, m := 24,
    g := [-1, 0, 0, 0, 0, 0], gb := 1 / 2 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def head2 : AHead :=
  { A := zrows, V := [z6, z6, z6, z6, [0, 0, 1, 0, 0, 0], z6], mask := Mask.causal, m := 24,
    g := [-1, 3, 0, 0, 0, 0], gb := 1 / 2 }

def blk2 : ABlock :=
  { heads := [head2], W1 := [[0, 0, 0, -1, 1, 0], [0, 0, 0, 1, -1, 0]], b1 := [0, 0],
    W2 := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [[0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0]],
    blocks := [blk1, blk2], outW := [0, 0, 0, 0, 0, 1], outB := 0 }

/-! ### Context -/

structure Ctx (u η M : ℝ) (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) : Prop where
  hr : Rnd u η M fl
  he : ExpM u η ex
  hu0 : 0 ≤ u
  hu1 : u ≤ 1 / 2 ^ 24
  hη0 : 0 ≤ η
  hη1 : η ≤ 1 / 2 ^ 149
  hp : p.Within (1 / 1000)
  hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5
  hn : u * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 256
  hnη : η * ((w.length + 1 : ℕ) : ℝ) ≤ 1 / 2 ^ 100
  hM : 2 ^ 40 * ((w.length + 1 : ℕ) : ℝ) ^ 2 ≤ M

def X6 : List ℝ := [1, 1, 1, 1, 1, 1]

section Steps

variable {u η M : ℝ} {fl ex : ℝ → ℝ} {p : APert} {w : List ℕ}

theorem Ctx.range (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : c ≤ 2 ^ 40) : c ≤ M :=
  range_const ev.hM (by omega) hc

theorem Ctx.rangeN (ev : Ctx u η M fl ex p w) (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 2 ^ 40) :
    c * ((w.length + 1 : ℕ) : ℝ) ≤ M :=
  range_lin ev.hM (by omega) hc0 hc

theorem u_mul (ev : Ctx u η M fl ex p w) (c : ℝ) (hc : 0 ≤ c) :
    u * (c * ((w.length + 1 : ℕ) : ℝ)) ≤ c / 256 := by
  have h : u * (c * ((w.length + 1 : ℕ) : ℝ)) = c * (u * ((w.length + 1 : ℕ) : ℝ)) := by ring
  rw [h]
  have := mul_le_mul_of_nonneg_left ev.hn hc
  linarith

theorem Ctx.u6 (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10 ^ 7 := by
  have h := ev.hu1
  have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 10 ^ 7 := by norm_num
  linarith

theorem Ctx.η6 (ev : Ctx u η M fl ex p w) : η ≤ 1 / 10 ^ 30 := by
  have h := eta_tiny ev.hη1
  have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10 ^ 30 := by norm_num
  linarith

theorem asw_c (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 2) : |asw fl a d - (a : ℝ)| ≤ 1 / 500 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have h := asw_near ev.hr ev.hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 10 ^ 7 * 3 :=
    mul_le_mul ev.u6 (by linarith) (by positivity) (by positivity)
  have h2 := ev.η6
  have h3 : (1 : ℝ) / 10 ^ 7 * 3 + 1 / 10 ^ 30 ≤ 1 / 1000 := by norm_num
  linarith

theorem add_near (ev : Ctx u η M fl ex p w) {x s t s' y e1 e2 : ℝ} (hx : |x - t| ≤ e1)
    (hs : |s - s'| ≤ e2) (hy : t + s' = y) (hy2 : |y| ≤ 2) (he1 : e1 ≤ 1 / 2) (he2 : e2 ≤ 1 / 2) :
    |fl (x + s) - y| ≤ e1 + e2 + 1 / 10 ^ 6 := by
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  have h1 : |x + s - y| ≤ e1 + e2 := by
    have : x + s - y = (x - t) + (s - s') := by rw [← hy]; ring
    rw [this]
    exact le_trans (abs_add_le _ _) (by linarith)
  have h2 : |x + s| ≤ 3 := by
    have h3 := abs_add_le (x + s - y) y
    have h4 : x + s - y + y = x + s := by ring
    rw [h4] at h3
    have := abs_nonneg (x + s - y)
    linarith
  have h3 := ev.hr.near ev.hu0 h1 h2 hM3
  have hu := ev.u6
  have hη := ev.η6
  have h5 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 10 ^ 7 := by norm_num
  have h6 : (1 : ℝ) / 10 ^ 7 * 3 + 1 / 10 ^ 7 ≤ 1 / 10 ^ 6 := by norm_num
  have h7 : u * 3 ≤ 1 / 10 ^ 7 * 3 := by linarith
  linarith

theorem closeL6 {a b c d e f a' b' c' d' e' f' ea eb ec ed ee ef : ℝ}
    (h1 : |a - a'| ≤ ea) (h2 : |b - b'| ≤ eb) (h3 : |c - c'| ≤ ec) (h4 : |d - d'| ≤ ed)
    (h5 : |e - e'| ≤ ee) (h6 : |f - f'| ≤ ef)
    (g1 : |a'| ≤ 1) (g2 : |b'| ≤ 1) (g3 : |c'| ≤ 1) (g4 : |d'| ≤ 1) (g5 : |e'| ≤ 1)
    (g6 : |f'| ≤ 1) :
    CloseL [a, b, c, d, e, f] [a', b', c', d', e', f'] [ea, eb, ec, ed, ee, ef] X6 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k
  · exact ⟨h1, g1⟩
  · exact ⟨h2, g2⟩
  · exact ⟨h3, g3⟩
  · exact ⟨h4, g4⟩
  · exact ⟨h5, g5⟩
  · exact ⟨h6, g6⟩

theorem closeL_len {x xh es : List ℝ} (hC : CloseL x xh es X6) : x.length = 6 := by
  have := hC.2.2.1
  simpa [X6] using this.symm

theorem closeL_es {x xh es : List ℝ} (hC : CloseL x xh es X6) : es.length = 6 := by
  have := hC.2.1
  rw [closeL_len hC] at this
  exact this

theorem X6_get (k : ℕ) (hk : k < 6) : X6.getD k 0 ≤ 1 := by
  interval_cases k <;> simp [X6]

theorem dot6 (ev : Ctx u η M fl ex p w) (r : List ℚ) (hr : r.length = 6)
    (hW : ∀ a ∈ r, |(a : ℝ)| ≤ 3)
    {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 20)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ wErr (1 / 1000) r es X6 + 1 / 1000 ∧
      |ardot fl r x d 0 0| ≤ 100 := by
  have hlen := closeL_len hC
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) r x xh es X6 d 3 1 (1 / 20) (by rw [hr, hlen]) (by omega) hC
    (fun k hk => ⟨hes k (by omega), X6_get k (by omega)⟩) hd hW (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hM30
  obtain ⟨k1, k2⟩ := key
  rw [hr] at k1 k2
  simp only [Nat.cast_ofNat] at k1 k2
  have e1 : (6 : ℝ) * (3 + 1) * (1 + 1 / 20 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 1 / 1000 := by norm_num
  have e2 : (6 : ℝ) * (3 + 1) * (1 + 1 / 20 + 1) * 2 ≤ 100 := by norm_num
  exact ⟨by linarith, by linarith⟩

theorem dotQ_zeros (x : List ℝ) : dotQ z6 x = 0 := by
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;> simp [dotQ, z6]

theorem dotR_zeros (x : List ℝ) : dotR x [0, 0, 0, 0, 0, 0] = 0 := by
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;> simp [dotR]

theorem zero_dot (ev : Ctx u η M fl ex p w) {x : List ℝ} (hx : x.length = 6)
    (hb : ∀ k, k < 6 → |x.getD k 0| ≤ 2) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl z6 x d 0 0| ≤ 1 / 70 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hC : Close x x 0 2 := ⟨rfl, fun k hk => ⟨by simp, hb k (by omega)⟩⟩
  have key := ardot_near_abs u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) z6 x x d 0 2 0 (by simp [z6, hx]) (by simp [z6]) hC hd
    (by intro a ha; simp [z6] at ha; rw [ha]; simp) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hM30
  rw [dotQ_zeros] at key
  have habs : absSum z6 = 0 := by simp [absSum, z6]
  rw [habs] at key
  have hl : (z6.length : ℝ) = 6 := by simp [z6]
  rw [hl] at key
  have e1 : (0 : ℝ) * 0 + 6 * (1 / 1000) * (2 + 0) + 6 * (0 + 1) * (2 + 0 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 1 / 70 := by norm_num
  have := sub_zero (ardot fl z6 x d 0 0)
  rw [this] at key
  linarith

theorem close_self {x : List ℝ} (hx : x.length = 6) (hb : ∀ k, k < 6 → |x.getD k 0| ≤ 2) :
    Close x x 0 2 := ⟨rfl, fun k hk => ⟨by simp, hb k (by omega)⟩⟩

theorem close_zero6 {a b c d e f : ℝ} (h1 : |a| ≤ 1 / 70) (h2 : |b| ≤ 1 / 70)
    (h3 : |c| ≤ 1 / 70) (h4 : |d| ≤ 1 / 70) (h5 : |e| ≤ 1 / 70) (h6 : |f| ≤ 1 / 70) :
    Close [a, b, c, d, e, f] [0, 0, 0, 0, 0, 0] (1 / 70) 0 := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k
  · exact ⟨by simpa using h1, by simp⟩
  · exact ⟨by simpa using h2, by simp⟩
  · exact ⟨by simpa using h3, by simp⟩
  · exact ⟨by simpa using h4, by simp⟩
  · exact ⟨by simpa using h5, by simp⟩
  · exact ⟨by simpa using h6, by simp⟩

/-- The content part of a score (zero score matrix) is tiny. -/
theorem content_le (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = zrows) (x : ℕ → Vec)
    (hx : ∀ j, j ≤ w.length → (x j).length = 6 ∧ ∀ k, k < 6 → |(x j).getD k 0| ≤ 2)
    (dA : ℕ → ℕ → ℝ) (hdA : ∀ r c, |dA r c| ≤ 1 / 1000) (i k : ℕ) (hi : i ≤ w.length)
    (hk : k ≤ w.length) :
    |Lane4.RSeq.pdot fl (x i) (armat fl h.A (x k) dA 0) 0| ≤ 1 / 5 := by
  obtain ⟨hli, hbi⟩ := hx i hi
  obtain ⟨hlk, hbk⟩ := hx k hk
  have hrow : ∀ r : ℕ, |ardot fl z6 (x k) (dA r) 0 0| ≤ 1 / 70 :=
    fun r => zero_dot ev hlk hbk (dA r) (hdA r)
  have hy : armat fl h.A (x k) dA 0 =
      [ardot fl z6 (x k) (dA 0) 0 0, ardot fl z6 (x k) (dA 1) 0 0, ardot fl z6 (x k) (dA 2) 0 0,
       ardot fl z6 (x k) (dA 3) 0 0, ardot fl z6 (x k) (dA 4) 0 0,
       ardot fl z6 (x k) (dA 5) 0 0] := by
    rw [hA]; rfl
  have hCy := close_zero6 (hrow 0) (hrow 1) (hrow 2) (hrow 3) (hrow 4) (hrow 5)
  rw [← hy] at hCy
  have hly : (armat fl h.A (x k) dA 0).length = 6 := by rw [hy]; rfl
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (x i) (x i)
    (armat fl h.A (x k) dA 0) [0, 0, 0, 0, 0, 0] 2 0 0 (1 / 70) (by rw [hli, hly]) (by omega)
    (close_self hli hbi) hCy (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hM30
  rw [dotR_zeros, sub_zero, hli] at p1
  refine le_trans p1 ?_
  norm_num

theorem bias_bnd (ev : Ctx u η M fl ex p w) (h : AHead) (hm : ((h.m : ℚ) : ℝ) = 24) (b k : ℕ)
    (i j : ℕ) (hi : i ≤ w.length + 1) (hj : 1 ≤ j) (hjn : j ≤ w.length + 1) :
    |h.bias fl (p.m b k) i j| ≤ 26 * (((w.length + 1 : ℕ) : ℝ) + 1) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨-, hg2⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) h (p.m b k) (ev.hp.m b k) (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j 0 (by omega) hjn hi ev.hn ev.hnη hM12
  rw [hm] at hg2
  linarith

theorem score_facts (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = zrows)
    (hm : ((h.m : ℚ) : ℝ) = 24) (x : ℕ → Vec)
    (hx : ∀ j, j ≤ w.length → (x j).length = 6 ∧ ∀ k, k < 6 → |(x j).getD k 0| ≤ 2)
    (b k : ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (∀ j, 1 ≤ j → j ≤ w.length →
      |h.score fl (p.A b k) (p.m b k) x i j| ≤ 54 * ((w.length + 1 : ℕ) : ℝ)) ∧
    (∀ j k', 1 ≤ k' → k' < j → j ≤ w.length →
      h.score fl (p.A b k) (p.m b k) x i k' ≤
        h.score fl (p.A b k) (p.m b k) x i j - 16 * ((j : ℝ) - (k' : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hB := ev.rangeN 53 (by norm_num) (by norm_num)
  have hu53 := u_mul ev 53 (by norm_num)
  have hη' := ev.η6
  have h10 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 1000 := by norm_num
  have hsum : ∀ j, 1 ≤ j → j ≤ w.length →
      |h.bias fl (p.m b k) i j + Lane4.RSeq.pdot fl (x i) (armat fl h.A (x j) (p.A b k) 0) 0|
        ≤ 53 * ((w.length + 1 : ℕ) : ℝ) := by
    intro j hj1 hj2
    have h1 := bias_bnd ev h hm b k i j (by omega) hj1 (by omega)
    have h2 := content_le ev h hA x hx (p.A b k) (ev.hp.A b k) i j hi hj2
    exact le_trans (abs_add_le _ _) (by linarith)
  constructor
  · intro j hj1 hj2
    have h3 := ev.hr.bound ev.hu0 (hsum j hj1 hj2) hB
    unfold AHead.score
    linarith
  · intro j k' hk1 hkj hj2
    have hbg : (1 : ℝ) ≤ ((h.m : ℚ) : ℝ) := by rw [hm]; norm_num
    have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
      have := ev.rangeN 8192 (by norm_num) (by norm_num)
      have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
      rw [h12]; linarith
    obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
      (by norm_num) (by norm_num) h (p.m b k) (ev.hp.m b k) (by rw [hm]; norm_num)
      (by rw [hm]; norm_num) (w.length + 1) i j k' hkj (by omega) (by omega) ev.hn ev.hnη hM12
    rw [hm] at hg1
    have hcj := content_le ev h hA x hx (p.A b k) (ev.hp.A b k) i j hi hj2
    have hck := content_le ev h hA x hx (p.A b k) (ev.hp.A b k) i k' hi (by omega)
    obtain ⟨hcj1, hcj2⟩ := abs_le.mp hcj
    obtain ⟨hck1, hck2⟩ := abs_le.mp hck
    have hgap := ev.hr.gap ev.hu0 (hsum k' hk1 (by omega)) (hsum j (by omega) hj2) hB
    have hjk : (k' : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkj
    unfold AHead.score
    linarith

/-- Softmax with a clear winner that is the largest candidate. -/
theorem att_core (ev : Ctx u η M fl ex p w) {c : List ℕ} (hnd : c.Nodup)
    (hlen : c.length ≤ w.length + 1) {s f : ℕ → ℝ} {j0 : ℕ} (hj0 : j0 ∈ c)
    (hmax : ∀ k ∈ c, k ≤ j0)
    (hgap : ∀ k ∈ c, k < j0 → s k ≤ s j0 - 16 * ((j0 : ℝ) - (k : ℝ)))
    (hS : ∀ k ∈ c, |s k| ≤ 54 * ((w.length + 1 : ℕ) : ℝ)) {B : ℝ}
    (hB : ∀ k ∈ c, |f k| ≤ B) (hB4 : 4 * B + 4 ≤ M) :
    |savg fl ex c s f - f j0| ≤ B / 100 + 1 / 2 ^ 90 := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hSM : 2 * (54 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 108 (by norm_num) (by norm_num)
    linarith
  have hg : ∀ k ∈ c, k ≠ j0 → s k ≤ s j0 - 16 * (ndist j0 k : ℝ) := by
    intro k hk hne
    have hlt : k < j0 := lt_of_le_of_ne (hmax k hk) hne
    rw [ndist_cast]
    have h1 : (k : ℝ) + 1 ≤ j0 := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (j0 : ℝ) - k)]
    exact hgap k hk hlt
  exact (soft_near ev.hr ev.he ev.hu0 ev.hu1 ev.hη0 ev.hη1 hnd hlen ev.hn ev.hnη hj0 hg hS hSM
    hB hB4).1

end Steps

end Lane4.Case
