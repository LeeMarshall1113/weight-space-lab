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
    {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl r x d 0 0 - dotQ r xh| ≤ wErr (1 / 1000) r es X6 + 1 / 1000 ∧
      |ardot fl r x d 0 0| ≤ 110 := by
  have hlen := closeL_len hC
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) r x xh es X6 d 3 1 (1 / 5) (by rw [hr, hlen]) (by omega) hC
    (fun k hk => ⟨hes k (by omega), X6_get k (by omega)⟩) hd hW (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hM30
  obtain ⟨k1, k2⟩ := key
  rw [hr] at k1 k2
  simp only [Nat.cast_ofNat] at k1 k2
  have e1 : (6 : ℝ) * (3 + 1) * (1 + 1 / 5 + 1) / 2 ^ 16 + 1 / 2 ^ 100 ≤ 1 / 1000 := by norm_num
  have e2 : (6 : ℝ) * (3 + 1) * (1 + 1 / 5 + 1) * 2 ≤ 110 := by norm_num
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

/-! ### Ideal values -/

def mkQ (t : ℕ) : ℚ := if code t = 0 then 0 else 1
def abQ (t : ℕ) : ℚ := if code t = 2 then 1 else 0
def cbQ (t : ℕ) : ℚ := (cbit t : ℚ)

noncomputable def Mk (t : ℕ) : ℝ := ((mkQ t : ℚ) : ℝ)
noncomputable def Ab (t : ℕ) : ℝ := ((abQ t : ℚ) : ℝ)
noncomputable def Cb (t : ℕ) : ℝ := ((cbQ t : ℚ) : ℝ)

open Classical in
noncomputable def Fl (w : List ℕ) (i : ℕ) : ℝ :=
  if ∃ k, k < i ∧ Mk (tokAt w k) = 1 then 1 else 0

theorem code_le (t : ℕ) : code t ≤ 2 := by
  unfold code; split_ifs <;> omega

theorem cbit_le (t : ℕ) : cbit t ≤ 1 := by
  unfold cbit; split_ifs <;> omega

theorem Mk_cases (t : ℕ) : (Mk t = 0 ∧ code t = 0) ∨ (Mk t = 1 ∧ code t ≠ 0) := by
  unfold Mk mkQ
  by_cases h : code t = 0
  · left; simp [h]
  · right; simp [h]

theorem Ab_cases (t : ℕ) : (Ab t = 1 ∧ code t = 2) ∨ (Ab t = 0 ∧ code t ≠ 2) := by
  unfold Ab abQ
  by_cases h : code t = 2
  · left; simp [h]
  · right; simp [h]

theorem Cb_cases (t : ℕ) : Cb t = 0 ∨ Cb t = 1 := by
  have := cbit_le t
  rcases (by omega : cbit t = 0 ∨ cbit t = 1) with h | h
  · left; simp [Cb, cbQ, h]
  · right; simp [Cb, cbQ, h]

theorem Mk_abs (t : ℕ) : |Mk t| ≤ 1 := by
  rcases Mk_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num

theorem Ab_abs (t : ℕ) : |Ab t| ≤ 1 := by
  rcases Ab_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> norm_num

theorem Cb_abs (t : ℕ) : |Cb t| ≤ 1 := by
  rcases Cb_cases t with h | h <;> rw [h] <;> norm_num

theorem Fl_abs (w : List ℕ) (i : ℕ) : |Fl w i| ≤ 1 := by
  unfold Fl; split_ifs <;> norm_num

theorem Fl_one {w : List ℕ} {i : ℕ} (h : ∃ k, k < i ∧ Mk (tokAt w k) = 1) : Fl w i = 1 := by
  unfold Fl; rw [if_pos h]

theorem Fl_zero {w : List ℕ} {i : ℕ} (h : ¬ ∃ k, k < i ∧ Mk (tokAt w k) = 1) : Fl w i = 0 := by
  unfold Fl; rw [if_neg h]

theorem tok_le (ev : Ctx u η M fl ex p w) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (ev.hw _ h).2

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [mkQ t, 0, abQ t, cbQ t, 0, 0] := by
  interval_cases t <;> first | rfl | simp [net, mkQ, abQ, cbQ, code, cbit]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j =
      [asw fl (mkQ (tokAt w j)) (p.E (tokAt w j) 0), asw fl 0 (p.E (tokAt w j) 1),
       asw fl (abQ (tokAt w j)) (p.E (tokAt w j) 2), asw fl (cbQ (tokAt w j)) (p.E (tokAt w j) 3),
       asw fl 0 (p.E (tokAt w j) 4), asw fl 0 (p.E (tokAt w j) 5)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

def E0 : List ℝ := [1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500, 1 / 500]

theorem asw_zero (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |asw fl 0 d - 0| ≤ 1 / 500 := by
  simpa using asw_c ev 0 hd (by simp)

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5] ∧
      |a0 - Mk (tokAt w j)| ≤ 1 / 500 ∧ |a1 - 0| ≤ 1 / 500 ∧ |a2 - Ab (tokAt w j)| ≤ 1 / 500 ∧
      |a3 - Cb (tokAt w j)| ≤ 1 / 500 ∧ |a4 - 0| ≤ 1 / 500 ∧ |a5 - 0| ≤ 1 / 500 := by
  have ht := tok_le ev j
  refine ⟨_, _, _, _, _, _, init_eq fl p w j ht, ?_, asw_zero ev (ev.hp.E _ 1), ?_, ?_,
    asw_zero ev (ev.hp.E _ 4), asw_zero ev (ev.hp.E _ 5)⟩
  · exact asw_c ev _ (ev.hp.E _ 0) (le_trans (Mk_abs _) (by norm_num))
  · exact asw_c ev _ (ev.hp.E _ 2) (le_trans (Ab_abs _) (by norm_num))
  · exact asw_c ev _ (ev.hp.E _ 3) (le_trans (Cb_abs _) (by norm_num))

theorem init_cl (ev : Ctx u η M fl ex p w) (j : ℕ) :
    CloseL (net.init fl p w j) [Mk (tokAt w j), 0, Ab (tokAt w j), Cb (tokAt w j), 0, 0] E0 X6 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hx, h0, h1, h2, h3, h4, h5⟩ := init_ent ev j
  rw [hx]
  unfold E0
  exact closeL6 h0 h1 h2 h3 h4 h5 (Mk_abs _) (by norm_num) (Ab_abs _) (Cb_abs _) (by norm_num)
    (by norm_num)

theorem es6 {a b c d e f : ℝ} (ha : a ≤ 1 / 5) (hb : b ≤ 1 / 5) (hc : c ≤ 1 / 5)
    (hd : d ≤ 1 / 5) (he : e ≤ 1 / 5) (hf : f ≤ 1 / 5) :
    ∀ k, k < 6 → ([a, b, c, d, e, f] : List ℝ).getD k 0 ≤ 1 / 5 := by
  intro k hk
  interval_cases k
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf

theorem E0_le : ∀ k, k < 6 → E0.getD k 0 ≤ 1 / 5 := by
  unfold E0; exact es6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

theorem cl_bound {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5) :
    x.length = 6 ∧ ∀ k, k < 6 → |x.getD k 0| ≤ 2 := by
  refine ⟨closeL_len hC, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hC.2.2.2 k (by rw [closeL_len hC]; exact hk)
  have h3 := X6_get k hk
  have h4 := hes k hk
  have h5 := abs_sub_abs_le_abs_sub (x.getD k 0) (xh.getD k 0)
  linarith

/-! ### Gates -/

theorem gate_pre (ev : Ctx u η M fl ex p w) (h : AHead) (hg : h.g.length = 6)
    (hW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 3) (hgb : |((h.gb : ℚ) : ℝ)| ≤ 2)
    {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000) :
    |(ardot fl h.g x dg 0 0 + asw fl h.gb dgb) - (dotQ h.g xh + ((h.gb : ℚ) : ℝ))|
        ≤ wErr (1 / 1000) h.g es X6 + 1 / 1000 + 1 / 500 ∧
      |ardot fl h.g x dg 0 0 + asw fl h.gb dgb| ≤ 113 := by
  obtain ⟨d1, d2⟩ := dot6 ev h.g hg hW hC hes dg hdg
  have a1 := asw_c ev h.gb hdgb hgb
  have h3 := abs_sub_abs_le_abs_sub (asw fl h.gb dgb) ((h.gb : ℚ) : ℝ)
  constructor
  · have e : (ardot fl h.g x dg 0 0 + asw fl h.gb dgb) - (dotQ h.g xh + ((h.gb : ℚ) : ℝ))
        = (ardot fl h.g x dg 0 0 - dotQ h.g xh) + (asw fl h.gb dgb - ((h.gb : ℚ) : ℝ)) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by linarith)
  · exact le_trans (abs_add_le _ _) (by linarith)

theorem gate_zero_of (ev : Ctx u η M fl ex p w) (h : AHead) (hg : h.g.length = 6)
    (hW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 3) (hgb : |((h.gb : ℚ) : ℝ)| ≤ 2)
    {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000) {E : ℝ}
    (hE : wErr (1 / 1000) h.g es X6 + 1 / 1000 + 1 / 500 ≤ E)
    (hq : dotQ h.g xh + ((h.gb : ℚ) : ℝ) ≤ -E) : h.gate fl dg dgb x = 0 := by
  obtain ⟨g1, g2⟩ := gate_pre ev h hg hW hgb hC hes dg dgb hdg hdgb
  have hM := ev.range 113 (by norm_num)
  obtain ⟨a1, a2⟩ := abs_le.mp g1
  obtain ⟨b1, b2⟩ := abs_le.mp g2
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_ne_of (ev : Ctx u η M fl ex p w) (h : AHead) (hg : h.g.length = 6)
    (hW : ∀ a ∈ h.g, |(a : ℝ)| ≤ 3) (hgb : |((h.gb : ℚ) : ℝ)| ≤ 2)
    {x xh es : List ℝ} (hC : CloseL x xh es X6) (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5)
    (dg : ℕ → ℝ) (dgb : ℝ) (hdg : ∀ k, |dg k| ≤ 1 / 1000) (hdgb : |dgb| ≤ 1 / 1000) {E : ℝ}
    (hE : wErr (1 / 1000) h.g es X6 + 1 / 1000 + 1 / 500 ≤ E)
    (hq : E + 1 / 100 ≤ dotQ h.g xh + ((h.gb : ℚ) : ℝ)) : h.gate fl dg dgb x ≠ 0 := by
  obtain ⟨g1, g2⟩ := gate_pre ev h hg hW hgb hC hes dg dgb hdg hdgb
  have hM := ev.range 113 (by norm_num)
  obtain ⟨a1, a2⟩ := abs_le.mp g1
  have hl := ev.hr.lower ev.hu0 g2 hM
  have hu := ev.u6
  have hη := ev.η6
  have h1 : (1 : ℝ) / 10 ^ 30 ≤ 1 / 10 ^ 7 := by norm_num
  have hpos : 0 < fl (ardot fl h.g x dg 0 0 + asw fl h.gb dgb) := by
    have h2 : u * 113 ≤ 113 / 10 ^ 7 := by linarith
    have h3 : (113 : ℝ) / 10 ^ 7 + 1 / 10 ^ 7 ≤ 1 / 200 := by norm_num
    linarith
  unfold AHead.gate Lane4.relu
  intro h0
  rw [max_eq_left hpos.le] at h0
  linarith

theorem gate1_iff (ev : Ctx u η M fl ex p w) (j : ℕ) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 ↔ Mk (tokAt w j) = 1 := by
  have hC := init_cl ev j
  have hg : head1.g.length = 6 := rfl
  have hW : ∀ a ∈ head1.g, |(a : ℝ)| ≤ 3 := by
    simp [head1, List.forall_mem_cons] <;> norm_num
  have hgb : |((head1.gb : ℚ) : ℝ)| ≤ 2 := by norm_num [head1]
  have hq : dotQ head1.g [Mk (tokAt w j), 0, Ab (tokAt w j), Cb (tokAt w j), 0, 0]
      + ((head1.gb : ℚ) : ℝ) = -Mk (tokAt w j) + 1 / 2 := by
    simp [dotQ, head1] <;> ring
  have hE : wErr (1 / 1000) head1.g E0 X6 + 1 / 1000 + 1 / 500 ≤ 1 / 50 := by
    simp [wErr, head1, E0, X6] <;> norm_num
  rcases Mk_cases (tokAt w j) with ⟨h0, _⟩ | ⟨h1, _⟩
  · constructor
    · intro hz
      exfalso
      exact gate_ne_of ev head1 hg hW hgb hC E0_le (p.g 0 0) (p.gb 0 0) (ev.hp.g 0 0)
        (ev.hp.gb 0 0) hE (by rw [hq, h0]; norm_num) hz
    · intro h; rw [h0] at h; norm_num at h
  · constructor
    · intro _; exact h1
    · intro _
      exact gate_zero_of ev head1 hg hW hgb hC E0_le (p.g 0 0) (p.gb 0 0) (ev.hp.g 0 0)
        (ev.hp.gb 0 0) hE (by rw [hq, h1]; norm_num)

theorem mem_cs1 (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i ↔
      j < i ∧ Mk (tokAt w j) = 1 := by
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict, gate1_iff ev j]

theorem Mk_pos (ev : Ctx u η M fl ex p w) {j : ℕ} (h : Mk (tokAt w j) = 1) : 1 ≤ j := by
  by_contra hj
  have : j = 0 := by omega
  subst this
  rcases Mk_cases (tokAt w 0) with ⟨h0, _⟩ | ⟨h1, hc⟩
  · rw [h0] at h; norm_num at h
  · apply hc
    rw [Lane4.Seq.tokAt_zero]
    rfl

/-! ### Heads -/

noncomputable def attv (h : AHead) (fl ex : ℝ → ℝ) (p : APert) (b k n : ℕ) (x : ℕ → Vec) (i : ℕ)
    (r : List ℚ) (t : ℕ) : ℝ :=
  savg fl ex (h.cands fl (p.g b k) (p.gb b k) n x i)
    (fun j => h.score fl (p.A b k) (p.m b k) x i j) (fun j => ardot fl r (x j) (p.V b k t) 0 0)

theorem attn6 (h : AHead) (fl ex : ℝ → ℝ) (p : APert) (b k n : ℕ) (x : ℕ → Vec) (i : ℕ)
    (r0 r1 r2 r3 r4 r5 : List ℚ) (hV : h.V = [r0, r1, r2, r3, r4, r5]) :
    h.attn fl ex (p.A b k) (p.V b k) (p.m b k) (p.g b k) (p.gb b k) n x i =
      [attv h fl ex p b k n x i r0 0, attv h fl ex p b k n x i r1 1,
       attv h fl ex p b k n x i r2 2, attv h fl ex p b k n x i r3 3,
       attv h fl ex p b k n x i r4 4, attv h fl ex p b k n x i r5 5] := by
  unfold AHead.attn
  rw [hV]
  rfl

theorem cands_len (h : AHead) (fl : ℝ → ℝ) (dg : ℕ → ℝ) (dgb : ℝ) (n i : ℕ) (x : ℕ → Vec)
    (hi : i < n) : (h.cands fl dg dgb n x i).length ≤ n := by
  have h1 : (h.cands fl dg dgb n x i).length ≤ (cand h.mask n i).length :=
    List.length_filter_le _ _
  have h2 : ∀ m : Mask, (cand m n i).length ≤ n := by
    intro m
    cases m <;> simp [cand] <;> omega
  have := h2 h.mask
  omega

theorem att_gen (ev : Ctx u η M fl ex p w) (h : AHead) (hA : h.A = zrows)
    (hm : ((h.m : ℚ) : ℝ) = 24) (x : ℕ → Vec)
    (hx : ∀ j, j ≤ w.length → (x j).length = 6 ∧ ∀ k, k < 6 → |(x j).getD k 0| ≤ 2)
    (b k : ℕ) (i : ℕ) (hi : i ≤ w.length)
    (hc : ∀ j ∈ h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i, 1 ≤ j ∧ j ≤ w.length)
    (r : List ℚ) (t : ℕ) {q ε B : ℝ}
    (hval : ∀ j ∈ h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i,
      |ardot fl r (x j) (p.V b k t) 0 0 - q| ≤ ε)
    (hB : ∀ j ∈ h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i,
      |ardot fl r (x j) (p.V b k t) 0 0| ≤ B) (hB4 : 4 * B + 4 ≤ M)
    (hq0 : h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i = [] →
      |q| ≤ ε + B / 100 + 1 / 2 ^ 90) :
    |attv h fl ex p b k (w.length + 1) x i r t - q| ≤ ε + B / 100 + 1 / 2 ^ 90 := by
  by_cases hce : h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i = []
  · have h0 : attv h fl ex p b k (w.length + 1) x i r t = 0 := by
      unfold attv
      rw [hce]
      exact soft_zeros ev.hr (by simp)
    rw [h0, zero_sub, abs_neg]
    exact hq0 hce
  · obtain ⟨j0, hj0, hmax⟩ : ∃ j0 ∈ h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i,
        ∀ k' ∈ h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i, k' ≤ j0 := by
      have hne : (h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i).toFinset.Nonempty := by
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hce
        exact ⟨a, List.mem_toFinset.mpr ha⟩
      obtain ⟨j0, hj0, hm'⟩ := Finset.exists_max_image _ (fun k => k) hne
      exact ⟨j0, List.mem_toFinset.mp hj0, fun k' hk' => hm' k' (List.mem_toFinset.mpr hk')⟩
    have hlen := cands_len h fl (p.g b k) (p.gb b k) (w.length + 1) i x (by omega)
    obtain ⟨hS, hgapall⟩ := score_facts ev h hA hm x hx b k i hi
    have hs := att_core ev (AHead.cands_nodup h fl (p.g b k) (p.gb b k) (w.length + 1) x i) hlen hj0
      hmax (s := fun j => h.score fl (p.A b k) (p.m b k) x i j)
      (f := fun j => ardot fl r (x j) (p.V b k t) 0 0)
      (fun k' hk' hlt => hgapall j0 k' (hc k' hk').1 hlt (hc j0 hj0).2)
      (fun k' hk' => hS k' (hc k' hk').1 (hc k' hk').2) hB hB4
    have e : attv h fl ex p b k (w.length + 1) x i r t =
        savg fl ex (h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i)
          (fun j => h.score fl (p.A b k) (p.m b k) x i j)
          (fun j => ardot fl r (x j) (p.V b k t) 0 0) := rfl
    rw [e]
    have h3 := abs_sub_le (savg fl ex (h.cands fl (p.g b k) (p.gb b k) (w.length + 1) x i)
          (fun j => h.score fl (p.A b k) (p.m b k) x i j)
          (fun j => ardot fl r (x j) (p.V b k t) 0 0)) (ardot fl r (x j0) (p.V b k t) 0 0) q
    have h4 := hval j0 hj0
    beta_reduce at hs
    linarith

theorem val_z6 (ev : Ctx u η M fl ex p w) {x xh es : List ℝ} (hC : CloseL x xh es X6)
    (hes : ∀ k, k < 6 → es.getD k 0 ≤ 1 / 5) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000)
    (hsum : wErr (1 / 1000) z6 es X6 + 1 / 1000 ≤ 1 / 140) :
    |ardot fl z6 x d 0 0| ≤ 1 / 140 := by
  have h := (dot6 ev z6 rfl (by simp [z6, List.forall_mem_cons]) hC hes d hd).1
  rw [dotQ_zeros, sub_zero] at h
  linarith

/-! ### Block 1 -/

theorem blk1_eq (fl ex : ℝ → ℝ) (p : APert) (n : ℕ) (x : ℕ → Vec) (i : ℕ) :
    blk1.apply fl ex p 0 n x i =
      Lane4.RSeq.radd fl
        (Lane4.RSeq.radd fl (x i)
          (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) n x i))
        [fl (0 + asw fl 0 (p.b2 0 0)), fl (0 + asw fl 0 (p.b2 0 1)),
         fl (0 + asw fl 0 (p.b2 0 2)), fl (0 + asw fl 0 (p.b2 0 3)),
         fl (0 + asw fl 0 (p.b2 0 4)), fl (0 + asw fl 0 (p.b2 0 5))] := rfl

theorem mlp0_small (ev : Ctx u η M fl ex p w) {d : ℝ} (hd : |d| ≤ 1 / 1000) :
    |fl (0 + asw fl 0 d)| ≤ 1 / 400 := by
  have h1 := asw_zero ev hd
  rw [sub_zero] at h1
  have h2 : |(0 : ℝ) + asw fl 0 d| ≤ 1 / 500 := by rw [zero_add]; exact h1
  have h3 := ev.hr.bound ev.hu0 h2 (ev.range (1 / 500) (by norm_num))
  have hu := ev.u6
  have hη := ev.η6
  have h4 : u * (1 / 500) ≤ 1 / 10 ^ 7 * (1 / 500) := by nlinarith
  have h5 : (1 : ℝ) / 10 ^ 7 * (1 / 500) + 1 / 10 ^ 30 ≤ 1 / 10 ^ 6 := by norm_num
  linarith

theorem ent3 (ev : Ctx u η M fl ex p w) {a s m t s' y e1 e2 e3 : ℝ} (hx : |a - t| ≤ e1)
    (hs : |s - s'| ≤ e2) (hm : |m| ≤ e3) (hy : t + s' = y) (hy2 : |y| ≤ 2) (he1 : e1 ≤ 1 / 4)
    (he2 : e2 ≤ 1 / 4) (he3 : e3 ≤ 1 / 4) :
    |fl (fl (a + s) + m) - y| ≤ e1 + e2 + e3 + 2 / 10 ^ 6 := by
  have h1 := add_near ev hx hs hy hy2 (by linarith) (by linarith)
  have h2 := add_near ev (x := fl (a + s)) (s := m) (t := y) (s' := 0) (y := y) h1
    (by rw [sub_zero]; exact hm) (add_zero y) hy2 (by linarith) (by linarith)
  linarith


end Steps

end Lane4.Case
