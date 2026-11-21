/-
Gated carry chain mod 3.  State width 5: [dg, cv, pr, res, aux].
Head: strict mask, slope 24, gate = relu(pr - 1/2) (propagate tokens and only they are removed),
value row 3 copies cv into res.  The nearest non-propagate earlier key (BOS included) wins.
MLP: one hidden unit relu(dg + res - 2), output -3 * hidden into aux.  Read-out dg + res + aux.
-/
namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.cdot false

/-! ### The network -/

def dgq (t : ℕ) : ℚ := if t = 1 then 1 else if t = 3 then 2 else if t = 5 then 1 else 0
def cvq (t : ℕ) : ℚ := if t = 1 then 1 else if t = 2 then 1 else 0
def prq (t : ℕ) : ℚ := if t = 5 then 1 else 0

def head1 : AHead :=
  { A := [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
    V := [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 0]],
    mask := Mask.strict, m := 24, g := [0, 0, 1, 0, 0], gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [[1, 0, 0, 1, 0]], b1 := [-2],
    W2 := [[0], [0], [0], [0], [-3]], b2 := [0, 0, 0, 0, 0] }

def net : ANet :=
  { embed := [[0, 0, 0, 0, 0], [1, 1, 0, 0, 0], [0, 1, 0, 0, 0], [2, 0, 0, 0, 0],
              [0, 0, 0, 0, 0], [1, 0, 1, 0, 0]],
    blocks := [blk], outW := [1, 0, 0, 1, 1], outB := 0 }

/-! ### Ideal side: nearest non-propagate key and the carry -/

def lastNP (w : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tokAt w (k + 1) = 5 then lastNP w k else k + 1

theorem lastNP_spec (w : List ℕ) : ∀ k, lastNP w k ≤ k ∧ tokAt w (lastNP w k) ≠ 5 ∧
    ∀ m, lastNP w k < m → m ≤ k → tokAt w m = 5 := by
  intro k
  induction k with
  | zero =>
    have e0 : lastNP w 0 = 0 := rfl
    rw [e0]
    refine ⟨le_refl _, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]; norm_num
    · intro m h1 h2; omega
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases h5 : tokAt w (k + 1) = 5
    · have e : lastNP w (k + 1) = lastNP w k := by
        first | simp [lastNP, h5] | (unfold lastNP; rw [if_pos h5])
      rw [e]
      refine ⟨by omega, h2, ?_⟩
      intro m hm1 hm2
      by_cases hmk : m = k + 1
      · rw [hmk]; exact h5
      · exact h3 m hm1 (by omega)
    · have e : lastNP w (k + 1) = k + 1 := by
        first | simp [lastNP, h5] | (unfold lastNP; rw [if_neg h5])
      rw [e]
      refine ⟨le_refl _, h5, ?_⟩
      intro m hm1 hm2; omega

theorem cls_eq_two (t : ℕ) : cls t = 2 ↔ t = 5 := by
  unfold cls
  split_ifs <;> constructor <;> intro h <;> omega

theorem carry_lastNP (w : List ℕ) : ∀ k, k ≤ w.length →
    carry (w.take k) = cls (tokAt w (lastNP w k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e0 : lastNP w 0 = 0 := rfl
    rw [e0, Lane4.Seq.tokAt_zero]
    simp [carry, cls]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := hk
    have ih' := ih (by omega)
    have htok : tokAt w (k + 1) = w[k] := Lane4.Seq.tokAt_succ w k hk'
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      first
        | (rw [List.take_succ, List.getElem?_eq_getElem hk']; rfl)
        | (rw [List.take_succ, List.getElem?_eq_getElem hk'])
        | simp [List.take_succ, hk']
    have hc : carry (w.take (k + 1)) =
        (if cls w[k] = 2 then carry (w.take k) else cls w[k]) := by
      rw [htake]
      unfold carry
      rw [List.foldl_append]
      try rfl
    by_cases h5 : tokAt w (k + 1) = 5
    · have e : lastNP w (k + 1) = lastNP w k := by
        first | simp [lastNP, h5] | (unfold lastNP; rw [if_pos h5])
      have hcls : cls w[k] = 2 := (cls_eq_two _).mpr (by rw [← htok]; exact h5)
      rw [hc, if_pos hcls, e, ih']
    · have e : lastNP w (k + 1) = k + 1 := by
        first | simp [lastNP, h5] | (unfold lastNP; rw [if_neg h5])
      have hcls : cls w[k] ≠ 2 := fun h => h5 (by rw [htok]; exact (cls_eq_two _).mp h)
      rw [hc, if_neg hcls, e, htok]

theorem target_eq (w : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    target w i = (dg (tokAt w i) + cls (tokAt w (lastNP w (i - 1)))) % 3 := by
  have h1 : w.getD (i - 1) 0 = tokAt w i := by
    cases i with
    | zero => omega
    | succ k => simp [tokAt]
  unfold target
  rw [h1, carry_lastNP w (i - 1) (by omega)]

theorem relu_ge0 (a : ℝ) : 0 ≤ Lane4.relu a := by
  unfold Lane4.relu
  exact le_max_right _ _

theorem relu_le1 {a : ℝ} (h : a ≤ 1) : Lane4.relu a ≤ 1 := by
  unfold Lane4.relu
  exact max_le h zero_le_one

theorem relu_nonpos' {a : ℝ} (h : a ≤ 0) : Lane4.relu a = 0 := by
  unfold Lane4.relu
  exact max_eq_right h

theorem relu_nonneg' {a : ℝ} (h : 0 ≤ a) : Lane4.relu a = a := by
  unfold Lane4.relu
  exact max_eq_left h

theorem relu_lip (a b : ℝ) : |Lane4.relu a - Lane4.relu b| ≤ |a - b| := by
  unfold Lane4.relu
  first
    | exact abs_max_sub_max_le_abs a b 0
    | (rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
       · rw [max_eq_right ha, max_eq_right hb]; simp
       · rw [max_eq_right ha, max_eq_left hb]; rw [abs_le]
         constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b), abs_nonneg (a - b)]
       · rw [max_eq_left ha, max_eq_right hb]; rw [abs_le]
         constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b), abs_nonneg (a - b)]
       · rw [max_eq_left ha, max_eq_left hb])

theorem ideal_out (D C : ℕ) (hD : D ≤ 2) (hC : C ≤ 1) :
    (((D + C) % 3 : ℕ) : ℝ) =
      (D : ℝ) + (C : ℝ) + (-3) * Lane4.relu ((D : ℝ) + (C : ℝ) + (-2)) := by
  interval_cases D <;> interval_cases C <;>
    first
    | (rw [relu_nonpos' (by norm_num)]; norm_num)
    | (rw [relu_nonneg' (by norm_num)]; norm_num)

theorem dg_le2 {t : ℕ} (h : t ≤ 5) : dg t ≤ 2 := by
  interval_cases t <;> simp [dg]

theorem cls_le1 {t : ℕ} (h : t ≤ 5) (h5 : t ≠ 5) : cls t ≤ 1 := by
  interval_cases t <;> first | exact absurd rfl h5 | simp [cls]

theorem dgq_cast {t : ℕ} (h : t ≤ 5) : ((dgq t : ℚ) : ℝ) = ((dg t : ℕ) : ℝ) := by
  interval_cases t <;> norm_num [dgq, dg]

theorem cvq_cast {t : ℕ} (h : t ≤ 5) (h5 : t ≠ 5) : ((cvq t : ℚ) : ℝ) = ((cls t : ℕ) : ℝ) := by
  interval_cases t <;> first | exact absurd rfl h5 | norm_num [cvq, cls]

theorem tq_bounds {t : ℕ} (h : t ≤ 5) :
    0 ≤ ((dgq t : ℚ) : ℝ) ∧ ((dgq t : ℚ) : ℝ) ≤ 2 ∧ 0 ≤ ((cvq t : ℚ) : ℝ) ∧
    ((cvq t : ℚ) : ℝ) ≤ 1 ∧ 0 ≤ ((prq t : ℚ) : ℝ) ∧ ((prq t : ℚ) : ℝ) ≤ 1 := by
  interval_cases t <;> norm_num [dgq, cvq, prq]

theorem abs_le_of {x X : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ X) : |x| ≤ X := by
  rw [abs_of_nonneg h0]; exact h1

theorem abs_sum_close {x1 x2 t1 t2 e1 e2 : ℝ} (h1 : |x1 - t1| ≤ e1) (h2 : |x2 - t2| ≤ e2) :
    |x1 + x2 - (t1 + t2)| ≤ e1 + e2 := by
  have := abs_add_le (x1 - t1) (x2 - t2)
  have e : x1 - t1 + (x2 - t2) = x1 + x2 - (t1 + t2) := by ring
  rw [e] at this; linarith

theorem abs_sum_close0 {x1 x2 t e1 e2 : ℝ} (h1 : |x1 - t| ≤ e1) (h2 : |x2 - 0| ≤ e2) :
    |x1 + x2 - t| ≤ e1 + e2 := by
  have := abs_add_le (x1 - t) (x2 - 0)
  have e : x1 - t + (x2 - 0) = x1 + x2 - t := by ring
  rw [e] at this; linarith

/-! ### Embedding rows and ideal states -/

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [dgq t, cvq t, prq t, 0, 0] := by
  interval_cases t <;> first | rfl | simp [net, dgq, cvq, prq]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (dgq (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (cvq (tokAt w j)) (p.E (tokAt w j) 1), asw fl (prq (tokAt w j)) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [((dgq (tokAt w j) : ℚ) : ℝ), ((cvq (tokAt w j) : ℚ) : ℝ), ((prq (tokAt w j) : ℚ) : ℝ), 0, 0]

theorem close5 {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 e X : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e) (h3 : |a3 - b3| ≤ e)
    (h4 : |a4 - b4| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) (g2 : |b2| ≤ X) (g3 : |b3| ≤ X) (g4 : |b4| ≤ X) :
    Close [a0, a1, a2, a3, a4] [b0, b1, b2, b3, b4] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk5 : k < 5 := by simpa using hk
  interval_cases k
  · first
      | exact ⟨h0, g0⟩
      | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
      | (simp; exact ⟨h0, g0⟩)
  · first
      | exact ⟨h1, g1⟩
      | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
      | (simp; exact ⟨h1, g1⟩)
  · first
      | exact ⟨h2, g2⟩
      | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
      | (simp; exact ⟨h2, g2⟩)
  · first
      | exact ⟨h3, g3⟩
      | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
      | (simp; exact ⟨h3, g3⟩)
  · first
      | exact ⟨h4, g4⟩
      | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)
      | (simp; exact ⟨h4, g4⟩)

/-! ### Sums of coefficient times ideal entry -/

theorem sum_zero (y0 y1 y2 y3 y4 : ℝ) :
    ((0 : ℚ) : ℝ) * y0 + ((0 : ℚ) : ℝ) * y1 + ((0 : ℚ) : ℝ) * y2 + ((0 : ℚ) : ℝ) * y3
      + ((0 : ℚ) : ℝ) * y4 = 0 := by simp

theorem sum_cv (y0 y1 y2 y3 y4 : ℝ) :
    ((0 : ℚ) : ℝ) * y0 + ((1 : ℚ) : ℝ) * y1 + ((0 : ℚ) : ℝ) * y2 + ((0 : ℚ) : ℝ) * y3
      + ((0 : ℚ) : ℝ) * y4 = y1 := by simp

theorem sum_pr (y0 y1 y2 y3 y4 : ℝ) :
    ((0 : ℚ) : ℝ) * y0 + ((0 : ℚ) : ℝ) * y1 + ((1 : ℚ) : ℝ) * y2 + ((0 : ℚ) : ℝ) * y3
      + ((0 : ℚ) : ℝ) * y4 = y2 := by simp

theorem sum_hid (y0 y1 y2 y3 y4 : ℝ) :
    ((1 : ℚ) : ℝ) * y0 + ((0 : ℚ) : ℝ) * y1 + ((0 : ℚ) : ℝ) * y2 + ((1 : ℚ) : ℝ) * y3
      + ((0 : ℚ) : ℝ) * y4 = y0 + y3 := by simp

theorem sum_out (y0 y1 y2 y3 y4 : ℝ) :
    ((1 : ℚ) : ℝ) * y0 + ((0 : ℚ) : ℝ) * y1 + ((0 : ℚ) : ℝ) * y2 + ((1 : ℚ) : ℝ) * y3
      + ((1 : ℚ) : ℝ) * y4 = y0 + y3 + y4 := by simp

/-! ### Names for the head -/

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) : ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i)
    (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

noncomputable def yvec (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : Vec :=
  Lane4.RSeq.radd fl (net.init fl p w i)
    [att fl ex p w i [0, 0, 0, 0, 0] 0, att fl ex p w i [0, 0, 0, 0, 0] 1,
     att fl ex p w i [0, 0, 0, 0, 0] 2, att fl ex p w i [0, 1, 0, 0, 0] 3,
     att fl ex p w i [0, 0, 0, 0, 0] 4]

noncomputable def hidv (fl : ℝ → ℝ) (p : APert) (y : Vec) : ℝ :=
  Lane4.relu (fl (ardot fl [1, 0, 0, 1, 0] y (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0)))

noncomputable def mlpr (fl : ℝ → ℝ) (p : APert) (r : ℕ) (a b : ℚ) (h : ℝ) : ℝ :=
  fl (fl (0 + fl (asw fl a (p.W2 0 r 0) * h)) + asw fl b (p.b2 0 r))

theorem out_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.out fl ex p w i =
      fl (ardot fl [1, 0, 0, 1, 1] (Lane4.RSeq.radd fl (yvec fl ex p w i)
        [mlpr fl p 0 0 0 (hidv fl p (yvec fl ex p w i)), mlpr fl p 1 0 0 (hidv fl p (yvec fl ex p w i)),
         mlpr fl p 2 0 0 (hidv fl p (yvec fl ex p w i)), mlpr fl p 3 0 0 (hidv fl p (yvec fl ex p w i)),
         mlpr fl p 4 (-3) 0 (hidv fl p (yvec fl ex p w i))]) p.oW 0 0 + asw fl 0 p.oB) := rfl

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

/-! ### The context -/

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

/-- Rounding adds at most 1/10000 for arguments of size at most 200. -/
theorem fl_near (ev : Ctx u η M fl ex p w) {x t e B : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ B)
    (hB2 : B ≤ 200) : |fl x - t| ≤ e + 1 / 10000 := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB
  have hBM : B ≤ M := ev.range B (le_trans hB2 (by norm_num))
  have h := ev.hr.near ev.hu0 hx hB hBM
  have h2 : u * B ≤ 1 / 2 ^ 24 * 200 := mul_le_mul ev.hu1 hB2 hB0 (by positivity)
  have h3 := eta_tiny ev.hη1
  have h4 : (1 : ℝ) / 2 ^ 24 * 200 + 1 / 10 ^ 40 ≤ 1 / 10000 := by norm_num
  linarith

theorem fl_step (ev : Ctx u η M fl ex p w) {x t e : ℝ} (hx : |x - t| ≤ e) (ht : |t| ≤ 50)
    (he : e ≤ 1) : |fl x - t| ≤ e + 1 / 10000 := by
  have h2 : |x| ≤ 51 := by
    have := abs_add_le (x - t) t
    have e' : x - t + t = x := by ring
    rw [e'] at this; linarith
  exact fl_near ev hx h2 (by norm_num)

theorem add_step (ev : Ctx u η M fl ex p w) {a s t s' e1 e2 : ℝ} (ha : |a - t| ≤ e1)
    (hs : |s - s'| ≤ e2) (hB : |t + s'| ≤ 50) (hee : e1 + e2 ≤ 1) :
    |fl (a + s) - (t + s')| ≤ e1 + e2 + 1 / 10000 := by
  have h1 : |a + s - (t + s')| ≤ e1 + e2 := abs_sum_close ha hs
  exact fl_step ev h1 hB hee

theorem add_step0 (ev : Ctx u η M fl ex p w) {a s t e1 e2 : ℝ} (ha : |a - t| ≤ e1)
    (hs : |s - 0| ≤ e2) (hB : |t| ≤ 50) (hee : e1 + e2 ≤ 1) :
    |fl (a + s) - t| ≤ e1 + e2 + 1 / 10000 :=
  fl_step ev (abs_sum_close0 ha hs) hB hee

theorem add_stepz (ev : Ctx u η M fl ex p w) {a s s' e1 e2 : ℝ} (ha : |a - 0| ≤ e1)
    (hs : |s - s'| ≤ e2) (hB : |s'| ≤ 50) (hee : e1 + e2 ≤ 1) :
    |fl (a + s) - s'| ≤ e1 + e2 + 1 / 10000 := by
  have h := abs_sum_close ha hs
  rw [zero_add] at h
  exact fl_step ev h hB hee

/-! ### Stored weights -/

theorem asw_c (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 3) : |asw fl a d - (a : ℝ)| ≤ 1 / 990 := by
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have h := asw_near ev.hr ev.hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul ev.hu1 (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny ev.hη1
  have h3 : (1 : ℝ) / 1000 + (1 / 2 ^ 24 * 4 + 1 / 10 ^ 40) ≤ 1 / 990 := by norm_num
  linarith

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a b c d e : ℝ, net.init fl p w j = [a, b, c, d, e] ∧
      |a - ((dgq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧ |b - ((cvq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧
      |c - ((prq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 500 ∧ |d - 0| ≤ 1 / 500 ∧ |e - 0| ≤ 1 / 500 := by
  have ht := tok_le w ev.hw j
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds ht
  have h0q : ((0 : ℚ) : ℝ) = 0 := by norm_num
  refine ⟨_, _, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_, ?_⟩
  · have h := asw_c ev (dgq (tokAt w j)) (ev.hp.E (tokAt w j) 0)
      (by rw [abs_of_nonneg b1]; linarith)
    linarith
  · have h := asw_c ev (cvq (tokAt w j)) (ev.hp.E (tokAt w j) 1)
      (by rw [abs_of_nonneg b3]; linarith)
    linarith
  · have h := asw_c ev (prq (tokAt w j)) (ev.hp.E (tokAt w j) 2)
      (by rw [abs_of_nonneg b5]; linarith)
    linarith
  · have h := asw_c ev (0 : ℚ) (ev.hp.E (tokAt w j) 3) (by norm_num)
    rw [h0q] at h
    linarith
  · have h := asw_c ev (0 : ℚ) (ev.hp.E (tokAt w j) 4) (by norm_num)
    rw [h0q] at h
    linarith

theorem init_close (ev : Ctx u η M fl ex p w) (j : ℕ) :
    (net.init fl p w j).length = 5 ∧ Close (net.init fl p w j) (xhat w j) (1 / 500) 2 := by
  obtain ⟨a, b, c, d, e, hx, ha, hb, hc, hd, he⟩ := init_ent ev j
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds (tok_le w ev.hw j)
  rw [hx]
  refine ⟨by simp, ?_⟩
  unfold xhat
  exact close5 ha hb hc hd he (abs_le_of b1 b2) (abs_le_of b3 (by linarith))
    (abs_le_of b5 (by linarith)) (by norm_num) (by norm_num)

/-! ### Five-term dot products, per coordinate -/

theorem dot5 (ev : Ctx u η M fl ex p w) (a0 a1 a2 a3 a4 : ℚ) (aa0 aa1 aa2 aa3 aa4 : ℝ)
    (ha0 : |(a0 : ℝ)| ≤ aa0) (ha1 : |(a1 : ℝ)| ≤ aa1) (ha2 : |(a2 : ℝ)| ≤ aa2)
    (ha3 : |(a3 : ℝ)| ≤ aa3) (ha4 : |(a4 : ℝ)| ≤ aa4)
    {x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 e0 e1 e2 e3 e4 X0 X1 X2 X3 X4 : ℝ}
    (c0 : |x0 - y0| ≤ e0) (c1 : |x1 - y1| ≤ e1) (c2 : |x2 - y2| ≤ e2) (c3 : |x3 - y3| ≤ e3)
    (c4 : |x4 - y4| ≤ e4)
    (b0 : |y0| ≤ X0) (b1 : |y1| ≤ X1) (b2 : |y2| ≤ X2) (b3 : |y3| ≤ X3) (b4 : |y4| ≤ X4)
    (hall : aa0 ≤ 3 ∧ aa1 ≤ 3 ∧ aa2 ≤ 3 ∧ aa3 ≤ 3 ∧ aa4 ≤ 3 ∧ e0 ≤ 1 / 5 ∧ e1 ≤ 1 / 5 ∧
      e2 ≤ 1 / 5 ∧ e3 ≤ 1 / 5 ∧ e4 ≤ 1 / 5 ∧ X0 ≤ 3 ∧ X1 ≤ 3 ∧ X2 ≤ 3 ∧ X3 ≤ 3 ∧ X4 ≤ 3)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [a0, a1, a2, a3, a4] [x0, x1, x2, x3, x4] d 0 0 -
        ((a0 : ℝ) * y0 + (a1 : ℝ) * y1 + (a2 : ℝ) * y2 + (a3 : ℝ) * y3 + (a4 : ℝ) * y4)|
      ≤ aa0 * e0 + 1 / 1000 * (X0 + e0) + (aa1 * e1 + 1 / 1000 * (X1 + e1))
        + (aa2 * e2 + 1 / 1000 * (X2 + e2)) + (aa3 * e3 + 1 / 1000 * (X3 + e3))
        + (aa4 * e4 + 1 / 1000 * (X4 + e4)) + 1 / 700 := by
  obtain ⟨k0, k1, k2, k3, k4, l0, l1, l2, l3, l4, m0, m1, m2, m3, m4⟩ := hall
  have n0 : 0 ≤ e0 := le_trans (abs_nonneg _) c0
  have n1 : 0 ≤ e1 := le_trans (abs_nonneg _) c1
  have n2 : 0 ≤ e2 := le_trans (abs_nonneg _) c2
  have n3 : 0 ≤ e3 := le_trans (abs_nonneg _) c3
  have n4 : 0 ≤ e4 := le_trans (abs_nonneg _) c4
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have hCL : CloseL [x0, x1, x2, x3, x4] [y0, y1, y2, y3, y4] [e0, e1, e2, e3, e4]
      [X0, X1, X2, X3, X4] := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro k hk
    have hk5 : k < 5 := by simpa using hk
    interval_cases k
    · first
        | exact ⟨c0, b0⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨c0, b0⟩)
        | (simp; exact ⟨c0, b0⟩)
    · first
        | exact ⟨c1, b1⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨c1, b1⟩)
        | (simp; exact ⟨c1, b1⟩)
    · first
        | exact ⟨c2, b2⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨c2, b2⟩)
        | (simp; exact ⟨c2, b2⟩)
    · first
        | exact ⟨c3, b3⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨c3, b3⟩)
        | (simp; exact ⟨c3, b3⟩)
    · first
        | exact ⟨c4, b4⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨c4, b4⟩)
        | (simp; exact ⟨c4, b4⟩)
  have hES : ∀ k, k < ([x0, x1, x2, x3, x4] : List ℝ).length →
      ([e0, e1, e2, e3, e4] : List ℝ).getD k 0 ≤ 1 / 5 ∧ ([X0, X1, X2, X3, X4] : List ℝ).getD k 0 ≤ 3 := by
    intro k hk
    have hk5 : k < 5 := by simpa using hk
    interval_cases k
    · first
        | exact ⟨l0, m0⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨l0, m0⟩)
        | (simp; exact ⟨l0, m0⟩)
    · first
        | exact ⟨l1, m1⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨l1, m1⟩)
        | (simp; exact ⟨l1, m1⟩)
    · first
        | exact ⟨l2, m2⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨l2, m2⟩)
        | (simp; exact ⟨l2, m2⟩)
    · first
        | exact ⟨l3, m3⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨l3, m3⟩)
        | (simp; exact ⟨l3, m3⟩)
    · first
        | exact ⟨l4, m4⟩
        | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨l4, m4⟩)
        | (simp; exact ⟨l4, m4⟩)
  have hW : ∀ a ∈ ([a0, a1, a2, a3, a4] : List ℚ), |(a : ℝ)| ≤ 3 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h <;> rw [h] <;> linarith
  have key := ardot_near_w u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (by norm_num)
    (by norm_num) [a0, a1, a2, a3, a4] [x0, x1, x2, x3, x4] [y0, y1, y2, y3, y4]
    [e0, e1, e2, e3, e4] [X0, X1, X2, X3, X4] d 3 3 (1 / 5) (by simp) (by simp) hCL hES hd hW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM30
  obtain ⟨kk, -⟩ := key
  have hdq : dotQ [a0, a1, a2, a3, a4] [y0, y1, y2, y3, y4] =
      (a0 : ℝ) * y0 + (a1 : ℝ) * y1 + (a2 : ℝ) * y2 + (a3 : ℝ) * y3 + (a4 : ℝ) * y4 := by
    simp [dotQ] <;> ring
  have hwe : wErr (1 / 1000) [a0, a1, a2, a3, a4] [e0, e1, e2, e3, e4] [X0, X1, X2, X3, X4] =
      |(a0 : ℝ)| * e0 + 1 / 1000 * (X0 + e0) + (|(a1 : ℝ)| * e1 + 1 / 1000 * (X1 + e1))
        + (|(a2 : ℝ)| * e2 + 1 / 1000 * (X2 + e2)) + (|(a3 : ℝ)| * e3 + 1 / 1000 * (X3 + e3))
        + (|(a4 : ℝ)| * e4 + 1 / 1000 * (X4 + e4)) := by
    simp [wErr] <;> ring
  have hR : (([a0, a1, a2, a3, a4] : List ℚ).length : ℝ) * (3 + 1) * (3 + 1 / 5 + 1) / 2 ^ 16
      + 1 / 2 ^ 100 ≤ 1 / 700 := by norm_num
  rw [hdq, hwe] at kk
  have q0 := mul_le_mul_of_nonneg_right ha0 n0
  have q1 := mul_le_mul_of_nonneg_right ha1 n1
  have q2 := mul_le_mul_of_nonneg_right ha2 n2
  have q3 := mul_le_mul_of_nonneg_right ha3 n3
  have q4 := mul_le_mul_of_nonneg_right ha4 n4
  linarith [kk, hR, q0, q1, q2, q3, q4]

/-! ### Rows applied to the stored embedding -/

theorem row_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [0, 0, 0, 0, 0] (net.init fl p w j) d 0 0 - 0| ≤ 1 / 180 := by
  obtain ⟨a, b, c, d', e, hx, ha, hb, hc, hd', he⟩ := init_ent ev j
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds (tok_le w ev.hw j)
  rw [hx]
  have h := dot5 ev 0 0 0 0 0 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha hb hc hd' he (abs_le_of b1 b2) (abs_le_of b3 b4) (abs_le_of b5 b6)
    (show |(0 : ℝ)| ≤ 0 by norm_num) (show |(0 : ℝ)| ≤ 0 by norm_num) (by norm_num) d hd
  rw [sum_zero] at h
  linarith [h]

theorem row_cv (ev : Ctx u η M fl ex p w) (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) d 0 0 - ((cvq (tokAt w j) : ℚ) : ℝ)|
      ≤ 1 / 130 := by
  obtain ⟨a, b, c, d', e, hx, ha, hb, hc, hd', he⟩ := init_ent ev j
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds (tok_le w ev.hw j)
  rw [hx]
  have h := dot5 ev 0 1 0 0 0 0 1 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha hb hc hd' he (abs_le_of b1 b2) (abs_le_of b3 b4) (abs_le_of b5 b6)
    (show |(0 : ℝ)| ≤ 0 by norm_num) (show |(0 : ℝ)| ≤ 0 by norm_num) (by norm_num) d hd
  rw [sum_cv] at h
  linarith [h]

theorem gate_dot (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0 - ((prq (tokAt w j) : ℚ) : ℝ)|
      ≤ 1 / 100 := by
  obtain ⟨a, b, c, d', e, hx, ha, hb, hc, hd', he⟩ := init_ent ev j
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds (tok_le w ev.hw j)
  rw [hx]
  have h := dot5 ev 0 0 1 0 0 0 0 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ha hb hc hd' he (abs_le_of b1 b2) (abs_le_of b3 b4) (abs_le_of b5 b6)
    (show |(0 : ℝ)| ≤ 0 by norm_num) (show |(0 : ℝ)| ≤ 0 by norm_num) (by norm_num) (p.g 0 0)
    (ev.hp.g 0 0)
  rw [sum_pr] at h
  have h2 : |ardot fl [0, 0, 1, 0, 0] [a, b, c, d', e] (p.g 0 0) 0 0
      - ((prq (tokAt w j) : ℚ) : ℝ)| ≤ 1 / 100 := by linarith [h]
  exact h2

/-! ### The gate -/

theorem gate_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j ≠ 5) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have hd := gate_dot ev j
  have hq : ((prq (tokAt w j) : ℚ) : ℝ) = 0 := by simp [prq, hj]
  rw [hq] at hd
  have hb := asw_c ev head1.gb (ev.hp.gb 0 0) (by norm_num [head1])
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  rw [hgb] at hb
  have hsum := abs_sum_close hd hb
  have hs := abs_le.mp hsum
  have hM3 : (3 : ℝ) ≤ M := ev.range 3 (by norm_num)
  unfold AHead.gate
  exact relu_fl_zero ev.hr (by linarith [hs.1, hs.2]) (by linarith [hs.1, hs.2])

theorem gate_pos (ev : Ctx u η M fl ex p w) (j : ℕ) (hj : tokAt w j = 5) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ≠ 0 := by
  have hd := gate_dot ev j
  have hq : ((prq (tokAt w j) : ℚ) : ℝ) = 1 := by simp [prq, hj]
  rw [hq] at hd
  have hb := asw_c ev head1.gb (ev.hp.gb 0 0) (by norm_num [head1])
  have hgb : ((head1.gb : ℚ) : ℝ) = -1 / 2 := by norm_num [head1]
  rw [hgb] at hb
  have hsum := abs_sum_close hd hb
  have hfl := fl_step ev hsum (by norm_num) (by norm_num)
  have hfl2 := abs_le.mp hfl
  unfold AHead.gate Lane4.relu
  intro h
  have h1 := le_max_left (fl (ardot fl head1.g (net.init fl p w j) (p.g 0 0) 0 0
    + asw fl head1.gb (p.gb 0 0))) 0
  linarith [hfl2.1, hfl2.2]

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j < i ∧ tokAt w j ≠ 5 := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h5 => gate_pos ev j h5 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, gate_zero ev j h2⟩

/-! ### Scores -/

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  obtain ⟨hli, hCi⟩ := init_close ev i
  obtain ⟨hlk, hCk⟩ := init_close ev k
  have hrow : ∀ r : ℕ, |ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 1 / 180 :=
    fun r => row_zero ev k (p.A 0 0 r) (ev.hp.A 0 0 r)
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 2) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 3) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 4) 0 0] := rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0, 0] (1 / 150) 0 := by
    rw [hy]
    exact close5 (le_trans (hrow 0) (by norm_num)) (le_trans (hrow 1) (by norm_num))
      (le_trans (hrow 2) (by norm_num)) (le_trans (hrow 3) (by norm_num))
      (le_trans (hrow 4) (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hlen_y : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 5 := by
    simp [hy]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0, 0] 2 0 (1 / 500)
    (1 / 150) (by rw [hli, hlen_y]) (by rw [hli]; norm_num) hCi hCy (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hM30
  have hdR : dotR (xhat w i) [0, 0, 0, 0, 0] = 0 := by simp [dotR, xhat]
  rw [hdR, sub_zero, hli] at p1
  refine le_trans p1 ?_
  norm_num

theorem head1_m : ((head1.m : ℚ) : ℝ) = 24 := by norm_num [head1]

theorem bias_abs (ev : Ctx u η M fl ex p w) (i t : ℕ) (hi : i ≤ w.length + 1)
    (ht : t ≤ w.length + 1) :
    |head1.bias fl (p.m 0 0) i t| ≤ 26 * ((w.length + 1 : ℕ) : ℝ) := by
  have hm := head1_m
  have habs : |((head1.m : ℚ) : ℝ)| = 24 := by rw [hm]; exact abs_of_nonneg (by norm_num)
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM4 : (25 : ℝ) ≤ M := ev.range 25 (by norm_num)
  have hS := asw_bound ev.hr ev.hu0 head1.m (ev.hp.m 0 0) (by rw [habs]; linarith)
  rw [habs] at hS
  have hu25 : u * (24 + 1 / 1000) ≤ 1 / 2 ^ 24 * 25 :=
    mul_le_mul ev.hu1 (by norm_num) (by norm_num) (by positivity)
  have hη' := eta_tiny ev.hη1
  have hS2 : |asw fl head1.m (p.m 0 0)| ≤ 25 := by
    have h1 : (1 : ℝ) / 2 ^ 24 * 25 + 1 / 10 ^ 40 ≤ 1 / 2 := by norm_num
    linarith
  have hbias : head1.bias fl (p.m 0 0) i t
      = fl (asw fl head1.m (p.m 0 0) * ((t : ℝ) - (i : ℝ))) := by
    simp [AHead.bias]
  rw [hbias]
  generalize asw fl head1.m (p.m 0 0) = S at hS hS2 ⊢
  have ht' : (t : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  have hi' : (i : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hti : |(t : ℝ) - (i : ℝ)| ≤ ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hab : |S * ((t : ℝ) - (i : ℝ))| ≤ 25 * ((w.length + 1 : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hS2 hti (abs_nonneg _) (by norm_num)
  have hB := ev.rangeN 25 (by norm_num) (by norm_num)
  have h := ev.hr.bound ev.hu0 hab hB
  have hu25n := u_mul ev 25 (by norm_num)
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  linarith

theorem score_abs (ev : Ctx u η M fl ex p w) (i k : ℕ) (hi : i ≤ w.length + 1)
    (hk : k ≤ w.length + 1) :
    |head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i k| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hbk := bias_abs ev i k hi hk
  have hck := content_small ev i k
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |head1.bias fl (p.m 0 0) i k + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have h := ev.hr.bound ev.hu0 ha hB
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hu27 := u_mul ev 27 (by norm_num)
  unfold AHead.score
  linarith

theorem score_gap (ev : Ctx u η M fl ex p w) (i j k : ℕ) (hi : i ≤ w.length + 1)
    (hj : j ≤ w.length + 1) (hkj : k < j) :
    head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i k ≤
      head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j - 16 * ((j : ℝ) - (k : ℝ)) := by
  have hm := head1_m
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ w.length + 1 by omega)
  have hM12 : (2 : ℝ) ^ 12 * (((w.length + 1 : ℕ) : ℝ) + 1) ≤ M := by
    have := ev.rangeN 8192 (by norm_num) (by norm_num)
    have h12 : (2 : ℝ) ^ 12 = 4096 := by norm_num
    rw [h12]; linarith
  obtain ⟨hg1, -⟩ := bias_gap u η M (1 / 1000) fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1
    (by norm_num) (by norm_num) head1 (p.m 0 0) (ev.hp.m 0 0) (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (w.length + 1) i j k hkj hj hi ev.hn ev.hnη hM12
  rw [hm] at hg1
  obtain ⟨hcj1, hcj2⟩ := abs_le.mp (content_small ev i j)
  obtain ⟨hck1, hck2⟩ := abs_le.mp (content_small ev i k)
  have hcj := content_small ev i j
  have hck := content_small ev i k
  have hbj := bias_abs ev i j hi hj
  have hbk := bias_abs ev i k hi (by omega)
  have hB := ev.rangeN 27 (by norm_num) (by norm_num)
  have ha : |head1.bias fl (p.m 0 0) i k + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hb : |head1.bias fl (p.m 0 0) i j + Lane4.RSeq.pdot fl (net.init fl p w i)
      (armat fl head1.A (net.init fl p w j) (p.A 0 0) 0) 0| ≤ 27 * ((w.length + 1 : ℕ) : ℝ) :=
    le_trans (abs_add_le _ _) (by linarith)
  have hgap := ev.hr.gap ev.hu0 ha hb hB
  have hu27 := u_mul ev 27 (by norm_num)
  have hη' := eta_tiny ev.hη1
  have h10 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hjk : (k : ℝ) + 1 ≤ (j : ℝ) := by
    have h : k + 1 ≤ j := hkj
    exact_mod_cast h
  unfold AHead.score
  linarith

/-! ### The head returns the value at the nearest non-propagate key -/

theorem att_gen (ev : Ctx u η M fl ex p w) (r : List ℚ) (k : ℕ) (g : ℕ → ℝ) (ε Q : ℝ)
    (hε0 : 0 ≤ ε) (hQ0 : 0 ≤ Q) (hQε : Q + ε ≤ 2)
    (hv : ∀ j, |ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0 - g j| ≤ ε)
    (hq : ∀ j, |g j| ≤ Q) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |att fl ex p w i r k - g (lastNP w (i - 1))| ≤ ε + (Q + ε) / 100 + 1 / 2 ^ 90 := by
  obtain ⟨hl1, hl2, hl3⟩ := lastNP_spec w (i - 1)
  have hj : lastNP w (i - 1) ∈ cs fl p w i := (mem_cs ev i _).mpr ⟨by omega, hl2⟩
  have hlen := cs_len fl p w i hi
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ lastNP w (i - 1) →
      sc fl p w i k' ≤ sc fl p w i (lastNP w (i - 1))
        - 16 * ((ndist (lastNP w (i - 1)) k' : ℕ) : ℝ) := by
    intro k' hk' hne
    obtain ⟨hk'i, hk'5⟩ := (mem_cs ev i k').mp hk'
    have hlt : k' < lastNP w (i - 1) := by
      by_contra hcon
      have hcon' : lastNP w (i - 1) ≤ k' := not_lt.mp hcon
      have hne' : lastNP w (i - 1) < k' := lt_of_le_of_ne hcon' (Ne.symm hne)
      exact hk'5 (hl3 k' hne' (by omega))
    rw [ndist_cast]
    have hg := score_gap ev i (lastNP w (i - 1)) k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ ((lastNP w (i - 1) : ℕ) : ℝ) := by
      have h : k' + 1 ≤ lastNP w (i - 1) := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    have := (mem_cs ev i k').mp hk'
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ Q + ε := by
    intro k' _
    have h1 := hv k'
    have h2 := hq k'
    have h3 := abs_sub_abs_le_abs_sub (ardot fl r (net.init fl p w k') (p.V 0 0 k) 0 0) (g k')
    linarith
  have hBM : 4 * (Q + ε) + 4 ≤ M := by
    have := ev.range 12 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0) ev.hr ev.he ev.hu0 ev.hu1
    ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS hSM hf hBM
  have hs1' : |att fl ex p w i r k - ardot fl r (net.init fl p w (lastNP w (i - 1))) (p.V 0 0 k) 0 0|
      ≤ (Q + ε) / 100 + 1 / 2 ^ 90 := hs1
  have hv' := hv (lastNP w (i - 1))
  have h3 := abs_sub_le (att fl ex p w i r k)
    (ardot fl r (net.init fl p w (lastNP w (i - 1))) (p.V 0 0 k) 0 0) (g (lastNP w (i - 1)))
  linarith

theorem att_vals (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    (∀ k, |att fl ex p w i [0, 0, 0, 0, 0] k - 0| ≤ 1 / 175) ∧
    |att fl ex p w i [0, 1, 0, 0, 0] 3 - ((cvq (tokAt w (lastNP w (i - 1))) : ℚ) : ℝ)| ≤ 1 / 55 := by
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 10 ^ 20 := by norm_num
  constructor
  · intro k
    have h : |att fl ex p w i [0, 0, 0, 0, 0] k - 0| ≤ 1 / 180 + (0 + 1 / 180) / 100 + 1 / 2 ^ 90 :=
      att_gen ev [0, 0, 0, 0, 0] k (fun _ => 0) (1 / 180) 0 (by norm_num) (le_refl _)
        (by norm_num) (fun j => row_zero ev j (p.V 0 0 k) (ev.hp.V 0 0 k)) (fun j => by simp)
        i hi1 hi
    linarith
  · have h : |att fl ex p w i [0, 1, 0, 0, 0] 3 - ((cvq (tokAt w (lastNP w (i - 1))) : ℚ) : ℝ)|
        ≤ 1 / 130 + (1 + 1 / 130) / 100 + 1 / 2 ^ 90 :=
      att_gen ev [0, 1, 0, 0, 0] 3 (fun j => ((cvq (tokAt w j) : ℚ) : ℝ)) (1 / 130) 1
        (by norm_num) (by norm_num) (by norm_num)
        (fun j => row_cv ev j (p.V 0 0 3) (ev.hp.V 0 0 3))
        (fun j => by
          obtain ⟨_, _, b3, b4, _, _⟩ := tq_bounds (tok_le w ev.hw j)
          exact abs_le_of b3 b4) i hi1 hi
    linarith

/-! ### The state after the head -/

theorem yvec_bounds (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    ∃ Y0 Y1 Y2 Y3 Y4 : ℝ, yvec fl ex p w i = [Y0, Y1, Y2, Y3, Y4] ∧
      |Y0 - ((dgq (tokAt w i) : ℚ) : ℝ)| ≤ 1 / 125 ∧
      |Y1 - ((cvq (tokAt w i) : ℚ) : ℝ)| ≤ 1 / 125 ∧
      |Y2 - ((prq (tokAt w i) : ℚ) : ℝ)| ≤ 1 / 125 ∧
      |Y3 - ((cvq (tokAt w (lastNP w (i - 1))) : ℚ) : ℝ)| ≤ 1 / 48 ∧
      |Y4 - 0| ≤ 1 / 125 := by
  obtain ⟨a, b, c, d, e, hx, ha, hb, hc, hd, he⟩ := init_ent ev i
  obtain ⟨t0, t3⟩ := att_vals ev i hi1 hi
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tq_bounds (tok_le w ev.hw i)
  have y0 := add_step0 ev ha (t0 0) (abs_le_of b1 (by linarith)) (by norm_num)
  have y1 := add_step0 ev hb (t0 1) (abs_le_of b3 (by linarith)) (by norm_num)
  have y2 := add_step0 ev hc (t0 2) (abs_le_of b5 (by linarith)) (by norm_num)
  have y3 := add_stepz ev hd t3
    (by
      obtain ⟨_, _, j3, j4, _, _⟩ := tq_bounds (tok_le w ev.hw (lastNP w (i - 1)))
      exact abs_le_of j3 (by linarith)) (by norm_num)
  have y4 := add_step0 ev he (t0 4) (by norm_num) (by norm_num)
  refine ⟨fl (a + att fl ex p w i [0, 0, 0, 0, 0] 0), fl (b + att fl ex p w i [0, 0, 0, 0, 0] 1),
    fl (c + att fl ex p w i [0, 0, 0, 0, 0] 2), fl (d + att fl ex p w i [0, 1, 0, 0, 0] 3),
    fl (e + att fl ex p w i [0, 0, 0, 0, 0] 4), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold yvec
    rw [hx]
    try rfl
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-! ### The MLP -/

theorem hid_bound (ev : Ctx u η M fl ex p w) {Y0 Y1 Y2 Y3 Y4 D cv pr C : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ 2) (hcv0 : 0 ≤ cv) (hcv : cv ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (h0 : |Y0 - D| ≤ 1 / 125) (h1 : |Y1 - cv| ≤ 1 / 125) (h2 : |Y2 - pr| ≤ 1 / 125)
    (h3 : |Y3 - C| ≤ 1 / 48) (h4 : |Y4 - 0| ≤ 1 / 125) :
    |hidv fl p [Y0, Y1, Y2, Y3, Y4] - Lane4.relu (D + C + (-2))| ≤ 1 / 27 := by
  unfold hidv
  refine le_trans (relu_lip _ _) ?_
  have hdot := dot5 ev 1 0 0 1 0 1 0 0 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h0 h1 h2 h3 h4 (abs_le_of hD0 hD) (abs_le_of hcv0 hcv)
    (abs_le_of hpr0 hpr) (abs_le_of hC0 hC) (show |(0 : ℝ)| ≤ 0 by norm_num) (by norm_num)
    (p.W1 0 0) (ev.hp.W1 0 0)
  rw [sum_hid] at hdot
  have hb := asw_c ev (-2 : ℚ) (ev.hp.b1 0 0) (by norm_num)
  have hbq : ((-2 : ℚ) : ℝ) = -2 := by norm_num
  rw [hbq] at hb
  have hsum := abs_sum_close hdot hb
  have hfl := fl_step ev hsum (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  linarith [hfl]

theorem mlp_row (ev : Ctx u η M fl ex p w) (a : ℚ) (r : ℕ) (hid ρ aa : ℝ)
    (ha : |(a : ℝ)| ≤ aa) (haa0 : 0 ≤ aa) (haa : aa ≤ 3)
    (hh : |hid - ρ| ≤ 1 / 27) (hρ : |ρ| ≤ 1) :
    |mlpr fl p r a 0 hid - (a : ℝ) * ρ| ≤ aa / 27 + 1 / 400 := by
  unfold mlpr
  have hA := asw_c ev a (ev.hp.W2 0 r 0) (by linarith)
  have hB := asw_c ev (0 : ℚ) (ev.hp.b2 0 r) (by norm_num)
  have h0q : ((0 : ℚ) : ℝ) = 0 := by norm_num
  rw [h0q] at hB
  have hhid : |hid| ≤ 28 / 27 := by
    have := abs_sub_abs_le_abs_sub hid ρ
    linarith
  have e1 : asw fl a (p.W2 0 r 0) * hid - (a : ℝ) * ρ
      = (asw fl a (p.W2 0 r 0) - (a : ℝ)) * hid + (a : ℝ) * (hid - ρ) := by ring
  have p1 : |(asw fl a (p.W2 0 r 0) - (a : ℝ)) * hid| ≤ 1 / 990 * (28 / 27) := by
    rw [abs_mul]; exact mul_le_mul hA hhid (abs_nonneg _) (by norm_num)
  have p2 : |(a : ℝ) * (hid - ρ)| ≤ aa * (1 / 27) := by
    rw [abs_mul]; exact mul_le_mul ha hh (abs_nonneg _) haa0
  have hP : |asw fl a (p.W2 0 r 0) * hid - (a : ℝ) * ρ| ≤ aa / 27 + 1 / 990 * (28 / 27) := by
    rw [e1]
    have := abs_add_le ((asw fl a (p.W2 0 r 0) - (a : ℝ)) * hid) ((a : ℝ) * (hid - ρ))
    linarith
  have hat : |(a : ℝ) * ρ| ≤ 3 := by
    rw [abs_mul]
    calc |(a : ℝ)| * |ρ| ≤ 3 * 1 := mul_le_mul (by linarith) hρ (abs_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  have s1 := fl_step ev hP (by linarith) (by linarith)
  have hx2 : |0 + fl (asw fl a (p.W2 0 r 0) * hid) - (a : ℝ) * ρ|
      ≤ aa / 27 + 1 / 990 * (28 / 27) + 1 / 10000 := by
    rw [zero_add]; exact s1
  have s2 := fl_step ev hx2 (by linarith) (by linarith)
  have hx3 := abs_sum_close0 s2 hB
  have s3 := fl_step ev hx3 (by linarith) (by linarith)
  linarith [s3]

theorem mlp_zero (ev : Ctx u η M fl ex p w) (r : ℕ) (H ρ : ℝ) (hh : |H - ρ| ≤ 1 / 27)
    (hρ : |ρ| ≤ 1) : |mlpr fl p r 0 0 H - 0| ≤ 1 / 400 := by
  have h := mlp_row ev 0 r H ρ 0 (by norm_num) (le_refl _) (by norm_num) hh hρ
  have e0 : ((0 : ℚ) : ℝ) * ρ = 0 := by simp
  rw [e0] at h
  linarith

theorem mlp_aux (ev : Ctx u η M fl ex p w) (H ρ : ℝ) (hh : |H - ρ| ≤ 1 / 27)
    (hρ : |ρ| ≤ 1) : |mlpr fl p 4 (-3) 0 H - (-3) * ρ| ≤ 3 / 27 + 1 / 400 := by
  have h := mlp_row ev (-3) 4 H ρ 3 (by norm_num) (by norm_num) (by norm_num) hh hρ
  have e0 : ((-3 : ℚ) : ℝ) * ρ = (-3) * ρ := by norm_num
  rw [e0] at h
  exact h

/-! ### The chain: from the state after the head to the output -/

theorem chain (ev : Ctx u η M fl ex p w) {Y0 Y1 Y2 Y3 Y4 D cv pr C : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ 2) (hcv0 : 0 ≤ cv) (hcv : cv ≤ 1) (hpr0 : 0 ≤ pr) (hpr : pr ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 1)
    (h0 : |Y0 - D| ≤ 1 / 125) (h1 : |Y1 - cv| ≤ 1 / 125) (h2 : |Y2 - pr| ≤ 1 / 125)
    (h3 : |Y3 - C| ≤ 1 / 48) (h4 : |Y4 - 0| ≤ 1 / 125) :
    |fl (ardot fl [1, 0, 0, 1, 1] (Lane4.RSeq.radd fl [Y0, Y1, Y2, Y3, Y4]
        [mlpr fl p 0 0 0 (hidv fl p [Y0, Y1, Y2, Y3, Y4]),
         mlpr fl p 1 0 0 (hidv fl p [Y0, Y1, Y2, Y3, Y4]),
         mlpr fl p 2 0 0 (hidv fl p [Y0, Y1, Y2, Y3, Y4]),
         mlpr fl p 3 0 0 (hidv fl p [Y0, Y1, Y2, Y3, Y4]),
         mlpr fl p 4 (-3) 0 (hidv fl p [Y0, Y1, Y2, Y3, Y4])]) p.oW 0 0 + asw fl 0 p.oB)
      - (D + C + (-3) * Lane4.relu (D + C + (-2)))| ≤ 1 / 4 := by
  have hhid := hid_bound ev hD0 hD hcv0 hcv hpr0 hpr hC0 hC h0 h1 h2 h3 h4
  generalize hidv fl p [Y0, Y1, Y2, Y3, Y4] = H at hhid ⊢
  have hρ0 : 0 ≤ Lane4.relu (D + C + (-2)) := relu_ge0 _
  have hρ1 : Lane4.relu (D + C + (-2)) ≤ 1 := relu_le1 (by linarith)
  generalize Lane4.relu (D + C + (-2)) = ρ at hhid hρ0 hρ1 ⊢
  have hρa : |ρ| ≤ 1 := abs_le_of hρ0 hρ1
  have hz : Lane4.RSeq.radd fl [Y0, Y1, Y2, Y3, Y4]
      [mlpr fl p 0 0 0 H, mlpr fl p 1 0 0 H, mlpr fl p 2 0 0 H, mlpr fl p 3 0 0 H,
       mlpr fl p 4 (-3) 0 H] =
      [fl (Y0 + mlpr fl p 0 0 0 H), fl (Y1 + mlpr fl p 1 0 0 H), fl (Y2 + mlpr fl p 2 0 0 H),
       fl (Y3 + mlpr fl p 3 0 0 H), fl (Y4 + mlpr fl p 4 (-3) 0 H)] := rfl
  rw [hz]
  have mz : ∀ r : ℕ, |mlpr fl p r 0 0 H - 0| ≤ 1 / 400 := fun r => mlp_zero ev r H ρ hhid hρa
  have ma := mlp_aux ev H ρ hhid hρa
  have z0 := add_step0 ev h0 (mz 0) (abs_le_of hD0 (by linarith)) (by norm_num)
  have z1 := add_step0 ev h1 (mz 1) (abs_le_of hcv0 (by linarith)) (by norm_num)
  have z2 := add_step0 ev h2 (mz 2) (abs_le_of hpr0 (by linarith)) (by norm_num)
  have z3 := add_step0 ev h3 (mz 3) (abs_le_of hC0 (by linarith)) (by norm_num)
  have z4 := add_stepz ev h4 ma (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  have hdot := dot5 ev 1 0 0 1 1 1 0 0 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) z0 z1 z2 z3 z4 (abs_le_of hD0 hD) (abs_le_of hcv0 hcv)
    (abs_le_of hpr0 hpr) (abs_le_of hC0 hC)
    (show |(-3 * ρ)| ≤ 3 by rw [abs_le]; constructor <;> linarith) (by norm_num)
    p.oW ev.hp.oW
  rw [sum_out] at hdot
  have hob := asw_c ev (0 : ℚ) ev.hp.oB (by norm_num)
  have h0q : ((0 : ℚ) : ℝ) = 0 := by norm_num
  rw [h0q] at hob
  have hsum := abs_sum_close0 hdot hob
  have hfl := fl_step ev hsum (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  linarith [hfl]

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨Y0, Y1, Y2, Y3, Y4, hY, hy0, hy1, hy2, hy3, hy4⟩ := yvec_bounds ev i hi1 hi
  have ht := tok_le w ev.hw i
  obtain ⟨lj1, lj2, lj3⟩ := lastNP_spec w (i - 1)
  have hj := tok_le w ev.hw (lastNP w (i - 1))
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := tq_bounds ht
  obtain ⟨j1, j2, j3, j4, j5, j6⟩ := tq_bounds hj
  have key := chain ev d1 d2 d3 d4 d5 d6 j3 j4 hy0 hy1 hy2 hy3 hy4
  have hT : ((target w i : ℕ) : ℝ) =
      ((dgq (tokAt w i) : ℚ) : ℝ) + ((cvq (tokAt w (lastNP w (i - 1))) : ℚ) : ℝ)
        + (-3) * Lane4.relu (((dgq (tokAt w i) : ℚ) : ℝ)
          + ((cvq (tokAt w (lastNP w (i - 1))) : ℚ) : ℝ) + (-2)) := by
    rw [target_eq w i hi1 hi, ideal_out _ _ (dg_le2 ht) (cls_le1 hj lj2),
      ← dgq_cast ht, ← cvq_cast hj lj2]
  rw [hT, out_eq fl ex p w i, hY]
  exact key

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
