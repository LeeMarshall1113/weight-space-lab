/-
Carry chain modulo 3, gated softmax transformer, width 5, one block (one head + 1-neuron MLP).

State coordinates: [cv, pf, dg, carry, out].
  cv  = 1 for generate tokens (1, 5), pf = 1 for the propagate token (3), dg = digit.
Head: strict mask, slope 24, gate on pf (gate bias -1/2) so propagate tokens are NOT candidates;
the nearest earlier non-propagate key (BOS included, cv = 0) wins; value row 3 copies cv into
coordinate 3 (the carry).
MLP: hidden = relu (dg + carry - 2), written with weight -3 into coordinate 4.
Read-out: dg + carry + coordinate 4 = dg + carry - 3 relu(dg + carry - 2) = (dg + carry) mod 3.
-/
namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network -/

def tcv (t : ℕ) : ℕ := if t = 1 ∨ t = 5 then 1 else 0
def tpf (t : ℕ) : ℕ := if t = 3 then 1 else 0

def head1 : AHead :=
  { A := [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
    V := [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
    mask := Mask.strict, m := 24, g := [0, 1, 0, 0, 0], gb := -1 / 2 }

def blk : ABlock :=
  { heads := [head1], W1 := [[0, 0, 1, 1, 0]], b1 := [-2],
    W2 := [[0], [0], [0], [0], [-3]], b2 := [0, 0, 0, 0, 0] }

def net : ANet :=
  { embed := [[0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 0, 0],
      [1, 0, 0, 0, 0]],
    blocks := [blk], outW := [0, 0, 1, 1, 1], outB := 0 }

/-! ### Definitions used in the proof -/

/-- The ideal state at position `j`. -/
noncomputable def xhat (w : List ℕ) (j : ℕ) : List ℝ :=
  [((tcv (tokAt w j) : ℕ) : ℝ), ((tpf (tokAt w j) : ℕ) : ℝ), ((dg (tokAt w j) : ℕ) : ℝ), 0, 0]

noncomputable def cs (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℕ :=
  head1.cands fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

noncomputable def sc (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : ℕ → ℝ :=
  fun j => head1.score fl (p.A 0 0) (p.m 0 0) (net.init fl p w) i j

noncomputable def att (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (r : List ℚ) (k : ℕ) :
    ℝ :=
  savg fl ex (cs fl p w i) (sc fl p w i) (fun j => ardot fl r (net.init fl p w j) (p.V 0 0 k) 0 0)

noncomputable def Yv (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : List ℝ :=
  Lane4.RSeq.radd fl (net.init fl p w i)
    (head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i)

noncomputable def hid (fl : ℝ → ℝ) (p : APert) (y : List ℝ) : ℝ :=
  Lane4.relu (fl (ardot fl [0, 0, 1, 1, 0] y (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0)))

noncomputable def mo (fl : ℝ → ℝ) (p : APert) (h : ℝ) (k : ℕ) (a : ℚ) : ℝ :=
  fl (ardot fl [a] [h] (p.W2 0 k) 0 0 + asw fl 0 (p.b2 0 k))

noncomputable def Zv (fl : ℝ → ℝ) (p : APert) (Y : List ℝ) : List ℝ :=
  Lane4.RSeq.radd fl Y [mo fl p (hid fl p Y) 0 0, mo fl p (hid fl p Y) 1 0,
    mo fl p (hid fl p Y) 2 0, mo fl p (hid fl p Y) 3 0, mo fl p (hid fl p Y) 4 (-3)]

/-! ### Unfolding the forward pass (definitional) -/

theorem attn_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    head1.attn fl ex (p.A 0 0) (p.V 0 0) (p.m 0 0) (p.g 0 0) (p.gb 0 0) (w.length + 1)
      (net.init fl p w) i =
    [att fl ex p w i [0, 0, 0, 0, 0] 0, att fl ex p w i [0, 0, 0, 0, 0] 1,
     att fl ex p w i [0, 0, 0, 0, 0] 2, att fl ex p w i [1, 0, 0, 0, 0] 3,
     att fl ex p w i [0, 0, 0, 0, 0] 4] := rfl

theorem run_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.run fl ex p w i = Zv fl p (Yv fl ex p w i) := rfl

theorem out_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) :
    net.out fl ex p w i =
      fl (ardot fl [0, 0, 1, 1, 1] (Zv fl p (Yv fl ex p w i)) p.oW 0 0 + asw fl 0 p.oB) := rfl

theorem Yv_eq (fl ex : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (a0 a1 a2 a3 a4 : ℝ)
    (hx : net.init fl p w i = [a0, a1, a2, a3, a4]) :
    Yv fl ex p w i =
      [fl (a0 + att fl ex p w i [0, 0, 0, 0, 0] 0), fl (a1 + att fl ex p w i [0, 0, 0, 0, 0] 1),
       fl (a2 + att fl ex p w i [0, 0, 0, 0, 0] 2), fl (a3 + att fl ex p w i [1, 0, 0, 0, 0] 3),
       fl (a4 + att fl ex p w i [0, 0, 0, 0, 0] 4)] := by
  unfold Yv
  rw [hx]
  rfl

theorem Zv_eq (fl : ℝ → ℝ) (p : APert) (y0 y1 y2 y3 y4 : ℝ) :
    Zv fl p [y0, y1, y2, y3, y4] =
      [fl (y0 + mo fl p (hid fl p [y0, y1, y2, y3, y4]) 0 0),
       fl (y1 + mo fl p (hid fl p [y0, y1, y2, y3, y4]) 1 0),
       fl (y2 + mo fl p (hid fl p [y0, y1, y2, y3, y4]) 2 0),
       fl (y3 + mo fl p (hid fl p [y0, y1, y2, y3, y4]) 3 0),
       fl (y4 + mo fl p (hid fl p [y0, y1, y2, y3, y4]) 4 (-3))] := rfl

/-! ### Facts about tokens -/

theorem tcv_le (t : ℕ) : tcv t ≤ 1 := by
  unfold tcv; split_ifs <;> omega

theorem tpf_le (t : ℕ) : tpf t ≤ 1 := by
  unfold tpf; split_ifs <;> omega

theorem dg_le (t : ℕ) : dg t ≤ 2 := by
  unfold dg; split_ifs <;> omega

theorem tpf_zero {t : ℕ} (h : t ≠ 3) : tpf t = 0 := by
  unfold tpf; simp [h]

theorem tpf_one {t : ℕ} (h : t = 3) : tpf t = 1 := by
  unfold tpf; simp [h]

theorem tcv_r (t : ℕ) : 0 ≤ ((tcv t : ℕ) : ℝ) ∧ ((tcv t : ℕ) : ℝ) ≤ 1 :=
  ⟨Nat.cast_nonneg _, by exact_mod_cast tcv_le t⟩

theorem tpf_r (t : ℕ) : 0 ≤ ((tpf t : ℕ) : ℝ) ∧ ((tpf t : ℕ) : ℝ) ≤ 1 :=
  ⟨Nat.cast_nonneg _, by exact_mod_cast tpf_le t⟩

theorem dg_r (t : ℕ) : 0 ≤ ((dg t : ℕ) : ℝ) ∧ ((dg t : ℕ) : ℝ) ≤ 2 :=
  ⟨Nat.cast_nonneg _, by exact_mod_cast dg_le t⟩

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [((tcv t : ℕ) : ℚ), ((tpf t : ℕ) : ℚ), ((dg t : ℕ) : ℚ), 0, 0] := by
  interval_cases t <;> first | rfl | simp [net, tcv, tpf, dg] | norm_num [net, tcv, tpf, dg]

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl ((tcv (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 0),
      asw fl ((tpf (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 1),
      asw fl ((dg (tokAt w j) : ℕ) : ℚ) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

theorem dq0 (w : List ℕ) (j : ℕ) : dotQ [0, 0, 0, 0, 0] (xhat w j) = 0 := by
  simp [dotQ, xhat]

theorem dq1 (w : List ℕ) (j : ℕ) :
    dotQ [1, 0, 0, 0, 0] (xhat w j) = ((tcv (tokAt w j) : ℕ) : ℝ) := by
  simp [dotQ, xhat]

theorem dqg (w : List ℕ) (j : ℕ) :
    dotQ [0, 1, 0, 0, 0] (xhat w j) = ((tpf (tokAt w j) : ℕ) : ℝ) := by
  simp [dotQ, xhat]

/-! ### Generic list helpers -/

theorem close5 {a b c d e a' b' c' d' e' ε X : ℝ} (ha : |a - a'| ≤ ε) (hb : |b - b'| ≤ ε)
    (hc : |c - c'| ≤ ε) (hd : |d - d'| ≤ ε) (he : |e - e'| ≤ ε)
    (ha' : |a'| ≤ X) (hb' : |b'| ≤ X) (hc' : |c'| ≤ X) (hd' : |d'| ≤ X) (he' : |e'| ≤ X) :
    Close [a, b, c, d, e] [a', b', c', d', e'] ε X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk5 : k < 5 := by simpa using hk
  interval_cases k
  · first | exact ⟨ha, ha'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨ha, ha'⟩)
  · first | exact ⟨hb, hb'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hb, hb'⟩)
  · first | exact ⟨hc, hc'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hc, hc'⟩)
  · first | exact ⟨hd, hd'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hd, hd'⟩)
  · first | exact ⟨he, he'⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨he, he'⟩)

theorem closeL5 {x0 x1 x2 x3 x4 v0 v1 v2 v3 v4 e0 e1 e2 e3 e4 X0 X1 X2 X3 X4 : ℝ}
    (hx0 : |x0 - v0| ≤ e0) (hv0 : |v0| ≤ X0) (hx1 : |x1 - v1| ≤ e1) (hv1 : |v1| ≤ X1)
    (hx2 : |x2 - v2| ≤ e2) (hv2 : |v2| ≤ X2) (hx3 : |x3 - v3| ≤ e3) (hv3 : |v3| ≤ X3)
    (hx4 : |x4 - v4| ≤ e4) (hv4 : |v4| ≤ X4) :
    CloseL [x0, x1, x2, x3, x4] [v0, v1, v2, v3, v4] [e0, e1, e2, e3, e4] [X0, X1, X2, X3, X4] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk5 : k < 5 := by simpa using hk
  interval_cases k
  · first | exact ⟨hx0, hv0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx0, hv0⟩)
  · first | exact ⟨hx1, hv1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx1, hv1⟩)
  · first | exact ⟨hx2, hv2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx2, hv2⟩)
  · first | exact ⟨hx3, hv3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx3, hv3⟩)
  · first | exact ⟨hx4, hv4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx4, hv4⟩)

theorem bnd5 {x0 x1 x2 x3 x4 e e0 e1 e2 e3 e4 X X0 X1 X2 X3 X4 : ℝ}
    (h0 : e0 ≤ e) (h1 : e1 ≤ e) (h2 : e2 ≤ e) (h3 : e3 ≤ e) (h4 : e4 ≤ e)
    (g0 : X0 ≤ X) (g1 : X1 ≤ X) (g2 : X2 ≤ X) (g3 : X3 ≤ X) (g4 : X4 ≤ X) :
    ∀ k, k < ([x0, x1, x2, x3, x4] : List ℝ).length →
      ([e0, e1, e2, e3, e4] : List ℝ).getD k 0 ≤ e ∧ ([X0, X1, X2, X3, X4] : List ℝ).getD k 0 ≤ X := by
  intro k hk
  have hk5 : k < 5 := by simpa using hk
  interval_cases k
  · first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)
  · first | exact ⟨h1, g1⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h1, g1⟩)
  · first | exact ⟨h2, g2⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h2, g2⟩)
  · first | exact ⟨h3, g3⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h3, g3⟩)
  · first | exact ⟨h4, g4⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h4, g4⟩)

theorem closeL1 {x0 v0 e0 X0 : ℝ} (hx0 : |x0 - v0| ≤ e0) (hv0 : |v0| ≤ X0) :
    CloseL [x0] [v0] [e0] [X0] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro k hk
  have hk1 : k < 1 := by simpa using hk
  interval_cases k
  first | exact ⟨hx0, hv0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨hx0, hv0⟩)

theorem bnd1 {x0 e e0 X X0 : ℝ} (h0 : e0 ≤ e) (g0 : X0 ≤ X) :
    ∀ k, k < ([x0] : List ℝ).length →
      ([e0] : List ℝ).getD k 0 ≤ e ∧ ([X0] : List ℝ).getD k 0 ≤ X := by
  intro k hk
  have hk1 : k < 1 := by simpa using hk
  interval_cases k
  first | exact ⟨h0, g0⟩ | (simp only [List.getD_cons_zero, List.getD_cons_succ]; exact ⟨h0, g0⟩)

theorem forall_mem5 {α : Type} {P : α → Prop} {a0 a1 a2 a3 a4 : α}
    (h0 : P a0) (h1 : P a1) (h2 : P a2) (h3 : P a3) (h4 : P a4) :
    ∀ a ∈ ([a0, a1, a2, a3, a4] : List α), P a := by
  intro a ha
  rcases List.mem_cons.mp ha with h | ha
  · rw [h]; exact h0
  rcases List.mem_cons.mp ha with h | ha
  · rw [h]; exact h1
  rcases List.mem_cons.mp ha with h | ha
  · rw [h]; exact h2
  rcases List.mem_cons.mp ha with h | ha
  · rw [h]; exact h3
  rcases List.mem_cons.mp ha with h | ha
  · rw [h]; exact h4
  simp at ha

theorem forall_mem1 {α : Type} {P : α → Prop} {a0 : α} (h0 : P a0) :
    ∀ a ∈ ([a0] : List α), P a := by
  intro a ha
  rw [List.mem_singleton] at ha
  rw [ha]; exact h0

theorem dotQ_cons (a : ℚ) (r : List ℚ) (v : ℝ) (x : List ℝ) :
    dotQ (a :: r) (v :: x) = (a : ℝ) * v + dotQ r x := by
  simp [dotQ]

theorem dotQ_nil : dotQ [] ([] : List ℝ) = 0 := by
  simp [dotQ]

theorem wErr_cons (δ : ℝ) (a : ℚ) (r : List ℚ) (e : ℝ) (es : List ℝ) (X : ℝ) (Xs : List ℝ) :
    wErr δ (a :: r) (e :: es) (X :: Xs) = |(a : ℝ)| * e + δ * (X + e) + wErr δ r es Xs := by
  first | rfl | simp [wErr]

theorem wErr_nil (δ : ℝ) : wErr δ [] [] [] = 0 := by
  first | rfl | simp [wErr]

/-- The per-coordinate dot-product bound, with plain numerals. -/
theorem arW {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) (hM : (2 : ℝ) ^ 30 ≤ M)
    (r : List ℚ) (x v es Xs : List ℝ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000)
    (W X e E q nR : ℝ) (hlen : r.length = x.length) (hl32 : r.length ≤ 32)
    (hC : CloseL x v es Xs)
    (hb : ∀ k, k < x.length → es.getD k 0 ≤ e ∧ Xs.getD k 0 ≤ X)
    (hWr : ∀ a ∈ r, |(a : ℝ)| ≤ W) (hW0 : 0 ≤ W) (hX0 : 0 ≤ X) (he0 : 0 ≤ e)
    (hT : (W + 1) * (X + e + 1) ≤ 1000000)
    (hE : wErr (1 / 1000) r es Xs ≤ E) (hq : dotQ r v = q) (hnR : (r.length : ℝ) = nR) :
    |ardot fl r x d 0 0 - q| ≤ E + nR * (W + 1) * (X + e + 1) / 65536 + 1 / 1000000 := by
  have hT' : (W + 1) * (X + e + 1) ≤ 2 ^ 20 := le_trans hT (by norm_num)
  have key := ardot_near_w u η M (1 / 1000) fl hr hu0 hu hη0 hη (by norm_num) (by norm_num)
    r x v es Xs d W X e hlen hl32 hC hb hd hWr hW0 hX0 he0 hT' hM
  obtain ⟨k1, -⟩ := key
  rw [hq, hnR] at k1
  have h16 : (2 : ℝ) ^ 16 = 65536 := by norm_num
  have h100 : (1 : ℝ) / 2 ^ 100 ≤ 1 / 1000000 := by norm_num
  rw [h16] at k1
  linarith

/-! ### The context: all hypotheses of `Statement`, bundled -/

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

/-- Rounding adds at most 1/50000 to an error, for arguments up to 100. -/
theorem fl_n (ev : Ctx u η M fl ex p w) {x t e : ℝ} (hx : |x - t| ≤ e) (hB : |x| ≤ 100) :
    |fl x - t| ≤ e + 1 / 50000 := by
  have hM : (100 : ℝ) ≤ M := ev.range 100 (by norm_num)
  have h := ev.hr.near ev.hu0 hx hB hM
  have hu : u * 100 ≤ 1 / 150000 := by
    have h1 := mul_le_mul_of_nonneg_right ev.hu1 (by norm_num : (0 : ℝ) ≤ 100)
    have h2 : (1 : ℝ) / 2 ^ 24 * 100 ≤ 1 / 150000 := by norm_num
    linarith
  have hη : η ≤ 1 / 150000 := by
    have h1 := eta_tiny ev.hη1
    have h2 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 150000 := by norm_num
    linarith
  linarith

theorem z_ok (ev : Ctx u η M fl ex p w) {y Y m Mm Yt ey em E : ℝ} (hy : |y - Y| ≤ ey)
    (hm : |m - Mm| ≤ em) (hs : Y + Mm = Yt) (hb : |Yt| ≤ 10) (hey : ey ≤ 1) (hem : em ≤ 1)
    (hE : ey + em + 1 / 50000 ≤ E) : |fl (y + m) - Yt| ≤ E := by
  subst hs
  have h1 : |y + m - (Y + Mm)| ≤ ey + em := by
    have := abs_add_le (y - Y) (m - Mm)
    have e : y - Y + (m - Mm) = y + m - (Y + Mm) := by ring
    rw [e] at this
    linarith
  have h2 : |y + m| ≤ 100 := by
    have h3 := abs_sub_abs_le_abs_sub (y + m) (Y + Mm)
    linarith
  have := fl_n ev h1 h2
  linarith

theorem asw_c (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 24) (hη : η ≤ 1 / 2 ^ 149)
    (hM : 4 ≤ M) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000) (ha : |(a : ℝ)| ≤ 3) :
    |asw fl a d - (a : ℝ)| ≤ 11 / 10000 := by
  have h := asw_near hr hu0 a hd (by linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 2 ^ 24 * 4 :=
    mul_le_mul hu (by linarith) (by positivity) (by positivity)
  have h2 := eta_tiny hη
  have h3 : (1 : ℝ) / 2 ^ 24 * 4 + 1 / 10 ^ 40 ≤ 1 / 10000 := by norm_num
  linarith

/-! ### Step 1: the starting state -/

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4] ∧
      |a0 - ((tcv (tokAt w j) : ℕ) : ℝ)| ≤ 11 / 10000 ∧
      |a1 - ((tpf (tokAt w j) : ℕ) : ℝ)| ≤ 11 / 10000 ∧
      |a2 - ((dg (tokAt w j) : ℕ) : ℝ)| ≤ 11 / 10000 ∧
      |a3 - 0| ≤ 11 / 10000 ∧ |a4 - 0| ≤ 11 / 10000 := by
  have ht := tok_le w ev.hw j
  have hM4 : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hc0 : (((tcv (tokAt w j) : ℕ) : ℚ) : ℝ) = ((tcv (tokAt w j) : ℕ) : ℝ) := by simp
  have hc1 : (((tpf (tokAt w j) : ℕ) : ℚ) : ℝ) = ((tpf (tokAt w j) : ℕ) : ℝ) := by simp
  have hc2 : (((dg (tokAt w j) : ℕ) : ℚ) : ℝ) = ((dg (tokAt w j) : ℕ) : ℝ) := by simp
  obtain ⟨t01, t02⟩ := tcv_r (tokAt w j)
  obtain ⟨t11, t12⟩ := tpf_r (tokAt w j)
  obtain ⟨t21, t22⟩ := dg_r (tokAt w j)
  refine ⟨_, _, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_, ?_⟩
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 ((tcv (tokAt w j) : ℕ) : ℚ)
      (ev.hp.E (tokAt w j) 0) (by rw [hc0, abs_of_nonneg t01]; linarith)
    rw [hc0] at h
    exact h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 ((tpf (tokAt w j) : ℕ) : ℚ)
      (ev.hp.E (tokAt w j) 1) (by rw [hc1, abs_of_nonneg t11]; linarith)
    rw [hc1] at h
    exact h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 ((dg (tokAt w j) : ℕ) : ℚ)
      (ev.hp.E (tokAt w j) 2) (by rw [hc2, abs_of_nonneg t21]; linarith)
    rw [hc2] at h
    exact h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (0 : ℚ) (ev.hp.E (tokAt w j) 3) (by simp)
    simpa using h
  · have h := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 hM4 (0 : ℚ) (ev.hp.E (tokAt w j) 4) (by simp)
    simpa using h

/-- A stored-weight dot product of a row of absolute sum at most 1 with the starting state. -/
theorem init_dot (ev : Ctx u η M fl ex p w) (a0 a1 a2 a3 a4 : ℚ)
    (hS : |(a0 : ℝ)| + |(a1 : ℝ)| + |(a2 : ℝ)| + |(a3 : ℝ)| + |(a4 : ℝ)| ≤ 1)
    (j : ℕ) (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) :
    |ardot fl [a0, a1, a2, a3, a4] (net.init fl p w j) d 0 0 -
        dotQ [a0, a1, a2, a3, a4] (xhat w j)| ≤ 6 / 1000 := by
  obtain ⟨x0, x1, x2, x3, x4, hx, b0, b1, b2, b3, b4⟩ := init_ent ev j
  rw [hx]
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have n0 := abs_nonneg (a0 : ℝ)
  have n1 := abs_nonneg (a1 : ℝ)
  have n2 := abs_nonneg (a2 : ℝ)
  have n3 := abs_nonneg (a3 : ℝ)
  have n4 := abs_nonneg (a4 : ℝ)
  have tc := tcv_r (tokAt w j)
  have tp := tpf_r (tokAt w j)
  have td := dg_r (tokAt w j)
  have key := arW ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 [a0, a1, a2, a3, a4]
    [x0, x1, x2, x3, x4]
    [((tcv (tokAt w j) : ℕ) : ℝ), ((tpf (tokAt w j) : ℕ) : ℝ), ((dg (tokAt w j) : ℕ) : ℝ), 0, 0]
    [11 / 10000, 11 / 10000, 11 / 10000, 11 / 10000, 11 / 10000] [1, 1, 2, 0, 0] d hd
    1 2 (11 / 10000) (52 / 10000) (dotQ [a0, a1, a2, a3, a4] (xhat w j)) 5 rfl (by simp)
    (closeL5 b0 (by rw [abs_of_nonneg tc.1]; exact tc.2) b1
      (by rw [abs_of_nonneg tp.1]; exact tp.2) b2 (by rw [abs_of_nonneg td.1]; exact td.2)
      b3 (by norm_num) b4 (by norm_num))
    (bnd5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (forall_mem5 (P := fun a : ℚ => |(a : ℝ)| ≤ 1) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_nil]
      linarith)
    rfl (by norm_num)
  have := le_trans key (by norm_num : _ ≤ (6 / 1000 : ℝ))
  exact this

/-! ### Step 2: the gate -/

theorem gate_pre (ev : Ctx u η M fl ex p w) (j : ℕ) :
    |ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) (p.g 0 0) 0 0 + asw fl (-1 / 2) (p.gb 0 0)
      - (((tpf (tokAt w j) : ℕ) : ℝ) - 1 / 2)| ≤ 8 / 1000 := by
  have h1 := init_dot ev 0 1 0 0 0 (by norm_num) j (p.g 0 0) (ev.hp.g 0 0)
  rw [dqg] at h1
  have e : (((-1 / 2 : ℚ)) : ℝ) = -1 / 2 := by norm_num
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (-1 / 2) (ev.hp.gb 0 0)
    (by rw [e, abs_le]; constructor <;> norm_num)
  rw [e] at hb
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨hba, hbb⟩ := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

theorem gate_zero (ev : Ctx u η M fl ex p w) (j : ℕ) (h : tpf (tokAt w j) = 0) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) = 0 := by
  have hp := gate_pre ev j
  have hpf : ((tpf (tokAt w j) : ℕ) : ℝ) = 0 := by rw [h]; simp
  rw [hpf] at hp
  have hM : (1 : ℝ) ≤ M := ev.range 1 (by norm_num)
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  show Lane4.relu (fl (ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) (p.g 0 0) 0 0
    + asw fl (-1 / 2) (p.gb 0 0))) = 0
  exact relu_fl_zero ev.hr (by linarith) (by linarith)

theorem gate_pos (ev : Ctx u η M fl ex p w) (j : ℕ) (h : tpf (tokAt w j) = 1) :
    head1.gate fl (p.g 0 0) (p.gb 0 0) (net.init fl p w j) ≠ 0 := by
  have hp := gate_pre ev j
  have hpf : ((tpf (tokAt w j) : ℕ) : ℝ) = 1 := by rw [h]; simp
  rw [hpf] at hp
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  have hM : (4 : ℝ) ≤ M := ev.range 4 (by norm_num)
  have hB : |ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) (p.g 0 0) 0 0
      + asw fl (-1 / 2) (p.gb 0 0)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hl := ev.hr.lower ev.hu0 hB (by linarith : (2 : ℝ) ≤ M)
  have hu : u * 2 ≤ 1 / 1000 := by
    have h1 := mul_le_mul_of_nonneg_right ev.hu1 (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : (1 : ℝ) / 2 ^ 24 * 2 ≤ 1 / 1000 := by norm_num
    linarith
  have hη' := eta_tiny ev.hη1
  have h40 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
  have hpos : 0 < fl (ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) (p.g 0 0) 0 0
      + asw fl (-1 / 2) (p.gb 0 0)) := by linarith
  show Lane4.relu (fl (ardot fl [0, 1, 0, 0, 0] (net.init fl p w j) (p.g 0 0) 0 0
    + asw fl (-1 / 2) (p.gb 0 0))) ≠ 0
  unfold Lane4.relu
  exact (lt_max_of_lt_left hpos).ne'

theorem mem_cs (ev : Ctx u η M fl ex p w) (i j : ℕ) :
    j ∈ cs fl p w i ↔ j < i ∧ tokAt w j ≠ 3 := by
  unfold cs
  rw [AHead.mem_cands]
  have hm : head1.mask = Mask.strict := rfl
  rw [hm, Lane4.Seq.mem_cand_strict]
  constructor
  · rintro ⟨hj, hg⟩
    refine ⟨hj, fun h3 => ?_⟩
    exact gate_pos ev j (tpf_one h3) hg
  · rintro ⟨hj, hne⟩
    exact ⟨hj, gate_zero ev j (tpf_zero hne)⟩

theorem cs_nodup (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) : (cs fl p w i).Nodup :=
  AHead.cands_nodup head1 fl (p.g 0 0) (p.gb 0 0) (w.length + 1) (net.init fl p w) i

theorem cs_len (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (i : ℕ) (hi : i ≤ w.length) :
    (cs fl p w i).length ≤ w.length + 1 := by
  have h1 : (cs fl p w i).length ≤ (cand Mask.strict (w.length + 1) i).length :=
    List.length_filter_le _ _
  have h2 : (cand Mask.strict (w.length + 1) i).length = i := by simp [cand]
  omega

/-! ### Step 3: scores -/

theorem content_small (ev : Ctx u η M fl ex p w) (i k : ℕ) :
    |Lane4.RSeq.pdot fl (net.init fl p w i)
        (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) 0| ≤ 1 / 10 := by
  have hrow : ∀ r : ℕ,
      |ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 r) 0 0 - 0| ≤ 6 / 1000 := by
    intro r
    have h := init_dot ev 0 0 0 0 0 (by norm_num) k (p.A 0 0 r) (ev.hp.A 0 0 r)
    rw [dq0] at h
    exact h
  have hy : armat fl head1.A (net.init fl p w k) (p.A 0 0) 0 =
      [ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 0) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 1) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 2) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 3) 0 0,
       ardot fl [0, 0, 0, 0, 0] (net.init fl p w k) (p.A 0 0 4) 0 0] := rfl
  obtain ⟨x0, x1, x2, x3, x4, hx, b0, b1, b2, b3, b4⟩ := init_ent ev i
  have hCi : Close (net.init fl p w i) (xhat w i) (11 / 10000) 2 := by
    rw [hx]
    have t1 := tcv_r (tokAt w i)
    have t2 := tpf_r (tokAt w i)
    have t3 := dg_r (tokAt w i)
    unfold xhat
    refine close5 b0 b1 b2 b3 b4 ?_ ?_ ?_ ?_ ?_
    · rw [abs_of_nonneg t1.1]; linarith [t1.2]
    · rw [abs_of_nonneg t2.1]; linarith [t2.2]
    · rw [abs_of_nonneg t3.1]; exact t3.2
    · norm_num
    · norm_num
  have hlenx : (net.init fl p w i).length = 5 := by rw [hx]; rfl
  have hCy : Close (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0, 0]
      (6 / 1000) 0 := by
    rw [hy]
    exact close5 (hrow 0) (hrow 1) (hrow 2) (hrow 3) (hrow 4) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hleny : (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0).length = 5 := by
    rw [hy]; rfl
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  obtain ⟨p1, -⟩ := pdot_near u η M fl ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 (net.init fl p w i)
    (xhat w i) (armat fl head1.A (net.init fl p w k) (p.A 0 0) 0) [0, 0, 0, 0, 0] 2 0
    (11 / 10000) (6 / 1000) (by rw [hlenx, hleny]) (by rw [hlenx]; norm_num) hCi hCy
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM30
  have hdR : dotR (xhat w i) [0, 0, 0, 0, 0] = 0 := by simp [dotR, xhat]
  rw [hdR, sub_zero, hlenx] at p1
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
  generalize asw fl head1.m (p.m 0 0) = S at hS2 ⊢
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

/-! ### Step 4: the head returns the value of the nearest non-propagate key -/

theorem row_attn (ev : Ctx u η M fl ex p w) (a0 a1 a2 a3 a4 : ℚ)
    (hS : |(a0 : ℝ)| + |(a1 : ℝ)| + |(a2 : ℝ)| + |(a3 : ℝ)| + |(a4 : ℝ)| ≤ 1)
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1)
    (hq : ∀ j, |dotQ [a0, a1, a2, a3, a4] (xhat w j)| ≤ Q) (k : ℕ)
    (i J : ℕ) (hi : i ≤ w.length) (hJi : J < i) (hJ3 : tokAt w J ≠ 3)
    (hJbet : ∀ j, J < j → j < i → tokAt w j = 3) :
    |att fl ex p w i [a0, a1, a2, a3, a4] k - dotQ [a0, a1, a2, a3, a4] (xhat w J)|
      ≤ 61 / 10000 + Q / 100 := by
  have hj : J ∈ cs fl p w i := (mem_cs ev i J).mpr ⟨hJi, hJ3⟩
  have hlen := cs_len fl p w i hi
  have hgap : ∀ k' ∈ cs fl p w i, k' ≠ J →
      sc fl p w i k' ≤ sc fl p w i J - 16 * ((ndist J k' : ℕ) : ℝ) := by
    intro k' hk' hne
    obtain ⟨hk'i, hk'3⟩ := (mem_cs ev i k').mp hk'
    have hlt : k' < J := by
      by_contra hcon
      have hJk : J < k' := by omega
      exact hk'3 (hJbet k' hJk hk'i)
    rw [ndist_cast]
    have hg := score_gap ev i J k' (by omega) (by omega) hlt
    have h1 : (k' : ℝ) + 1 ≤ (J : ℝ) := by
      have h : k' + 1 ≤ J := hlt
      exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact hg
  have hS' : ∀ k' ∈ cs fl p w i, |sc fl p w i k'| ≤ 28 * ((w.length + 1 : ℕ) : ℝ) := by
    intro k' hk'
    obtain ⟨hk'i, -⟩ := (mem_cs ev i k').mp hk'
    exact score_abs ev i k' (by omega) (by omega)
  have hSM : 2 * (28 * ((w.length + 1 : ℕ) : ℝ)) ≤ M := by
    have := ev.rangeN 56 (by norm_num) (by norm_num)
    linarith
  have hf : ∀ k' ∈ cs fl p w i,
      |ardot fl [a0, a1, a2, a3, a4] (net.init fl p w k') (p.V 0 0 k) 0 0| ≤ Q + 6 / 1000 := by
    intro k' _
    have h1 := init_dot ev a0 a1 a2 a3 a4 hS k' (p.V 0 0 k) (ev.hp.V 0 0 k)
    have h2 := hq k'
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rw [abs_le]; constructor <;> linarith
  have hBM : 4 * (Q + 6 / 1000) + 4 ≤ M := by
    have := ev.range 13 (by norm_num)
    linarith
  obtain ⟨hs1, -⟩ := soft_near (s := sc fl p w i)
    (f := fun j => ardot fl [a0, a1, a2, a3, a4] (net.init fl p w j) (p.V 0 0 k) 0 0)
    ev.hr ev.he ev.hu0 ev.hu1 ev.hη0 ev.hη1 (cs_nodup fl p w i) hlen ev.hn ev.hnη hj hgap hS'
    hSM hf hBM
  have hs1' : |att fl ex p w i [a0, a1, a2, a3, a4] k -
      ardot fl [a0, a1, a2, a3, a4] (net.init fl p w J) (p.V 0 0 k) 0 0|
      ≤ (Q + 6 / 1000) / 100 + 1 / 2 ^ 90 := hs1
  have hv := init_dot ev a0 a1 a2 a3 a4 hS J (p.V 0 0 k) (ev.hp.V 0 0 k)
  have h90 : (1 : ℝ) / 2 ^ 90 ≤ 1 / 1000000 := by norm_num
  have h3 := abs_sub_le (att fl ex p w i [a0, a1, a2, a3, a4] k)
    (ardot fl [a0, a1, a2, a3, a4] (net.init fl p w J) (p.V 0 0 k) 0 0)
    (dotQ [a0, a1, a2, a3, a4] (xhat w J))
  linarith

/-! ### Step 5: ReLU algebra -/

theorem relu_lip (a b : ℝ) : |Lane4.relu a - Lane4.relu b| ≤ |a - b| := by
  unfold Lane4.relu
  first
  | exact abs_max_sub_max_le_abs a b 0
  | (have h1 := le_abs_self (a - b)
     have h2 := neg_abs_le (a - b)
     have h3 := neg_le_abs (a - b)
     have h4 := abs_nonneg (a - b)
     rw [abs_le]
     constructor <;>
       (rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
         simp only [max_eq_left, max_eq_right, ha, hb] <;> linarith))

theorem relu_nat (s : ℕ) : Lane4.relu ((s : ℝ) - 2) = ((s - 2 : ℕ) : ℝ) := by
  unfold Lane4.relu
  rcases Nat.lt_or_ge s 2 with h | h
  · have h1 : s - 2 = 0 := by omega
    have h2 : (s : ℝ) ≤ 2 := by exact_mod_cast h.le
    rw [h1, max_eq_right (by linarith)]
    simp
  · have h3 : (2 : ℝ) ≤ s := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_left (by linarith)]
    norm_num

theorem nat_key (a c : ℕ) (ha : a ≤ 2) (hc : c ≤ 1) :
    (a + c) % 3 + 3 * (a + c - 2) = a + c := by omega

theorem ideal_eq (t c : ℕ) (hc : c ≤ 1) :
    (((dg t + c) % 3 : ℕ) : ℝ) =
      (dg t : ℝ) + (c : ℝ) - 3 * Lane4.relu ((dg t : ℝ) + (c : ℝ) - 2) := by
  have key := nat_key (dg t) c (dg_le t) hc
  have e : ((dg t : ℝ) + (c : ℝ) - 2) = (((dg t + c : ℕ)) : ℝ) - 2 := by push_cast; ring
  rw [e, relu_nat]
  have k2 : (((dg t + c) % 3 : ℕ) : ℝ) + 3 * (((dg t + c - 2 : ℕ)) : ℝ)
      = (dg t : ℝ) + (c : ℝ) := by
    first
    | exact_mod_cast key
    | (have h := congrArg (Nat.cast : ℕ → ℝ) key
       push_cast at h
       linarith)
  linarith

/-! ### Step 6: the hidden neuron, the MLP rows, the read-out -/

theorem hid_bound (ev : Ctx u η M fl ex p w) {y0 y1 y2 y3 y4 Y0 Y1 D C : ℝ}
    (h0 : |y0 - Y0| ≤ 73 / 10000) (h1 : |y1 - Y1| ≤ 73 / 10000) (h2 : |y2 - D| ≤ 73 / 10000)
    (h3 : |y3 - C| ≤ 174 / 10000) (h4 : |y4 - 0| ≤ 73 / 10000)
    (hY0 : |Y0| ≤ 1) (hY1 : |Y1| ≤ 1) (hD : |D| ≤ 2) (hC : |C| ≤ 1) :
    |fl (ardot fl [0, 0, 1, 1, 0] [y0, y1, y2, y3, y4] (p.W1 0 0) 0 0 + asw fl (-2) (p.b1 0 0))
      - (D + C - 2)| ≤ 32 / 1000 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := arW ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 [0, 0, 1, 1, 0] [y0, y1, y2, y3, y4]
    [Y0, Y1, D, C, 0] [73 / 10000, 73 / 10000, 73 / 10000, 174 / 10000, 73 / 10000]
    [1, 1, 2, 1, 0] (p.W1 0 0) (ev.hp.W1 0 0) 1 2 (174 / 10000) (298 / 10000) (D + C) 5
    rfl (by simp)
    (closeL5 h0 hY0 h1 hY1 h2 hD h3 hC h4 (by norm_num))
    (bnd5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (forall_mem5 (P := fun a : ℚ => |(a : ℝ)| ≤ 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_nil]
      norm_num)
    (by
      first
      | (simp [dotQ_cons, dotQ_nil]; done)
      | (simp [dotQ_cons, dotQ_nil]; ring)
      | (norm_num [dotQ_cons, dotQ_nil]; ring))
    (by norm_num)
  obtain ⟨k1, k2⟩ := abs_le.mp (le_trans key (by norm_num : _ ≤ (3027 / 100000 : ℝ)))
  have e2 : (((-2 : ℚ)) : ℝ) = -2 := by norm_num
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (-2 : ℚ) (ev.hp.b1 0 0)
    (by rw [e2, abs_le]; constructor <;> norm_num)
  rw [e2] at hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨hDa, hDb⟩ := abs_le.mp hD
  obtain ⟨hCa, hCb⟩ := abs_le.mp hC
  have h5 : |ardot fl [0, 0, 1, 1, 0] [y0, y1, y2, y3, y4] (p.W1 0 0) 0 0
      + asw fl (-2) (p.b1 0 0) - (D + C - 2)| ≤ 3137 / 100000 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  have h6 : |ardot fl [0, 0, 1, 1, 0] [y0, y1, y2, y3, y4] (p.W1 0 0) 0 0
      + asw fl (-2) (p.b1 0 0)| ≤ 100 := by
    rw [abs_le]; constructor <;> linarith
  have h7 := fl_n ev h5 h6
  linarith

theorem mo_zero (ev : Ctx u η M fl ex p w) {h H : ℝ} (hh : |h - H| ≤ 32 / 1000) (hH : |H| ≤ 1)
    (k : ℕ) : |mo fl p h k 0 - 0| ≤ 23 / 10000 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := arW ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 [0] [h] [H] [32 / 1000] [1] (p.W2 0 k)
    (ev.hp.W2 0 k) 0 1 (32 / 1000) (11 / 10000) 0 1 rfl (by simp) (closeL1 hh hH)
    (bnd1 (by norm_num) (by norm_num))
    (forall_mem1 (P := fun a : ℚ => |(a : ℝ)| ≤ 0) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [wErr_cons, wErr_nil]
      norm_num)
    (by
      first
      | (simp [dotQ_cons, dotQ_nil]; done)
      | (simp [dotQ_cons, dotQ_nil]; ring)
      | (norm_num [dotQ_cons, dotQ_nil]; ring))
    (by norm_num)
  obtain ⟨k1, k2⟩ := abs_le.mp (le_trans key (by norm_num : _ ≤ (114 / 100000 : ℝ)))
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) (ev.hp.b2 0 k)
    (by norm_num)
  have hb' : |asw fl 0 (p.b2 0 k)| ≤ 11 / 10000 := by simpa using hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb'
  have h5 : |ardot fl [0] [h] (p.W2 0 k) 0 0 + asw fl 0 (p.b2 0 k) - 0| ≤ 225 / 100000 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  have h6 : |ardot fl [0] [h] (p.W2 0 k) 0 0 + asw fl 0 (p.b2 0 k)| ≤ 100 := by
    rw [abs_le]; constructor <;> linarith
  have h7 := fl_n ev h5 h6
  unfold mo
  linarith

theorem mo_neg3 (ev : Ctx u η M fl ex p w) {h H : ℝ} (hh : |h - H| ≤ 32 / 1000) (hH : |H| ≤ 1)
    (k : ℕ) : |mo fl p h k (-3) - (-3 * H)| ≤ 994 / 10000 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := arW ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 [-3] [h] [H] [32 / 1000] [1] (p.W2 0 k)
    (ev.hp.W2 0 k) 3 1 (32 / 1000) (98 / 1000) (-3 * H) 1 rfl (by simp) (closeL1 hh hH)
    (bnd1 (by norm_num) (by norm_num))
    (forall_mem1 (P := fun a : ℚ => |(a : ℝ)| ≤ 3) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [wErr_cons, wErr_nil]
      norm_num)
    (by
      first
      | (simp [dotQ_cons, dotQ_nil]; done)
      | (simp [dotQ_cons, dotQ_nil]; ring)
      | (norm_num [dotQ_cons, dotQ_nil]; ring))
    (by norm_num)
  obtain ⟨k1, k2⟩ := abs_le.mp (le_trans key (by norm_num : _ ≤ (9815 / 100000 : ℝ)))
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) (ev.hp.b2 0 k)
    (by norm_num)
  have hb' : |asw fl 0 (p.b2 0 k)| ≤ 11 / 10000 := by simpa using hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb'
  obtain ⟨hHa, hHb⟩ := abs_le.mp hH
  have h5 : |ardot fl [-3] [h] (p.W2 0 k) 0 0 + asw fl 0 (p.b2 0 k) - (-3 * H)| ≤ 9925 / 100000 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  have h6 : |ardot fl [-3] [h] (p.W2 0 k) 0 0 + asw fl 0 (p.b2 0 k)| ≤ 100 := by
    rw [abs_le]; constructor <;> linarith
  have h7 := fl_n ev h5 h6
  unfold mo
  linarith

theorem read_ok (ev : Ctx u η M fl ex p w) {z0 z1 z2 z3 z4 Y0 Y1 D C H T : ℝ}
    (h0 : |z0 - Y0| ≤ 97 / 10000) (h1 : |z1 - Y1| ≤ 97 / 10000) (h2 : |z2 - D| ≤ 97 / 10000)
    (h3 : |z3 - C| ≤ 198 / 10000) (h4 : |z4 - (-3 * H)| ≤ 1068 / 10000)
    (hY0 : 0 ≤ Y0) (hY0' : Y0 ≤ 1) (hY1 : 0 ≤ Y1) (hY1' : Y1 ≤ 1) (hD0 : 0 ≤ D) (hD1 : D ≤ 2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hH0 : 0 ≤ H) (hH1 : H ≤ 1) (hT : T = D + C - 3 * H)
    (d : ℕ → ℝ) (hd : ∀ k, |d k| ≤ 1 / 1000) (db : ℝ) (hdb : |db| ≤ 1 / 1000) :
    |fl (ardot fl [0, 0, 1, 1, 1] [z0, z1, z2, z3, z4] d 0 0 + asw fl 0 db) - T| ≤ 1 / 4 := by
  have hM30 : (2 : ℝ) ^ 30 ≤ M := ev.range _ (by norm_num)
  have key := arW ev.hr ev.hu0 ev.hu1 ev.hη0 ev.hη1 hM30 [0, 0, 1, 1, 1] [z0, z1, z2, z3, z4]
    [Y0, Y1, D, C, -3 * H] [97 / 10000, 97 / 10000, 97 / 10000, 198 / 10000, 1068 / 10000]
    [1, 1, 2, 1, 3] d hd 1 3 (1068 / 10000) (1450 / 10000) (D + C + -3 * H) 5 rfl (by simp)
    (closeL5 h0 (by rw [abs_of_nonneg hY0]; exact hY0') h1
      (by rw [abs_of_nonneg hY1]; exact hY1') h2 (by rw [abs_of_nonneg hD0]; exact hD1)
      h3 (by rw [abs_of_nonneg hC0]; exact hC1) h4
      (by rw [abs_le]; constructor <;> linarith))
    (bnd5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (forall_mem5 (P := fun a : ℚ => |(a : ℝ)| ≤ 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_cons, wErr_nil]
      norm_num)
    (by
      first
      | (simp [dotQ_cons, dotQ_nil]; done)
      | (simp [dotQ_cons, dotQ_nil]; ring)
      | (norm_num [dotQ_cons, dotQ_nil]; ring))
    (by norm_num)
  obtain ⟨k1, k2⟩ := abs_le.mp (le_trans key (by norm_num : _ ≤ (1457 / 10000 : ℝ)))
  have hb := asw_c ev.hr ev.hu0 ev.hu1 ev.hη1 (ev.range 4 (by norm_num)) (0 : ℚ) hdb (by norm_num)
  have hb' : |asw fl 0 db| ≤ 11 / 10000 := by simpa using hb
  obtain ⟨b1, b2⟩ := abs_le.mp hb'
  have h5 : |ardot fl [0, 0, 1, 1, 1] [z0, z1, z2, z3, z4] d 0 0 + asw fl 0 db - T|
      ≤ 1470 / 10000 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h5a, h5b⟩ := abs_le.mp h5
  have h6 : |ardot fl [0, 0, 1, 1, 1] [z0, z1, z2, z3, z4] d 0 0 + asw fl 0 db| ≤ 100 := by
    rw [abs_le]; constructor <;> linarith
  have h7 := fl_n ev h5 h6
  linarith

theorem stage_all (ev : Ctx u η M fl ex p w) {y0 y1 y2 y3 y4 Y0 Y1 D C T : ℝ}
    (h0 : |y0 - Y0| ≤ 73 / 10000) (h1 : |y1 - Y1| ≤ 73 / 10000) (h2 : |y2 - D| ≤ 73 / 10000)
    (h3 : |y3 - C| ≤ 174 / 10000) (h4 : |y4 - 0| ≤ 73 / 10000)
    (hY0 : 0 ≤ Y0) (hY0' : Y0 ≤ 1) (hY1 : 0 ≤ Y1) (hY1' : Y1 ≤ 1) (hD0 : 0 ≤ D) (hD1 : D ≤ 2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hT : T = D + C - 3 * Lane4.relu (D + C - 2)) :
    |fl (ardot fl [0, 0, 1, 1, 1] (Zv fl p [y0, y1, y2, y3, y4]) p.oW 0 0 + asw fl 0 p.oB) - T|
      ≤ 1 / 4 := by
  obtain ⟨H, hH⟩ : ∃ H, H = Lane4.relu (D + C - 2) := ⟨_, rfl⟩
  rw [← hH] at hT
  have hH0 : 0 ≤ H := by rw [hH]; unfold Lane4.relu; exact le_max_right _ _
  have hH1 : H ≤ 1 := by
    rw [hH]; unfold Lane4.relu; exact max_le (by linarith) (by norm_num)
  have hHabs : |H| ≤ 1 := by rw [abs_of_nonneg hH0]; exact hH1
  have aY0 : |Y0| ≤ 1 := by rw [abs_of_nonneg hY0]; exact hY0'
  have aY1 : |Y1| ≤ 1 := by rw [abs_of_nonneg hY1]; exact hY1'
  have aD : |D| ≤ 2 := by rw [abs_of_nonneg hD0]; exact hD1
  have aC : |C| ≤ 1 := by rw [abs_of_nonneg hC0]; exact hC1
  have hb := hid_bound ev h0 h1 h2 h3 h4 aY0 aY1 aD aC
  have hhid : |hid fl p [y0, y1, y2, y3, y4] - H| ≤ 32 / 1000 := by
    rw [hH]; unfold hid; exact le_trans (relu_lip _ _) hb
  have m0 := mo_zero ev hhid hHabs 0
  have m1 := mo_zero ev hhid hHabs 1
  have m2 := mo_zero ev hhid hHabs 2
  have m3 := mo_zero ev hhid hHabs 3
  have m4 := mo_neg3 ev hhid hHabs 4
  have z0 := z_ok ev h0 m0 (add_zero Y0) (by rw [abs_of_nonneg hY0]; linarith) (by norm_num)
    (by norm_num) (E := 97 / 10000) (by norm_num)
  have z1 := z_ok ev h1 m1 (add_zero Y1) (by rw [abs_of_nonneg hY1]; linarith) (by norm_num)
    (by norm_num) (E := 97 / 10000) (by norm_num)
  have z2 := z_ok ev h2 m2 (add_zero D) (by rw [abs_of_nonneg hD0]; linarith) (by norm_num)
    (by norm_num) (E := 97 / 10000) (by norm_num)
  have z3 := z_ok ev h3 m3 (add_zero C) (by rw [abs_of_nonneg hC0]; linarith) (by norm_num)
    (by norm_num) (E := 198 / 10000) (by norm_num)
  have z4 := z_ok ev h4 m4 (zero_add (-3 * H)) (by rw [abs_le]; constructor <;> linarith)
    (by norm_num) (by norm_num) (E := 1068 / 10000) (by norm_num)
  rw [Zv_eq]
  exact read_ok ev z0 z1 z2 z3 z4 hY0 hY0' hY1 hY1' hD0 hD1 hC0 hC1 hH0 hH1 hT p.oW
    (fun k => ev.hp.oW k) p.oB ev.hp.oB

/-! ### Step 7: the winner (nearest non-propagate key) and the carry -/

theorem tokAt_succ_getD (w : List ℕ) (k : ℕ) : tokAt w (k + 1) = w.getD k 0 := by
  first | rfl | simp [tokAt]

theorem tokAt_getD (w : List ℕ) (i : ℕ) (hi : 1 ≤ i) : tokAt w i = w.getD (i - 1) 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [tokAt_succ_getD]
  first | rfl | simp

theorem carry_step (p : List ℕ) (t : ℕ) :
    carry (p ++ [t]) = if cls t = 2 then carry p else cls t := by
  first
  | (unfold carry; rw [List.foldl_append]; rfl)
  | simp [carry, List.foldl_append]

theorem take_snoc_aux (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    w.take (k + 1) = w.take k ++ [w.getD k 0] := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a w ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h := ih k (by simpa using hk)
      simp [h]

theorem cls_tcv (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) (h3 : t ≠ 3) :
    cls t ≠ 2 ∧ cls t = tcv t := by
  interval_cases t <;> first | exact absurd rfl h3 | (constructor <;> decide)

theorem winner (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) :
    ∀ k : ℕ, k ≤ w.length → ∃ J : ℕ, J < k + 1 ∧ tokAt w J ≠ 3 ∧
      (∀ j, J < j → j < k + 1 → tokAt w j = 3) ∧ carry (w.take k) = tcv (tokAt w J) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, by omega, ?_, ?_, ?_⟩
    · rw [Lane4.Seq.tokAt_zero]; norm_num
    · intro j h1 h2; exfalso; omega
    · simp [carry, Lane4.Seq.tokAt_zero, tcv]
  | succ k ih =>
    intro hk
    have hk' : k < w.length := by omega
    obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := ih (by omega)
    have htok : tokAt w (k + 1) = w[k] := Lane4.Seq.tokAt_succ w k hk'
    have hmemt : tokAt w (k + 1) ∈ w := by rw [htok]; exact List.getElem_mem hk'
    obtain ⟨hlo, hhi⟩ := hw _ hmemt
    have hcar : carry (w.take (k + 1)) =
        if cls (tokAt w (k + 1)) = 2 then carry (w.take k) else cls (tokAt w (k + 1)) := by
      rw [take_snoc_aux w k hk', carry_step, tokAt_succ_getD]
    by_cases h3 : tokAt w (k + 1) = 3
    · have hc3 : cls (tokAt w (k + 1)) = 2 := by rw [h3]; decide
      refine ⟨J, by omega, hJ2, ?_, ?_⟩
      · intro j hj1 hj2
        by_cases hjk : j < k + 1
        · exact hJ3 j hj1 hjk
        · have hjj : j = k + 1 := by omega
          rw [hjj]; exact h3
      · rw [hcar, if_pos hc3]; exact hJ4
    · have hc := cls_tcv (tokAt w (k + 1)) hlo hhi h3
      refine ⟨k + 1, by omega, h3, ?_, ?_⟩
      · intro j hj1 hj2; exfalso; omega
      · rw [hcar, if_neg hc.1]; exact hc.2

/-! ### The theorem -/

theorem out_near (ev : Ctx u η M fl ex p w) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ w.length) :
    |net.out fl ex p w i - ((target w i : ℕ) : ℝ)| ≤ 1 / 4 := by
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := winner w ev.hw (i - 1) (by omega)
  have hJi : J < i := by omega
  have hJbet : ∀ j, J < j → j < i → tokAt w j = 3 := fun j h1 h2 => hJ3 j h1 (by omega)
  obtain ⟨a0, a1, a2, a3, a4, hx, ha0, ha1, ha2, ha3, ha4⟩ := init_ent ev i
  have hS0 : |((0 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)|
      + |((0 : ℚ) : ℝ)| ≤ 1 := by norm_num
  have hS1 : |((1 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)| + |((0 : ℚ) : ℝ)|
      + |((0 : ℚ) : ℝ)| ≤ 1 := by norm_num
  have tc := tcv_r (tokAt w i)
  have tp := tpf_r (tokAt w i)
  have td := dg_r (tokAt w i)
  have tcJ := tcv_r (tokAt w J)
  have hq0 : ∀ j, |dotQ [0, 0, 0, 0, 0] (xhat w j)| ≤ 0 := fun j => by rw [dq0]; simp
  have hq1 : ∀ j, |dotQ [1, 0, 0, 0, 0] (xhat w j)| ≤ 1 := fun j => by
    rw [dq1, abs_of_nonneg (tcv_r _).1]; exact (tcv_r _).2
  have r0 := row_attn ev 0 0 0 0 0 hS0 (Q := 0) le_rfl (by norm_num) hq0 0 i J hi hJi hJ2 hJbet
  have r1 := row_attn ev 0 0 0 0 0 hS0 (Q := 0) le_rfl (by norm_num) hq0 1 i J hi hJi hJ2 hJbet
  have r2 := row_attn ev 0 0 0 0 0 hS0 (Q := 0) le_rfl (by norm_num) hq0 2 i J hi hJi hJ2 hJbet
  have r4 := row_attn ev 0 0 0 0 0 hS0 (Q := 0) le_rfl (by norm_num) hq0 4 i J hi hJi hJ2 hJbet
  have r3 := row_attn ev 1 0 0 0 0 hS1 (Q := 1) (by norm_num) le_rfl hq1 3 i J hi hJi hJ2 hJbet
  rw [dq0] at r0 r1 r2 r4
  rw [dq1] at r3
  have y0 : |fl (a0 + att fl ex p w i [0, 0, 0, 0, 0] 0) - ((tcv (tokAt w i) : ℕ) : ℝ)|
      ≤ 73 / 10000 :=
    z_ok ev ha0 r0 (add_zero _) (by rw [abs_of_nonneg tc.1]; linarith [tc.2]) (by norm_num)
      (by norm_num) (by norm_num)
  have y1 : |fl (a1 + att fl ex p w i [0, 0, 0, 0, 0] 1) - ((tpf (tokAt w i) : ℕ) : ℝ)|
      ≤ 73 / 10000 :=
    z_ok ev ha1 r1 (add_zero _) (by rw [abs_of_nonneg tp.1]; linarith [tp.2]) (by norm_num)
      (by norm_num) (by norm_num)
  have y2 : |fl (a2 + att fl ex p w i [0, 0, 0, 0, 0] 2) - ((dg (tokAt w i) : ℕ) : ℝ)|
      ≤ 73 / 10000 :=
    z_ok ev ha2 r2 (add_zero _) (by rw [abs_of_nonneg td.1]; linarith [td.2]) (by norm_num)
      (by norm_num) (by norm_num)
  have y3 : |fl (a3 + att fl ex p w i [1, 0, 0, 0, 0] 3) - ((tcv (tokAt w J) : ℕ) : ℝ)|
      ≤ 174 / 10000 :=
    z_ok ev ha3 r3 (zero_add _) (by rw [abs_of_nonneg tcJ.1]; linarith [tcJ.2]) (by norm_num)
      (by norm_num) (by norm_num)
  have y4 : |fl (a4 + att fl ex p w i [0, 0, 0, 0, 0] 4) - 0| ≤ 73 / 10000 :=
    z_ok ev ha4 r4 (add_zero _) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hT : ((target w i : ℕ) : ℝ) = ((dg (tokAt w i) : ℕ) : ℝ) + ((tcv (tokAt w J) : ℕ) : ℝ) -
      3 * Lane4.relu (((dg (tokAt w i) : ℕ) : ℝ) + ((tcv (tokAt w J) : ℕ) : ℝ) - 2) := by
    have e : target w i = (dg (tokAt w i) + tcv (tokAt w J)) % 3 := by
      unfold target
      rw [← tokAt_getD w i hi1, hJ4]
    rw [e]
    exact ideal_eq _ _ (tcv_le _)
  rw [out_eq, Yv_eq fl ex p w i a0 a1 a2 a3 a4 hx]
  exact stage_all ev y0 y1 y2 y3 y4 tc.1 tc.2 tp.1 tp.2 td.1 td.2 tcJ.1 tcJ.2 hT

end Steps

theorem net_ok : Statement net := by
  intro u η M fl ex hr he hu0 hu1 hη0 hη1 p hp w hw hn hnη hM i hi1 hi
  have ctx : Ctx u η M fl ex p w := ⟨hr, he, hu0, hu1, hη0, hη1, hp, hw, hn, hnη, hM⟩
  exact out_near ctx i hi1 hi

end Lane4.Case
