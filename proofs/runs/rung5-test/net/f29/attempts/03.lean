set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z7, z7, z7, z7, [0, 0, 0, 0, 0, -20, 0], [0, 0, -40, 0, 0, 0, 0], z7],
    V := [z7, z7, z7, [1, 0, 0, 0, 0, 0, 0], z7, z7, z7],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [[0, 1, 0, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [0], [-2], [0], [0], [0]], b2 := z7 }

def net : TNet :=
  { embed := [[0, 0, 1, 0], [0, 0, 0, 0], [0, 1, 1, 0], [0, 0, 1, 0], [1, 0, 0, 0], [1, 0, 0, 0]],
    blocks := [blk],
    outW := [0, 1, 0, 1, 0, 0, 0],
    outB := 0 }

noncomputable def av (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 4 ∨ t = 5 then sw fl 1 (p.E t 0) else 0
noncomputable def cv (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 2 then sw fl 1 (p.E t 1) else 0
noncomputable def uv (fl : ℝ → ℝ) (p : Pert) (t : ℕ) : ℝ :=
  if t = 1 ∨ t = 4 ∨ t = 5 then 0 else sw fl 1 (p.E t 2)

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [av fl p (tokAt w j), cv fl p (tokAt w j), uv fl p (tokAt w j), 0]
      ++ pos fl j (w.length + 1) := by
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by
    have := tok_le w hw j
    omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, av, cv, uv, sw_zero hr]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g : ℝ) :
    rdot fl z7 [a, b, c, d, e, f, g] dV 0 0 = 0 := by
  simp [z7, rdot, sw_zero hr, hr.zero]

theorem val_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dV : ℕ → ℝ) (a b c d e f g : ℝ)
    (hI : fl (fl (sw fl 1 (dV 0) * a)) = fl (sw fl 1 (dV 0) * a)) :
    rdot fl [1, 0, 0, 0, 0, 0, 0] [a, b, c, d, e, f, g] dV 0 0 = fl (sw fl 1 (dV 0) * a) := by
  simp [rdot, sw_zero hr, hr.zero, hI]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a b c d f g ak bk uk dk fk gk : ℝ)
    (hI1 : fl (fl (sw fl (-20) (dA 4 5) * fk)) = fl (sw fl (-20) (dA 4 5) * fk))
    (hI2 : fl (fl (sw fl (-40) (dA 5 2) * uk)) = fl (sw fl (-40) (dA 5 2) * uk))
    (hI3 : fl (fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl (-40) (dA 5 2) * uk))))
      = fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl (-40) (dA 5 2) * uk)))) :
    hd.score fl dA [a, b, c, d, 1, f, g] [ak, bk, uk, dk, 1, fk, gk]
      = fl (fl (sw fl (-20) (dA 4 5) * fk) + fl (f * fl (sw fl (-40) (dA 5 2) * uk))) := by
  simp [Head.score, hd, z7, pdot, rmat, rdot, sw_zero hr, hr.zero, hI1, hI2, hI3]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [1, 0, 0, 0, 0, 0, 0] (net.init fl p w j) (p.V 0 0 3) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z7, z7, z7, [1, 0, 0, 0, 0, 0, 0], z7, z7, z7] := rfl
  have hm : hd.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z7 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) (A : ℝ)
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, 0, A, 0, 0, 0])
    (hA : fl A = A)
    (hfa : fl (av fl p (tokAt w i)) = av fl p (tokAt w i))
    (hfc : fl (cv fl p (tokAt w i)) = cv fl p (tokAt w i))
    (hfu : fl (uv fl p (tokAt w i)) = uv fl p (tokAt w i))
    (hfi : fl (fl (i : ℝ)) = fl (i : ℝ))
    (hfn : fl (fl ((w.length + 1 : ℕ) : ℝ)) = fl ((w.length + 1 : ℕ) : ℝ))
    (hfn' : fl (fl ((w.length : ℝ) + 1)) = fl ((w.length : ℝ) + 1))
    (hI1 : fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)))
      = fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)))
    (hI2 : fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)))
      = fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)))
    (hI3 : fl (fl (sw fl (-2) (p.W2 0 3 0) * Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)) + sw fl (-1) (p.b1 0 0)))))
      = fl (sw fl (-2) (p.W2 0 3 0) * Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)) + sw fl (-1) (p.b1 0 0)))))
    (hI4 : fl (fl (sw fl 1 (p.oW 1) * cv fl p (tokAt w i))) = fl (sw fl 1 (p.oW 1) * cv fl p (tokAt w i)))
    (hI5 : fl (fl (fl (sw fl 1 (p.oW 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.oW 3) * fl (A + fl (sw fl (-2) (p.W2 0 3 0) * Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)) + sw fl (-1) (p.b1 0 0))))))))
      = fl (fl (sw fl 1 (p.oW 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.oW 3) * fl (A + fl (sw fl (-2) (p.W2 0 3 0) * Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)) + sw fl (-1) (p.b1 0 0)))))))) :
    sout net fl ex p w i
      = fl (fl (sw fl 1 (p.oW 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.oW 3) * fl (A + fl (sw fl (-2) (p.W2 0 3 0) * Lane4.relu (fl (fl (fl (sw fl 1 (p.W1 0 0 1) * cv fl p (tokAt w i)) + fl (sw fl 1 (p.W1 0 0 3) * A)) + sw fl (-1) (p.b1 0 0))))))) := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 1, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn]
  simp only [init_eq hr p w hw]
  simp [z7, pos, rdot, radd, raffine, sw_zero hr, hr.zero, hr.one, hA, hfa, hfc, hfu, hfi, hfn,
    hfn', hI1, hI2, hI3, hI4, hI5]

set_option maxHeartbeats 800000 in
theorem score_facts {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2 ^ 24) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 149) {n : ℝ} (hn1 : 1 ≤ n)
    (hn : u * n ≤ 1 / 256) (hnη : η * n ≤ 1 / 2 ^ 100) (hM : 100 * n ≤ M)
    {S0 Pn uk fi fk : ℝ} (hS : |S0| ≤ 101 / 5) (hP : |Pn| ≤ 41) (hu : |uk| ≤ 101 / 100)
    (hfi0 : 0 ≤ fi) (hfi1 : fi ≤ n + 1 / 100) (hfk0 : 0 ≤ fk) (hfk1 : fk ≤ n + 1 / 100) :
    fl (fl (S0 * fk)) = fl (S0 * fk) ∧ fl (fl (Pn * uk)) = fl (Pn * uk) ∧
    fl (fl (fl (S0 * fk) + fl (fi * fl (Pn * uk))))
      = fl (fl (S0 * fk) + fl (fi * fl (Pn * uk))) ∧
    |fl (fl (S0 * fk) + fl (fi * fl (Pn * uk))) - (S0 * fk + fi * (Pn * uk))| ≤ 3 / 4 ∧
    |fl (fl (S0 * fk) + fl (fi * fl (Pn * uk)))| ≤ 67 * n := by
  have hη1 := eta_tiny hη
  have hη2 : η ≤ 1 / 1000 := by
    have : (1 : ℝ) / 10 ^ 40 ≤ 1 / 1000 := by norm_num
    linarith
  have hnn : 0 ≤ n := by linarith
  have hM1 : (100 : ℝ) ≤ M := by linarith
  have hu6 : u ≤ 1 / 1000000 := by
    have : (1 : ℝ) / 2 ^ 24 ≤ 1 / 1000000 := by norm_num
    linarith
  -- T
  have b1 : |S0 * fk| ≤ 21 * n := by
    rw [abs_mul, abs_of_nonneg hfk0]
    have := mul_le_mul hS hfk1 hfk0 (by norm_num)
    linarith
  have hu21 : u * (21 * n) = 21 * (u * n) := by ring
  have e1 := hr.abs hu0 b1 (by linarith)
  have hT := hr.bound hu0 b1 (by linarith)
  have hI1 := hr.idem _ (le_trans b1 (by linarith))
  -- q
  have b2 : |Pn * uk| ≤ 42 := by
    rw [abs_mul]
    have := mul_le_mul hP hu (abs_nonneg _) (by norm_num)
    linarith
  have e2 := hr.abs hu0 b2 (by linarith)
  have hq := hr.bound hu0 b2 (by linarith)
  have hI2 := hr.idem _ (le_trans b2 (by linarith))
  have hq43 : |fl (Pn * uk)| ≤ 43 := by linarith
  -- r
  have b3 : |fi * fl (Pn * uk)| ≤ 44 * n := by
    rw [abs_mul, abs_of_nonneg hfi0]
    have := mul_le_mul hfi1 hq43 (abs_nonneg _) (by linarith)
    linarith
  have hu44 : u * (44 * n) = 44 * (u * n) := by ring
  have e3 := hr.abs hu0 b3 (by linarith)
  have hr3 := hr.bound hu0 b3 (by linarith)
  have hfq : |fi * fl (Pn * uk) - fi * (Pn * uk)| ≤ (n + 1 / 100) * (u * 42 + η) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hfi0]
    exact mul_le_mul hfi1 e2 (abs_nonneg _) (by linarith)
  have hfq2 : (n + 1 / 100) * (u * 42 + η) = 42 * (u * n) + η * n + 42 / 100 * u + η / 100 := by ring
  -- sum
  have b4 : |fl (S0 * fk) + fl (fi * fl (Pn * uk))| ≤ 66 * n := by
    have := abs_add_le (fl (S0 * fk)) (fl (fi * fl (Pn * uk)))
    linarith
  have hu66 : u * (66 * n) = 66 * (u * n) := by ring
  have e4 := hr.abs hu0 b4 (by linarith)
  have hs4 := hr.bound hu0 b4 (by linarith)
  have hI3 := hr.idem _ (le_trans b4 (by linarith))
  refine ⟨hI1, hI2, hI3, ?_, ?_⟩
  · have a1 := abs_le.mp e1
    have a3 := abs_le.mp e3
    have a4 := abs_le.mp e4
    have a5 := abs_le.mp hfq
    rw [abs_le]
    constructor <;> linarith [hfq2, hu21, hu44, hu66, hn, hnη, hu6, hη2]
  · linarith
theorem firstc_snoc (p : List ℕ) (t : ℕ) :
    firstc (p ++ [t]) = if firstc p = 0 then code t else firstc p := by
  unfold firstc
  rw [List.foldl_append]
  rfl

theorem take_snoc (w : List ℕ) (i : ℕ) (h : i < w.length) :
    w.take (i + 1) = w.take i ++ [tokAt w (i + 1)] := by
  rw [Lane4.Seq.tokAt_succ w i h, List.take_add_one, List.getElem?_eq_getElem h]
  rfl

theorem code_zero_iff (t : ℕ) : code t = 0 ↔ ¬ (t = 1 ∨ t = 4 ∨ t = 5) := by
  unfold code
  split_ifs <;> constructor <;> intro h <;> omega

theorem code_two_iff (t : ℕ) : code t = 2 ↔ (t = 4 ∨ t = 5) := by
  unfold code
  split_ifs <;> constructor <;> intro h <;> omega

theorem first_ex (w : List ℕ) : ∀ i, i ≤ w.length →
    ((∀ k, 1 ≤ k → k ≤ i → ¬ (tokAt w k = 1 ∨ tokAt w k = 4 ∨ tokAt w k = 5))
      ∧ firstc (w.take i) = 0)
    ∨ (∃ j, 1 ≤ j ∧ j ≤ i ∧ (tokAt w j = 1 ∨ tokAt w j = 4 ∨ tokAt w j = 5) ∧
        (∀ k, 1 ≤ k → k < j → ¬ (tokAt w k = 1 ∨ tokAt w k = 4 ∨ tokAt w k = 5)) ∧
        firstc (w.take i) = code (tokAt w j)) := by
  intro i
  induction i with
  | zero =>
    intro _
    left
    exact ⟨fun k h1 h2 => by omega, by simp [firstc]⟩
  | succ i ih =>
    intro hi
    have hi' : i < w.length := by omega
    rw [take_snoc w i hi', firstc_snoc]
    rcases ih (by omega) with ⟨hn, hf⟩ | ⟨j, hj1, hj2, hjm, hjn, hf⟩
    · rw [hf, if_pos rfl]
      by_cases hm : (tokAt w (i + 1) = 1 ∨ tokAt w (i + 1) = 4 ∨ tokAt w (i + 1) = 5)
      · right
        exact ⟨i + 1, by omega, le_refl _, hm, fun k h1 h2 => hn k h1 (by omega), rfl⟩
      · left
        refine ⟨fun k h1 h2 => ?_, (code_zero_iff _).mpr hm⟩
        by_cases hk : k = i + 1
        · subst hk
          exact hm
        · exact hn k h1 (by omega)
    · have hne : firstc (w.take i) ≠ 0 := by
        rw [hf]
        intro h0
        exact ((code_zero_iff _).mp h0) hjm
      rw [if_neg hne]
      right
      exact ⟨j, hj1, by omega, hjm, hjn, hf⟩

set_option maxHeartbeats 800000 in
theorem num {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2 ^ 24)
    (hη : η ≤ 1 / 2 ^ 149) (h100 : (100 : ℝ) ≤ M)
    {a c cs A Wc W3 bb Wq O2 O3 : ℝ}
    (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1)
    (hcs : |cs - c| ≤ 1 / 100) (hA : |A - a| ≤ 3 / 100)
    (hWc : |Wc - 1| ≤ 1 / 150) (hW3 : |W3 - 1| ≤ 1 / 150) (hbb : |bb - (-1)| ≤ 1 / 150)
    (hWq : |Wq - (-2)| ≤ 1 / 50) (hO2 : |O2 - 1| ≤ 1 / 150) (hO3 : |O3 - 1| ≤ 1 / 150) :
    fl (fl (Wc * cs)) = fl (Wc * cs) ∧
    fl (fl (fl (Wc * cs) + fl (W3 * A))) = fl (fl (Wc * cs) + fl (W3 * A)) ∧
    fl (fl (Wq * Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb))))
      = fl (Wq * Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb))) ∧
    fl (fl (O2 * cs)) = fl (O2 * cs) ∧
    fl (fl (fl (O2 * cs) + fl (O3 * fl (A + fl (Wq * Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb)))))))
      = fl (fl (O2 * cs) + fl (O3 * fl (A + fl (Wq * Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb)))))) ∧
    |fl (fl (O2 * cs) + fl (O3 * fl (A + fl (Wq * Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb))))))
      - (a + c - 2 * max (a + c - 1) 0)| ≤ 1 / 4 := by
  have hη1 := eta_tiny hη
  have fn : ∀ x t e : ℝ, |x - t| ≤ e → |x| ≤ 100 → |fl x - t| ≤ e + 1 / 1000 := by
    intro x t e hx hb
    have h1 := hr.near hu0 hx hb h100
    have h3 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10000 := by norm_num
    have h4 : (1 : ℝ) / 2 ^ 24 * 100 ≤ 1 / 10000 := by norm_num
    linarith
  have hid : ∀ x : ℝ, |x| ≤ 100 → fl (fl x) = fl x := fun x hx => hr.idem x (le_trans hx h100)
  have bnd : ∀ x t e : ℝ, |x - t| ≤ e → |t| ≤ 2 → e ≤ 1 → |x| ≤ 100 := by
    intro x t e hx ht he
    have := abs_sub_abs_le_abs_sub x t
    linarith
  have hsum : ∀ x y s t e f : ℝ, |x - s| ≤ e → |y - t| ≤ f → |x + y - (s + t)| ≤ e + f := by
    intro x y s t e f hx hy
    have h1 := abs_le.mp hx
    have h2 := abs_le.mp hy
    rw [abs_le]
    constructor <;> linarith
  have ha0 : 0 ≤ a := by rcases ha with h | h <;> rw [h] <;> norm_num
  have ha1 : a ≤ 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
  have hc0 : 0 ≤ c := by rcases hc with h | h <;> rw [h] <;> norm_num
  have hc1 : c ≤ 1 := by rcases hc with h | h <;> rw [h] <;> norm_num
  have haa : |a| ≤ 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have hcc : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  -- P = fl (Wc * cs)
  have m1 := mul_near hWc hcs
  rw [one_mul, abs_one] at m1
  have m1' : |Wc * cs - c| ≤ 1 / 50 := by linarith
  have hb1 : |Wc * cs| ≤ 100 := bnd _ c (1 / 50) m1' (by linarith) (by norm_num)
  have hI1 := hid _ hb1
  have eP := fn _ _ _ m1' hb1
  -- Q3 = fl (W3 * A)
  have m3 := mul_near hW3 hA
  rw [one_mul, abs_one] at m3
  have m3' : |W3 * A - a| ≤ 37 / 1000 := by linarith
  have hb3 : |W3 * A| ≤ 100 := bnd _ a (37 / 1000) m3' (by linarith) (by norm_num)
  have eQ := fn _ _ _ m3' hb3
  -- R
  have sR := hsum _ _ _ _ _ _ eP eQ
  have hbR : |fl (Wc * cs) + fl (W3 * A)| ≤ 100 := bnd _ _ _ sR (by linarith) (by norm_num)
  have hI2 := hid _ hbR
  have eR := fn _ _ _ sR hbR
  -- pre
  have sp := hsum _ _ _ _ _ _ eR hbb
  have hbp : |fl (fl (Wc * cs) + fl (W3 * A)) + bb| ≤ 100 := bnd _ _ _ sp (by linarith) (by norm_num)
  have ep := fn _ _ _ sp hbp
  -- H
  have hrelu : ∀ x : ℝ, Lane4.relu x = max x 0 := fun x => rfl
  have hH0 := abs_max_sub_max_le_abs (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb)) (a + c - 1) 0
  have hH1 : |fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb) - (a + c - 1)| ≤ 69 / 1000 := by
    have : fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb) - (a + c - 1)
        = fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb) - (c + a + -1) := by ring
    rw [this]
    linarith
  have hH : |Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb)) - max (a + c - 1) 0| ≤ 69 / 1000 := by
    rw [hrelu]
    linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = max (a + c - 1) 0 := ⟨_, rfl⟩
  rw [← ht] at hH ⊢
  have ht0 : 0 ≤ t := by rw [ht]; exact le_max_right _ _
  have ht1 : t ≤ 1 := by rw [ht]; exact max_le (by linarith) (by norm_num)
  have htt : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  -- Qn = fl (Wq * H)
  generalize hHd : Lane4.relu (fl (fl (fl (Wc * cs) + fl (W3 * A)) + bb)) = H at hH ⊢
  have m2 := mul_near hWq hH
  rw [h2] at m2
  have m2' : |Wq * H - (-2) * t| ≤ 16 / 100 := by nlinarith [abs_nonneg t]
  have ht2 : |(-2 : ℝ) * t| ≤ 2 := by rw [abs_mul, h2]; linarith
  have hb2 : |Wq * H| ≤ 100 := bnd _ _ _ m2' ht2 (by norm_num)
  have hI3 := hid _ hb2
  have eN := fn _ _ _ m2' hb2
  -- A' = fl (A + Qn)
  have sA := hsum _ _ _ _ _ _ hA eN
  have hat : |a + (-2) * t| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hbA : |A + fl (Wq * H)| ≤ 100 := bnd _ _ _ sA hat (by norm_num)
  have eA := fn _ _ _ sA hbA
  -- V = fl (O3 * A')
  have m4 := mul_near hO3 eA
  rw [one_mul, abs_one] at m4
  have m4' : |O3 * fl (A + fl (Wq * H)) - (a + (-2) * t)| ≤ 21 / 100 := by nlinarith [abs_nonneg (a + (-2) * t)]
  have hb4 : |O3 * fl (A + fl (Wq * H))| ≤ 100 := bnd _ _ _ m4' hat (by norm_num)
  have eV := fn _ _ _ m4' hb4
  -- U = fl (O2 * cs)
  have m5 := mul_near hO2 hcs
  rw [one_mul, abs_one] at m5
  have m5' : |O2 * cs - c| ≤ 17 / 1000 := by linarith
  have hb5 : |O2 * cs| ≤ 100 := bnd _ c _ m5' (by linarith) (by norm_num)
  have hI4 := hid _ hb5
  have eU := fn _ _ _ m5' hb5
  -- out
  have sO := hsum _ _ _ _ _ _ eU eV
  have hbO : |fl (O2 * cs) + fl (O3 * fl (A + fl (Wq * H)))| ≤ 100 :=
    bnd _ _ _ sO (by rw [abs_le]; constructor <;> nlinarith) (by norm_num)
  have hI5 := hid _ hbO
  have eO := fn _ _ _ sO hbO
  refine ⟨hI1, hI2, hI3, hI4, hI5, ?_⟩
  have : a + c - 2 * t = c + (a + (-2) * t) := by ring
  rw [this]
  linarith

theorem net_ok : Statement net := by
  skip

end Lane4.Case
