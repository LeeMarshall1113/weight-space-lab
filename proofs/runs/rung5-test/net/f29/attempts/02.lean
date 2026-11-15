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
    constructor <;> nlinarith [hfq2]
  · linarith
theorem firstc_snoc (p : List ℕ) (t : ℕ) :
    firstc (p ++ [t]) = if firstc p = 0 then code t else firstc p := by
  simp [firstc, List.foldl_append]

theorem take_snoc (w : List ℕ) (i : ℕ) (h : i < w.length) :
    w.take (i + 1) = w.take i ++ [tokAt w (i + 1)] := by
  rw [Lane4.Seq.tokAt_succ w i h]
  simp [List.take_succ, List.getElem?_eq_getElem h]

theorem code_zero_iff (t : ℕ) : code t = 0 ↔ ¬ (t = 1 ∨ t = 4 ∨ t = 5) := by
  unfold code
  split_ifs <;> omega

theorem code_two_iff (t : ℕ) : code t = 2 ↔ (t = 4 ∨ t = 5) := by
  unfold code
  split_ifs <;> omega

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

theorem net_ok : Statement net := by
  skip

end Lane4.Case
