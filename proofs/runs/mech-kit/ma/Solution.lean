set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.unusedTactic false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Lane4.Case

open Lane4.Seq (Mask cand tokAt)
open Lane4.RSeq (Vec pdot radd)
open Lane4.RSoft Lane4.AGate Lane4.Cert Lane4.Cert8 Lane4.R7K2

theorem sum_ge_mem' (c : List ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (p : ℕ) (hp : p ∈ c) :
    f p ≤ (c.map f).sum := by
  induction c with
  | nil => simp at hp
  | cons a c ih =>
    rw [List.map_cons, List.sum_cons]
    have hnn : 0 ≤ (c.map f).sum :=
      List.sum_nonneg (by
        intro x hx
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
        exact hf k)
    rcases List.mem_cons.mp hp with h | h
    · rw [h]; linarith
    · have := ih h
      linarith [hf a]

theorem head_tail8 : HeadTail8 := by
  intro u η M fl hC δ hδ0 hδ1 h E hc dd hok hsh hdd sA sV sg sgb hrows dA dV dm dg dgb hdA hdV hdm
    hdg hdgb n x tok hun hηn hM hx i hi hti P hW hlen hfull
  obtain ⟨hmask, hm1, hm2, hlen', hgate, hVE, hBv, hBv20, hsp, hpair, hL1, hL3, hroom⟩ :=
    Lane4.R8KG.open8 hok
  have env : Lane4.R8KG.Env8 u η M fl δ h E hc dd dA dV dm dg dgb n x tok :=
    ⟨hC, hδ0, hδ1, hok, hsh, hdd, sA, sV, sg, sgb, hrows, hdA, hdV, hdm, hdg, hdgb, hun, hηn, hM,
      hx, hmask, hm1, hm2, hlen', hgate, hVE, hBv, hBv20, hsp, hpair, hL1, hL3, hroom⟩
  obtain ⟨c, hcdef⟩ : ∃ c : List ℕ, c = h.cands fl dg dgb n x i := ⟨_, rfl⟩
  rw [← hcdef]
  have hcmem : ∀ k, k ∈ c ↔ k ∈ cand h.mask n i ∧ hc.cands.getD (tok k) false = true := by
    intro k
    rw [hcdef]
    exact Lane4.R8KG.e_mem_cands env hi k
  have hcnd : c.Nodup := by
    rw [hcdef]
    exact AHead.cands_nodup h fl dg dgb n x i
  have h3 : (0 : ℝ) ≤ ((3 * tailB δ h hc : ℚ) : ℝ) := by
    have h0 : (0 : ℚ) ≤ 3 * tailB δ h hc := by
      have := Lane4.R8KG.tailB_nonneg hroom
      linarith
    exact_mod_cast h0
  have htot : 0 ≤ (c.map (fun k => Real.exp (h.score fl dA dm x i k))).sum :=
    List.sum_nonneg (by
      intro y hy
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
      exact (Real.exp_pos _).le)
  by_cases hfl : P.length < fullLen h hc (tok i)
  · have hnil : c.filter (fun k => decide (k ∉ P)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro k hk
      obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
      have hk3 := (hcmem k).mp hk1
      have hk4 := decide_eq_true_eq.mp hk2
      exact hk4 (hfull hfl k hk3.1 hk3.2)
    rw [hnil, List.map_nil, List.sum_nil]
    exact mul_nonneg h3 htot
  · have hPeq : P.length = fullLen h hc (tok i) := le_antisymm hlen (not_lt.mp hfl)
    have hLP : hc.L ≤ P.length := by
      rw [hPeq]; unfold fullLen; exact Nat.le_add_right _ _
    have hpos : 0 < P.length := by omega
    have hp0P : P.getD 0 0 ∈ P := by
      cases P with
      | nil => simp at hpos
      | cons a P' => simp
    obtain ⟨hP1, hP2, hP3⟩ := hW
    have hp0c := hP2 _ hp0P
    have hp0i : P.getD 0 0 ≤ i := Lane4.R8KG.cand_le hmask hp0c.1
    have hp0mem : P.getD 0 0 ∈ c := (hcmem _).mpr hp0c
    have hTk : ∀ k ∈ c.filter (fun k => decide (k ∉ P)),
        k + hc.L ≤ P.getD 0 0 ∧ k ≤ i ∧ hc.cands.getD (tok k) false = true := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := List.mem_filter.mp hk
      have hk3 := (hcmem k).mp hk1
      have hk4 := decide_eq_true_eq.mp hk2
      have := Lane4.R8KG.pos_tail (m := h.mask) (cd := hc.cands) (tok := tok) (n := n) (i := i)
        (P := P) (c := c) ⟨hP1, hP2, hP3⟩ hpos (fun k hk => (hcmem k).mp hk) k hk1 hk4
      exact ⟨by omega, Lane4.R8KG.cand_le hmask hk3.1, hk3.2⟩
    have htail := Lane4.R8KG.tail_real env hi hti (c.filter (fun k => decide (k ∉ P)))
      (hcnd.filter _) (P.getD 0 0) (P.getD 0 0) hp0i hp0c.2
      (by rw [sub_self]; norm_num) hTk
    have key : ∀ l : List ℕ,
        (l.map (fun k => Real.exp (h.score fl dA dm x i k))).sum
          = Real.exp (h.score fl dA dm x i (P.getD 0 0)) *
            (l.map (fun k => Real.exp (h.score fl dA dm x i k
              - h.score fl dA dm x i (P.getD 0 0)))).sum := by
      intro l
      have : l.map (fun k => Real.exp (h.score fl dA dm x i k))
          = l.map (fun k => Real.exp (h.score fl dA dm x i (P.getD 0 0)) *
              Real.exp (h.score fl dA dm x i k - h.score fl dA dm x i (P.getD 0 0))) := by
        apply List.map_congr_left
        intro k _
        rw [← Real.exp_add]
        congr 1
        ring
      rw [this, List.sum_map_mul_left]
    rw [key]
    have hE : Real.exp (h.score fl dA dm x i (P.getD 0 0))
        ≤ (c.map (fun k => Real.exp (h.score fl dA dm x i k))).sum :=
      sum_ge_mem' c (fun k => Real.exp (h.score fl dA dm x i k)) (fun k => (Real.exp_pos _).le)
        _ hp0mem
    calc Real.exp (h.score fl dA dm x i (P.getD 0 0)) *
          ((c.filter (fun k => decide (k ∉ P))).map (fun k => Real.exp (h.score fl dA dm x i k
              - h.score fl dA dm x i (P.getD 0 0)))).sum
        ≤ Real.exp (h.score fl dA dm x i (P.getD 0 0)) * ((3 * tailB δ h hc : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
      _ = ((3 * tailB δ h hc : ℚ) : ℝ) * Real.exp (h.score fl dA dm x i (P.getD 0 0)) :=
          mul_comm _ _
      _ ≤ ((3 * tailB δ h hc : ℚ) : ℝ) *
          (c.map (fun k => Real.exp (h.score fl dA dm x i k))).sum :=
          mul_le_mul_of_nonneg_left hE h3

theorem attn_window8 : AttnWindow8 := by
  intro δ N T c hchk u η M fl hR hu0 hu1 hη0 hη1 p hp w hw hu hη hM B hB a h hc ha hh hhc i hi1 hi2
  have hn1 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hn2 : (1 : ℝ) ≤ ((w.length + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hM1 : (2 : ℝ) ^ 40 ≤ M := by nlinarith
  have hC : Ctx u η M fl := ⟨hR, hu0, hu1, hη0, hη1, hM1⟩
  obtain ⟨B', hB', hδ0, hδ1, hshape, hweights, hcl, hzip, hslen, hinit, hcase⟩ :=
    Lane4.R8K.check8_open hchk
  have hBB : B' = B := by
    have e := hB.symm.trans hB'
    simpa using e.symm
  rw [hBB] at hweights hcl hzip
  obtain ⟨d, hd24, hembl, hembrows, hblocks, houtW⟩ := Lane4.R8K.shape_facts hshape
  have hBshape : B.shapeOK d = true := hblocks B (by rw [hB]; simp)
  obtain ⟨hhl4, hheadsh, hb1l, hW1l, hW1r, hW2l, hW2r, hb2l⟩ := Lane4.R8K.block_shape hBshape
  obtain ⟨wEmb, wOut, wOutB, wW1, wb1, wW2, wb2, wHeads⟩ := Lane4.R8K.weights_facts hweights
  generalize hE : N.embed.map (embIV δ) = E at hzip
  have hEl : E.length = T.ntok + 1 := by rw [← hE, List.length_map, hembl]
  have hdbd : ∀ k : ℕ, |(fun _ : ℕ => (0 : ℝ)) k| ≤ (δ : ℝ) := fun k => by
    simp only [abs_zero]; exact Rat.cast_nonneg.mpr hδ0
  have hrows : ∀ row ∈ E, row.length = d ∧ Bdd 16 row := by
    intro row hrow
    rw [← hE] at hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    exact ⟨by simp [embIV, hembrows r hr],
      (emb_sound u η M fl hC δ hδ0 hδ1 r (fun _ => 0) hdbd (zsmallM_mem wEmb r hr)).2⟩
  have htok : ∀ j, tokAt w j = 0 ∨ tokAt w j ∈ w := Lane4.Seq.tokAt_zero_or_mem w
  have htokle : ∀ j, tokAt w j ≤ T.ntok := by
    intro j
    rcases htok j with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (hw _ h).2
  have hxE : ∀ j, j < w.length + 1 →
      tokAt w j < E.length ∧ InIVs (N.init fl p w j) (E.getD (tokAt w j) []) := by
    intro j _
    have hlt : tokAt w j < N.embed.length := by have := htokle j; omega
    refine ⟨by rw [hEl]; have := htokle j; omega, ?_⟩
    have hget : E.getD (tokAt w j) [] = embIV δ (N.embed.getD (tokAt w j) []) := by
      rw [← hE]; exact zgetD_map'' (embIV δ) [] [] rfl N.embed _ hlt
    rw [hget]
    exact (emb_sound u η M fl hC δ hδ0 hδ1 _ (p.E (tokAt w j)) (fun k => hp.E _ k)
      (zsmallM_mem wEmb _ (zgetD_mem' [] N.embed _ hlt))).1
  have hmem : h ∈ B.heads := by
    have := zgetD_mem' h B.heads a ha
    rwa [hh] at this
  have hOK : headOK8 δ E h hc = true := by
    have := Lane4.R8K.zipWith_all_getD _ h hc B.heads c.heads hcl hzip a ha
    rw [hh, hhc] at this
    exact this
  have hshd := hheadsh _ hmem
  obtain ⟨wA, wV, wg, wgb⟩ := wHeads _ hmem
  obtain ⟨hne, hL⟩ := Lane4.R8K.headOK8_facts hOK
  have hti : tokAt w i ∈ w := by
    have h1 := Lane4.Seq.tokAt_succ w (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at h1
    rw [h1]; exact List.getElem_mem _
  have hti1 := (hw _ hti).1
  obtain ⟨P, hP1, hP2, hP3, hP4⟩ := Lane4.R8KF.abs_keys8 T c.heads w i a h hc hi1 hi2
    (by omega) hhc hne hL
  have hfl : fullLen h hc (tokAt w i) ≤ hc.L + 1 := by
    unfold fullLen; split_ifs <;> omega
  refine ⟨P, hP1, le_trans hP3 hfl, ?_⟩
  exact head_tail8 u η M fl hC δ hδ0 hδ1 h E hc d hOK hshd hd24 wA wV wg wgb hrows
    (p.A 0 a) (p.V 0 a) (p.m 0 a) (p.g 0 a) (p.gb 0 a)
    (hp.A 0 a) (hp.V 0 a) (hp.m 0 a) (hp.g 0 a) (hp.gb 0 a)
    (w.length + 1) (N.init fl p w) (tokAt w) hu hη hM hxE i (by omega) hti1 P hP1 hP3 hP4

end Lane4.Case
