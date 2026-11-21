namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! coordinates: 0 mk, 1 a, 2 c, 3 f (=F/4), 4 A, 5 y -/

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]
def z2 : List ℚ := [0, 0]

def head0 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, [1/4, 0, 0, 0, 0, 0], z6, z6],
    mask := Mask.strict, m := 24, g := [-1, 0, 0, 0, 0, 0], gb := 1/2 }

def head1 : AHead :=
  { A := [z6, z6, z6, z6, z6, z6],
    V := [z6, z6, z6, z6, [0, 1, 0, 0, 0, 0], z6],
    mask := Mask.causal, m := 24, g := [-1, 0, 0, 4, 0, 0], gb := 1/2 }

def blk0 : ABlock :=
  { heads := [head0], W1 := [], b1 := [], W2 := [[], [], [], [], [], []], b2 := z6 }

def blk1 : ABlock :=
  { heads := [head1], W1 := [[0, 0, 1, 0, -1, 0], [0, 0, -1, 0, 1, 0]], b1 := z2,
    W2 := [z2, z2, z2, z2, z2, [1, 1]], b2 := z6 }

def net : ANet :=
  { embed := [z6, [0, 0, 1, 0, 0, 0], z6, z6, [1, 1, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0]],
    blocks := [blk0, blk1], outW := [0, 0, 0, 0, 0, 1], outB := 0 }


/-! ### ideal quantities -/

noncomputable def mkR (t : ℕ) : ℝ := if t = 4 ∨ t = 5 then 1 else 0
noncomputable def aR (t : ℕ) : ℝ := if t = 4 then 1 else 0
noncomputable def cR (t : ℕ) : ℝ := if t = 1 ∨ t = 4 ∨ t = 5 then 1 else 0

def mkQ (t : ℕ) : ℚ := if t = 4 ∨ t = 5 then 1 else 0
def aQ (t : ℕ) : ℚ := if t = 4 then 1 else 0
def cQ (t : ℕ) : ℚ := if t = 1 ∨ t = 4 ∨ t = 5 then 1 else 0

theorem mkQ_R (t : ℕ) : ((mkQ t : ℚ) : ℝ) = mkR t := by
  unfold mkQ mkR; split_ifs <;> simp
theorem aQ_R (t : ℕ) : ((aQ t : ℚ) : ℝ) = aR t := by
  unfold aQ aR; split_ifs <;> simp
theorem cQ_R (t : ℕ) : ((cQ t : ℚ) : ℝ) = cR t := by
  unfold cQ cR; split_ifs <;> simp

theorem mkR_01 (t : ℕ) : mkR t = 0 ∨ mkR t = 1 := by
  unfold mkR; split_ifs <;> simp
theorem aR_01 (t : ℕ) : aR t = 0 ∨ aR t = 1 := by
  unfold aR; split_ifs <;> simp
theorem cR_01 (t : ℕ) : cR t = 0 ∨ cR t = 1 := by
  unfold cR; split_ifs <;> simp

theorem embed_row {t : ℕ} (h : t ≤ 5) :
    net.embed.getD t [] = [mkQ t, aQ t, cQ t, 0, 0, 0] := by
  interval_cases t <;> simp [net, z6, mkQ, aQ, cQ]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 5) :
    net.init fl p w j = [asw fl (mkQ (tokAt w j)) (p.E (tokAt w j) 0),
      asw fl (aQ (tokAt w j)) (p.E (tokAt w j) 1), asw fl (cQ (tokAt w j)) (p.E (tokAt w j) 2),
      asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4),
      asw fl 0 (p.E (tokAt w j) 5)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

/-- `Close` for six entries. -/
theorem close6 {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 e X : ℝ}
    (h0 : |a0 - b0| ≤ e) (h1 : |a1 - b1| ≤ e) (h2 : |a2 - b2| ≤ e)
    (h3 : |a3 - b3| ≤ e) (h4 : |a4 - b4| ≤ e) (h5 : |a5 - b5| ≤ e)
    (g0 : |b0| ≤ X) (g1 : |b1| ≤ X) (g2 : |b2| ≤ X) (g3 : |b3| ≤ X) (g4 : |b4| ≤ X)
    (g5 : |b5| ≤ X) :
    Close [a0, a1, a2, a3, a4, a5] [b0, b1, b2, b3, b4, b5] e X := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have hk6 : k < 6 := by simpa using hk
  interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
    first | exact ⟨h0, g0⟩ | exact ⟨h1, g1⟩ | exact ⟨h2, g2⟩ | exact ⟨h3, g3⟩ |
      exact ⟨h4, g4⟩ | exact ⟨h5, g5⟩

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

/-- small constants -/
theorem Ctx.small (ev : Ctx u η M fl ex p w) : u ≤ 1 / 10000000 ∧ η ≤ 1 / 10 ^ 30 := by
  refine ⟨le_trans ev.hu1 (by norm_num), le_trans (eta_tiny ev.hη1) (by norm_num)⟩

/-- A stored weight `fl (a + d)`, `|a| ≤ 5`, is within 1/900 of `a`. -/
theorem asw_c (ev : Ctx u η M fl ex p w) (a : ℚ) {d : ℝ} (hd : |d| ≤ 1 / 1000)
    (ha : |(a : ℝ)| ≤ 5) : |asw fl a d - (a : ℝ)| ≤ 1 / 900 := by
  have h := asw_near ev.hr ev.hu0 a hd (by have := ev.range 6 (by norm_num); linarith)
  have h1 : u * (|(a : ℝ)| + 1 / 1000) ≤ 1 / 10000000 * 6 := by
    have := ev.small
    exact mul_le_mul this.1 (by linarith) (by positivity) (by positivity)
  have h2 := ev.small.2
  linarith

theorem init_ent (ev : Ctx u η M fl ex p w) (j : ℕ) :
    ∃ a0 a1 a2 a3 a4 a5 : ℝ, net.init fl p w j = [a0, a1, a2, a3, a4, a5] ∧
      |a0 - mkR (tokAt w j)| ≤ 1 / 900 ∧ |a1 - aR (tokAt w j)| ≤ 1 / 900 ∧
      |a2 - cR (tokAt w j)| ≤ 1 / 900 ∧ |a3 - 0| ≤ 1 / 900 ∧ |a4 - 0| ≤ 1 / 900 ∧
      |a5 - 0| ≤ 1 / 900 := by
  have ht := tok_le w ev.hw j
  refine ⟨_, _, _, _, _, _, init_eq fl p w j ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := asw_c ev (mkQ (tokAt w j)) (ev.hp.E _ 0)
      (by rw [mkQ_R]; rcases mkR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [mkQ_R] at h
  · have h := asw_c ev (aQ (tokAt w j)) (ev.hp.E _ 1)
      (by rw [aQ_R]; rcases aR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [aQ_R] at h
  · have h := asw_c ev (cQ (tokAt w j)) (ev.hp.E _ 2)
      (by rw [cQ_R]; rcases cR_01 (tokAt w j) with h | h <;> rw [h] <;> norm_num)
    rwa [cQ_R] at h
  · have h := asw_c ev 0 (ev.hp.E _ 3) (by simp)
    simpa using h
  · have h := asw_c ev 0 (ev.hp.E _ 4) (by simp)
    simpa using h
  · have h := asw_c ev 0 (ev.hp.E _ 5) (by simp)
    simpa using h

end Steps

end Lane4.Case
