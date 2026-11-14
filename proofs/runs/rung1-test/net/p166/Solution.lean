namespace Lane4.Case
open Lane4

def net : Net :=
  { hidden :=
      [ { W := [[3, 0], [0, 2], [1, 1]], b := [9/2, 2, 5/2] },
        { W := [[1, 0, 0], [0, 0, 1], [1, 0, 0], [0, 1, 0], [0, 0, 1]], b := [-5, -1, 0, 0, 0] },
        { W := [[1, 0, -1, 1, 0], [-1, 0, 1, 0, 0], [0, -1, 0, 0, 1], [0, 0, 0, 1, 0]],
          b := [1/2, 0, 0, 0] },
        { W := [[1, 1, -1, 0], [-1, 0, 0, 1], [1, 1, 0, 0]], b := [-2, 1/2, 0] },
        { W := [[-1, -1, 1], [0, 1, 0]], b := [0, 0] },
        { W := [[1, 1], [1, 1]], b := [-2, -4] } ],
    out := { W := [[1, -1]], b := [-1/2] } }

noncomputable def n1 (x0 x1 : ℝ) : ℝ := relu (3*x0+2+5/2)
noncomputable def n2 (x0 x1 : ℝ) : ℝ := relu (2*x1+2)
noncomputable def n3 (x0 x1 : ℝ) : ℝ := relu (x0+x1+2+1/2)
noncomputable def r1 (x0 x1 : ℝ) : ℝ := relu (n1 x0 x1 - 5)
noncomputable def r2 (x0 x1 : ℝ) : ℝ := relu (n3 x0 x1 - 1)
noncomputable def A2 (x0 x1 : ℝ) : ℝ := relu (n1 x0 x1)
noncomputable def B2 (x0 x1 : ℝ) : ℝ := relu (n2 x0 x1)
noncomputable def V2 (x0 x1 : ℝ) : ℝ := relu (n3 x0 x1)
noncomputable def tt (x0 x1 : ℝ) : ℝ := relu (B2 x0 x1 - A2 x0 x1 + r1 x0 x1 + 1/2)
noncomputable def CC (x0 x1 : ℝ) : ℝ := relu (A2 x0 x1 - r1 x0 x1)
noncomputable def DD (x0 x1 : ℝ) : ℝ := relu (V2 x0 x1 - r2 x0 x1)
noncomputable def Bp (x0 x1 : ℝ) : ℝ := relu (B2 x0 x1)
noncomputable def ss (x0 x1 : ℝ) : ℝ := relu (CC x0 x1 + tt x0 x1 - DD x0 x1 - 2)
noncomputable def mm (x0 x1 : ℝ) : ℝ := relu (Bp x0 x1 + 1/2 - tt x0 x1)
noncomputable def Mn (x0 x1 : ℝ) : ℝ := relu (CC x0 x1 + tt x0 x1)
noncomputable def ww (x0 x1 : ℝ) : ℝ := relu (Mn x0 x1 - ss x0 x1 - mm x0 x1)
noncomputable def mp (x0 x1 : ℝ) : ℝ := relu (mm x0 x1)
noncomputable def q1 (x0 x1 : ℝ) : ℝ := relu (mp x0 x1 + ww x0 x1 - 2)
noncomputable def q2 (x0 x1 : ℝ) : ℝ := relu (mp x0 x1 + ww x0 x1 - 4)
noncomputable def fout (x0 x1 : ℝ) : ℝ := q1 x0 x1 - q2 x0 x1 - 1/2

theorem relu_nn (a : ℝ) : 0 ≤ relu a := le_max_right _ _

theorem clip5 (y : ℝ) :
    relu (y+5/2) - relu (relu (y+5/2) - 5) = min (max y (-5/2)) (5/2) + 5/2 := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem clip1 (y : ℝ) :
    relu (y+1/2) - relu (relu (y+1/2) - 1) = min (max y (-1/2)) (1/2) + 1/2 := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem nn5 (y : ℝ) : 0 ≤ min (max y (-5/2)) (5/2) + 5/2 := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem nn1 (y : ℝ) : 0 ≤ min (max y (-1/2)) (1/2) + 1/2 := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem clipF (f : ℝ) :
    relu (f+1/2) - relu (f-3/2) - 1/2 = min (max f (-1/2)) (3/2) := by
  simp only [relu, max_def, min_def]
  split_ifs <;> linarith

theorem key (x0 x1 : ℝ) (h0 : -8 ≤ x0) (h0' : x0 ≤ 2) (h1 : -1 ≤ x1) (h1' : x1 ≤ 8) :
    fout x0 x1 = spec x0 x1 := by
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = min (max (3*x0+2) (-5/2)) (5/2) := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = min (max (x0+x1+2) (-1/2)) (1/2) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c + 5/2 := by rw [hcd]; exact nn5 _
  have hd0 : 0 ≤ d + 1/2 := by rw [hdd]; exact nn1 _
  have hn2 : n2 x0 x1 = 2*x1+2 := by unfold n2; exact relu_of_nonneg (by linarith)
  have hA2 : A2 x0 x1 = n1 x0 x1 := by unfold A2; exact relu_of_nonneg (relu_nn _)
  have hB2 : B2 x0 x1 = n2 x0 x1 := by unfold B2; exact relu_of_nonneg (relu_nn _)
  have hV2 : V2 x0 x1 = n3 x0 x1 := by unfold V2; exact relu_of_nonneg (relu_nn _)
  have hBp : Bp x0 x1 = B2 x0 x1 := by unfold Bp; exact relu_of_nonneg (relu_nn _)
  have hc5 : A2 x0 x1 - r1 x0 x1 = c + 5/2 := by
    rw [hA2, hcd]; exact clip5 (3*x0+2)
  have hd1 : V2 x0 x1 - r2 x0 x1 = d + 1/2 := by
    rw [hV2, hdd]; exact clip1 (x0+x1+2)
  have hC : CC x0 x1 = c + 5/2 := by
    have h : 0 ≤ A2 x0 x1 - r1 x0 x1 := by rw [hc5]; exact hc0
    unfold CC; rw [relu_of_nonneg h, hc5]
  have hD : DD x0 x1 = d + 1/2 := by
    have h : 0 ≤ V2 x0 x1 - r2 x0 x1 := by rw [hd1]; exact hd0
    unfold DD; rw [relu_of_nonneg h, hd1]
  have ht : tt x0 x1 = relu (2*x1 - c) := by
    have h : B2 x0 x1 - A2 x0 x1 + r1 x0 x1 + 1/2 = 2*x1 - c := by
      rw [hB2, hn2]; linarith
    unfold tt; rw [h]
  have htn : 0 ≤ tt x0 x1 := by unfold tt; exact relu_nn _
  have hm : 2*x1 - tt x0 x1 = min (2*x1) c := by rw [ht]; exact sub_relu_sub _ _
  have hM : c + tt x0 x1 = max c (2*x1) := by rw [ht]; exact add_relu_sub _ _
  have hmin : -5/2 ≤ min (2*x1) c := le_min (by linarith) (by linarith)
  have hs : ss x0 x1 = relu (max c (2*x1) - d) := by
    have h : CC x0 x1 + tt x0 x1 - DD x0 x1 - 2 = max c (2*x1) - d := by
      rw [hC, hD]; linarith
    unfold ss; rw [h]
  have he : max c (2*x1) - ss x0 x1 = min (max c (2*x1)) d := by
    rw [hs]; exact sub_relu_sub _ _
  have hmm : mm x0 x1 = min (2*x1) c + 5/2 := by
    have hnn : 0 ≤ Bp x0 x1 + 1/2 - tt x0 x1 := by
      rw [hBp, hB2, hn2]; linarith
    unfold mm; rw [relu_of_nonneg hnn, hBp, hB2, hn2]; linarith
  have hMn : Mn x0 x1 = max c (2*x1) + 5/2 := by
    have hnn : 0 ≤ CC x0 x1 + tt x0 x1 := by rw [hC]; linarith
    unfold Mn; rw [relu_of_nonneg hnn, hC]; linarith
  have hw : ww x0 x1 = relu (min (max c (2*x1)) d - min (2*x1) c) := by
    have h : Mn x0 x1 - ss x0 x1 - mm x0 x1 = min (max c (2*x1)) d - min (2*x1) c := by
      rw [hMn, hmm]; linarith
    unfold ww; rw [h]
  have hf : min (2*x1) c + ww x0 x1
      = max (min (2*x1) c) (min (max c (2*x1)) d) := by
    rw [hw]; exact add_relu_sub _ _
  have hmp : mp x0 x1 = mm x0 x1 := by
    unfold mp; exact relu_of_nonneg (by rw [hmm]; linarith)
  have hq1 : q1 x0 x1 = relu (max (min (2*x1) c) (min (max c (2*x1)) d) + 1/2) := by
    have h : mp x0 x1 + ww x0 x1 - 2 = max (min (2*x1) c) (min (max c (2*x1)) d) + 1/2 := by
      rw [hmp, hmm]; linarith
    unfold q1; rw [h]
  have hq2 : q2 x0 x1 = relu (max (min (2*x1) c) (min (max c (2*x1)) d) - 3/2) := by
    have h : mp x0 x1 + ww x0 x1 - 4 = max (min (2*x1) c) (min (max c (2*x1)) d) - 3/2 := by
      rw [hmp, hmm]; linarith
    unfold q2; rw [h]
  unfold fout
  rw [hq1, hq2, clipF, max_comm c (2*x1)]
  unfold spec
  rw [hcd, hdd]

theorem net_correct : Statement net := by
  intro x0 x1 h0 h0' h1 h1'
  have hk := key x0 x1 h0 h0' h1 h1'
  simp only [net, Net.eval, Layer.apply, dot, List.foldl, List.map, List.zipWith,
    List.sum_cons, List.sum_nil, List.cons.injEq, and_true]
  push_cast
  rw [← hk]
  simp only [fout, q1, q2, mp, ww, Mn, mm, ss, Bp, DD, CC, tt, V2, B2, A2, r2, r1, n3, n2, n1]
  ring_nf

end Lane4.Case
