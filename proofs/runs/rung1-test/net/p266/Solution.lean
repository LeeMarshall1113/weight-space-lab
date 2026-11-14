namespace Lane4.Case
open Lane4

def L1a : Layer :=
  { W := [[-2, 0, 1/2], [2, 0, -1/2], [0, 0, -1/2], [0, 0, 1/2], [-2, 0, 1], [3, -1, 0], [-1, 0, 0], [1, 0, 0]],
    b := [-3/2, 3/2, -1, 1, -1/2, 5, -3, 3] }
def L2a : Layer :=
  { W := [[1, -1, 0, 0, -1, 0, 0, 0], [-1, 1, 0, 0, 1, 0, 0, 0],
          [0, 0, 1, -1, 1, 0, 0, 0], [0, 0, -1, 1, -1, 0, 0, 0],
          [0, 0, 1, -1, 1, -1, -1, 1]],
    b := [0, 0, 0, 0, 0] }
def L3a : Layer :=
  { W := [[-1, 1, 1, -1, -1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0]], b := [0, 0, 0] }
def L4a : Layer :=
  { W := [[1, 1, -1]], b := [0] }

def net : Net :=
  { hidden := [L1a, L2a, L3a, L4a], out := { W := [[1]], b := [0] } }

theorem g1 (x0 x1 x2 a b c d : ℝ) (ha : a = -2 * x0 + 1 / 2 * x2 + -3 / 2)
    (hb : b = -1 / 2 * x2 + -1) (hc : c = 2 * x0 + -1 * x1 + 2) (hd : d = -1 * x0 + -3) :
    (L1a.apply [x0, x1, x2]).map relu =
      [relu a, relu (-a), relu b, relu (-b), relu (a - b), relu (c - d), relu d, relu (-d)] := by
  subst ha hb hc hd
  simp only [L1a, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> ring

theorem g2 (a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    (L2a.apply [a1, a2, a3, a4, a5, a6, a7, a8]).map relu =
      [relu (a1 - a2 - a5), relu (-a1 + a2 + a5), relu (a3 - a4 + a5), relu (-a3 + a4 - a5),
        relu (a3 - a4 + a5 - a6 - a7 + a8)] := by
  simp only [L2a, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> ring

theorem g3 (s1 s2 s3 s4 s5 : ℝ) :
    (L3a.apply [s1, s2, s3, s4, s5]).map relu =
      [relu (-s1 + s2 + s3 - s4 - s5), relu s1, relu s2] := by
  simp only [L3a, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> ring

theorem g4 (w p q : ℝ) :
    (L4a.apply [w, p, q]).map relu = [relu (w + p - q)] := by
  simp only [L4a, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  congr 1
  ring

theorem net_correct : Statement net := by
  intro x0 x1 x2 _ _ _ _ _ _
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = -2 * x0 + 1 / 2 * x2 + -3 / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = -1 / 2 * x2 + -1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * x0 + -1 * x1 + 2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = -1 * x0 + -3 := ⟨_, rfl⟩
  have hsp : spec x0 x1 x2 = max (max (min a b) (min (max a b) (max c d))) 0 := by
    rw [ha, hb, hc, hd]; rfl
  have rr : ∀ x : ℝ, relu (relu x) = relu x := fun x => relu_of_nonneg (le_max_right _ _)
  have hs : relu a - relu (-a) - relu (a - b) = min a b := by
    have h1 := relu_sub_relu_neg a
    have h2 := sub_relu_sub a b
    linarith
  have hs' : -relu a + relu (-a) + relu (a - b) = -min a b := by
    have h1 := relu_sub_relu_neg a
    have h2 := sub_relu_sub a b
    linarith
  have hM : relu b - relu (-b) + relu (a - b) = max a b := by
    have h1 := relu_sub_relu_neg b
    have h2 := add_relu_sub b a
    rw [max_comm a b]
    linarith
  have hM' : -relu b + relu (-b) - relu (a - b) = -max a b := by
    have h1 := relu_sub_relu_neg b
    have h2 := add_relu_sub b a
    rw [max_comm a b]
    linarith
  have hr : relu b - relu (-b) + relu (a - b) - relu (c - d) - relu d + relu (-d)
      = max a b - max c d := by
    have h1 := relu_sub_relu_neg d
    have h2 := add_relu_sub d c
    rw [max_comm c d]
    linarith
  have hw : -relu (min a b) + relu (-min a b) + relu (max a b) - relu (-max a b)
      - relu (max a b - max c d) = min (max a b) (max c d) - min a b := by
    have h1 := relu_sub_relu_neg (min a b)
    have h2 := relu_sub_relu_neg (max a b)
    have h3 := sub_relu_sub (max a b) (max c d)
    linarith
  have h4 : relu (min (max a b) (max c d) - min a b) + relu (min a b) - relu (-min a b)
      = max (min a b) (min (max a b) (max c d)) := by
    have h1 := relu_sub_relu_neg (min a b)
    have h2 := add_relu_sub (min a b) (min (max a b) (max c d))
    linarith
  simp only [net, Net.eval, List.foldl_cons, List.foldl_nil]
  rw [g1 x0 x1 x2 a b c d ha hb hc hd, g2, g3, g4, hsp]
  simp only [Layer.apply, dot, List.zipWith, List.sum_cons, List.sum_nil, List.cons.injEq,
    and_true]
  push_cast
  rw [hr, hs, hs', hM, hM', hw]
  simp only [rr]
  rw [h4]
  simp [relu]
end Lane4.Case
