namespace Lane4.Case
open Lane4

def L1 : Layer :=
  { W := [[3, 0, -1], [-3, 0, 1], [3, 0, 0], [-3, 0, 0], [0, 3, -1/2]],
    b := [1, -1, 0, 0, 4] }

def L2 : Layer :=
  { W := [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0],
          [1, -1, -1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]],
    b := [0, 0, 0, 0, 0, 0, -5/2] }

def L3 : Layer :=
  { W := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 1, -1, 1, -1, 1]],
    b := [0, 0, 0, 0, 0, 3/2] }

def L4 : Layer :=
  { W := [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0],
          [-1, 1, 1, -1, 2, -1]],
    b := [0, 0, 0, 0] }

def Lo : Layer :=
  { W := [[1, -1, -1, 1]], b := [0] }

def net : Net := { hidden := [L1, L2, L3, L4], out := Lo }

theorem relu_eq' {x y : ℝ} (h : 0 ≤ y) (e : x = y) : relu x = y := by
  subst e; exact relu_of_nonneg h

theorem s1 (x0 x1 x2 : ℝ) : ∃ A An B Bn M : ℝ,
    (L1.apply [x0, x1, x2]).map relu = [A, An, B, Bn, M] ∧ 0 ≤ A ∧ 0 ≤ An ∧ 0 ≤ B ∧ 0 ≤ Bn ∧
    A - An = 3 * x0 + (-1) * x2 + 1 ∧ B - Bn = 3 * x0 ∧
    M = max (3 * x1 + (-1/2) * x2 + (5/2) + 3/2) 0 := by
  refine ⟨relu (3 * x0 + (-1) * x2 + 1), relu (-(3 * x0 + (-1) * x2 + 1)), relu (3 * x0),
    relu (-(3 * x0)), relu (3 * x1 + (-1/2) * x2 + (5/2) + 3/2), ?_,
    le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    relu_sub_relu_neg _, relu_sub_relu_neg _, rfl⟩
  simp only [L1, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨congrArg relu (by ring), congrArg relu (by ring), congrArg relu (by ring),
    congrArg relu (by ring), congrArg relu (by ring)⟩

theorem s2 (A An B Bn M : ℝ) (hA : 0 ≤ A) (hAn : 0 ≤ An) (hB : 0 ≤ B) (hBn : 0 ≤ Bn)
    (hM : 0 ≤ M) : ∃ D E : ℝ,
    (L2.apply [A, An, B, Bn, M]).map relu = [A, An, B, Bn, D, M, E] ∧
    D = max (A - An - B + Bn) 0 ∧ E = max (M - 5/2) 0 := by
  refine ⟨relu (A - An - B + Bn), relu (M - 5/2), ?_, rfl, rfl⟩
  simp only [L2, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨relu_eq' hA (by ring), relu_eq' hAn (by ring), relu_eq' hB (by ring),
    relu_eq' hBn (by ring), congrArg relu (by ring), relu_eq' hM (by ring),
    congrArg relu (by ring)⟩

theorem s3 (A An B Bn D M E : ℝ) (hA : 0 ≤ A) (hAn : 0 ≤ An) (hB : 0 ≤ B) (hBn : 0 ≤ Bn)
    (hD : 0 ≤ D) : ∃ F : ℝ,
    (L3.apply [A, An, B, Bn, D, M, E]).map relu = [A, An, B, Bn, D, F] ∧
    F = max (B - Bn + D - (M - 3/2 - E)) 0 := by
  refine ⟨relu (B - Bn + D - (M - 3/2 - E)), ?_, rfl⟩
  simp only [L3, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨relu_eq' hA (by ring), relu_eq' hAn (by ring), relu_eq' hB (by ring),
    relu_eq' hBn (by ring), relu_eq' hD (by ring), congrArg relu (by ring)⟩

theorem s4 (A An B Bn D F : ℝ) (hA : 0 ≤ A) (hAn : 0 ≤ An) (hD : 0 ≤ D) : ∃ G : ℝ,
    (L4.apply [A, An, B, Bn, D, F]).map relu = [A, An, D, G] ∧
    G = max (-A + An + B - Bn + 2 * D - F) 0 := by
  refine ⟨relu (-A + An + B - Bn + 2 * D - F), ?_, rfl⟩
  simp only [L4, Layer.apply, dot, List.zipWith, List.map, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  refine ⟨relu_eq' hA (by ring), relu_eq' hAn (by ring), relu_eq' hD (by ring),
    congrArg relu (by ring)⟩

theorem core (a b c D F G : ℝ) (eD : D = max (a - b) 0) (eF : F = max (b + D - c) 0)
    (eG : G = max (b + D - F - (a - D)) 0) :
    a - D + G = max (min a b) (min (max a b) c) := by
  subst eG
  subst eF
  subst eD
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem hc (u M E : ℝ) (eM : M = max (u + 3/2) 0) (eE : E = max (M - 5/2) 0) :
    min (max u (-3/2)) 1 = M - 3/2 - E := by
  subst eE
  subst eM
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem key (a b u A An B Bn D M E F G : ℝ) (hAA : A - An = a) (hBB : B - Bn = b)
    (eD : D = max (A - An - B + Bn) 0) (eM : M = max (u + 3/2) 0) (eE : E = max (M - 5/2) 0)
    (eF : F = max (B - Bn + D - (M - 3/2 - E)) 0)
    (eG : G = max (-A + An + B - Bn + 2 * D - F) 0) :
    A - An - D + G = max (min a b) (min (max a b) (min (max u (-3/2)) 1)) := by
  have eD' : D = max (a - b) 0 := by rw [eD]; congr 1; linarith
  have eF' : F = max (b + D - (M - 3/2 - E)) 0 := by rw [eF]; congr 1; linarith
  have eG' : G = max (b + D - F - (a - D)) 0 := by rw [eG]; congr 1; linarith
  have h := core a b (M - 3/2 - E) D F G eD' eF' eG'
  rw [← hc u M E eM eE] at h
  linarith

theorem net_correct : Statement net := by
  intro x0 x1 x2 _ _ _ _ _ _
  obtain ⟨A, An, B, Bn, M, h1, hA, hAn, hB, hBn, eA, eB, eM⟩ := s1 x0 x1 x2
  obtain ⟨D, E, h2, eD, eE⟩ := s2 A An B Bn M hA hAn hB hBn (by rw [eM]; exact le_max_right _ _)
  have hD : 0 ≤ D := by rw [eD]; exact le_max_right _ _
  obtain ⟨F, h3, eF⟩ := s3 A An B Bn D M E hA hAn hB hBn hD
  obtain ⟨G, h4, eG⟩ := s4 A An B Bn D F hA hAn hD
  simp only [net, Net.eval, List.foldl, h1, h2, h3, h4]
  simp only [Lo, Layer.apply, dot, List.zipWith, List.sum_cons, List.sum_nil,
    List.cons.injEq, and_true]
  push_cast
  have hk := key (3 * x0 + (-1) * x2 + 1) (3 * x0) (3 * x1 + (-1/2) * x2 + (5/2))
    A An B Bn D M E F G eA eB eD eM eE eF eG
  have hs : spec x0 x1 x2 = max (min (3 * x0 + (-1) * x2 + 1) (3 * x0))
      (min (max (3 * x0 + (-1) * x2 + 1) (3 * x0))
        (min (max (3 * x1 + (-1/2) * x2 + (5/2)) (-3/2)) 1)) := rfl
  rw [hs]
  linarith

end Lane4.Case
