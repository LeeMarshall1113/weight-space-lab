set_option linter.unusedVariables false
set_option linter.style.longLine false
namespace Lane4.Case
open Lane4.RSeq Lane4.RSoft
open Lane4.Seq (Mask cand tokAt)

def z6 : List ℚ := [0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z6, z6, z6, [0, 0, 0, 0, -20, 0], [-120, -60, 0, 0, 0, 0], z6],
    V := [z6, z6, [0, 0, 1, 0, 0, 0], z6, z6, z6],
    mask := Mask.causal }

def blk : Block :=
  { heads := [hd], W1 := [[0, 0, 1, 0, 0, 0]], b1 := [-1],
    W2 := [[0], [0], [-2], [0], [0], [0]], b2 := z6 }

def net : TNet :=
  { embed := [[0, 1, 0], [0, 0, 0], [1, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 1]],
    blocks := [blk],
    outW := [0, 0, 1, 0, 0, 0],
    outB := 0 }

def uq (t : ℕ) : ℚ := if t = 2 then 1 else 0
def bq (t : ℕ) : ℚ := if t = 0 then 1 else 0
def fq (t : ℕ) : ℚ := if t = 5 then 1 else 0

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) : tokAt w j ≤ 5 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (j : ℕ) :
    net.init fl p w j = [sw fl (uq (tokAt w j)) (p.E (tokAt w j) 0),
      sw fl (bq (tokAt w j)) (p.E (tokAt w j) 1),
      sw fl (fq (tokAt w j)) (p.E (tokAt w j) 2)] ++ pos fl j (w.length + 1) := by
  have h5 := tok_le w hw j
  have h6 : tokAt w j = 0 ∨ tokAt w j = 1 ∨ tokAt w j = 2 ∨ tokAt w j = 3 ∨ tokAt w j = 4
      ∨ tokAt w j = 5 := by omega
  rcases h6 with h | h | h | h | h | h <;>
    simp [TNet.init, net, swRow, h, uq, bq, fq, sw_zero hr]

theorem zrow_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (a b c e f g : ℝ) :
    rdot fl z6 [a, b, c, e, f, g] d 0 0 = 0 := by
  simp [z6, rdot, sw_zero hr, hr.zero]

noncomputable def R4 (fl : ℝ → ℝ) (d : ℕ → ℝ) (v : Vec) : ℝ :=
  rdot fl [-120, -60, 0, 0, 0, 0] v d 0 0

theorem r4_fold (fl : ℝ → ℝ) (d : ℕ → ℝ) (v : Vec) :
    rdot fl [-120, -60, 0, 0, 0, 0] v d 0 0 = R4 fl d v := rfl

theorem r3_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (d : ℕ → ℝ) (a b c e f g : ℝ)
    (hP : fl (fl (sw fl (-20) (d 4) * f)) = fl (sw fl (-20) (d 4) * f)) :
    rdot fl [0, 0, 0, 0, -20, 0] [a, b, c, e, f, g] d 0 0 = fl (sw fl (-20) (d 4) * f) := by
  simp [rdot, sw_zero hr, hr.zero, hP]

theorem score_eq {u η M : ℝ} {fl : ℝ → ℝ} (hr : Rnd u η M fl) (dA : ℕ → ℕ → ℝ)
    (a b c I nn x y f K nK : ℝ)
    (hP : fl (fl (sw fl (-20) (dA 3 4) * K)) = fl (sw fl (-20) (dA 3 4) * K))
    (hI : fl (fl (fl (sw fl (-20) (dA 3 4) * K)
        + fl (I * R4 fl (dA 4) [x, y, f, 1, K, nK])))
      = fl (fl (sw fl (-20) (dA 3 4) * K) + fl (I * R4 fl (dA 4) [x, y, f, 1, K, nK]))) :
    hd.score fl dA [a, b, c, 1, I, nn] [x, y, f, 1, K, nK]
      = fl (fl (sw fl (-20) (dA 3 4) * K) + fl (I * R4 fl (dA 4) [x, y, f, 1, K, nK])) := by
  have h3 := r3_eq hr (dA 3) x y f 1 K nK hP
  simp [Head.score, hd, pdot, rmat, zrow_eq hr, h3, r4_fold, hr.zero, hI]

theorem attn_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 5) (i : ℕ) :
    sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, savg fl ex (cand Mask.causal (w.length + 1) i)
              (hscore hd fl (p.A 0 0) (net.init fl p w) i)
              (fun j => rdot fl [0, 0, 1, 0, 0, 0] (net.init fl p w j) (p.V 0 0 2) 0 0),
         0, 0, 0] := by
  have hV : hd.V = [z6, z6, [0, 0, 1, 0, 0, 0], z6, z6, z6] := rfl
  have hm : hd.mask = Mask.causal := rfl
  have hz : ∀ d : ℕ → ℝ,
      savg fl ex (cand Mask.causal (w.length + 1) i)
        (hscore hd fl (p.A 0 0) (net.init fl p w) i)
        (fun j => rdot fl z6 (net.init fl p w j) d 0 0) = 0 := by
    intro d
    apply soft_zeros hr
    intro k _
    simp only [init_eq hr p w hw, pos, List.cons_append, List.nil_append]
    exact zrow_eq hr d _ _ _ _ _ _
  unfold sattn
  rw [hV, hm]
  simp [sattnRows, hz]

theorem out_eq {u η M : ℝ} {fl ex : ℝ → ℝ} (hr : Rnd u η M fl) (p : Pert) (w : List ℕ)
    (i : ℕ) (a b f I nn A : ℝ)
    (hinit : net.init fl p w i = [a, b, f, 1, I, nn])
    (hattn : sattn hd fl ex (p.A 0 0) (p.V 0 0) (w.length + 1) (net.init fl p w) i
      = [0, 0, A, 0, 0, 0])
    (hA : fl A = A)
    (hq1 : fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A))) = fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)))
    (hq2 : fl (fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))
      = fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))
    (hq3 : fl (fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0)))))))
      = fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0))))))) :
    sout net fl ex p w i
      = fl (sw fl 1 (p.oW 2) * fl (fl (f + A) + fl (sw fl (-2) (p.W2 0 2 0) *
        Lane4.relu (fl (fl (sw fl 1 (p.W1 0 0 2) * fl (f + A)) + sw fl (-1) (p.b1 0 0))))))  := by
  have hb : net.blocks = [blk] := rfl
  have ho : net.outW = [0, 0, 1, 0, 0, 0] := rfl
  have hc : net.outB = 0 := rfl
  unfold sout srun
  rw [hb, ho, hc]
  simp only [srunFrom, sblock, blk, sheadsApply, hattn, hinit]
  simp [z6, rdot, radd, raffine, sw_zero hr, hr.zero, hA, hq1, hq2, hq3]

end Lane4.Case
