namespace Lane4.Case
open Lane4.RSeq (Vec)
open Lane4.RSoft Lane4.AGate
open Lane4.Seq (Mask cand tokAt)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

/-! ### The network.  State: [E1,E2,E3,P1,P2,P3,Y]. -/

def z7 : List ℚ := [0, 0, 0, 0, 0, 0, 0]
def A7 : List (List ℚ) := [z7, z7, z7, z7, z7, z7, z7]
def cr3 : List ℚ := [1/5, 0, 0, 0, 0, 0, 0]
def cr4 : List ℚ := [0, 1/5, 0, 0, 0, 0, 0]
def cr5 : List ℚ := [0, 0, 1/5, 0, 0, 0, 0]
def vrow : List ℚ := [0, 4/5, 2/5, 0, 0, 0, 0]

def head1 : AHead :=
  { A := A7, V := [z7, z7, z7, cr3, cr4, cr5, z7], mask := Mask.strict, m := 32,
    g := z7, gb := -1 }

def block0 : ABlock :=
  { heads := [head1], W1 := [], b1 := [], W2 := [[], [], [], [], [], [], []], b2 := z7 }

def hd1 : AHead :=
  { A := A7, V := [vrow, z7, z7, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, -1, 0, 0, 0], gb := 1/2 }
def hd2 : AHead :=
  { A := A7, V := [z7, vrow, z7, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, 0, -1, 0, 0], gb := 1/2 }
def hd3 : AHead :=
  { A := A7, V := [z7, z7, vrow, z7, z7, z7, z7], mask := Mask.causal, m := 32,
    g := [0, 0, 0, 0, 0, -1, 0], gb := 1/2 }

def block1 : ABlock :=
  { heads := [hd1, hd2, hd3],
    W1 := [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0]],
    b1 := [-9/2, -9/2, -9/2],
    W2 := [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [1, 1, 1]],
    b2 := z7 }

def net : ANet :=
  { embed := [z7, [5, 0, 0, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [0, 0, 5, 0, 0, 0, 0]],
    blocks := [block0, block1], outW := [0, 0, 0, 0, 0, 0, 1/2], outB := -1/4 }

theorem shape_chk : ANet.shapeOK net 3 = true := by decide

/-- The embedding row of a token `t ≤ 3`. -/
theorem embed_row {t : ℕ} (ht : t ≤ 3) : net.embed.getD t [] =
    [if t = 1 then 5 else 0, if t = 2 then 5 else 0, if t = 3 then 5 else 0, 0, 0, 0, 0] := by
  interval_cases t <;> first | rfl | simp [net, z7]

theorem tok_le (w : List ℕ) (hw : ∀ t ∈ w, 1 ≤ t ∧ t ≤ 3) (j : ℕ) : tokAt w j ≤ 3 := by
  rcases Lane4.Seq.tokAt_zero_or_mem w j with h | h
  · omega
  · exact (hw _ h).2

theorem init_eq (fl : ℝ → ℝ) (p : APert) (w : List ℕ) (j : ℕ) (h : tokAt w j ≤ 3) :
    net.init fl p w j =
      [asw fl (if tokAt w j = 1 then 5 else 0) (p.E (tokAt w j) 0),
       asw fl (if tokAt w j = 2 then 5 else 0) (p.E (tokAt w j) 1),
       asw fl (if tokAt w j = 3 then 5 else 0) (p.E (tokAt w j) 2),
       asw fl 0 (p.E (tokAt w j) 3), asw fl 0 (p.E (tokAt w j) 4),
       asw fl 0 (p.E (tokAt w j) 5), asw fl 0 (p.E (tokAt w j) 6)] := by
  show aswRow fl (net.embed.getD (tokAt w j) []) (p.E (tokAt w j)) 0 = _
  rw [embed_row h]
  rfl

end Lane4.Case
