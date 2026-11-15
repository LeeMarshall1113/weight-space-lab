"""Rung 6c usage example (writeup/NOTE_tokenblind_usage.md): a hand-written network that is
not one of the lab's task networks, checked token-blind by `decide`, with a radius bound
for ITS task (majority) derived from the proved collision theorem.

    python tools/r6c_example.py     -> runs/r6c/example/Example.lean (compile with tools/lean_lease.sh)

The file is runs/r6c/final/R6C.lean (all proofs of rung 6c) followed by the example.
"""
import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
base = open(os.path.join(HERE, "runs", "r6c", "final", "R6C.lean"), encoding="utf-8").read()
base = base[:base.index("#print axioms")]

EX = """namespace Lane4.Example.maj
open Lane4.Seq Lane4.Coll Lane4.TB

/-! A majority network over tokens 1 and 2, written by hand for the usage note.
Embedding: one token coordinate (coordinate 0): token 1 -> 1, token 2 -> -1, BOS -> 0, and
one spare coordinate. One block, one head: zero score matrix, mask `all` (a global uniform
average), value row 1 reads coordinate 0. So coordinate 1 becomes (#1 - #2) / n at every
position, and the read-out reads coordinate 1. The output is positive exactly when token 1
is in the majority (checked numerically for the written weights, not proved here). -/

def z10 : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def hd : Head :=
  { A := [z10, z10, z10, z10, z10, z10, z10, z10, z10, z10],
    V := [z10, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0], z10, z10, z10, z10, z10, z10, z10, z10],
    mask := Mask.all }

def blk : Block :=
  { heads := [hd], W1 := [z10], b1 := [0],
    W2 := [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0]], b2 := z10 }

def net : TNet :=
  { embed := [[0, 0], [1, 0], [-1, 0]],
    blocks := [blk],
    outW := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    outB := 0 }

/-- Step 1 of the usage note: membership is one `decide`. -/
theorem member : tokenBlind net 2 [0] = true := by decide

/-- "Every network in the relative ball of radius τ decides majority (more 1s than 2s) by
the sign of its output at the last position, on every non-empty input over {1, 2} of
length at most L." -/
def MajOnBall (N : TNet) (τ : ℚ) (L : ℕ) : Prop :=
  ∀ N', netRel τ N N' → ∀ w : List ℕ, w ≠ [] → (∀ t ∈ w, 1 ≤ t ∧ t ≤ 2) → w.length ≤ L →
    (0 < N'.out w w.length ↔ w.count 2 < w.count 1)

/-- Step 2: the bound for this network's own task, from the collision theorem. -/
theorem radius (τ : ℚ) (a : ℕ) (h1 : τ ≤ 1) (ha : 1 ≤ a)
    (hb : MajOnBall net τ (2 * a + 1)) : τ * (2 * (a : ℚ) + 1) < 1 := by
  by_contra hcon
  have h : 1 ≤ τ * (2 * (a : ℚ) + 1) := not_lt.mp hcon
  obtain ⟨N₁, N₂, r1, r2, heq⟩ := Lane4Final.collision net 2 [0] 1 2 member
    (by decide) (by decide) (by decide) (by decide) τ a a h1 ha ha h h
  have hl1 : (List.replicate a 1 ++ List.replicate (a + 1) 2).length = 2 * a + 1 := by
    simp; omega
  have hl2 : (List.replicate (a + 1) 1 ++ List.replicate a 2).length = 2 * a + 1 := by
    simp; omega
  have hv1 : ∀ t ∈ List.replicate a 1 ++ List.replicate (a + 1) 2, 1 ≤ t ∧ t ≤ 2 := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht <;> rw [List.eq_of_mem_replicate ht] <;> decide
  have hv2 : ∀ t ∈ List.replicate (a + 1) 1 ++ List.replicate a 2, 1 ≤ t ∧ t ≤ 2 := by
    intro t ht
    simp only [List.mem_append] at ht
    rcases ht with ht | ht <;> rw [List.eq_of_mem_replicate ht] <;> decide
  have hn1 : List.replicate a 1 ++ List.replicate (a + 1) 2 ≠ [] := by
    intro hn
    have := congrArg List.length hn
    simp at this
  have hn2 : List.replicate (a + 1) 1 ++ List.replicate a 2 ≠ [] := by
    intro hn
    have := congrArg List.length hn
    simp at this
  have c1 := hb N₁ r1 _ hn1 hv1 (le_of_eq hl1)
  have c2 := hb N₂ r2 _ hn2 hv2 (le_of_eq hl2)
  have e := heq (2 * a + 1) (by omega)
  rw [hl1] at c1
  rw [hl2] at c2
  rw [e] at c1
  have k11 : (List.replicate a 1 ++ List.replicate (a + 1) 2).count 1 = a := by
    simp [List.count_append, List.count_replicate]
  have k12 : (List.replicate a 1 ++ List.replicate (a + 1) 2).count 2 = a + 1 := by
    simp [List.count_append, List.count_replicate]
  have k21 : (List.replicate (a + 1) 1 ++ List.replicate a 2).count 1 = a + 1 := by
    simp [List.count_append, List.count_replicate]
  have k22 : (List.replicate (a + 1) 1 ++ List.replicate a 2).count 2 = a := by
    simp [List.count_append, List.count_replicate]
  rw [k11, k12] at c1
  rw [k21, k22] at c2
  have key : (a + 1 < a) ↔ (a < a + 1) := c1.symm.trans c2
  omega

end Lane4.Example.maj

#print axioms Lane4.Example.maj.member
#print axioms Lane4.Example.maj.radius
"""
d = os.path.join(HERE, "runs", "r6c", "example")
os.makedirs(d, exist_ok=True)
open(os.path.join(d, "Example.lean"), "w", encoding="utf-8", newline="\n").write(base + EX)
print("wrote", os.path.join(d, "Example.lean"))
