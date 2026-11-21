import Lane4.R8Cert

namespace Lane4.NetT
open Lane4.Cert

def target (w : List ℕ) (i : ℕ) : ℕ :=
  ((w.getD (i - 1) 0 - 1) + (if 2 ≤ i then w.getD (i - 2) 0 - 1 else 0)) % 5

def task : Task :=
  { ntok := 5, init := 0,
    step := fun _ t => t - 1,
    out := fun s t => ((t - 1) + s) % 5 }

theorem fold_last (w : List ℕ) (k : ℕ) (hk : k < w.length) :
    (w.take (k + 1)).foldl (fun _ t => t - 1) 0 = w.getD k 0 - 1 := by
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem target_eq (w : List ℕ) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w.length) :
    task.target w i = target w i := by
  by_cases h : 2 ≤ i
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    have e := fold_last w k (by omega)
    show ((w.getD (k + 2 - 1) 0 - 1) + (w.take (k + 2 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (k + 2 - 1) 0 - 1) + (if 2 ≤ k + 2 then w.getD (k + 2 - 2) 0 - 1 else 0)) % 5
    rw [if_pos h, show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl, e]
  · have hi : i = 1 := by omega
    subst hi
    show ((w.getD (1 - 1) 0 - 1) + (w.take (1 - 1)).foldl (fun _ t => t - 1) 0) % 5
      = ((w.getD (1 - 1) 0 - 1) + (if 2 ≤ 1 then w.getD (1 - 2) 0 - 1 else 0)) % 5
    simp

end Lane4.NetT
#print axioms Lane4.NetT.target_eq
