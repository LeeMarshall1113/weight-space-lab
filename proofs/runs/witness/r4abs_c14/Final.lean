namespace Lane4Final
theorem shape : Lane4.RSeq.TNet.shapeOK Lane4.Case.net 5 = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_ok
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape

namespace Lane4Final
theorem witness : Lane4.Case.netNear Lane4.Case.net Lane4.Case.netP = true ∧
    Lane4.Case.target [5, 5, 4, 3, 1, 1, 1, 3, 4, 5, 3, 1, 3, 2, 2, 1, 1, 5, 4, 5, 2, 3] 19 = 2 ∧
    |Lane4.RSeq.TNet.out Lane4.Case.netP (fun x => x) Lane4.QR.pert0 [5, 5, 4, 3, 1, 1, 1, 3, 4, 5, 3, 1, 3, 2, 2, 1, 1, 5, 4, 5, 2, 3] 19 - (2 : ℝ)| > 1 / 4 :=
  ⟨Lane4.Case.witness_near, Lane4.Case.witness_target, Lane4.Case.witness_off⟩
end Lane4Final
#print axioms Lane4Final.witness
