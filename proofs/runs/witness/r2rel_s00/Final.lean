namespace Lane4Final
theorem shape : Lane4.Seq.TNet.shapeOK Lane4.Case.net 2 = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_correct
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape

namespace Lane4Final
theorem witness : Lane4.Case.netClose Lane4.Case.net Lane4.Case.netP = true ∧
    Lane4.Case.IsRank [2] 1 2 ∧ |Lane4.Case.netP.out [2] 1 - (2 : ℚ)| ≥ 1 / 2 :=
  ⟨Lane4.Case.witness_close, Lane4.Case.witness_target, Lane4.Case.witness_off⟩
end Lane4Final
#print axioms Lane4Final.witness
