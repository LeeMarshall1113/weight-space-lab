namespace Lane4Final
theorem shape : Lane4.RSeq.TNet.shapeOK Lane4.Case.net 3 = true := by decide
theorem final : Lane4.Case.Statement Lane4.Case.net := Lane4.Case.net_ok
end Lane4Final
#print axioms Lane4Final.final
#print axioms Lane4Final.shape
