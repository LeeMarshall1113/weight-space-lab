namespace Lane4Final
theorem final : Lane4.Case.AFRange ∧ Lane4.Case.EmbAF ∧ Lane4.Case.DotAF ∧ Lane4.Case.AffAF ∧ Lane4.Case.AddAF ∧ Lane4.Case.ReluAF ∧ Lane4.Case.ShiftAF :=
  ⟨Lane4.Case.af_range, Lane4.Case.emb_af, Lane4.Case.dot_af, Lane4.Case.aff_af, Lane4.Case.add_af, Lane4.Case.relu_af, Lane4.Case.shift_af⟩
end Lane4Final
#print axioms Lane4Final.final
