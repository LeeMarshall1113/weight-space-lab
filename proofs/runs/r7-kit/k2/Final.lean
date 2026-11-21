namespace Lane4Final
theorem final : Lane4.Case.EmbSound ∧ Lane4.Case.DotSound ∧ Lane4.Case.MatSound ∧ Lane4.Case.AffSound ∧ Lane4.Case.AddSound ∧ Lane4.Case.ReluSound ∧ Lane4.Case.GateSound ∧ Lane4.Case.ScoreSound :=
  ⟨Lane4.Case.emb_sound, Lane4.Case.dot_sound, Lane4.Case.mat_sound, Lane4.Case.aff_sound, Lane4.Case.add_sound, Lane4.Case.relu_sound, Lane4.Case.gate_sound, Lane4.Case.score_sound⟩
end Lane4Final
#print axioms Lane4Final.final
