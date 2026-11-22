namespace Lane4Final
theorem final : Lane4.LNC.RsumRel ∧ Lane4.LNC.ArdotRel ∧ Lane4.LNC.PdotRel ∧ Lane4.LNC.DotRelSound ∧ Lane4.LNC.ScoreRelSound :=
  ⟨Lane4.Case.rsum_rel, Lane4.Case.ardot_rel, Lane4.Case.pdot_rel, Lane4.Case.dot_rel_sound, Lane4.Case.score_rel_sound⟩
end Lane4Final
#print axioms Lane4Final.final
