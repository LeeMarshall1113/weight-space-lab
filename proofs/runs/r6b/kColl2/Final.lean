namespace Lane4Final
theorem final : Lane4.Coll.CollisionBound ∧ Lane4.Coll.CollisionBound' :=
  ⟨Lane4.Case.collision_bound, Lane4.Case.collision_bound'⟩
end Lane4Final
#print axioms Lane4Final.final
