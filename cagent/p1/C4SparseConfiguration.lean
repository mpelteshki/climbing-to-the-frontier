import C4NeighborCount

namespace C4SparseConfiguration

open C4Configuration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]

/-- An angle-maximizing configuration can be chosen so that each line has at
most `n - dim E` nonorthogonal neighbors. -/
theorem exists_sparse_maximizer {n : ℕ} (hdn : Module.finrank ℝ E ≤ n)
    (u : UnitVector E) :
    ∃ v : Configuration E n,
      (∀ w : Configuration E n, totalAngle w ≤ totalAngle v) ∧
      (∀ w : Configuration E n, totalAngle w = totalAngle v →
        orthogonalityCount w ≤ orthogonalityCount v) ∧
      ∀ i : Fin n, (C4NeighborCount.nonorthogonalNeighbors v i).card ≤
        n - Module.finrank ℝ E := by
  obtain ⟨v, hmax, hselect⟩ := exists_lex_max (n := n) u
  refine ⟨v, hmax, hselect, ?_⟩
  exact C4NeighborCount.nonorthogonal_neighbors_le v hdn
    (fun i hi => C4MaximalSparse.orthogonalNeighbor_finrank v i hmax hselect hi)

/-- The C4 reduction to a nonorthogonality graph of maximum degree two. -/
theorem exists_degree_two_maximizer (u : UnitVector E) :
    ∃ v : Configuration E (Module.finrank ℝ E + 2),
      (∀ w : Configuration E (Module.finrank ℝ E + 2), totalAngle w ≤ totalAngle v) ∧
      ∀ i, (C4NeighborCount.nonorthogonalNeighbors v i).card ≤ 2 := by
  obtain ⟨v, hmax, _, hdegree⟩ :=
    exists_sparse_maximizer (n := Module.finrank ℝ E + 2) (by omega) u
  refine ⟨v, hmax, ?_⟩
  simpa using hdegree

#print axioms exists_sparse_maximizer
#print axioms exists_degree_two_maximizer
end C4SparseConfiguration
