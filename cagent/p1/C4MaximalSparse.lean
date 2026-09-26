import C4Configuration
import C4LocalRotation
import C4Direction
import C4Replacement
import Mathlib.LinearAlgebra.Span.Basic

open scoped InnerProductSpace

namespace C4MaximalSparse

open C4Configuration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem unit_norm (x : UnitVector E) : ‖x.1‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.2

noncomputable def orthogonalNeighborSpan {n : ℕ} (v : Configuration E n) (i : Fin n) :
    Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun j : {j : Fin n // ⟪(v i).1, (v j).1⟫_ℝ = 0} =>
    (v j.1).1))

theorem neighbor_mem_span {n : ℕ} (v : Configuration E n) (i j : Fin n)
    (h : ⟪(v i).1, (v j).1⟫_ℝ = 0) :
    (v j).1 ∈ orthogonalNeighborSpan v i := by
  apply Submodule.subset_span
  exact ⟨⟨j, h⟩, rfl⟩

private theorem replacement_incident {n : ℕ} (v : Configuration E n) (i : Fin n)
    (w : UnitVector E) :
    C4Replacement.incidentAngle (C4Replacement.replacement v i w) i =
      ∑ j : {j : Fin n // j ≠ i}, Real.arccos |⟪w.1, (v j.1).1⟫_ℝ| := by
  classical
  rw [C4Replacement.incidentAngle_eq_sum_neighbors]
  apply Finset.sum_congr rfl
  intro j _
  simp only [C4Replacement.replacement, Function.update_self,
    Function.update_of_ne j.property]

/-- At a maximizer with the largest orthogonality count, a vertex that has a
nonorthogonal neighbor has an orthogonal-neighbor span of codimension at most one. -/
theorem orthogonalNeighbor_finrank [FiniteDimensional ℝ E] {n : ℕ}
    (v : Configuration E n) (i : Fin n)
    (hmax : ∀ w : Configuration E n, totalAngle w ≤ totalAngle v)
    (hselect : ∀ w : Configuration E n, totalAngle w = totalAngle v →
      orthogonalityCount w ≤ orthogonalityCount v)
    (hactive : ∃ j : Fin n, j ≠ i ∧ ⟪(v i).1, (v j).1⟫_ℝ ≠ 0) :
    Module.finrank ℝ E ≤ Module.finrank ℝ (orthogonalNeighborSpan v i) + 1 := by
  classical
  by_contra hn
  have hdim : Module.finrank ℝ (orthogonalNeighborSpan v i) + 1 <
      Module.finrank ℝ E := lt_of_not_ge hn
  obtain ⟨y, hy, hxy, hyW⟩ := C4Direction.exists_unit_orthogonal
    (orthogonalNeighborSpan v i) (v i).1 hdim
  let z : {j : Fin n // j ≠ i} → E := fun j => (v j.1).1
  have hz : ∀ j, ‖z j‖ = 1 := fun j => unit_norm (v j.1)
  have hactive' : ∃ j, ⟪(v i).1, z j⟫_ℝ ≠ 0 := by
    obtain ⟨j, hji, hj⟩ := hactive
    exact ⟨⟨j, hji⟩, hj⟩
  have hpreserve : ∀ j, ⟪(v i).1, z j⟫_ℝ = 0 → ⟪y, z j⟫_ℝ = 0 := by
    intro j hj
    exact hyW (z j) (neighbor_mem_span v i j.1 hj)
  have hstarmax : ∀ t : ℝ,
      (∑ j, Real.arccos |⟪C4Geometry.rotation (v i).1 y t, z j⟫_ℝ|) ≤
        ∑ j, Real.arccos |⟪(v i).1, z j⟫_ℝ| := by
    intro t
    let w : UnitVector E := ⟨C4Geometry.rotation (v i).1 y t, by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        C4Geometry.rotation_unit (v i).1 y t (unit_norm (v i)) hy hxy⟩
    have hb := C4Replacement.incidentAngle_le_of_totalAngle_max v i w hmax
    rw [replacement_incident, C4Replacement.incidentAngle_eq_sum_neighbors] at hb
    exact hb
  obtain ⟨t, hunit, ht, hold, j, hj, hnew⟩ := C4LocalRotation.add_orthogonality
    (v i).1 y z (unit_norm (v i)) hy hxy hz hactive' hpreserve hstarmax
  let w : UnitVector E := ⟨C4Geometry.rotation (v i).1 y t, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hunit⟩
  have hincident : C4Replacement.incidentAngle (C4Replacement.replacement v i w) i =
      C4Replacement.incidentAngle v i := by
    rw [replacement_incident, C4Replacement.incidentAngle_eq_sum_neighbors]
    exact ht
  have hscore : totalAngle (C4Replacement.replacement v i w) = totalAngle v :=
    C4Replacement.totalAngle_replacement_eq_of_incident_eq v i w hincident
  have hstrict : orthogonalityCount v <
      orthogonalityCount (C4Replacement.replacement v i w) := by
    apply C4Replacement.orthogonalityCount_replacement_strict v i w
    · intro k hki hk
      exact hold ⟨k, hki⟩ hk
    · exact ⟨j.1, j.2, hj, hnew⟩
  exact (not_lt_of_ge (hselect (C4Replacement.replacement v i w) hscore)) hstrict

#print axioms neighbor_mem_span
#print axioms orthogonalNeighbor_finrank
end C4MaximalSparse
