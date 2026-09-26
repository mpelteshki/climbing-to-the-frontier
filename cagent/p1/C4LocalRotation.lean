import C4Geometry
import C4SignedSparse

open scoped InnerProductSpace

namespace C4LocalRotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If a line can move in an orthonormal plane while preserving every old
orthogonality, a maximal sum of its angles to a finite family can be preserved
while creating a new orthogonality. -/
theorem add_orthogonality {ι : Type*} [Fintype ι]
    (x y : E) (z : ι → E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℝ = 0)
    (hz : ∀ i, ‖z i‖ = 1)
    (hactive : ∃ i, ⟪x, z i⟫_ℝ ≠ 0)
    (hpreserve : ∀ i, ⟪x, z i⟫_ℝ = 0 → ⟪y, z i⟫_ℝ = 0)
    (hmax : ∀ t : ℝ,
      (∑ i, Real.arccos |⟪C4Geometry.rotation x y t, z i⟫_ℝ|) ≤
      ∑ i, Real.arccos |⟪x, z i⟫_ℝ|) :
    ∃ t : ℝ, ‖C4Geometry.rotation x y t‖ = 1 ∧
      (∑ i, Real.arccos |⟪C4Geometry.rotation x y t, z i⟫_ℝ|) =
        (∑ i, Real.arccos |⟪x, z i⟫_ℝ|) ∧
      (∀ i, ⟪x, z i⟫_ℝ = 0 → ⟪C4Geometry.rotation x y t, z i⟫_ℝ = 0) ∧
      ∃ i, ⟪x, z i⟫_ℝ ≠ 0 ∧ ⟪C4Geometry.rotation x y t, z i⟫_ℝ = 0 := by
  have hcoeff : ∀ i, ⟪x, z i⟫_ℝ ^ 2 + ⟪y, z i⟫_ℝ ^ 2 ≤ 1 :=
    fun i => C4Geometry.bessel_two x y (z i) hx hy hxy (hz i)
  have hmax' : ∀ t : ℝ,
      (∑ i, Real.arccos |⟪x, z i⟫_ℝ * Real.cos t + ⟪y, z i⟫_ℝ * Real.sin t|) ≤
        ∑ i, Real.arccos |⟪x, z i⟫_ℝ| := by
    intro t
    simpa only [C4Geometry.inner_rotation] using hmax t
  obtain ⟨t, ht, hold, i, hi, hnew⟩ := C4SignedSparse.coefficient_endpoint
    (fun i => ⟪x, z i⟫_ℝ) (fun i => ⟪y, z i⟫_ℝ)
    hactive hpreserve hcoeff hmax'
  refine ⟨t, C4Geometry.rotation_unit x y t hx hy hxy, ?_, ?_, i, hi, ?_⟩
  · simpa only [C4Geometry.inner_rotation] using ht
  · intro j hj
    simpa only [C4Geometry.inner_rotation] using hold j hj
  · simpa only [C4Geometry.inner_rotation] using hnew

#print axioms add_orthogonality
end C4LocalRotation
