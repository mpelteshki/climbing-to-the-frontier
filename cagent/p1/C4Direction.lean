import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped InnerProductSpace

namespace C4Direction

/-- If a subspace and one extra vector leave room in a finite-dimensional
real inner-product space, choose a unit vector orthogonal to both. -/
theorem exists_unit_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) (x : E)
    (hdim : Module.finrank ℝ W + 1 < Module.finrank ℝ E) :
    ∃ y : E, ‖y‖ = 1 ∧ ⟪x, y⟫_ℝ = 0 ∧
      ∀ w ∈ W, ⟪y, w⟫_ℝ = 0 := by
  let K : Submodule ℝ E := W ⊔ ℝ ∙ x
  have hspan : Module.finrank ℝ (ℝ ∙ x) ≤ 1 := by
    simpa using (finrank_span_le_card ({x} : Set E))
  have hK : Module.finrank ℝ K ≤ Module.finrank ℝ W + 1 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq W (ℝ ∙ x)
    dsimp [K]
    omega
  have horth : 0 < Module.finrank ℝ Kᗮ := by
    have hdimorth := K.finrank_add_finrank_orthogonal
    omega
  have hne : Kᗮ ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at horth
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let y : E := (‖z‖⁻¹ : ℝ) • z
  have hy : y ∈ Kᗮ := Submodule.smul_mem _ _ hz
  have hynorm : ‖y‖ = 1 := by
    change ‖(‖z‖⁻¹ : ℝ) • z‖ = 1
    convert norm_smul_inv_norm (𝕜 := ℝ) hz0 using 1
  refine ⟨y, hynorm, ?_, ?_⟩
  · have hxK : x ∈ K := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have h := (K.mem_orthogonal' y).mp hy x hxK
    rwa [real_inner_comm] at h
  · intro w hw
    exact (K.mem_orthogonal' y).mp hy w (Submodule.mem_sup_left hw)

#print axioms C4Direction.exists_unit_orthogonal

end C4Direction
