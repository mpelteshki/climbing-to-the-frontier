import C4MaximalSparse
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Card

open scoped InnerProductSpace

namespace C4NeighborCount

open C4Configuration C4MaximalSparse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def nonorthogonalNeighbors {n : ℕ}
    (v : Configuration E n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ ⟪(v i).1, (v j).1⟫_ℝ ≠ 0)

theorem neighbor_span_finrank_le_zero_count {n : ℕ}
    (v : Configuration E n) (i : Fin n) :
    Module.finrank ℝ (orthogonalNeighborSpan v i) ≤
      (Finset.univ.filter (fun j : Fin n =>
        ⟪(v i).1, (v j).1⟫_ℝ = 0)).card := by
  classical
  have hcard : Fintype.card {j : Fin n // ⟪(v i).1, (v j).1⟫_ℝ = 0} =
      (Finset.univ.filter (fun j : Fin n =>
        ⟪(v i).1, (v j).1⟫_ℝ = 0)).card := by
    rw [Fintype.card_subtype]
  have h := finrank_range_le_card (R := ℝ)
    (fun j : {j : Fin n // ⟪(v i).1, (v j).1⟫_ℝ = 0} => (v j.1).1)
  rw [hcard] at h
  convert h using 1
  rfl

theorem nonorthogonal_neighbors_le {n d : ℕ} (v : Configuration E n)
    (hdn : d ≤ n)
    (hrank : ∀ i : Fin n, (∃ j : Fin n,
        j ≠ i ∧ ⟪(v i).1, (v j).1⟫_ℝ ≠ 0) →
      d ≤ Module.finrank ℝ (orthogonalNeighborSpan v i) + 1)
    (i : Fin n) : (nonorthogonalNeighbors v i).card ≤ n - d := by
  classical
  let P : Fin n → Prop := fun j => ⟪(v i).1, (v j).1⟫_ℝ = 0
  let Z := Finset.univ.filter P
  let N := Finset.univ.filter (fun j => ¬ P j)
  have hself : ¬ P i := by
    dsimp [P]
    rw [real_inner_self_eq_norm_sq, unit_norm (v i)]
    norm_num
  have hiN : i ∈ N := by simp [N, hself]
  have hdegree : (nonorthogonalNeighbors v i).card + 1 = N.card := by
    have hset : nonorthogonalNeighbors v i = N.erase i := by
      ext j
      simp [nonorthogonalNeighbors, N, P, Finset.mem_erase]
    rw [hset]
    exact Finset.card_erase_add_one hiN
  have hpartition : Z.card + N.card = n := by
    simpa [Z, N, P] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) P)
  by_cases hactive : ∃ j : Fin n,
      j ≠ i ∧ ⟪(v i).1, (v j).1⟫_ℝ ≠ 0
  · have hspan := neighbor_span_finrank_le_zero_count v i
    have hlower := hrank i hactive
    change Module.finrank ℝ (orthogonalNeighborSpan v i) ≤ Z.card at hspan
    omega
  · have hempty : nonorthogonalNeighbors v i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hactive ⟨j, (Finset.mem_filter.mp hj).2⟩
    simp [hempty]

#print axioms C4NeighborCount.neighbor_span_finrank_le_zero_count
#print axioms C4NeighborCount.nonorthogonal_neighbors_le

end C4NeighborCount
