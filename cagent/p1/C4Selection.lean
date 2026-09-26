import Mathlib.Topology.Order.Compact
import Mathlib.Order.Preorder.Finite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace C4Selection

/-- Choose a score maximizer with greatest natural-number complexity among all ties. -/
theorem compact_lex_max {α : Type*} [TopologicalSpace α]
    {K : Set α} {S : α → ℝ} {C : α → ℕ} {M : ℕ}
    (hK : IsCompact K) (hne : K.Nonempty) (hS : ContinuousOn S K)
    (hC : ∀ x ∈ K, C x ≤ M) :
    ∃ x ∈ K, (∀ y ∈ K, S y ≤ S x) ∧
      (∀ y ∈ K, S y = S x → C y ≤ C x) := by
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne hS
  let T : Set α := {y | y ∈ K ∧ S y = S x₀}
  have hTne : T.Nonempty := ⟨x₀, hx₀, rfl⟩
  have hfinite : (C '' T).Finite := by
    apply (Set.finite_Icc 0 M).subset
    rintro n ⟨y, hy, rfl⟩
    exact ⟨Nat.zero_le _, hC y hy.1⟩
  obtain ⟨x, hcx⟩ := Set.Finite.exists_maximalFor' C T hfinite hTne
  have hx : x ∈ K ∧ S x = S x₀ := hcx.1
  refine ⟨x, hx.1, ?_, ?_⟩
  · intro y hy
    rw [hx.2]
    exact hmax hy
  · intro y hy hscore
    have hyT : y ∈ T := ⟨hy, hscore.trans hx.2⟩
    rcases le_total (C y) (C x) with h | h
    · exact h
    · exact hcx.2 hyT h

#print axioms compact_lex_max

end C4Selection
