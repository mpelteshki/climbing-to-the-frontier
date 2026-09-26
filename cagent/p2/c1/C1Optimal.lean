import LowerBound
import Q3
import Q4

namespace Hypercube

theorem q3_optimal :
    ∃ order, IsLabelling 3 order ∧ pathCount 3 order = 14 ∧
      ∀ other, IsLabelling 3 other → 14 ≤ pathCount 3 other :=
  ⟨q3, q3_labelling, q3_count, pathCount_lower3⟩

theorem q4_optimal :
    ∃ order, IsLabelling 4 order ∧ pathCount 4 order = 34 ∧
      ∀ other, IsLabelling 4 other → 34 ≤ pathCount 4 other :=
  ⟨q4, q4_labelling, q4_count, pathCount_lower4⟩

#print axioms q3_optimal
#print axioms q4_optimal

end Hypercube
