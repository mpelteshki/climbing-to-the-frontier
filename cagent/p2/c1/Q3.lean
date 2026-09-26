import Fast

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Hypercube
def q3 : List Nat := [0, 1, 2, 4, 7, 3, 5, 6]
theorem q3_labelling : IsLabelling 3 q3 := by unfold IsLabelling; decide
theorem q3_count : pathCount 3 q3 = 14 := by
  rw [fast_count 3 q3 q3_labelling]
  decide
theorem q3_witness : ∃ order, IsLabelling 3 order ∧ pathCount 3 order = 14 :=
  ⟨q3, q3_labelling, q3_count⟩
#print axioms q3_labelling
#print axioms q3_count
#print axioms q3_witness
end Hypercube
