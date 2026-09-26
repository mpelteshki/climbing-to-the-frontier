import Fast

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Hypercube
def q4 : List Nat := [0, 15, 1, 2, 4, 7, 8, 11, 13, 14, 3, 5, 6, 9, 10, 12]
theorem q4_labelling : IsLabelling 4 q4 := by unfold IsLabelling; decide
theorem q4_count : pathCount 4 q4 = 34 := by
  rw [fast_count 4 q4 q4_labelling]
  decide
theorem q4_witness : ∃ order, IsLabelling 4 order ∧ pathCount 4 order = 34 :=
  ⟨q4, q4_labelling, q4_count⟩
#print axioms q4_labelling
#print axioms q4_count
#print axioms q4_witness
end Hypercube
