import Fast

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Hypercube
def q5 : List Nat := [0, 15, 1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31, 3, 5, 6, 9, 10, 12, 17, 18, 20, 23, 24, 27, 29, 30]
theorem q5_labelling : IsLabelling 5 q5 := by unfold IsLabelling; decide
theorem q5_count : pathCount 5 q5 = 88 := by
  rw [fast_count 5 q5 q5_labelling]
  decide
theorem q5_witness : ∃ order, IsLabelling 5 order ∧ pathCount 5 order = 88 :=
  ⟨q5, q5_labelling, q5_count⟩
#print axioms q5_labelling
#print axioms q5_count
#print axioms q5_witness
end Hypercube
