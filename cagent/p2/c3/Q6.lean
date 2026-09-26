import Fast

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Hypercube
def q6 : List Nat := [0, 15, 51, 60, 1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31, 32, 35, 37, 38, 41, 42, 44, 47, 49, 50, 52, 55, 56, 59, 61, 62, 3, 5, 6, 9, 10, 12, 17, 18, 20, 23, 24, 27, 29, 30, 33, 34, 36, 39, 40, 43, 45, 46, 48, 53, 54, 57, 58, 63]
theorem q6_labelling : IsLabelling 6 q6 := by unfold IsLabelling; decide
theorem q6_count : pathCount 6 q6 = 204 := by
  rw [fast_count 6 q6 q6_labelling]
  decide
theorem q6_witness : ∃ order, IsLabelling 6 order ∧ pathCount 6 order = 204 :=
  ⟨q6, q6_labelling, q6_count⟩
#print axioms q6_labelling
#print axioms q6_count
#print axioms q6_witness
end Hypercube
