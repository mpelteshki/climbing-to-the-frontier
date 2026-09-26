import Fast

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Hypercube
def q7 : List Nat := [0, 15, 51, 60, 85, 90, 102, 105, 1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31, 32, 35, 37, 38, 41, 42, 44, 47, 49, 50, 52, 55, 56, 59, 61, 62, 64, 67, 69, 70, 73, 74, 76, 79, 81, 82, 84, 87, 88, 91, 93, 94, 97, 98, 100, 103, 104, 107, 109, 110, 112, 115, 117, 118, 121, 122, 124, 127, 3, 5, 6, 9, 10, 12, 17, 18, 20, 23, 24, 27, 29, 30, 33, 34, 36, 39, 40, 43, 45, 46, 48, 53, 54, 57, 58, 63, 65, 66, 68, 71, 72, 75, 77, 78, 80, 83, 86, 89, 92, 95, 96, 99, 101, 106, 108, 111, 113, 114, 116, 119, 120, 123, 125, 126]
theorem q7_labelling : IsLabelling 7 q7 := by unfold IsLabelling; decide
theorem q7_count : pathCount 7 q7 = 464 := by
  rw [fast_count 7 q7 q7_labelling]
  decide
theorem q7_witness : ∃ order, IsLabelling 7 order ∧ pathCount 7 order = 464 :=
  ⟨q7, q7_labelling, q7_count⟩
#print axioms q7_labelling
#print axioms q7_count
#print axioms q7_witness
end Hypercube
