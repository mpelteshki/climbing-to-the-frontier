import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 13. -/
theorem maximumDepth_13 : MaximumDepth 13 9 := by
  constructor
  · exact upper_of_check (p := 5) (by decide) (by cbv)
  · refine ⟨[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 5) (by decide) (by cbv)
#print axioms maximumDepth_13
end ProofPursuit.P3
