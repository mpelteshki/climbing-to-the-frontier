import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 1. -/
theorem maximumDepth_1 : MaximumDepth 1 0 := by
  constructor
  · exact upper_of_check (p := 1) (by decide) (by cbv)
  · refine ⟨[1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 1) (by decide) (by cbv)
#print axioms maximumDepth_1
end ProofPursuit.P3
