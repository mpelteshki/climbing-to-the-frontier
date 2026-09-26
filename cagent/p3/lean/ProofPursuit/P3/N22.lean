import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 22. -/
theorem maximumDepth_22 : MaximumDepth 22 24 := by
  constructor
  · exact upper_of_check (p := 7) (by decide) (by cbv)
  · refine ⟨[5, 5, 4, 3, 2, 2, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 7) (by decide) (by cbv)
#print axioms maximumDepth_22
end ProofPursuit.P3
