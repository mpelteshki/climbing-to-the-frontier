import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 2. -/
theorem maximumDepth_2 : MaximumDepth 2 0 := by
  constructor
  · exact upper_of_check (p := 2) (by decide) (by cbv)
  · refine ⟨[2], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 2) (by decide) (by cbv)
#print axioms maximumDepth_2
end ProofPursuit.P3
