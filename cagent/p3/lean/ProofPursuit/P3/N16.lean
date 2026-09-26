import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 16. -/
theorem maximumDepth_16 : MaximumDepth 16 15 := by
  constructor
  · exact upper_of_check (p := 6) (by decide) (by cbv)
  · refine ⟨[4, 4, 3, 2, 2, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 6) (by decide) (by cbv)
#print axioms maximumDepth_16
end ProofPursuit.P3
