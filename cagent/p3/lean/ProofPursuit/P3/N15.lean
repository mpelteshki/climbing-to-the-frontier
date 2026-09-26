import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 15. -/
theorem maximumDepth_15 : MaximumDepth 15 20 := by
  constructor
  · exact upper_of_check (p := 5) (by decide) (by cbv)
  · refine ⟨[4, 4, 3, 2, 1, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 5) (by decide) (by cbv)
#print axioms maximumDepth_15
end ProofPursuit.P3
