import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 9. -/
theorem maximumDepth_9 : MaximumDepth 9 7 := by
  constructor
  · exact upper_of_check (p := 4) (by decide) (by cbv)
  · refine ⟨[3, 2, 2, 1, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 4) (by decide) (by cbv)
#print axioms maximumDepth_9
end ProofPursuit.P3
