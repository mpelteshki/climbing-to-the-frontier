import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 7. -/
theorem maximumDepth_7 : MaximumDepth 7 4 := by
  constructor
  · exact upper_of_check (p := 4) (by decide) (by cbv)
  · refine ⟨[1, 1, 1, 1, 1, 1, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 4) (by decide) (by cbv)
#print axioms maximumDepth_7
end ProofPursuit.P3
