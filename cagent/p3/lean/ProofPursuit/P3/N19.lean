import ProofPursuit.P3.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ProofPursuit.P3
/-- Exhaustive, kernel-checked upper and lower bounds for n = 19. -/
theorem maximumDepth_19 : MaximumDepth 19 16 := by
  constructor
  · exact upper_of_check (p := 6) (by decide) (by cbv)
  · refine ⟨[5, 4, 3, 3, 2, 1, 1], by unfold IsPartition; decide, ?_⟩
    exact exact_of_check (p := 6) (by decide) (by cbv)
#print axioms maximumDepth_19
end ProofPursuit.P3
