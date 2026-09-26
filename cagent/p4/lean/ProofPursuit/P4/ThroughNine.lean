import ProofPursuit.P4.Progress
import ProofPursuit.P4.Nine
import ProofPursuit.P4.CommonPrime
namespace ProofPursuit.P4.ThroughNine
/-- The common-parity obstruction discharges the last premise of Nine.step. -/
theorem nine : Statement 9 := by
  apply Nine.step Seven.solution (Eight.step Seven.solution)
  intro a m hm hd hn
  apply no_common_two_nine Five.solution a m hm hd
  intro i j hij
  exact (bounds hm hd hn hij).2
/-- Unconditional contiguous progress beyond the full C3 requirement. -/
theorem solution : ∀ k : Nat, 2 ≤ k → k ≤ 9 → Statement k := by
  intro k hlo hhi
  by_cases h : k ≤ 8
  · exact Progress.solution k hlo h
  · have : k = 9 := by omega
    subst k
    exact nine
#print axioms solution
end ProofPursuit.P4.ThroughNine
