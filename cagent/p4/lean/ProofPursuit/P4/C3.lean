import ProofPursuit.P4.Progress

namespace ProofPursuit.P4.C3

/-- Every size from 2 through 8, with no assumption about smaller cases. -/
def target : Prop := ∀ k : Nat, 2 ≤ k → k ≤ 8 → Statement k

theorem solution : target := Progress.solution

#print axioms solution

end ProofPursuit.P4.C3
