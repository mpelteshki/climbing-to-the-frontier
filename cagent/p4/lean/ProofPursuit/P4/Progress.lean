import ProofPursuit.P4.C1
import ProofPursuit.P4.C2
import ProofPursuit.P4.Five
import ProofPursuit.P4.Six

namespace ProofPursuit.P4.Progress

/-- The k = 2 base case, included to make the certified range contiguous. -/
theorem two : Statement 2 := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have := bounds hm hd hn (by decide : (0 : Fin 2) ≠ 1)
  omega

/-- This is a partial result for C3. It deliberately does not claim k = 7 or k = 8. -/
def target : Prop := ∀ k : Nat, 2 ≤ k → k ≤ 6 → Statement k

theorem solution : target := by
  intro k hlo hhi
  have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact two
  · exact C1.solution
  · exact C2.solution
  · exact Five.solution
  · exact Six.solution

#print axioms solution
#print axioms C1.solution
#print axioms C2.solution
#print axioms Five.solution
#print axioms Six.solution

end ProofPursuit.P4.Progress
