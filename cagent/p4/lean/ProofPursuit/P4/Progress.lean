import ProofPursuit.P4.C1
import ProofPursuit.P4.C2
import ProofPursuit.P4.Five
import ProofPursuit.P4.Six
import ProofPursuit.P4.Seven
import ProofPursuit.P4.Eight

namespace ProofPursuit.P4.Progress

/-- The k = 2 base case, included to make the certified range contiguous. -/
theorem two : Statement 2 := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have := bounds hm hd hn (by decide : (0 : Fin 2) ≠ 1)
  omega

/-- The complete contiguous range required by P4 C3. -/
def target : Prop := ∀ k : Nat, 2 ≤ k → k ≤ 8 → Statement k

theorem solution : target := by
  intro k hlo hhi
  have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact two
  · exact C1.solution
  · exact C2.solution
  · exact Five.solution
  · exact Six.solution
  · exact Seven.solution
  · exact Eight.step Seven.solution

#print axioms solution
#print axioms C1.solution
#print axioms C2.solution
#print axioms Five.solution
#print axioms Six.solution
#print axioms Seven.solution
#print axioms Eight.step

end ProofPursuit.P4.Progress
