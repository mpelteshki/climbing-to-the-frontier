import ProofPursuit.P3.Enumeration

namespace ProofPursuit.P3

/-- A one-card fixed point has exact depth zero, so depth one is rejected. -/
theorem one_card_not_depth_one : ¬ DepthExactly [1] 1 := by
  intro h
  apply h.2 0 (by decide)
  exact ⟨1, by decide, by decide⟩

example : exactCheck [1] 1 1 = false := by decide

#print axioms one_card_not_depth_one

end ProofPursuit.P3
