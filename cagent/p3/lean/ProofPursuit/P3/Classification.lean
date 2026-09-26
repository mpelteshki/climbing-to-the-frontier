import ProofPursuit.P3.HighestDiagonal
import ProofPursuit.P3.BoundaryReconstruction

namespace ProofPursuit.P3

/-- Every cyclic partition is a staircase with a binary boundary. -/
theorem cyclic_is_boundary {n : Nat} {s : State} (hp : IsPartition n s)
    (hc : Cyclic s) :
    ∃ bits : List Bool, bits.length = highestDiagonal s ∧ boundary bits = s := by
  exact boundary_of_height_bounds hp.2.1 (length_le_highestDiagonal s)
    (cyclic_height_bounds hp hc)

/-- Complete qualitative characterization; no cycle-count formula is asserted. -/
theorem cyclic_iff_boundary {n : Nat} {s : State} (hp : IsPartition n s) :
    Cyclic s ↔ ∃ bits : List Bool, boundary bits = s := by
  constructor
  · intro hc
    obtain ⟨bits, _, he⟩ := cyclic_is_boundary hp hc
    exact ⟨bits, he⟩
  · rintro ⟨bits, rfl⟩
    exact boundary_cyclic bits

#print axioms cyclic_is_boundary
#print axioms cyclic_iff_boundary
end ProofPursuit.P3
