import Std

namespace ProofPursuit.P3

/-- Abstract bound for a pattern whose predecessor has smaller width.
The application must prove `width_pos` and `retreat` for its own pattern relation. -/
theorem sandwich_start_bound
    (Valid : Nat → Nat → Nat → Prop)
    (width_pos : ∀ p x w, Valid p x w → 2 ≤ w)
    (retreat : ∀ p x w, Valid p x w →
      p ≤ x ∨ ∃ p' x' w', Valid p' x' w' ∧ x' ≤ x ∧ w' < w ∧ p ≤ p' + x) :
    ∀ w p x, Valid p x w → p ≤ x * (w - 1) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro p x hv
    have hw := width_pos p x w hv
    rcases retreat p x w hv with hb | ⟨p', x', w', hv', hx', hw', hp⟩
    · have hm := Nat.mul_le_mul_left x (show 1 ≤ w - 1 by omega)
      simp only [Nat.mul_one] at hm
      omega
    · have hrec := ih w' hw' p' x' hv'
      have hwidth := width_pos p' x' w' hv'
      have hm := Nat.mul_le_mul_right (w' - 1) hx'
      have hs : x * (w' - 1) + x = x * w' := by
        have he : w' - 1 + 1 = w' := by omega
        calc
          x * (w' - 1) + x = x * (w' - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = x * w' := by rw [he]
      have ht := Nat.mul_le_mul_left x (show w' ≤ w - 1 by omega)
      omega

#print axioms sandwich_start_bound
end ProofPursuit.P3
