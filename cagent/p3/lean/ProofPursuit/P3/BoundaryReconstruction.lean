import ProofPursuit.P3.Boundary
import ProofPursuit.P3.CyclicStep

namespace ProofPursuit.P3

private theorem boundary_false_cons (bits : List Bool) (h : 0 < bits.length) :
    boundary (false :: bits) = bits.length :: boundary bits := by
  rw [boundary_cons]
  change ([bits.length].filter (· > 0)) ++ boundary bits = bits.length :: boundary bits
  simp [h]

private theorem boundary_true_cons (bits : List Bool) :
    boundary (true :: bits) = (bits.length+1) :: boundary bits := by
  rw [boundary_cons]
  change ([bits.length+1].filter (· > 0)) ++ boundary bits =
    (bits.length+1) :: boundary bits
  simp

/-- The staircase-width height sandwich determines a binary boundary word. -/
theorem boundary_of_height_bounds {k : Nat} {s : State}
    (hp : ∀ a ∈ s, 0 < a) (hlen : s.length ≤ k)
    (hb : ∀ j, j < k → k-1-j ≤ height s j ∧ height s j ≤ k-j) :
    ∃ bits : List Bool, bits.length = k ∧ boundary bits = s := by
  induction k generalizing s with
  | zero =>
    cases s with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons a tail => simp at hlen
  | succ k ih =>
    cases s with
    | nil =>
      have hk : k = 0 := by
        have h := (hb 0 (by omega)).1
        simp only [height] at h
        omega
      subst k
      exact ⟨[false], by decide, by decide⟩
    | cons a tail =>
      have ha : 0 < a := hp a (by simp)
      have htailPos : ∀ x ∈ tail, 0 < x := by
        intro x hx
        exact hp x (by simp [hx])
      have htailLen : tail.length ≤ k := by
        simp only [List.length_cons] at hlen
        omega
      have htailBounds :
          ∀ j, j < k → k-1-j ≤ height tail j ∧ height tail j ≤ k-j := by
        intro j hj
        have h := hb (j+1) (by omega)
        simp only [height] at h
        constructor <;> omega
      obtain ⟨bits, hbits, hboundary⟩ := ih htailPos htailLen htailBounds
      have hfirst := hb 0 (by omega)
      simp only [height, Nat.sub_zero] at hfirst
      have hchoice : a = k ∨ a = k+1 := by omega
      rcases hchoice with hfalse | htrue
      · have hk : 0 < k := by omega
        refine ⟨false :: bits, by simp [hbits], ?_⟩
        rw [boundary_false_cons bits (by omega), hbits, hboundary, hfalse]
      · refine ⟨true :: bits, by simp [hbits], ?_⟩
        rw [boundary_true_cons bits, hbits, hboundary, htrue]

#print axioms boundary_of_height_bounds

end ProofPursuit.P3
