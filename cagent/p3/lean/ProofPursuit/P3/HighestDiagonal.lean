import ProofPursuit.P3.DiagonalOrder

namespace ProofPursuit.P3

/-- Highest occupied diagonal for a positive partition; zero for the empty one. -/
def highestDiagonal : State → Nat
  | [] => 0
  | a :: s => max a (highestDiagonal s + 1)

theorem length_le_highestDiagonal (s : State) : s.length ≤ highestDiagonal s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    have hm := Nat.le_max_right a (highestDiagonal s+1)
    simp only [highestDiagonal, List.length_cons]
    omega

theorem height_add_index_le {s : State} {j : Nat} (hj : j < s.length) :
    height s j + j ≤ highestDiagonal s := by
  induction s generalizing j with
  | nil => simp at hj
  | cons a s ih =>
    cases j with
    | zero => simp [height, highestDiagonal, Nat.le_max_left]
    | succ j =>
      have h : height s j + j ≤ highestDiagonal s :=
        ih (by simp only [List.length_cons] at hj; omega)
      have hm := Nat.le_max_right a (highestDiagonal s+1)
      simp only [height, highestDiagonal]
      omega

theorem highestDiagonal_attained {s : State} (hp : ∀ a ∈ s, 0 < a) (hne : s ≠ []) :
    ∃ j, j < s.length ∧ highestDiagonal s = height s j + j := by
  induction s with
  | nil => exact False.elim (hne rfl)
  | cons a s ih =>
    have ha := hp a (by simp)
    have hs : ∀ b ∈ s, 0 < b := by intro b hb; exact hp b (by simp [hb])
    by_cases hm : highestDiagonal s+1 ≤ a
    · refine ⟨0, by simp, ?_⟩
      simp [highestDiagonal, height, Nat.max_eq_left hm]
    · have hn : s ≠ [] := by
        intro he
        simp [he, highestDiagonal] at hm
        omega
      obtain ⟨j, hj, he⟩ := ih hs hn
      refine ⟨j+1, by simp only [List.length_cons]; omega, ?_⟩
      rw [highestDiagonal, Nat.max_eq_right (by omega), he]
      simp [height, Nat.add_assoc]

theorem cyclic_height_bounds {n : Nat} {s : State} (hp : IsPartition n s)
    (hc : Cyclic s) :
    ∀ j, j < highestDiagonal s →
      highestDiagonal s - 1 - j ≤ height s j ∧ height s j ≤ highestDiagonal s - j := by
  intro j hj
  have hu : height s j ≤ highestDiagonal s-j := by
    by_cases hlen : j < s.length
    · have := height_add_index_le hlen
      omega
    · have hz := height_pos_iff hp.2.1 j
      omega
  refine ⟨?_, hu⟩
  by_cases hsmall : j < highestDiagonal s-1
  · have hn : s ≠ [] := by
      intro he
      simp [he, highestDiagonal] at hj
    obtain ⟨q, hq, he⟩ := highestDiagonal_attained hp.2.1 hn
    have hlen := length_le_highestDiagonal s
    have hw : 0 < highestDiagonal s-1 := by omega
    have hcard : diagonalCell s ((highestDiagonal s-1)+1) q := by
      unfold diagonalCell
      omega
    have hf := lower_diagonal_filled_of_upper_cell hp hc hw (by omega) hcard j hsmall
    exact hf
  · omega

#print axioms cyclic_height_bounds
end ProofPursuit.P3
