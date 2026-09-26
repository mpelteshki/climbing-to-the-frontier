import ProofPursuit.P3.Energy

namespace ProofPursuit.P3

/-- Column height, extended by zero outside the partition. -/
def height : State → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: s, j+1 => height s j

theorem height_mem_or_zero (s : State) (j : Nat) : height s j ∈ s ∨ height s j = 0 := by
  induction s generalizing j with
  | nil => exact Or.inr rfl
  | cons a s ih =>
    cases j with
    | zero => exact Or.inl (by simp [height])
    | succ j =>
      rcases ih j with hm | hz
      · exact Or.inl (by simp [height, hm])
      · exact Or.inr hz

theorem height_zero_of_all_zero {s : State} (h : ∀ a ∈ s, a = 0) (j : Nat) :
    height s j = 0 := by
  rcases height_mem_or_zero s j with hm | hz
  · exact h _ hm
  · exact hz

theorem height_pos_iff {s : State} (h : ∀ a ∈ s, 0 < a) (j : Nat) :
    0 < height s j ↔ j < s.length := by
  induction s generalizing j with
  | nil => simp [height]
  | cons a s ih =>
    have ha := h a (by simp)
    have hs : ∀ b ∈ s, 0 < b := by intro b hb; exact h b (by simp [hb])
    cases j with
    | zero => simp [height, ha]
    | succ j => simpa [height] using ih hs j

theorem height_filter_positive {s : State} (h : s.Pairwise (· ≥ ·)) (j : Nat) :
    height (s.filter (· > 0)) j = height s j := by
  induction s generalizing j with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp h
    by_cases hz : a = 0
    · have hall : ∀ b ∈ a :: s, b = 0 := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hz
        · have := ha b hb; omega
      rw [height_zero_of_all_zero hall]
      apply height_zero_of_all_zero
      intro b hb
      exact hall b ((List.mem_filter.mp hb).1)
    · have hp : 0 < a := by omega
      cases j with
      | zero => simp [hp, height]
      | succ j => simpa [hp, height] using ih hs j

theorem height_predecessors (s : State) (j : Nat) :
    height (s.map (· - 1)) j = height s j - 1 := by
  induction s generalizing j with
  | nil => rfl
  | cons a s ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem cyclic_rotation_sorted {n : Nat} {s : State} (h : IsPartition n s)
    (hc : Cyclic s) : (s.length :: s.map (· - 1)).Pairwise (· ≥ ·) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    cases s with
    | nil => simp at ha
    | cons b s =>
      have hb := cyclic_head_bound h hc
      have hab : a ≤ b := by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Nat.le_refl _
        · exact (List.pairwise_cons.mp h.2.2).1 a ha
      omega
  · exact h.2.2.map (fun x => x-1) (by intro x y hxy; omega)

theorem cyclic_step_eq_rotation {n : Nat} {s : State} (h : IsPartition n s)
    (hc : Cyclic s) : step s = (s.length :: s.map (· - 1)).filter (· > 0) := by
  exact sort_of_sorted ((cyclic_rotation_sorted h hc).filter _)

theorem height_step_zero {n : Nat} {s : State} (h : IsPartition n s)
    (hc : Cyclic s) : height (step s) 0 = s.length := by
  rw [cyclic_step_eq_rotation h hc, height_filter_positive (cyclic_rotation_sorted h hc)]
  rfl

theorem height_step_succ {n : Nat} {s : State} (h : IsPartition n s)
    (hc : Cyclic s) (j : Nat) : height (step s) (j+1) = height s j - 1 := by
  rw [cyclic_step_eq_rotation h hc, height_filter_positive (cyclic_rotation_sorted h hc)]
  exact height_predecessors s j

#print axioms cyclic_step_eq_rotation
#print axioms height_step_zero
#print axioms height_step_succ
end ProofPursuit.P3
