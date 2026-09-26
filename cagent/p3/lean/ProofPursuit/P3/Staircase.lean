import ProofPursuit.P3.Basic

namespace ProofPursuit.P3

@[simp] theorem mem_insert {a x : Nat} {s : State} : x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  induction s with
  | nil => simp [insert]
  | cons b s ih =>
    simp only [insert]
    split <;> simp_all [or_left_comm]

@[simp] theorem mem_sort {x : Nat} {s : State} : x ∈ sort s ↔ x ∈ s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [sort, ih]

theorem insert_sorted (a : Nat) {s : State} (h : s.Pairwise (· ≥ ·)) :
    (insert a s).Pairwise (· ≥ ·) := by
  induction s with
  | nil => simp [insert]
  | cons b s ih =>
    obtain ⟨hb, ht⟩ := List.pairwise_cons.mp h
    simp only [insert]
    split
    next hab =>
      apply List.pairwise_cons.mpr
      constructor
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hab
        · have := hb x hx; omega
      · exact List.pairwise_cons.mpr ⟨hb, ht⟩
    next hab =>
      apply List.pairwise_cons.mpr
      constructor
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · omega
        · exact hb x hx
      · exact ih ht

theorem sort_sorted (s : State) : (sort s).Pairwise (· ≥ ·) := by
  induction s with
  | nil => simp [sort]
  | cons a s ih => exact insert_sorted a ih

theorem sort_of_sorted {s : State} (h : s.Pairwise (· ≥ ·)) : sort s = s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    simp only [sort, ih ht]
    cases s with
    | nil => rfl
    | cons b tail => simp [insert, ha b (by simp)]

theorem step_isPartition {n : Nat} {s : State} (h : IsPartition n s) :
    IsPartition n (step s) := by
  refine ⟨(step_sum s h.2.1).trans h.1, ?_, sort_sorted _⟩
  intro a ha
  simp only [step, mem_sort, List.mem_filter] at ha
  exact of_decide_eq_true ha.2

def staircase : Nat → State
  | 0 => []
  | k+1 => (k+1) :: staircase k

@[simp] theorem staircase_length (k : Nat) : (staircase k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [staircase, ih]

theorem staircase_bounds {k a : Nat} (h : a ∈ staircase k) : 0 < a ∧ a ≤ k := by
  induction k with
  | zero => simp [staircase] at h
  | succ k ih =>
    simp only [staircase, List.mem_cons] at h
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem staircase_sorted (k : Nat) : (staircase k).Pairwise (· ≥ ·) := by
  induction k with
  | zero => simp [staircase]
  | succ k ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro a ha
    have := staircase_bounds ha
    omega

theorem staircase_predecessors (k : Nat) :
    ((staircase (k+1)).map (· - 1)) = staircase k ++ [0] := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [staircase, List.map_cons] using congrArg (List.cons (k+1)) ih

theorem staircase_filter (k : Nat) : (staircase k).filter (· > 0) = staircase k := by
  apply List.filter_eq_self.mpr
  intro a ha
  exact decide_eq_true (staircase_bounds ha).1

theorem staircase_fixed (k : Nat) : step (staircase k) = staircase k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [step, staircase_length, staircase_predecessors, List.filter_cons,
      List.filter_append, staircase_filter]
    simpa [staircase] using sort_of_sorted (staircase_sorted (k+1))

theorem staircase_sum_twice (k : Nat) : 2 * (staircase k).sum = k*(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [staircase, List.sum_cons, Nat.mul_add, Nat.add_mul] at *
    omega

theorem staircase_partition (k : Nat) : IsPartition (k*(k+1)/2) (staircase k) := by
  refine ⟨?_, ?_, staircase_sorted k⟩
  · have := staircase_sum_twice k; omega
  · intro a ha; exact (staircase_bounds ha).1

theorem staircase_cyclic (k : Nat) : Cyclic (staircase k) :=
  ⟨1, by decide, by simp [run, staircase_fixed]⟩

#print axioms staircase_fixed
#print axioms staircase_partition
#print axioms staircase_cyclic
#print axioms step_isPartition
end ProofPursuit.P3
