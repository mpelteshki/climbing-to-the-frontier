import ProofPursuit.P3.Enumeration
import ProofPursuit.P3.Staircase

namespace ProofPursuit.P3

theorem run_isPartition {n : Nat} {s : State} (h : IsPartition n s) (t : Nat) :
    IsPartition n (run t s) := by
  induction t generalizing s with
  | zero => exact h
  | succ t ih => exact ih (step_isPartition h)

/-- Every partition reaches a cycle before the finite enumeration is exhausted.
This is a general existence bound, not the sharp bounds requested in C2--C5. -/
theorem eventually_cyclic {n : Nat} {s : State} (h : IsPartition n s) :
    ∃ t, t < (partitions n).length ∧ Cyclic (run t s) := by
  classical
  let m := (partitions n).length
  let orbit := (List.range (m+1)).map (fun t => run t s)
  have hsub : orbit ⊆ partitions n := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact partitions_complete (run_isPartition h t)
  have hdup : ¬ orbit.Nodup := by
    intro hn
    have hb := hn.length_le_of_subset hsub
    have hl : orbit.length = m+1 := by simp [orbit]
    change orbit.length ≤ m at hb
    omega
  have hex : ∃ i j, i < m+1 ∧ j < m+1 ∧ i ≠ j ∧ run i s = run j s := by
    apply Classical.byContradiction
    intro hn
    apply hdup
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj he
    have hi' : i < m+1 := by simpa [orbit] using hi
    have hj' : j < m+1 := by simpa [orbit] using hj
    have he' : run i s = run j s := by simpa [orbit] using he
    apply Classical.byContradiction
    intro hne
    exact hn ⟨i, j, hi', hj', hne, he'⟩
  obtain ⟨i, j, hi, hj, hne, he⟩ := hex
  have repeated {a b : Nat} (hab : a < b) (hb : b < m+1)
      (heq : run a s = run b s) :
      ∃ t, t < m ∧ Cyclic (run t s) := by
    refine ⟨a, by omega, b-a, by omega, ?_⟩
    rw [← run_add, Nat.add_sub_of_le (by omega : a ≤ b)]
    exact heq.symm
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact repeated hij hj he
  · exact repeated hji hi he.symm

theorem depth_exists {n : Nat} {s : State} (h : IsPartition n s) :
    ∃ t, t < (partitions n).length ∧ DepthExactly s t := by
  obtain ⟨d, hd, hc⟩ := eventually_cyclic h
  obtain ⟨t, ht, he⟩ := depth_exists_of_cyclic_run hc
  exact ⟨t, by omega, he⟩

#print axioms eventually_cyclic
#print axioms depth_exists
end ProofPursuit.P3
