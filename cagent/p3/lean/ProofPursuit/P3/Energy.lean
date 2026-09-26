import ProofPursuit.P3.Eventual

namespace ProofPursuit.P3

def triangle : Nat → Nat
  | 0 => 0
  | k+1 => triangle k + (k+1)

/-- Sum of diagonal indices of all cards in the Ferrers diagram. -/
def energy : State → Nat
  | [] => 0
  | a :: s => triangle a + s.sum + energy s

theorem energy_insert_le (a : Nat) (s : State) :
    energy (insert a s) ≤ energy (a :: s) := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons b s ih =>
    simp only [insert]
    split
    · exact Nat.le_refl _
    next hab =>
      simp only [energy, insert_sum, List.sum_cons] at *
      omega

theorem energy_sort_le (s : State) : energy (sort s) ≤ energy s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    have hi := energy_insert_le a (sort s)
    simp only [energy, sort_sum] at hi
    simp only [sort, energy]
    omega

theorem energy_filter_le (s : State) : energy (s.filter (· > 0)) ≤ energy s := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons a s ih =>
    by_cases ha : a = 0
    · simp only [ha, List.filter_cons, Nat.lt_irrefl, decide_false, Bool.false_eq_true,
        ↓reduceIte, energy, triangle]
      omega
    · have hp : 0 < a := by omega
      simp only [List.filter_cons, hp, decide_true, ↓reduceIte, energy,
        sum_filter_positive]
      omega

theorem energy_predecessors (s : State) (h : ∀ a ∈ s, 0 < a) :
    energy s + s.length = energy (s.map (· - 1)) + s.sum + triangle s.length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    have ha := h a (by simp)
    have hs : ∀ b ∈ s, 0 < b := by intro b hb; exact h b (by simp [hb])
    have hi := ih hs
    have hsum := sum_predecessors s hs
    have ht : triangle a = triangle (a-1) + a := by
      cases a with
      | zero => omega
      | succ a => rfl
    simp only [energy, List.length_cons, List.sum_cons, List.map_cons, triangle]
    omega

/-- Before zero deletion and sorting, diagonal rotation preserves energy. -/
theorem energy_rotation (s : State) (h : ∀ a ∈ s, 0 < a) :
    energy (s.length :: s.map (· - 1)) = energy s := by
  have he := energy_predecessors s h
  have hs := sum_predecessors s h
  simp only [energy]
  omega

theorem step_energy_le {n : Nat} {s : State} (h : IsPartition n s) :
    energy (step s) ≤ energy s := by
  unfold step
  have hsort := energy_sort_le ((s.length :: s.map (· - 1)).filter (· > 0))
  have hfilter := energy_filter_le (s.length :: s.map (· - 1))
  have hrotation := energy_rotation s h.2.1
  omega

theorem run_energy_le {n : Nat} {s : State} (h : IsPartition n s) (t : Nat) :
    energy (run t s) ≤ energy s := by
  induction t generalizing s with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    have hi := ih (step_isPartition h)
    have hs := step_energy_le h
    exact Nat.le_trans hi hs

/-- Periodic orbits cannot lose any energy at an individual move. -/
theorem cyclic_energy_constant {n : Nat} {s : State} (h : IsPartition n s)
    (hc : Cyclic s) : energy (step s) = energy s := by
  obtain ⟨p, hp, he⟩ := hc
  cases p with
  | zero => omega
  | succ p =>
    have hback := run_energy_le (step_isPartition h) p
    have hforward := step_energy_le h
    change run p (step s) = s at he
    rw [he] at hback
    omega

theorem energy_insert_lt {a b : Nat} (s : State) (hab : a < b) :
    energy (insert a (b :: s)) < energy (a :: b :: s) := by
  have hi := energy_insert_le a s
  have hnot : ¬ a ≥ b := by omega
  simp only [insert, hnot, ↓reduceIte, energy, insert_sum, List.sum_cons] at *
  omega

/-- A pile taller than one plus the pile count forces strict energy loss. -/
theorem step_energy_lt_of_tall {n a : Nat} {s : State}
    (h : IsPartition n (a :: s)) (htall : (a :: s).length + 1 < a) :
    energy (step (a :: s)) < energy (a :: s) := by
  let l := (a :: s).length
  let tail := (s.map (· - 1)).filter (· > 0)
  have hl : 0 < l := by simp [l]
  have ha : 0 < a-1 := by simp only [List.length_cons] at htall; omega
  have hab : l < a-1 := by change (a :: s).length < a-1; omega
  have hs : ((a-1) :: tail).Pairwise (· ≥ ·) := by
    have hm : ((a :: s).map (fun x => x-1)).Pairwise (· ≥ ·) :=
      h.2.2.map (fun x => x-1) (by intro x y hxy; omega)
    have hf := hm.filter (fun x => decide (x > 0))
    simpa [tail, ha] using hf
  have heq : ((a :: s).length :: (a :: s).map (· - 1)).filter (· > 0) =
      l :: (a-1) :: tail := by simp [tail, l, ha]
  have hst : step (a :: s) = insert l ((a-1) :: tail) := by
    unfold step
    rw [heq]
    change insert l (sort ((a-1) :: tail)) = _
    rw [sort_of_sorted hs]
  have hi := energy_insert_lt tail hab
  have hf := energy_filter_le ((a :: s).length :: (a :: s).map (· - 1))
  rw [heq, energy_rotation (a :: s) h.2.1] at hf
  rw [hst]
  omega

theorem cyclic_head_bound {n a : Nat} {s : State}
    (h : IsPartition n (a :: s)) (hc : Cyclic (a :: s)) :
    a ≤ (a :: s).length + 1 := by
  have he := cyclic_energy_constant h hc
  by_cases hb : a ≤ (a :: s).length + 1
  · exact hb
  · have hl := step_energy_lt_of_tall h (by omega)
    omega

#print axioms step_energy_le
#print axioms cyclic_energy_constant
#print axioms cyclic_head_bound
end ProofPursuit.P3
