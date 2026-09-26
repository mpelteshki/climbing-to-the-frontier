import Std

namespace ProofPursuit.P3

abbrev State := List Nat

def IsPartition (n : Nat) (s : State) : Prop :=
  s.sum = n ∧ (∀ a ∈ s, 0 < a) ∧ s.Pairwise (· ≥ ·)

/-- Structural insertion sort: its computation reduces in the Lean kernel. -/
def insert (a : Nat) : State → State
  | [] => [a]
  | b :: tail => if a ≥ b then a :: b :: tail else b :: insert a tail

def sort : State → State
  | [] => []
  | a :: tail => insert a (sort tail)

theorem insert_sum (a : Nat) (s : State) : (insert a s).sum = a + s.sum := by
  induction s with
  | nil => simp [insert]
  | cons b s ih =>
    simp only [insert]
    split <;> simp_all [List.sum_cons, Nat.add_left_comm]

theorem sort_sum (s : State) : (sort s).sum = s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [sort, insert_sum, ih]

def step (s : State) : State :=
  sort ((s.length :: s.map (· - 1)).filter (· > 0))

def run : Nat → State → State
  | 0, s => s
  | t + 1, s => run t (step s)

def Cyclic (s : State) : Prop := ∃ p, 0 < p ∧ run p s = s

def DepthExactly (s : State) (d : Nat) : Prop :=
  Cyclic (run d s) ∧ ∀ t, t < d → ¬ Cyclic (run t s)

def MaximumDepth (n d : Nat) : Prop :=
  (∀ s, IsPartition n s → ∃ t, t ≤ d ∧ DepthExactly s t) ∧
  ∃ s, IsPartition n s ∧ DepthExactly s d

@[simp] theorem run_zero (s : State) : run 0 s = s := rfl
@[simp] theorem run_succ (t : Nat) (s : State) : run (t+1) s = run t (step s) := rfl

theorem run_add (a b : Nat) (s : State) : run (a+b) s = run b (run a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih => simpa [Nat.succ_add, run] using ih (step s)

theorem run_comm (a b : Nat) (s : State) : run a (run b s) = run b (run a s) := by
  rw [← run_add, ← run_add, Nat.add_comm]

theorem run_multiple {p : Nat} {s : State} (h : run p s = s) (q : Nat) :
    run (p*q) s = s := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, run_add, ih, h]

/-- On a periodic orbit, any period visible later is already a period now. -/
theorem period_backwards {s : State} {d p : Nat} (hc : Cyclic s)
    (h : run p (run d s) = run d s) : run p s = s := by
  obtain ⟨q, hq, hqcycle⟩ := hc
  have hlarge : d ≤ q * (d+1) := by
    have := Nat.mul_le_mul_right (d+1) hq
    omega
  let z := q * (d+1) - d
  have hz : run z (run d s) = s := by
    rw [← run_add]
    have he : d + z = q * (d+1) := by dsimp [z]; omega
    rw [he]
    exact run_multiple hqcycle (d+1)
  calc
    run p s = run p (run z (run d s)) := by rw [hz]
    _ = run z (run p (run d s)) := run_comm p z _
    _ = s := by rw [h, hz]

/-- A finite, positive-period test proves an exact transient length. -/
theorem depth_of_period_checks {s : State} {d p : Nat} (hp : 0 < p)
    (hfinal : run p (run d s) = run d s)
    (hearlier : ∀ t, t < d → run p (run t s) ≠ run t s) : DepthExactly s d := by
  constructor
  · exact ⟨p, hp, hfinal⟩
  · intro t ht hc
    apply hearlier t ht
    apply period_backwards (d := d-t) hc
    have he : run (d-t) (run t s) = run d s := by
      rw [← run_add, Nat.add_sub_of_le (Nat.le_of_lt ht)]
    rw [he]
    exact hfinal

/-- Removing zero piles preserves the number of cards. -/
theorem sum_filter_positive (s : State) : (s.filter (· > 0)).sum = s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    by_cases h : a = 0
    · simp [h, ih]
    · have ha : 0 < a := by omega
      simp [ha, ih]

theorem sum_predecessors (s : State) (h : ∀ a ∈ s, 0 < a) :
    s.length + (s.map (· - 1)).sum = s.sum := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    have ha := h a (by simp)
    have hs : ∀ b ∈ s, 0 < b := by intro b hb; exact h b (by simp [hb])
    have hi := ih hs
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem step_sum (s : State) (h : ∀ a ∈ s, 0 < a) : (step s).sum = s.sum := by
  unfold step
  rw [sort_sum, sum_filter_positive, List.sum_cons]
  exact sum_predecessors s h

theorem cyclic_run {s : State} (h : Cyclic s) (t : Nat) : Cyclic (run t s) := by
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, hp, by rw [run_comm, he]⟩

theorem depth_exists_of_cyclic_run {s : State} {d : Nat} (h : Cyclic (run d s)) :
    ∃ t, t ≤ d ∧ DepthExactly s t := by
  classical
  induction d with
  | zero => exact ⟨0, by omega, h, by intro t ht; omega⟩
  | succ d ih =>
    by_cases hd : Cyclic (run d s)
    · obtain ⟨t, ht, he⟩ := ih hd
      exact ⟨t, by omega, he⟩
    · refine ⟨d+1, by omega, h, ?_⟩
      intro t ht hc
      apply hd
      have hcyc := cyclic_run hc (d-t)
      rw [← run_add, Nat.add_sub_of_le (by omega : t ≤ d)] at hcyc
      exact hcyc

end ProofPursuit.P3
