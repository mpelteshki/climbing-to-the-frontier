import ProofPursuit.P3.Staircase

namespace ProofPursuit.P3

private def bit (b : Bool) : Nat := if b then 1 else 0

private theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

/-- The unfiltered pile sizes specified by a binary boundary word. -/
def boundaryRaw : List Bool → State
  | [] => []
  | b :: tail => (tail.length + bit b) :: boundaryRaw tail

/-- Drop the only possible zero pile, at the end of the boundary. -/
def boundary (bits : List Bool) : State :=
  (boundaryRaw bits).filter (· > 0)

def baseSum : Nat → Nat
  | 0 => 0
  | k+1 => k + baseSum k

def bitCount (bits : List Bool) : Nat := (bits.map bit).sum

theorem bitCount_le_length (bits : List Bool) : bitCount bits ≤ bits.length := by
  induction bits with
  | nil => simp [bitCount]
  | cons b tail ih =>
    change bit b + bitCount tail ≤ tail.length + 1
    have := bit_le_one b
    omega

theorem baseSum_eq_staircase_sum (k : Nat) :
    baseSum (k+1) = (staircase k).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (k+1) + baseSum (k+1) = (k+1) + (staircase k).sum
    rw [ih]

theorem boundaryRaw_sum (bits : List Bool) :
    (boundaryRaw bits).sum = baseSum bits.length + bitCount bits := by
  induction bits with
  | nil => rfl
  | cons b tail ih =>
    change tail.length + bit b + (boundaryRaw tail).sum =
      (tail.length + baseSum tail.length) + (bit b + bitCount tail)
    rw [ih]
    omega

theorem boundaryRaw_length (bits : List Bool) : (boundaryRaw bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b tail ih => simp [boundaryRaw, ih]

theorem boundaryRaw_bound {bits : List Bool} {x : Nat}
    (h : x ∈ boundaryRaw bits) : x ≤ bits.length := by
  induction bits with
  | nil => simp [boundaryRaw] at h
  | cons b tail ih =>
    simp only [boundaryRaw, List.mem_cons] at h
    rcases h with rfl | h
    · have := bit_le_one b; simp only [List.length_cons]; omega
    · have := ih h; simp only [List.length_cons]; omega

theorem boundaryRaw_sorted (bits : List Bool) :
    (boundaryRaw bits).Pairwise (· ≥ ·) := by
  induction bits with
  | nil => simp [boundaryRaw]
  | cons b tail ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro x hx
      have := boundaryRaw_bound hx
      omega
    · exact ih

theorem boundary_sorted (bits : List Bool) :
    (boundary bits).Pairwise (· ≥ ·) := by
  exact (boundaryRaw_sorted bits).filter _

theorem boundary_partition (bits : List Bool) :
    IsPartition (baseSum bits.length + bitCount bits) (boundary bits) := by
  refine ⟨?_, ?_, boundary_sorted bits⟩
  · exact (sum_filter_positive (boundaryRaw bits)).trans (boundaryRaw_sum bits)
  · intro x hx
    simp only [boundary, List.mem_filter] at hx
    exact of_decide_eq_true hx.2

theorem boundary_partition_triangular {k : Nat} {bits : List Bool}
    (h : bits.length = k+1) :
    IsPartition (k*(k+1)/2 + bitCount bits) (boundary bits) := by
  have hs := (staircase_partition k).1
  simpa [h, baseSum_eq_staircase_sum, hs] using boundary_partition bits

theorem boundaryRaw_append_singleton (pre : List Bool) (last : Bool) :
    boundaryRaw (pre ++ [last]) = (boundaryRaw pre).map (· + 1) ++ [bit last] := by
  induction pre with
  | nil => simp [boundaryRaw]
  | cons b pre ih =>
    simp only [List.cons_append, boundaryRaw, List.length_append, List.length_cons,
      List.length_nil, List.map_cons, ih]
    congr 1
    omega

private theorem filter_succ (xs : State) :
    (xs.map (· + 1)).filter (· > 0) = xs.map (· + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem boundary_append_singleton (pre : List Bool) (last : Bool) :
    boundary (pre ++ [last]) =
      (boundaryRaw pre).map (· + 1) ++ (if last then [1] else []) := by
  rw [boundary, boundaryRaw_append_singleton, List.filter_append, filter_succ]
  cases last <;> rfl

theorem boundary_length_append_singleton (pre : List Bool) (last : Bool) :
    (boundary (pre ++ [last])).length = pre.length + bit last := by
  rw [boundary_append_singleton]
  cases last <;> simp [boundaryRaw_length, bit]

theorem boundary_predecessors (pre : List Bool) (last : Bool) :
    (((boundary (pre ++ [last])).map (· - 1)).filter (· > 0)) = boundary pre := by
  rw [boundary_append_singleton]
  simp only [List.map_append, List.filter_append]
  simp only [List.map_map, Function.comp_def, Nat.add_sub_cancel]
  cases last <;> simp [boundary]

theorem boundary_cons (head : Bool) (tail : List Bool) :
    boundary (head :: tail) =
      ([tail.length + bit head].filter (· > 0)) ++ boundary tail := by
  simp only [boundary, boundaryRaw, List.filter_cons]
  split <;> simp

theorem step_boundary_rotate (pre : List Bool) (last : Bool) :
    step (boundary (pre ++ [last])) = boundary (last :: pre) := by
  unfold step
  rw [boundary_length_append_singleton]
  have hfilter :
      (((pre.length + bit last) :: (boundary (pre ++ [last])).map (· - 1)).filter (· > 0)) =
      boundary (last :: pre) := by
    rw [List.filter_cons, boundary_predecessors, boundary_cons]
    split <;> simp_all
  rw [hfilter]
  exact sort_of_sorted (boundary_sorted _)

theorem run_boundary_rotate (pre suffix : List Bool) :
    run suffix.length (boundary (pre ++ suffix)) = boundary (suffix ++ pre) := by
  induction suffix generalizing pre with
  | nil => simp
  | cons b tail ih =>
    have hin : pre ++ b :: tail = (pre ++ [b]) ++ tail := by simp [List.append_assoc]
    have hout : tail ++ (pre ++ [b]) = (tail ++ pre) ++ [b] := by
      simp [List.append_assoc]
    calc
      run (b :: tail).length (boundary (pre ++ b :: tail)) =
          run 1 (run tail.length (boundary (pre ++ b :: tail))) := by
        simpa only [List.length_cons] using
          run_add tail.length 1 (boundary (pre ++ b :: tail))
      _ = run 1 (boundary (tail ++ (pre ++ [b]))) := by rw [hin, ih]
      _ = step (boundary ((tail ++ pre) ++ [b])) := by rw [hout]; rfl
      _ = boundary (b :: (tail ++ pre)) := step_boundary_rotate _ _
      _ = boundary ((b :: tail) ++ pre) := rfl

theorem boundary_period (bits : List Bool) :
    run bits.length (boundary bits) = boundary bits := by
  simpa using run_boundary_rotate [] bits

theorem boundary_cyclic (bits : List Bool) : Cyclic (boundary bits) := by
  cases bits with
  | nil => exact ⟨1, by decide, by decide⟩
  | cons b tail =>
    refine ⟨(b :: tail).length, by simp, ?_⟩
    exact boundary_period (b :: tail)

/-- Every binary boundary of length `k+1` gives a valid periodic partition
of `k(k+1)/2` plus its number of marked boundary cells. -/
theorem boundary_orbit {k : Nat} (bits : List Bool) (h : bits.length = k+1) :
    IsPartition (k*(k+1)/2 + bitCount bits) (boundary bits) ∧
    run (k+1) (boundary bits) = boundary bits := by
  constructor
  · exact boundary_partition_triangular h
  · rw [← h]
    exact boundary_period bits

#print axioms boundary_cyclic
#print axioms boundary_orbit

end ProofPursuit.P3
