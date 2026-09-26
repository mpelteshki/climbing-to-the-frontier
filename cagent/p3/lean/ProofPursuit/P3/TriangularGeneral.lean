import ProofPursuit.P3.Classification

namespace ProofPursuit.P3

private theorem baseSum_succ (m : Nat) : baseSum (m+1) = baseSum m + m := by
  simp [baseSum, Nat.add_comm]

private theorem baseSum_mono {a b : Nat} (h : a ≤ b) : baseSum a ≤ baseSum b := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · have hi := ih hab
      rw [baseSum_succ]
      omega
    · have ha : a = b+1 := by omega
      subst a
      exact Nat.le_refl _

private theorem baseSum_lt_succ {m : Nat} (h : 0 < m) :
    baseSum m < baseSum (m+1) := by
  rw [baseSum_succ]
  omega

private theorem baseSum_eq_triangular (k : Nat) :
    baseSum (k+1) = k*(k+1)/2 := by
  rw [baseSum_eq_staircase_sum]
  exact (staircase_partition k).1

private theorem boundary_length_options {k : Nat} {bits : List Bool} (hk : 0 < k)
    (hsum : (boundary bits).sum = k*(k+1)/2) :
    bits.length = k ∨ bits.length = k+1 := by
  have hn : baseSum bits.length + bitCount bits = baseSum (k+1) := by
    have hb := (boundary_partition bits).1
    have ht := baseSum_eq_triangular k
    omega
  have hc := bitCount_le_length bits
  have hlo : k ≤ bits.length := by
    apply Classical.byContradiction
    intro hnot
    have hm : bits.length+1 ≤ k := by omega
    have hmono := baseSum_mono hm
    have hs := baseSum_succ bits.length
    have hstrict := baseSum_lt_succ hk
    omega
  have hhi : bits.length ≤ k+1 := by
    apply Classical.byContradiction
    intro hnot
    have hm : k+2 ≤ bits.length := by omega
    have hmono := baseSum_mono hm
    have hstrict : baseSum (k+1) < baseSum (k+2) := by
      simpa [Nat.add_assoc] using (baseSum_lt_succ (by omega : 0 < k+1))
    omega
  omega

private theorem boundary_cons_true (bits : List Bool) :
    boundary (true :: bits) = (bits.length+1) :: boundary bits := by
  rw [boundary_cons]
  change ([bits.length+1].filter (· > 0)) ++ boundary bits =
    (bits.length+1) :: boundary bits
  simp

private theorem boundary_cons_false (bits : List Bool) (h : 0 < bits.length) :
    boundary (false :: bits) = bits.length :: boundary bits := by
  rw [boundary_cons]
  change ([bits.length].filter (· > 0)) ++ boundary bits =
    bits.length :: boundary bits
  simp [h]

private theorem boundary_full :
    ∀ bits : List Bool, bitCount bits = bits.length →
      boundary bits = staircase bits.length := by
  intro bits
  induction bits with
  | nil => intro _; rfl
  | cons b tail ih =>
    intro h
    cases b with
    | false =>
      have ht := bitCount_le_length tail
      change 0 + bitCount tail = tail.length+1 at h
      omega
    | true =>
      have ht : bitCount tail = tail.length := by
        change 1 + bitCount tail = tail.length+1 at h
        omega
      rw [boundary_cons_true, ih ht]
      rfl

private theorem boundary_zero :
    ∀ bits : List Bool, bitCount bits = 0 →
      boundary bits = staircase (bits.length-1) := by
  intro bits
  induction bits with
  | nil => intro _; rfl
  | cons b tail ih =>
    intro h
    cases b with
    | true =>
      change 1 + bitCount tail = 0 at h
      omega
    | false =>
      have ht : bitCount tail = 0 := by
        change 0 + bitCount tail = 0 at h
        omega
      cases tail with
      | nil => rfl
      | cons c rest =>
        have hpos : 0 < (c :: rest).length := by simp
        rw [boundary_cons_false (c :: rest) hpos, ih ht]
        simp [staircase]

private theorem positive_sum_zero_empty (s : State)
    (hp : ∀ a ∈ s, 0 < a) (hsum : s.sum = 0) : s = [] := by
  cases s with
  | nil => rfl
  | cons a tail =>
    have ha := hp a (by simp)
    simp only [List.sum_cons] at hsum
    omega

private theorem boundary_triangular_unique {k : Nat} {bits : List Bool}
    (hsum : (boundary bits).sum = k*(k+1)/2) :
    boundary bits = staircase k := by
  cases k with
  | zero =>
    have he := positive_sum_zero_empty (boundary bits) (boundary_partition bits).2.1
      (by simpa using hsum)
    simp [he, staircase]
  | succ k =>
    have hk : 0 < k+1 := by omega
    have hn : baseSum bits.length + bitCount bits = baseSum ((k+1)+1) := by
      have hb := (boundary_partition bits).1
      have ht := baseSum_eq_triangular (k+1)
      omega
    obtain hm | hm := boundary_length_options hk hsum
    · have hc : bitCount bits = k+1 := by
        rw [hm] at hn
        have hs := baseSum_succ (k+1)
        omega
      rw [boundary_full bits (by simpa [hm] using hc), hm]
    · have hc : bitCount bits = 0 := by
        rw [hm] at hn
        omega
      rw [boundary_zero bits hc, hm]
      simp

/-- At every triangular card count, the staircase is the only cyclic partition. -/
theorem triangular_cyclic_unique (k : Nat) {s : State}
    (hp : IsPartition (k*(k+1)/2) s) (hc : Cyclic s) :
    s = staircase k := by
  obtain ⟨bits, he⟩ := (cyclic_iff_boundary hp).mp hc
  have hs : (boundary bits).sum = k*(k+1)/2 := by
    rw [he]
    exact hp.1
  exact he.symm.trans (boundary_triangular_unique hs)

/-- Every partition at a triangular card count eventually reaches its staircase. -/
theorem triangular_eventually_staircase (k : Nat) {s : State}
    (hp : IsPartition (k*(k+1)/2) s) :
    ∃ t, run t s = staircase k := by
  obtain ⟨t, _, hc⟩ := eventually_cyclic hp
  exact ⟨t, triangular_cyclic_unique k (run_isPartition hp t) hc⟩

#print axioms triangular_cyclic_unique
#print axioms triangular_eventually_staircase

end ProofPursuit.P3
