import ProofPursuit.P3.TriangularGeneral

namespace ProofPursuit.P3

private theorem rank_base_succ (m : Nat) :
    baseSum (m+1) = baseSum m + m := by
  simp [baseSum, Nat.add_comm]

private theorem rank_base_mono {a b : Nat} (h : a ≤ b) :
    baseSum a ≤ baseSum b := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · have hi := ih hab
      rw [rank_base_succ]
      omega
    · have ha : a = b+1 := by omega
      subst a
      exact Nat.le_refl _

private theorem rank_base_lt_succ {m : Nat} (h : 0 < m) :
    baseSum m < baseSum (m+1) := by
  rw [rank_base_succ]
  omega

private theorem bitCount_replicate_true (k : Nat) :
    bitCount (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 1 + bitCount (List.replicate k true) = k+1
    omega

private theorem boundary_replicate_true (k : Nat) :
    boundary (List.replicate k true) = staircase k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change boundary (true :: List.replicate k true) = staircase (k+1)
    rw [boundary_cons]
    simp only [List.length_replicate]
    change ([k+1].filter (· > 0)) ++ boundary (List.replicate k true) =
      (k+1) :: staircase k
    simp [ih]

private theorem rank_boundary_length_options {k n : Nat} {bits : List Bool}
    (hk : 0 < k) (hlo : baseSum k < n) (hhi : n ≤ baseSum (k+1))
    (hsum : n = baseSum bits.length + bitCount bits) :
    bits.length = k ∨ bits.length = k+1 := by
  have hc := bitCount_le_length bits
  have hlo' : k ≤ bits.length := by
    apply Classical.byContradiction
    intro hnot
    have hm : bits.length+1 ≤ k := by omega
    have hmono := rank_base_mono hm
    have hs := rank_base_succ bits.length
    omega
  have hhi' : bits.length ≤ k+1 := by
    apply Classical.byContradiction
    intro hnot
    have hm : k+2 ≤ bits.length := by omega
    have hmono := rank_base_mono hm
    have hstrict : baseSum (k+1) < baseSum (k+2) := by
      simpa [Nat.add_assoc] using (rank_base_lt_succ (by omega : 0 < k+1))
    omega
  omega

/-- Normalize every cyclic partition in the `k`th triangular rank interval to
exactly `k` boundary bits, including its triangular upper endpoint. -/
theorem ranked_cyclic_iff_boundary {k n : Nat} (hk : 0 < k)
    (hlo : baseSum k < n) (hhi : n ≤ baseSum (k+1))
    {s : State} (hp : IsPartition n s) :
    Cyclic s ↔ ∃ bits : List Bool,
      bits.length = k ∧ bitCount bits = n - baseSum k ∧ boundary bits = s := by
  constructor
  · intro hc
    obtain ⟨bits, _, he⟩ := cyclic_is_boundary hp hc
    have hn : n = baseSum bits.length + bitCount bits := by
      have hb := (boundary_partition bits).1
      rw [he] at hb
      have hs := hp.1
      omega
    rcases rank_boundary_length_options hk hlo hhi hn with hlen | hlen
    · refine ⟨bits, hlen, ?_, he⟩
      rw [hlen] at hn
      omega
    · have htop : n = baseSum (k+1) := by
        rw [hlen] at hn
        omega
      have htri : n = k*(k+1)/2 := by
        have hb := baseSum_eq_staircase_sum k
        have hs := (staircase_partition k).1
        omega
      have hpTri : IsPartition (k*(k+1)/2) s := by
        rw [← htri]
        exact hp
      have heq := triangular_cyclic_unique k hpTri hc
      refine ⟨List.replicate k true, by simp, ?_, ?_⟩
      · rw [bitCount_replicate_true]
        have hb := rank_base_succ k
        omega
      · rw [boundary_replicate_true]
        exact heq.symm
  · rintro ⟨bits, _, _, rfl⟩
    exact boundary_cyclic bits

#print axioms ranked_cyclic_iff_boundary

end ProofPursuit.P3
