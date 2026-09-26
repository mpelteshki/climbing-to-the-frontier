import C4Configuration

open scoped InnerProductSpace

namespace C4Replacement

open C4Configuration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def replacement {n : ℕ} (v : Configuration E n) (i : Fin n)
    (w : UnitVector E) : Configuration E n := Function.update v i w

def pairInner {n : ℕ} (v : Configuration E n) (p : Fin n × Fin n) : ℝ :=
  ⟪(v p.1).1, (v p.2).1⟫_ℝ

noncomputable def pairAngle {n : ℕ} (v : Configuration E n) (p : Fin n × Fin n) : ℝ :=
  Real.arccos |pairInner v p|

def incidentPairs (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) :=
  (pairs n).filter (fun p => p.1 = i ∨ p.2 = i)

noncomputable def incidentAngle {n : ℕ} (v : Configuration E n) (i : Fin n) : ℝ :=
  ∑ p ∈ incidentPairs n i, pairAngle v p

theorem pairInner_replacement_nonincident {n : ℕ} (v : Configuration E n)
    (i : Fin n) (w : UnitVector E) (p : Fin n × Fin n)
    (h₁ : p.1 ≠ i) (h₂ : p.2 ≠ i) :
    pairInner (replacement v i w) p = pairInner v p := by
  simp [pairInner, replacement, Function.update_of_ne h₁, Function.update_of_ne h₂]

theorem pairAngle_replacement_nonincident {n : ℕ} (v : Configuration E n)
    (i : Fin n) (w : UnitVector E) (p : Fin n × Fin n)
    (h₁ : p.1 ≠ i) (h₂ : p.2 ≠ i) :
    pairAngle (replacement v i w) p = pairAngle v p := by
  rw [pairAngle, pairAngle, pairInner_replacement_nonincident v i w p h₁ h₂]

/-- A replacement changes only the incident contribution to the total angle. -/
theorem totalAngle_replacement_balance {n : ℕ} (v : Configuration E n)
    (i : Fin n) (w : UnitVector E) :
    totalAngle (replacement v i w) + incidentAngle v i =
      totalAngle v + incidentAngle (replacement v i w) i := by
  classical
  let q : Fin n × Fin n → Prop := fun p => p.1 = i ∨ p.2 = i
  have hother :
      ∑ p ∈ (pairs n).filter (fun p => ¬ q p), pairAngle (replacement v i w) p =
      ∑ p ∈ (pairs n).filter (fun p => ¬ q p), pairAngle v p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : ¬ q p := (Finset.mem_filter.mp hp).2
    have h₁ : p.1 ≠ i := fun h => hp' (Or.inl h)
    have h₂ : p.2 ≠ i := fun h => hp' (Or.inr h)
    exact pairAngle_replacement_nonincident v i w p h₁ h₂
  have hsplit (u : Configuration E n) :
      totalAngle u = incidentAngle u i +
        ∑ p ∈ (pairs n).filter (fun p => ¬ q p), pairAngle u p := by
    simp only [totalAngle, incidentAngle, incidentPairs, pairAngle]
    exact (Finset.sum_filter_add_sum_filter_not (pairs n) q
      (fun p => Real.arccos |pairInner u p|)).symm
  rw [hsplit (replacement v i w), hsplit v, hother]
  ring

theorem totalAngle_replacement_eq_of_incident_eq {n : ℕ}
    (v : Configuration E n) (i : Fin n) (w : UnitVector E)
    (h : incidentAngle (replacement v i w) i = incidentAngle v i) :
    totalAngle (replacement v i w) = totalAngle v := by
  have hb := totalAngle_replacement_balance v i w
  rw [h] at hb
  exact add_right_cancel hb

theorem incidentAngle_le_of_totalAngle_max {n : ℕ}
    (v : Configuration E n) (i : Fin n) (w : UnitVector E)
    (hmax : ∀ u : Configuration E n, totalAngle u ≤ totalAngle v) :
    incidentAngle (replacement v i w) i ≤ incidentAngle v i := by
  have hb := totalAngle_replacement_balance v i w
  have hm := hmax (replacement v i w)
  linarith

/-- The uniquely ordered pair corresponding to two distinct indices. -/
def edge {n : ℕ} (i j : Fin n) : Fin n × Fin n :=
  if i < j then (i, j) else (j, i)

theorem edge_mem_pairs {n : ℕ} {i j : Fin n} (hij : j ≠ i) :
    edge i j ∈ pairs n := by
  have hne : i ≠ j := Ne.symm hij
  rcases lt_or_gt_of_ne hne with h | h
  · simp [edge, pairs, h]
  · have hnot : ¬ i < j := not_lt.mpr h.le
    simp [edge, pairs, hnot, h]

theorem pairInner_edge {n : ℕ} (v : Configuration E n)
    (i j : Fin n) :
    pairInner v (edge i j) = ⟪(v i).1, (v j).1⟫_ℝ := by
  by_cases h : i < j
  · simp [pairInner, edge, h]
  · simp [pairInner, edge, h, real_inner_comm]

theorem pairInner_replacement_edge {n : ℕ} (v : Configuration E n)
    (i j : Fin n) (w : UnitVector E) (hji : j ≠ i) :
    pairInner (replacement v i w) (edge i j) = ⟪w.1, (v j).1⟫_ℝ := by
  by_cases h : i < j
  · simp [pairInner, edge, h, replacement, hji]
  · simp [pairInner, edge, h, replacement, hji, real_inner_comm]

theorem edge_injective_away {n : ℕ} (i j k : Fin n)
    (hji : j ≠ i) (hki : k ≠ i)
    (h : edge i j = edge i k) : j = k := by
  by_cases hj : i < j
  · by_cases hk : i < k
    · simpa [edge, hj, hk] using congrArg Prod.snd h
    · have hki' : k < i := (lt_or_gt_of_ne (Ne.symm hki)).resolve_left hk
      have hi : i = k := by simpa [edge, hj, hk] using congrArg Prod.fst h
      exact (hki hi.symm).elim
  · by_cases hk : i < k
    · have hji' : j < i := (lt_or_gt_of_ne (Ne.symm hji)).resolve_left hj
      have hi : j = i := by simpa [edge, hj, hk] using congrArg Prod.fst h
      exact (hji hi).elim
    · simpa [edge, hj, hk] using congrArg Prod.fst h

/-- The incident pair sum is the usual star sum over all other vertices. -/
theorem incidentAngle_eq_star {n : ℕ} (v : Configuration E n) (i : Fin n) :
    incidentAngle v i =
      ∑ j ∈ Finset.univ.erase i, Real.arccos |⟪(v i).1, (v j).1⟫_ℝ| := by
  classical
  unfold incidentAngle
  symm
  apply Finset.sum_bij (fun j _ => edge i j)
  · intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    apply Finset.mem_filter.mpr
    refine ⟨edge_mem_pairs hji, ?_⟩
    by_cases h : i < j
    · simp [edge, h]
    · simp [edge, h]
  · intro j hj k hk heq
    exact edge_injective_away i j k (Finset.mem_erase.mp hj).1
      (Finset.mem_erase.mp hk).1 heq
  · intro p hp
    obtain ⟨hpair, hinc⟩ := Finset.mem_filter.mp hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hpair).2
    rcases hinc with hleft | hright
    · refine ⟨p.2, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · intro heq
        exact (ne_of_lt hlt) (hleft.trans heq.symm)
      · rcases p with ⟨a, b⟩
        simp only at hleft hlt
        subst a
        simp [edge, hlt]
    · refine ⟨p.1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · intro heq
        exact (ne_of_lt hlt) (heq.trans hright.symm)
      · rcases p with ⟨a, b⟩
        simp only at hright hlt
        subst b
        have hnot : ¬ i < a := not_lt.mpr hlt.le
        simp [edge, hnot]
  · intro j hj
    rw [pairAngle, pairInner_edge]

/-- The incident sum indexed by neighbors as a subtype. -/
theorem incidentAngle_eq_sum_neighbors {n : ℕ}
    (v : Configuration E n) (i : Fin n) :
    incidentAngle v i =
      ∑ j : {j : Fin n // j ≠ i},
        Real.arccos |⟪(v i).1, (v j.1).1⟫_ℝ| := by
  classical
  rw [incidentAngle_eq_star]
  symm
  apply Finset.sum_bij (fun j _ => j.1)
  · intro j _
    exact Finset.mem_erase.mpr ⟨j.property, Finset.mem_univ _⟩
  · intro j _ k _ h
    exact Subtype.ext h
  · intro j hj
    exact ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

/-- Exact replacement balance with the usual neighbor-index sums. -/
theorem totalAngle_replacement_star_balance {n : ℕ}
    (v : Configuration E n) (i : Fin n) (w : UnitVector E) :
    totalAngle (replacement v i w) +
      (∑ j ∈ Finset.univ.erase i,
        Real.arccos |⟪(v i).1, (v j).1⟫_ℝ|) =
    totalAngle v +
      (∑ j ∈ Finset.univ.erase i,
        Real.arccos |⟪w.1, (v j).1⟫_ℝ|) := by
  classical
  have hb := totalAngle_replacement_balance v i w
  rw [incidentAngle_eq_star v i,
    incidentAngle_eq_star (replacement v i w) i] at hb
  have hnewsum :
      (∑ j ∈ Finset.univ.erase i,
        Real.arccos |⟪(replacement v i w i).1,
          (replacement v i w j).1⟫_ℝ|) =
      (∑ j ∈ Finset.univ.erase i,
        Real.arccos |⟪w.1, (v j).1⟫_ℝ|) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [replacement, hji]
  rw [hnewsum] at hb
  exact hb

theorem neighbor_sum_le_of_totalAngle_max {n : ℕ}
    (v : Configuration E n) (i : Fin n) (w : UnitVector E)
    (hmax : ∀ u : Configuration E n, totalAngle u ≤ totalAngle v) :
    (∑ j : {j : Fin n // j ≠ i},
      Real.arccos |⟪w.1, (v j.1).1⟫_ℝ|) ≤
    (∑ j : {j : Fin n // j ≠ i},
      Real.arccos |⟪(v i).1, (v j.1).1⟫_ℝ|) := by
  have h := incidentAngle_le_of_totalAngle_max v i w hmax
  rw [incidentAngle_eq_sum_neighbors (replacement v i w) i,
    incidentAngle_eq_sum_neighbors v i] at h
  have hnewsum :
      (∑ j : {j : Fin n // j ≠ i},
        Real.arccos |⟪(replacement v i w i).1,
          (replacement v i w j.1).1⟫_ℝ|) =
      (∑ j : {j : Fin n // j ≠ i},
        Real.arccos |⟪w.1, (v j.1).1⟫_ℝ|) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [replacement, j.property]
  rw [hnewsum] at h
  exact h

theorem pairInner_zero_preserved {n : ℕ} (v : Configuration E n)
    (i : Fin n) (w : UnitVector E)
    (hpres : ∀ j : Fin n, j ≠ i →
      ⟪(v i).1, (v j).1⟫_ℝ = 0 → ⟪w.1, (v j).1⟫_ℝ = 0)
    (p : Fin n × Fin n) (hp : p ∈ pairs n)
    (hzero : pairInner v p = 0) :
    pairInner (replacement v i w) p = 0 := by
  by_cases hleft : p.1 = i
  · have hright : p.2 ≠ i := by
      intro heq
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      simp [hleft, heq] at hlt
    have hold : ⟪(v i).1, (v p.2).1⟫_ℝ = 0 := by
      simpa [pairInner, hleft] using hzero
    have hnew := hpres p.2 hright hold
    simpa [pairInner, replacement, hleft, hright] using hnew
  · by_cases hright : p.2 = i
    · have hold : ⟪(v i).1, (v p.1).1⟫_ℝ = 0 := by
        rw [real_inner_comm]
        simpa [pairInner, hright] using hzero
      have hnew := hpres p.1 hleft hold
      rw [real_inner_comm] at hnew
      simpa [pairInner, replacement, hleft, hright] using hnew
    · rw [pairInner_replacement_nonincident v i w p hleft hright]
      exact hzero

/-- Preserving old incident zeros and creating one new zero increases the count. -/
theorem orthogonalityCount_replacement_strict {n : ℕ}
    (v : Configuration E n) (i : Fin n) (w : UnitVector E)
    (hpres : ∀ j : Fin n, j ≠ i →
      ⟪(v i).1, (v j).1⟫_ℝ = 0 → ⟪w.1, (v j).1⟫_ℝ = 0)
    (hgain : ∃ j : Fin n, j ≠ i ∧
      ⟪(v i).1, (v j).1⟫_ℝ ≠ 0 ∧ ⟪w.1, (v j).1⟫_ℝ = 0) :
    orthogonalityCount v < orthogonalityCount (replacement v i w) := by
  classical
  let old := (pairs n).filter (fun p => pairInner v p = 0)
  let new := (pairs n).filter (fun p => pairInner (replacement v i w) p = 0)
  have hsubset : old ⊆ new := by
    intro p hp
    obtain ⟨hpair, hzero⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨hpair, pairInner_zero_preserved v i w hpres p hpair hzero⟩
  obtain ⟨j, hji, hold, hnew⟩ := hgain
  have hp : edge i j ∈ pairs n := edge_mem_pairs hji
  have hpnew : edge i j ∈ new := by
    apply Finset.mem_filter.mpr
    constructor
    · exact hp
    · rw [pairInner_replacement_edge v i j w hji]
      exact hnew
  have hpnot : edge i j ∉ old := by
    intro h
    have hz : pairInner v (edge i j) = 0 := (Finset.mem_filter.mp h).2
    rw [pairInner_edge] at hz
    exact hold hz
  have hstrict : old ⊂ new :=
    (Finset.ssubset_iff_of_subset hsubset).2 ⟨edge i j, hpnew, hpnot⟩
  exact Finset.card_lt_card hstrict

#print axioms totalAngle_replacement_balance
#print axioms totalAngle_replacement_eq_of_incident_eq
#print axioms incidentAngle_le_of_totalAngle_max
#print axioms incidentAngle_eq_star
#print axioms incidentAngle_eq_sum_neighbors
#print axioms totalAngle_replacement_star_balance
#print axioms neighbor_sum_le_of_totalAngle_max
#print axioms orthogonalityCount_replacement_strict

end C4Replacement
