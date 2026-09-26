import C4SparseStep

namespace C4SignedSparse

/-- A maximizing rotation can create a new zero among the nonzero initial
coefficients; coefficients initially zero remain identically zero. -/
theorem coefficient_endpoint {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hne : ∃ i, a i ≠ 0)
    (hzero : ∀ i, a i = 0 → b i = 0)
    (hab : ∀ i, a i ^ 2 + b i ^ 2 ≤ 1)
    (hmax : ∀ t : ℝ,
      (∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t|) ≤
        ∑ i, Real.arccos |a i|) :
    ∃ t : ℝ,
      (∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t|) =
        ∑ i, Real.arccos |a i| ∧
      (∀ i, a i = 0 → a i * Real.cos t + b i * Real.sin t = 0) ∧
      ∃ i, a i ≠ 0 ∧ a i * Real.cos t + b i * Real.sin t = 0 := by
  classical
  let J := {i : ι // a i ≠ 0}
  let K := {i : ι // ¬a i ≠ 0}
  have hJ : Nonempty J := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨⟨i, hi⟩⟩
  let A : J → ℝ := fun j => |a j.1|
  let B : J → ℝ := fun j => if 0 < a j.1 then b j.1 else -b j.1
  have hA (j : J) : 0 < A j := abs_pos.mpr j.2
  have hAB (j : J) : A j ^ 2 + B j ^ 2 ≤ 1 := by
    by_cases hp : 0 < a j.1
    · simpa [A, B, hp, abs_of_pos hp] using hab j.1
    · have hn : a j.1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) j.2
      simpa [A, B, hp, abs_of_neg hn] using hab j.1
  have hterm (j : J) (t : ℝ) :
      |A j * Real.cos t + B j * Real.sin t| =
        |a j.1 * Real.cos t + b j.1 * Real.sin t| := by
    by_cases hp : 0 < a j.1
    · simp [A, B, hp, abs_of_pos hp]
    · have hn : a j.1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) j.2
      simp only [A, B, hp, ↓reduceIte, abs_of_neg hn]
      calc
        |-a j.1 * Real.cos t + -b j.1 * Real.sin t| =
            |-(a j.1 * Real.cos t + b j.1 * Real.sin t)| := by congr 1; ring
        _ = _ := abs_neg _
  let F : ℝ → ι → ℝ := fun t i => Real.arccos |a i * Real.cos t + b i * Real.sin t|
  have hsplit (t : ℝ) :
      (∑ i, F t i) = (∑ j : J, F t j.1) + ∑ k : K, F t k.1 := by
    exact (Fintype.sum_subtype_add_sum_subtype (fun i => a i ≠ 0) (F t)).symm
  have hK (t : ℝ) : (∑ k : K, F t k.1) = ∑ k : K, F 0 k.1 := by
    apply Finset.sum_congr rfl
    intro k _
    have ha : a k.1 = 0 := by simpa using k.2
    simp [F, ha, hzero k.1 ha]
  have hmaxJ (t : ℝ) :
      (∑ j : J, Real.arccos |A j * Real.cos t + B j * Real.sin t|) ≤
        ∑ j : J, Real.arccos |A j| := by
    have htot : (∑ i, F t i) ≤ ∑ i, F 0 i := by
      simpa [F] using hmax t
    rw [hsplit t, hsplit 0, hK t] at htot
    have hJbound : (∑ j : J, F t j.1) ≤ ∑ j : J, F 0 j.1 := by linarith
    simpa [F, A, hterm] using hJbound
  have : Nonempty J := hJ
  obtain ⟨t, hsumJ, j, hj⟩ :=
    C4SparseStep.positive_coefficient_endpoint A B hA hAB hmaxJ
  refine ⟨t, ?_, ?_, j.1, j.2, ?_⟩
  · have hsumJ' : (∑ j : J, F t j.1) = ∑ j : J, F 0 j.1 := by
      simpa [F, A, hterm] using hsumJ
    calc
      (∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t|) =
          (∑ i, F t i) := rfl
      _ = (∑ j : J, F t j.1) + ∑ k : K, F t k.1 := hsplit t
      _ = (∑ j : J, F 0 j.1) + ∑ k : K, F 0 k.1 := by rw [hsumJ', hK]
      _ = ∑ i, F 0 i := (hsplit 0).symm
      _ = ∑ i, Real.arccos |a i| := by simp [F]
  · intro i hi
    simp [hi, hzero i hi]
  · by_cases hp : 0 < a j.1
    · simpa [A, B, hp, abs_of_pos hp] using hj
    · have hn : a j.1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) j.2
      simp only [A, B, hp, ↓reduceIte, abs_of_neg hn] at hj
      nlinarith [hj]

#print axioms C4SignedSparse.coefficient_endpoint

end C4SignedSparse
