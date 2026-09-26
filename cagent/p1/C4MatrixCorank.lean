import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Corank bounds for matrices with a nonzero interior superdiagonal. -/
namespace C4MatrixCorank

private theorem kernel_zero_of_first_two {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0)
    (x : Fin n → ℝ) (hMx : M.mulVecLin x = 0)
    (h0 : x ⟨0, by omega⟩ = 0) (h1 : x ⟨1, by omega⟩ = 0) : x = 0 := by
  funext j
  have hcoord : ∀ k : ℕ, (hk : k < n) → x ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        simpa using h0
      by_cases hk1 : k = 1
      · subst k
        simpa using h1
      have hk2 : 2 ≤ k := by omega
      let i : Fin n := ⟨k - 1, by omega⟩
      let target : Fin n := ⟨k, hk⟩
      have hi1 : 1 ≤ i.val := by dsimp [i]; omega
      have hi2 : i.val + 1 < n := by dsimp [i]; omega
      have hrow : ∑ t : Fin n, M i t * x t = 0 := by
        have hh := congrArg (fun f : Fin n → ℝ => f i) hMx
        simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum,
          Pi.zero_apply] using hh
      have hsum : (∑ t : Fin n, M i t * x t) = M i target * x target := by
        classical
        apply Finset.sum_eq_single target
        · intro t _ hne
          by_cases htk : t.val < k
          · have ht0 : x t = 0 := by simpa using ih t.val htk t.isLt
            simp [ht0]
          · have htail : i.val + 1 < t.val := by
              dsimp [i]
              have : t.val ≠ k := by
                intro heq
                apply hne
                exact Fin.ext heq
              omega
            simp [hband i t hi1 hi2 (Or.inr htail)]
        · simp
      have htarget : M i target * x target = 0 := by rw [← hsum]; exact hrow
      exact (mul_eq_zero.mp htarget).resolve_left
        (hsuper i target hi1 hi2 (by dsimp [i, target]; omega))
  simpa using hcoord j.val j.isLt

/-- At most two independent kernel vectors can survive the interior recurrence. -/
theorem finrank_ker_le_two {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0) :
    Module.finrank ℝ (LinearMap.ker M.mulVecLin) ≤ 2 := by
  let K := LinearMap.ker M.mulVecLin
  let obs : K →ₗ[ℝ] ℝ × ℝ := {
    toFun := fun x => (x.1 ⟨0, by omega⟩, x.1 ⟨1, by omega⟩)
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  have hinj : Function.Injective obs := by
    intro x y hxy
    have h0 : (x - y).1 ⟨0, by omega⟩ = 0 := by
      have h := congrArg Prod.fst hxy
      change x.1 ⟨0, by omega⟩ = y.1 ⟨0, by omega⟩ at h
      simpa using sub_eq_zero.mpr h
    have h1 : (x - y).1 ⟨1, by omega⟩ = 0 := by
      have h := congrArg Prod.snd hxy
      change x.1 ⟨1, by omega⟩ = y.1 ⟨1, by omega⟩ at h
      simpa using sub_eq_zero.mpr h
    have hz : x - y = 0 := by
      apply Subtype.ext
      exact kernel_zero_of_first_two hn M hband hsuper (x - y).1 (x - y).2 h0 h1
    exact sub_eq_zero.mp hz
  simpa using obs.finrank_le_finrank_of_injective hinj

/-- The range of a cycle-tridiagonal matrix has codimension at most two. -/
theorem finrank_range_add_two_ge {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0) :
    n ≤ Module.finrank ℝ (LinearMap.range M.mulVecLin) + 2 := by
  have hker := finrank_ker_le_two hn M hband hsuper
  have hnull := (M.mulVecLin).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  omega

/-- A cycle-tridiagonal matrix with nonzero interior superdiagonal has corank at most two. -/
theorem rank_add_two_ge {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0) :
    n ≤ M.rank + 2 := by
  exact finrank_range_add_two_ge hn M hband hsuper

private theorem path_kernel_zero_of_first_one {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0)
    (hfirst : ∀ j : Fin n, 1 < j.val → M ⟨0, by omega⟩ j = 0)
    (h01 : M ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0)
    (x : Fin n → ℝ) (hMx : M.mulVecLin x = 0)
    (h0 : x ⟨0, by omega⟩ = 0) : x = 0 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨1, by omega⟩
  have hrow : ∑ j : Fin n, M i0 j * x j = 0 := by
    have hh := congrArg (fun f : Fin n → ℝ => f i0) hMx
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum,
      Pi.zero_apply] using hh
  have hsum : (∑ j : Fin n, M i0 j * x j) = M i0 j1 * x j1 := by
    classical
    apply Finset.sum_eq_single j1
    · intro j _ hne
      by_cases hj0 : j.val = 0
      · have : j = i0 := Fin.ext hj0
        subst j
        simp [i0, h0]
      · have hjgt : 1 < j.val := by
          have hj1 : j.val ≠ 1 := by
            intro heq
            apply hne
            exact Fin.ext heq
          omega
        have hz : M i0 j = 0 := by simpa only [i0] using hfirst j hjgt
        simp [hz]
    · simp
  have h1 : x j1 = 0 := by
    have hprod : M i0 j1 * x j1 = 0 := by rw [← hsum]; exact hrow
    exact (mul_eq_zero.mp hprod).resolve_left (by simpa [i0, j1] using h01)
  exact kernel_zero_of_first_two hn M hband hsuper x hMx h0 (by simpa [j1] using h1)

/-- A path matrix with a nonzero first superdiagonal entry has corank at most one. -/
theorem path_finrank_ker_le_one {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0)
    (hfirst : ∀ j : Fin n, 1 < j.val → M ⟨0, by omega⟩ j = 0)
    (h01 : M ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker M.mulVecLin) ≤ 1 := by
  let K := LinearMap.ker M.mulVecLin
  let obs : K →ₗ[ℝ] ℝ := {
    toFun := fun x => x.1 ⟨0, by omega⟩
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  have hinj : Function.Injective obs := by
    intro x y hxy
    have h0 : (x - y).1 ⟨0, by omega⟩ = 0 := by
      change x.1 ⟨0, by omega⟩ = y.1 ⟨0, by omega⟩ at hxy
      simpa using sub_eq_zero.mpr hxy
    have hz : x - y = 0 := by
      apply Subtype.ext
      exact path_kernel_zero_of_first_one hn M hband hsuper hfirst h01
        (x - y).1 (x - y).2 h0
    exact sub_eq_zero.mp hz
  simpa using obs.finrank_le_finrank_of_injective hinj

/-- A path matrix with the stated band and nonzero superdiagonal has rank at least `n-1`. -/
theorem path_rank_add_one_ge {n : ℕ} (hn : 2 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hband : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      (j.val + 1 < i.val ∨ i.val + 1 < j.val) → M i j = 0)
    (hsuper : ∀ i j : Fin n, 1 ≤ i.val → i.val + 1 < n →
      j.val = i.val + 1 → M i j ≠ 0)
    (hfirst : ∀ j : Fin n, 1 < j.val → M ⟨0, by omega⟩ j = 0)
    (h01 : M ⟨0, by omega⟩ ⟨1, by omega⟩ ≠ 0) :
    n ≤ M.rank + 1 := by
  have hker := path_finrank_ker_le_one hn M hband hsuper hfirst h01
  have hnull := (M.mulVecLin).finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  change M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) =
    Module.finrank ℝ (Fin n → ℝ) at hnull
  omega

#print axioms finrank_ker_le_two
#print axioms finrank_range_add_two_ge
#print axioms rank_add_two_ge
#print axioms path_finrank_ker_le_one
#print axioms path_rank_add_one_ge
end C4MatrixCorank
