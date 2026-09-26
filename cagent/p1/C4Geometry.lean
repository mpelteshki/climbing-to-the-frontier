import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

namespace C4Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rotation in the orthonormal plane spanned by `x` and `y`. -/
noncomputable def rotation (x y : E) (t : ℝ) : E := Real.cos t • x + Real.sin t • y

theorem inner_rotation (x y z : E) (t : ℝ) :
    ⟪rotation x y t, z⟫_ℝ = ⟪x, z⟫_ℝ * Real.cos t + ⟪y, z⟫_ℝ * Real.sin t := by
  simp only [rotation, inner_add_left, real_inner_smul_left]
  ring

theorem rotation_preserves_orthogonality (x y z : E) (t : ℝ)
    (hxz : ⟪x, z⟫_ℝ = 0) (hyz : ⟪y, z⟫_ℝ = 0) :
    ⟪rotation x y t, z⟫_ℝ = 0 := by
  rw [inner_rotation, hxz, hyz]
  ring

theorem rotation_unit (x y : E) (t : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℝ = 0) :
    ‖rotation x y t‖ = 1 := by
  have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : ⟪y, y⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy]
  have hrot : ⟪rotation x y t, rotation x y t⟫_ℝ =
      (Real.cos t) ^ 2 + (Real.sin t) ^ 2 := by
    simp only [rotation, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hxx, hyy, hxy, hyx]
    ring
  have hn : ‖rotation x y t‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hrot]
    nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg (rotation x y t)]

theorem bessel_two (x y z : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℝ = 0)
    (hz : ‖z‖ = 1) :
    ⟪x, z⟫_ℝ ^ 2 + ⟪y, z⟫_ℝ ^ 2 ≤ 1 := by
  let a : ℝ := ⟪x, z⟫_ℝ
  let b : ℝ := ⟪y, z⟫_ℝ
  let p : E := a • x + b • y
  have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyy : ⟪y, y⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hy]; norm_num
  have hyx : ⟪y, x⟫_ℝ = 0 := by rw [real_inner_comm, hxy]
  have hzx : ⟪z, x⟫_ℝ = a := by rw [real_inner_comm]
  have hzy : ⟪z, y⟫_ℝ = b := by rw [real_inner_comm]
  have hpp : ⟪p, p⟫_ℝ = a ^ 2 + b ^ 2 := by
    simp only [p, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hxx, hyy, hxy, hyx]
    ring
  have hzp : ⟪z, p⟫_ℝ = a ^ 2 + b ^ 2 := by
    simp only [p, inner_add_right, real_inner_smul_right, hzx, hzy]
    ring
  have hpn : ‖p‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hpp
  have hres := norm_sub_sq_real z p
  rw [hz, hzp, hpn] at hres
  have hres0 : 0 ≤ ‖z - p‖ ^ 2 := sq_nonneg _
  dsimp [a, b] at *
  nlinarith

#print axioms inner_rotation
#print axioms rotation_preserves_orthogonality
#print axioms rotation_unit
#print axioms bessel_two

end C4Geometry
