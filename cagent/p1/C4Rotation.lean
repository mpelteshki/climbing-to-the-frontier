import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace C4Rotation

private theorem inner_sq_lt_one {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (r * Real.cos t) ^ 2 < 1 := by
  have hc := Real.abs_cos_le_one t
  have hcsq : (Real.cos t) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (abs_nonneg (Real.cos t)) (sub_nonneg.mpr hc),
      sq_abs (Real.cos t)]
  have hr2 : r ^ 2 < 1 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hcsq)]

private theorem denominator_pos {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < Real.sqrt (1 - (r * Real.cos t) ^ 2) := by
  exact Real.sqrt_pos.2 (by linarith [inner_sq_lt_one hr0 hr1 (t := t)])

theorem hasDerivAt_angle {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (fun x : ℝ => Real.arccos (r * Real.cos x))
      (r * Real.sin t / Real.sqrt (1 - (r * Real.cos t) ^ 2)) t := by
  have hsq := inner_sq_lt_one hr0 hr1 (t := t)
  have hlt : r * Real.cos t < 1 := by nlinarith
  have hgt : -1 < r * Real.cos t := by nlinarith
  have houter := Real.hasDerivAt_arccos (by linarith : r * Real.cos t ≠ -1)
    (by linarith : r * Real.cos t ≠ 1)
  have hinner : HasDerivAt (fun x : ℝ => r * Real.cos x) (r * -Real.sin t) t :=
    (Real.hasDerivAt_cos t).const_mul r
  convert houter.comp t hinner using 1
  · rfl
  · simp only [div_eq_mul_inv]
    ring

theorem hasDerivAt_slope {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt
      (fun x : ℝ => r * Real.sin x / Real.sqrt (1 - (r * Real.cos x) ^ 2))
      (r * (1 - r ^ 2) * Real.cos t /
        ((1 - (r * Real.cos t) ^ 2) * Real.sqrt (1 - (r * Real.cos t) ^ 2))) t := by
  have hcos : HasDerivAt (fun x : ℝ => r * Real.cos x) (r * -Real.sin t) t :=
    (Real.hasDerivAt_cos t).const_mul r
  have hD : HasDerivAt (fun x : ℝ => 1 - (r * Real.cos x) ^ 2)
      (2 * r ^ 2 * Real.cos t * Real.sin t) t := by
    convert (hcos.pow 2).const_sub 1 using 1; ring
  have hDpos : 0 < 1 - (r * Real.cos t) ^ 2 := by
    linarith [inner_sq_lt_one hr0 hr1 (t := t)]
  have hsqrt : HasDerivAt
      (fun x : ℝ => Real.sqrt (1 - (r * Real.cos x) ^ 2))
      ((1 / (2 * Real.sqrt (1 - (r * Real.cos t) ^ 2))) *
        (2 * r ^ 2 * Real.cos t * Real.sin t)) t := by
    convert (Real.hasDerivAt_sqrt hDpos.ne').comp t hD using 1; rfl
  have hnum : HasDerivAt (fun x : ℝ => r * Real.sin x)
      (r * Real.cos t) t := (Real.hasDerivAt_sin t).const_mul r
  have hsqrt_ne : Real.sqrt (1 - (r * Real.cos t) ^ 2) ≠ 0 :=
    (denominator_pos hr0 hr1 (t := t)).ne'
  convert hnum.div hsqrt hsqrt_ne using 1
  have hsqrt2 : (Real.sqrt (1 - (r * Real.cos t) ^ 2)) ^ 2 =
      1 - (r * Real.cos t) ^ 2 := Real.sq_sqrt hDpos.le
  have htrig := Real.sin_sq_add_cos_sq t
  field_simp
  ring_nf at hsqrt2
  have hden : (1 - r ^ 2 * Real.cos t ^ 2) *
      Real.sqrt (1 - r ^ 2 * Real.cos t ^ 2) =
      Real.sqrt (1 - r ^ 2 * Real.cos t ^ 2) ^ 3 := by
    calc
      _ = (Real.sqrt (1 - r ^ 2 * Real.cos t ^ 2)) ^ 2 *
          Real.sqrt (1 - r ^ 2 * Real.cos t ^ 2) := by rw [hsqrt2]
      _ = _ := by ring
  rw [hden]
  congr 1
  have hnumid : Real.sqrt (1 - r ^ 2 * Real.cos t ^ 2) ^ 2 -
      r ^ 2 * Real.sin t ^ 2 = 1 - r ^ 2 := by
    rw [hsqrt2]
    nlinarith [htrig]
  rw [hnumid]
  ring

private theorem convexOn_angle_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ConvexOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
      (fun t => Real.arccos (r * Real.cos t)) := by
  let D : Set ℝ := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
  have hD : Convex ℝ D := convex_Icc _ _
  have hcont : ContinuousOn (fun t => Real.arccos (r * Real.cos t)) D :=
    (Real.continuous_arccos.comp (continuous_const.mul Real.continuous_cos)).continuousOn
  apply convexOn_of_hasDerivWithinAt2_nonneg hD hcont
    (fun t _ => (hasDerivAt_angle hr0 hr1).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_slope hr0 hr1).hasDerivWithinAt)
  intro t ht
  have htD : t ∈ D := interior_subset ht
  have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc htD
  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hdp : 0 < 1 - (r * Real.cos t) ^ 2 := by
    linarith [inner_sq_lt_one hr0 hr1 (t := t)]
  have hsp : 0 < Real.sqrt (1 - (r * Real.cos t) ^ 2) :=
    denominator_pos hr0 hr1
  exact div_nonneg (mul_nonneg (mul_nonneg hr0 hr2) hcos)
    (mul_nonneg hdp.le hsp.le)

theorem convexOn_angle {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ConvexOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
      (fun t => Real.arccos (r * Real.cos t)) := by
  by_cases hr : r < 1
  · exact convexOn_angle_lt_one hr0 hr
  have hreq : r = 1 := by linarith
  subst r
  have hnorm : ConvexOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
      (fun t : ℝ => |t|) := by
    have hnorm0 : ConvexOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
        (norm : ℝ → ℝ) := convexOn_norm (convex_Icc _ _)
    convert hnorm0 using 1
  apply hnorm.congr
  intro t ht
  rcases ht with ⟨hl, hu⟩
  simp only [one_mul]
  rcases le_total 0 t with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg, Real.arccos_cos hnonneg]
    linarith [Real.pi_pos]
  · have hneg : 0 ≤ -t := by linarith
    rw [abs_of_nonpos hnonpos, ← Real.cos_neg, Real.arccos_cos hneg]
    linarith [Real.pi_pos]

#print axioms C4Rotation.convexOn_angle

end C4Rotation
