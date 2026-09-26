import C4Pentagon

/-! The explicit coordinate five-cycle scalar inequality. -/
namespace C4FiveCycle

private theorem asin_ratio_data {x y L : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hLpos : 0 < L) (hL2 : L ^ 2 = x ^ 2 + y ^ 2) :
    Real.sin (Real.arcsin (x / L)) = x / L ∧
      Real.cos (Real.arcsin (x / L)) = y / L ∧
      0 ≤ Real.arcsin (x / L) ∧ Real.arcsin (x / L) ≤ Real.pi / 2 := by
  have hxL : x ≤ L := by nlinarith only [hL2, hx0, hy0, hLpos, sq_nonneg y]
  have hxratio0 : 0 ≤ x / L := div_nonneg hx0 hLpos.le
  have hxratio1 : x / L ≤ 1 := (div_le_one hLpos).mpr hxL
  have hcos : Real.cos (Real.arcsin (x / L)) = y / L := by
    rw [Real.cos_arcsin]
    have hrad : 0 ≤ 1 - (x / L) ^ 2 := by nlinarith [sq_nonneg (x / L - 1)]
    have hsq : (Real.sqrt (1 - (x / L) ^ 2)) ^ 2 = (y / L) ^ 2 := by
      rw [Real.sq_sqrt hrad]
      calc
        1 - (x / L) ^ 2 = (L ^ 2 - x ^ 2) / L ^ 2 := by field_simp
        _ = (y / L) ^ 2 := by rw [div_pow, hL2]; ring
    nlinarith only [hsq, Real.sqrt_nonneg (1 - (x / L) ^ 2),
      div_nonneg hy0 hLpos.le]
  exact ⟨Real.sin_arcsin (by linarith) hxratio1, hcos,
    Real.arcsin_nonneg.mpr hxratio0, Real.arcsin_le_pi_div_two _⟩

set_option maxHeartbeats 1000000 in
/-- Five-cycle deficiency bound for the nondegenerate coordinate model. -/
theorem explicit_five_cycle {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Real.pi ≤
      Real.arcsin (c * Real.sqrt (1 - a ^ 2) /
        Real.sqrt (a ^ 2 + c ^ 2 - a ^ 2 * c ^ 2)) +
      Real.arcsin (a * Real.sqrt (1 - c ^ 2) /
        Real.sqrt (a ^ 2 + c ^ 2 - a ^ 2 * c ^ 2)) +
      Real.arcsin c +
      Real.arcsin (Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - c ^ 2)) +
      Real.arcsin a := by
  let s := Real.sqrt (1 - a ^ 2)
  let t := Real.sqrt (1 - c ^ 2)
  let L := Real.sqrt (a ^ 2 + c ^ 2 - a ^ 2 * c ^ 2)
  let u := c * s / L
  let v := a * t / L
  let E := Real.arcsin (a * c / (1 + s * t))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have ht2 : t ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs1 : s ≤ 1 := by nlinarith only [hs0, hs2, sq_nonneg a]
  have ht1 : t ≤ 1 := by nlinarith only [ht0, ht2, sq_nonneg c]
  have hL2 : L ^ 2 = a ^ 2 + c ^ 2 - a ^ 2 * c ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [mul_nonneg (sq_nonneg c) (by nlinarith only [ha0.le, ha1.le])]
  have hLpos : 0 < L := by
    have hL0 := Real.sqrt_nonneg (a ^ 2 + c ^ 2 - a ^ 2 * c ^ 2)
    have haux := mul_nonneg (sq_nonneg c) (by nlinarith only [ha0.le, ha1.le] : 0 ≤ 1 - a ^ 2)
    dsimp [L] at *
    nlinarith only [hL0, hL2, haux, ha0]
  have hxsq : L ^ 2 = (c * s) ^ 2 + a ^ 2 := by
    rw [mul_pow, hs2, hL2]
    ring
  have hysq : L ^ 2 = (a * t) ^ 2 + c ^ 2 := by
    rw [mul_pow, ht2, hL2]
    ring
  have hu := asin_ratio_data (mul_nonneg hc0.le hs0) ha0.le hLpos hxsq
  have hv := asin_ratio_data (mul_nonneg ha0.le ht0) hc0.le hLpos hysq
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hst1 : s * t ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) ht0]
  have hdpos : 0 < 1 + s * t := by linarith
  have hprod : (s * t) ^ 2 = (1 - a ^ 2) * (1 - c ^ 2) := by
    rw [mul_pow, hs2, ht2]
  have hLrelation : L ^ 2 = 1 - (s * t) ^ 2 := by
    rw [hL2, hprod]
    ring
  have hratioE0 : 0 ≤ a * c / (1 + s * t) := by positivity
  have hratioE1 : a * c / (1 + s * t) ≤ 1 := by
    apply (div_le_one hdpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1.le) hc0.le]
  have hsinE : Real.sin E = a * c / (1 + s * t) :=
    Real.sin_arcsin (by linarith) hratioE1
  have hE0 : 0 ≤ E := Real.arcsin_nonneg.mpr hratioE0
  have hE1 : E ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsumcos : Real.cos (Real.arcsin u + Real.arcsin v) =
      a * c / (1 + s * t) := by
    rw [Real.cos_add, hu.2.1, hv.2.1, hu.1, hv.1]
    calc
      a / L * (c / L) - c * s / L * (a * t / L) =
          (a * c * (1 - s * t)) / L ^ 2 := by ring
      _ = a * c / (1 + s * t) := by
        have hLne : L ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hLpos)
        field_simp
        nlinarith only [hLrelation]
  have hsum0 : 0 ≤ Real.arcsin u + Real.arcsin v := add_nonneg hu.2.2.1 hv.2.2.1
  have hsumpi : Real.arcsin u + Real.arcsin v ≤ Real.pi := by
    linarith [hu.2.2.2, hv.2.2.2]
  have hsum : Real.arcsin u + Real.arcsin v = Real.pi / 2 - E := by
    have hcosTarget : Real.cos (Real.pi / 2 - E) = a * c / (1 + s * t) := by
      rw [Real.cos_pi_div_two_sub, hsinE]
    have htarget0 : 0 ≤ Real.pi / 2 - E := by linarith
    have htargetpi : Real.pi / 2 - E ≤ Real.pi := by linarith [Real.pi_pos]
    have h1 := Real.arccos_cos hsum0 hsumpi
    have h2 := Real.arccos_cos htarget0 htargetpi
    rw [hsumcos] at h1
    rw [hcosTarget] at h2
    linarith
  have hacosS : Real.arccos s = Real.arcsin a := by
    have haasin0 : 0 ≤ Real.arcsin a := Real.arcsin_nonneg.mpr ha0.le
    have haasin1 : Real.arcsin a ≤ Real.pi := by
      linarith [Real.arcsin_le_pi_div_two a, Real.pi_pos]
    rw [← Real.arccos_cos haasin0 haasin1, Real.cos_arcsin]
  have hacosT : Real.arccos t = Real.arcsin c := by
    have hcasin0 : 0 ≤ Real.arcsin c := Real.arcsin_nonneg.mpr hc0.le
    have hcasin1 : Real.arcsin c ≤ Real.pi := by
      linarith [Real.arcsin_le_pi_div_two c, Real.pi_pos]
    rw [← Real.arccos_cos hcasin0 hcasin1, Real.cos_arcsin]
  have hP := C4Pentagon.pentagon_scalar hs0 hs1 ht0 ht1
  rw [show 1 - s ^ 2 = a ^ 2 by nlinarith [hs2],
      show 1 - t ^ 2 = c ^ 2 by nlinarith [ht2],
      Real.sqrt_sq ha0.le, Real.sqrt_sq hc0.le, hacosS, hacosT] at hP
  have hst : Real.arcsin (s * t) = Real.pi / 2 - Real.arccos (s * t) :=
    Real.arcsin_eq_pi_div_two_sub_arccos _
  change Real.arccos (s * t) + E ≤ Real.arcsin a + Real.arcsin c at hP
  change Real.pi ≤ Real.arcsin u + Real.arcsin v + Real.arcsin c +
    Real.arcsin (s * t) + Real.arcsin a
  linarith only [hsum, hP, hst]

#print axioms explicit_five_cycle
end C4FiveCycle
