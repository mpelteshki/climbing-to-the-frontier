import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! A scalar pentagon inequality for acute angles. -/
namespace C4Pentagon

private theorem sqrt_one_sub_sq_ge_one_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    1 - a ≤ Real.sqrt (1 - a ^ 2) := by
  have hsq : (Real.sqrt (1 - a ^ 2)) ^ 2 = 1 - a ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hs := Real.sqrt_nonneg (1 - a ^ 2)
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]

/-- The scalar estimate needed to close the acute C4 pentagon argument. -/
theorem pentagon_scalar {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.arccos (a * b) +
      Real.arcsin ((Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2)) / (1 + a * b)) ≤
    Real.arccos a + Real.arccos b := by
  let s := Real.sqrt (1 - a ^ 2)
  let t := Real.sqrt (1 - b ^ 2)
  let r := s * t
  let u := a * b
  let d := 1 + u
  let L := Real.sqrt (1 - u ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have ht2 : t ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hr0 : 0 ≤ r := mul_nonneg hs0 ht0
  have hu0 : 0 ≤ u := mul_nonneg ha0 hb0
  have hu1 : u ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb0]
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hL2 : L ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by nlinarith)
  have hL1 : L ≤ 1 := by nlinarith
  have hr2 : r ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) := by
    dsimp [r]
    rw [mul_pow, hs2, ht2]
  have hidentity : d ^ 2 - r ^ 2 = (a + b) ^ 2 := by
    dsimp [d, u]
    rw [hr2]
    ring
  have hab0 : 0 ≤ a + b := by linarith
  have hrd : r ≤ d := by nlinarith [sq_nonneg (a + b)]
  have hratio0 : 0 ≤ r / d := div_nonneg hr0 hdpos.le
  have hratio1 : r / d ≤ 1 := (div_le_one hdpos).mpr hrd
  have hcosE : Real.cos (Real.arcsin (r / d)) = (a + b) / d := by
    rw [Real.cos_arcsin]
    have hrad : 0 ≤ 1 - (r / d) ^ 2 := by nlinarith [sq_nonneg (r / d - 1)]
    have hsq : (Real.sqrt (1 - (r / d) ^ 2)) ^ 2 = ((a + b) / d) ^ 2 := by
      rw [Real.sq_sqrt hrad]
      calc
        1 - (r / d) ^ 2 = (d ^ 2 - r ^ 2) / d ^ 2 := by field_simp
        _ = ((a + b) / d) ^ 2 := by rw [hidentity, div_pow]
    nlinarith only [hsq, Real.sqrt_nonneg (1 - (r / d) ^ 2),
      div_nonneg hab0 hdpos.le]
  have hrbound : (1 - a) * (1 - b) ≤ r := by
    have hsa : 1 - a ≤ s := sqrt_one_sub_sq_ge_one_sub ha0 ha1
    have htb : 1 - b ≤ t := sqrt_one_sub_sq_ge_one_sub hb0 hb1
    have h1a : 0 ≤ 1 - a := by linarith
    have h1b : 0 ≤ 1 - b := by linarith
    exact (mul_le_mul hsa htb h1b hs0).trans_eq rfl
  have hcosc : Real.cos (Real.arccos u) = u := Real.cos_arccos (by linarith) hu1
  have hcospa : Real.cos (Real.arccos a) = a := Real.cos_arccos (by linarith) ha1
  have hcosqb : Real.cos (Real.arccos b) = b := Real.cos_arccos (by linarith) hb1
  have hsinc : Real.sin (Real.arccos u) = L := Real.sin_arccos u
  have hsinpa : Real.sin (Real.arccos a) = s := Real.sin_arccos a
  have hsinqb : Real.sin (Real.arccos b) = t := Real.sin_arccos b
  have hsinE : Real.sin (Real.arcsin (r / d)) = r / d :=
    Real.sin_arcsin (by linarith) hratio1
  have hcosineq :
      Real.cos (Real.arccos a + Real.arccos b) ≤
      Real.cos (Real.arccos u + Real.arcsin (r / d)) := by
    rw [Real.cos_add, Real.cos_add, hcospa, hcosqb, hsinpa, hsinqb,
      hcosc, hsinc, hcosE, hsinE]
    have hfactor : u * (1 - a) * (1 - b) ≤ u * r := by
      calc
        u * (1 - a) * (1 - b) = u * ((1 - a) * (1 - b)) := by ring
        _ ≤ u * r := mul_le_mul_of_nonneg_left hrbound hu0
    have hL : L * r ≤ r := by simpa using mul_le_mul_of_nonneg_right hL1 hr0
    have htarget : (u - r) * d ≤ u * (a + b) - L * r := by
      dsimp [d]
      nlinarith only [hfactor, hL, hu0, hr0]
    change u - r ≤ u * ((a + b) / d) - L * (r / d)
    calc
      u - r ≤ (u * (a + b) - L * r) / d := (le_div_iff₀ hdpos).2 htarget
      _ = u * ((a + b) / d) - L * (r / d) := by ring
  have hleft0 : 0 ≤ Real.arccos u + Real.arcsin (r / d) :=
    add_nonneg (Real.arccos_nonneg _) (Real.arcsin_nonneg.mpr hratio0)
  have hleftpi : Real.arccos u + Real.arcsin (r / d) ≤ Real.pi := by
    linarith [Real.arccos_le_pi_div_two.mpr hu0, Real.arcsin_le_pi_div_two (r / d)]
  have hright0 : 0 ≤ Real.arccos a + Real.arccos b :=
    add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _)
  have hrightpi : Real.arccos a + Real.arccos b ≤ Real.pi := by
    linarith [Real.arccos_le_pi_div_two.mpr ha0, Real.arccos_le_pi_div_two.mpr hb0]
  have hangle : Real.arccos u + Real.arcsin (r / d) ≤
      Real.arccos a + Real.arccos b := by
    by_contra hn
    have hstrict := Real.strictAntiOn_cos ⟨hright0, hrightpi⟩
      ⟨hleft0, hleftpi⟩ (lt_of_not_ge hn)
    exact (not_lt_of_ge hcosineq) hstrict
  simpa only [s, t, r, u, d] using hangle

/-- Angle form of `pentagon_scalar` for angles in the first quadrant. -/
theorem pentagon_scalar_angles {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ Real.pi / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ Real.pi / 2) :
    Real.arccos (Real.cos p * Real.cos q) +
      Real.arcsin ((Real.sin p * Real.sin q) / (1 + Real.cos p * Real.cos q)) ≤
    p + q := by
  have hcp : 0 ≤ Real.cos p := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hp1⟩
  have hcq : 0 ≤ Real.cos q := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hq1⟩
  have hsp : 0 ≤ Real.sin p :=
    Real.sin_nonneg_of_nonneg_of_le_pi hp0 (by linarith [Real.pi_pos])
  have hsq : 0 ≤ Real.sin q :=
    Real.sin_nonneg_of_nonneg_of_le_pi hq0 (by linarith [Real.pi_pos])
  have hsp' : Real.sqrt (1 - Real.cos p ^ 2) = Real.sin p := by
    rw [show 1 - Real.cos p ^ 2 = Real.sin p ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq p], Real.sqrt_sq hsp]
  have hsq' : Real.sqrt (1 - Real.cos q ^ 2) = Real.sin q := by
    rw [show 1 - Real.cos q ^ 2 = Real.sin q ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq q], Real.sqrt_sq hsq]
  have h := pentagon_scalar hcp (Real.cos_le_one p) hcq (Real.cos_le_one q)
  rw [hsp', hsq', Real.arccos_cos hp0 (by linarith [Real.pi_pos]),
    Real.arccos_cos hq0 (by linarith [Real.pi_pos])] at h
  exact h

/-- The reverse three-angle certificate used for the six-cycle estimate. -/
theorem arccos_triple_ge_pi {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z ≤ 1) :
    Real.pi ≤ Real.arccos x + Real.arccos y + Real.arccos z := by
  have hsx : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hsy : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hprod : (Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2)) ^ 2 =
      (1 - x ^ 2) * (1 - y ^ 2) := by rw [mul_pow, hsx, hsy]
  have hxy0 : 0 ≤ x * y + z := by positivity
  have hroot0 : 0 ≤ Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2) := by
    positivity
  have hroot : x * y + z ≤ Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2) := by
    nlinarith only [h, hprod, hxy0, hroot0]
  have hcos : Real.cos (Real.arccos x + Real.arccos y) ≤ -z := by
    rw [Real.cos_add, Real.cos_arccos (by linarith) hx1,
      Real.cos_arccos (by linarith) hy1, Real.sin_arccos, Real.sin_arccos]
    linarith
  have hsum0 : 0 ≤ Real.arccos x + Real.arccos y :=
    add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _)
  have hsump : Real.arccos x + Real.arccos y ≤ Real.pi := by
    linarith [Real.arccos_le_pi_div_two.mpr hx0, Real.arccos_le_pi_div_two.mpr hy0]
  have hc' := Real.arccos_le_arccos hcos
  rw [Real.arccos_neg, Real.arccos_cos hsum0 hsump] at hc'
  linarith

/-- A spherical right-triangle relation identifies the gap angle. -/
theorem gap_angle_add_projection {B U T : ℝ}
    (hB0 : 0 ≤ B) (hB1 : B ≤ Real.pi / 2)
    (hU0 : 0 ≤ U) (hU1 : U ≤ Real.pi / 2)
    (hT0 : 0 ≤ T) (hT1 : T ≤ Real.pi / 2)
    (hrel : Real.sin B * Real.sin T = Real.cos B * Real.sin U * Real.cos T) :
    Real.arcsin ((Real.sin B * Real.sin U) / (1 + Real.cos B * Real.cos U)) + T =
      Real.arccos (Real.cos T * Real.cos U) := by
  let a := Real.cos B
  let b := Real.cos U
  let r := Real.sin B * Real.sin U
  let d := 1 + a * b
  have ha0 : 0 ≤ a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hB1⟩
  have hb0 : 0 ≤ b := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hU1⟩
  have ha1 : a ≤ 1 := Real.cos_le_one B
  have hb1 : b ≤ 1 := Real.cos_le_one U
  have hsB0 : 0 ≤ Real.sin B :=
    Real.sin_nonneg_of_nonneg_of_le_pi hB0 (by linarith [Real.pi_pos])
  have hsU0 : 0 ≤ Real.sin U :=
    Real.sin_nonneg_of_nonneg_of_le_pi hU0 (by linarith [Real.pi_pos])
  have hr0 : 0 ≤ r := mul_nonneg hsB0 hsU0
  have hdpos : 0 < d := by dsimp [d]; nlinarith [mul_nonneg ha0 hb0]
  have hBsq : (Real.sin B) ^ 2 = 1 - a ^ 2 := by
    dsimp [a]
    nlinarith [Real.sin_sq_add_cos_sq B]
  have hUsq : (Real.sin U) ^ 2 = 1 - b ^ 2 := by
    dsimp [b]
    nlinarith [Real.sin_sq_add_cos_sq U]
  have hr2 : r ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) := by
    dsimp [r]
    rw [mul_pow, hBsq, hUsq]
  have hidentity : d ^ 2 - r ^ 2 = (a + b) ^ 2 := by
    dsimp [d]
    rw [hr2]
    ring
  have hrd : r ≤ d := by nlinarith [sq_nonneg (a + b)]
  have hratio0 : 0 ≤ r / d := div_nonneg hr0 hdpos.le
  have hratio1 : r / d ≤ 1 := (div_le_one hdpos).mpr hrd
  have hcosE : Real.cos (Real.arcsin (r / d)) = (a + b) / d := by
    rw [Real.cos_arcsin]
    have hrad : 0 ≤ 1 - (r / d) ^ 2 := by nlinarith [sq_nonneg (r / d - 1)]
    have hsq : (Real.sqrt (1 - (r / d) ^ 2)) ^ 2 = ((a + b) / d) ^ 2 := by
      rw [Real.sq_sqrt hrad]
      calc
        1 - (r / d) ^ 2 = (d ^ 2 - r ^ 2) / d ^ 2 := by field_simp
        _ = ((a + b) / d) ^ 2 := by rw [hidentity, div_pow]
    nlinarith only [hsq, Real.sqrt_nonneg (1 - (r / d) ^ 2),
      div_nonneg (add_nonneg ha0 hb0) hdpos.le]
  have hsinE : Real.sin (Real.arcsin (r / d)) = r / d :=
    Real.sin_arcsin (by linarith) hratio1
  have hcos : Real.cos (Real.arcsin (r / d) + T) = Real.cos T * b := by
    rw [Real.cos_add, hcosE, hsinE]
    have hrelMul := congrArg (fun v : ℝ => v * Real.sin U) hrel
    have hUtrig := congrArg (fun v : ℝ => a * Real.cos T * v)
      (Real.sin_sq_add_cos_sq U)
    calc
      (a + b) / d * Real.cos T - r / d * Real.sin T =
          (Real.cos T * (a + b) - Real.sin T * r) / d := by ring
      _ = Real.cos T * b := by
        apply (div_eq_iff (ne_of_gt hdpos)).2
        dsimp [d, r, a, b] at *
        nlinarith only [hrelMul, hUtrig]
  have hangle0 : 0 ≤ Real.arcsin (r / d) + T :=
    add_nonneg (Real.arcsin_nonneg.mpr hratio0) hT0
  have hanglepi : Real.arcsin (r / d) + T ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two (r / d)]
  have htarget := Real.arccos_cos hangle0 hanglepi
  rw [hcos] at htarget
  simpa only [r, d, a, b] using htarget.symm

/-- Companion scalar inequality for the C4 six-cycle projection. -/
theorem six_cycle_scalar {T U V : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ Real.pi / 2)
    (hU0 : 0 ≤ U) (hU1 : U ≤ Real.pi / 2)
    (hV0 : 0 ≤ V) (hV1 : V ≤ Real.pi / 2) :
    Real.arcsin (Real.sin U * Real.sin V) ≤
      Real.arccos (Real.cos T * Real.cos U) +
        Real.arccos (Real.sin T * Real.cos V) - Real.pi / 2 := by
  let x := Real.cos T * Real.cos U
  let y := Real.sin T * Real.cos V
  let z := Real.sin U * Real.sin V
  have hcT0 : 0 ≤ Real.cos T := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hT1⟩
  have hcU0 : 0 ≤ Real.cos U := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hU1⟩
  have hcV0 : 0 ≤ Real.cos V := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hV1⟩
  have hsT0 : 0 ≤ Real.sin T := Real.sin_nonneg_of_nonneg_of_le_pi hT0 (by linarith [Real.pi_pos])
  have hsU0 : 0 ≤ Real.sin U := Real.sin_nonneg_of_nonneg_of_le_pi hU0 (by linarith [Real.pi_pos])
  have hsV0 : 0 ≤ Real.sin V := Real.sin_nonneg_of_nonneg_of_le_pi hV0 (by linarith [Real.pi_pos])
  have hx0 : 0 ≤ x := mul_nonneg hcT0 hcU0
  have hy0 : 0 ≤ y := mul_nonneg hsT0 hcV0
  have hz0 : 0 ≤ z := mul_nonneg hsU0 hsV0
  have hx1 : x ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (Real.cos_le_one T)) hcU0, Real.cos_le_one U]
  have hy1 : y ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_le_one T)) hcV0, Real.cos_le_one V]
  have hz1 : z ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_le_one U)) hsV0, Real.sin_le_one V]
  have hT : (Real.cos T) ^ 2 + (Real.sin T) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq T]
  have hU : (Real.cos U) ^ 2 + (Real.sin U) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq U]
  have hV : (Real.cos V) ^ 2 + (Real.sin V) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq V]
  have hcoeff : (Real.sin T) ^ 2 + (Real.cos T) ^ 2 * (Real.sin U) ^ 2 =
      (Real.sin U) ^ 2 + (Real.sin T) ^ 2 * (Real.cos U) ^ 2 := by
    have hcT : (Real.cos T) ^ 2 = 1 - (Real.sin T) ^ 2 := by linarith
    have hcU : (Real.cos U) ^ 2 = 1 - (Real.sin U) ^ 2 := by linarith
    rw [hcT, hcU]
    ring
  let w := Real.cos T * Real.sin U * Real.cos V -
    Real.sin T * Real.sin V * Real.cos U
  have hidentity : x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z + w ^ 2 = 1 := by
    calc
      x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z + w ^ 2 =
          (Real.cos T) ^ 2 * (Real.cos U) ^ 2 +
          (Real.cos V) ^ 2 * ((Real.sin T) ^ 2 + (Real.cos T) ^ 2 * (Real.sin U) ^ 2) +
          (Real.sin V) ^ 2 * ((Real.sin U) ^ 2 + (Real.sin T) ^ 2 * (Real.cos U) ^ 2) := by
        dsimp [x, y, z, w]
        ring
      _ = (Real.cos T) ^ 2 * (Real.cos U) ^ 2 +
          ((Real.cos V) ^ 2 + (Real.sin V) ^ 2) *
            ((Real.sin U) ^ 2 + (Real.sin T) ^ 2 * (Real.cos U) ^ 2) := by
        rw [hcoeff]
        ring
      _ = (Real.cos T) ^ 2 * (Real.cos U) ^ 2 +
          ((Real.sin U) ^ 2 + (Real.sin T) ^ 2 * (Real.cos U) ^ 2) := by rw [hV]; ring
      _ = ((Real.cos T) ^ 2 + (Real.sin T) ^ 2) * (Real.cos U) ^ 2 +
          (Real.sin U) ^ 2 := by ring
      _ = 1 := by rw [hT, one_mul, hU]
  have hcert : x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y * z ≤ 1 := by
    nlinarith only [hidentity, sq_nonneg w]
  have htri := arccos_triple_ge_pi hx0 hx1 hy0 hy1 hz0 hcert
  rw [show Real.arccos z = Real.pi / 2 - Real.arcsin z from rfl] at htri
  dsimp [x, y, z] at htri ⊢
  linarith

/-- The local C4 projection estimate under the exact right-triangle relations. -/
theorem local_projection_inequality {T B C U V : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T ≤ Real.pi / 2)
    (hB0 : 0 ≤ B) (hB1 : B ≤ Real.pi / 2)
    (hC0 : 0 ≤ C) (hC1 : C ≤ Real.pi / 2)
    (hU0 : 0 ≤ U) (hU1 : U ≤ Real.pi / 2)
    (hV0 : 0 ≤ V) (hV1 : V ≤ Real.pi / 2)
    (h1 : Real.sin B * Real.sin T = Real.cos B * Real.sin U * Real.cos T)
    (h2 : Real.sin C * Real.cos T = Real.cos C * Real.sin V * Real.sin T) :
    Real.arcsin (Real.sin U * Real.sin V) ≤
      (B + U - Real.arccos (Real.cos B * Real.cos U)) +
      (C + V - Real.arccos (Real.cos C * Real.cos V)) := by
  have hgap1 := gap_angle_add_projection hB0 hB1 hU0 hU1 hT0 hT1 h1
  have hT'0 : 0 ≤ Real.pi / 2 - T := by linarith
  have hT'1 : Real.pi / 2 - T ≤ Real.pi / 2 := by linarith
  have h2' : Real.sin C * Real.sin (Real.pi / 2 - T) =
      Real.cos C * Real.sin V * Real.cos (Real.pi / 2 - T) := by
    simpa only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] using h2
  have hgap2 := gap_angle_add_projection hC0 hC1 hV0 hV1 hT'0 hT'1 h2'
  rw [Real.cos_pi_div_two_sub] at hgap2
  have hbound1 := pentagon_scalar_angles hB0 hB1 hU0 hU1
  have hbound2 := pentagon_scalar_angles hC0 hC1 hV0 hV1
  have hsix := six_cycle_scalar hT0 hT1 hU0 hU1 hV0 hV1
  linarith

#print axioms pentagon_scalar
#print axioms pentagon_scalar_angles
#print axioms arccos_triple_ge_pi
#print axioms six_cycle_scalar
#print axioms gap_angle_add_projection
#print axioms local_projection_inequality
end C4Pentagon
