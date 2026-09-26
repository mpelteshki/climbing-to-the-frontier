import C4Pentagon

/-! The local six-cycle projection inequality in raw coordinates. -/
namespace C4SixCycle

private theorem arccos_ratio_data {x y L : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hLpos : 0 < L) (hL2 : L ^ 2 = x ^ 2 + y ^ 2) :
    Real.cos (Real.arccos (x / L)) = x / L ∧
      Real.sin (Real.arccos (x / L)) = y / L ∧
      0 ≤ Real.arccos (x / L) ∧ Real.arccos (x / L) ≤ Real.pi / 2 := by
  have hxL : x ≤ L := by nlinarith only [hL2, hx0, hy0, hLpos, sq_nonneg y]
  have hxratio0 : 0 ≤ x / L := div_nonneg hx0 hLpos.le
  have hxratio1 : x / L ≤ 1 := (div_le_one hLpos).mpr hxL
  have hsin : Real.sin (Real.arccos (x / L)) = y / L := by
    rw [Real.sin_arccos]
    have hrad : 0 ≤ 1 - (x / L) ^ 2 := by nlinarith [sq_nonneg (x / L - 1)]
    have hsq : (Real.sqrt (1 - (x / L) ^ 2)) ^ 2 = (y / L) ^ 2 := by
      rw [Real.sq_sqrt hrad]
      calc
        1 - (x / L) ^ 2 = (L ^ 2 - x ^ 2) / L ^ 2 := by field_simp
        _ = (y / L) ^ 2 := by rw [div_pow, hL2]; ring
    nlinarith only [hsq, Real.sqrt_nonneg (1 - (x / L) ^ 2),
      div_nonneg hy0 hLpos.le]
  exact ⟨Real.cos_arccos (by linarith) hxratio1, hsin,
    Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr hxratio0⟩

/-- Raw-coordinate local projection estimate for an irreducible six-cycle. -/
theorem raw_projection_inequality {a b c d u v : ℝ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d)
    (hu0 : 0 < u) (hv0 : 0 < v)
    (hleft : a ^ 2 + b ^ 2 + u ^ 2 = 1)
    (hright : c ^ 2 + d ^ 2 + v ^ 2 = 1)
    (hcross : u * v = b * c) :
    Real.arcsin (a / Real.sqrt (1 - b ^ 2)) +
      Real.arcsin (d / Real.sqrt (1 - c ^ 2)) +
      Real.arcsin (b * c /
        (Real.sqrt (1 - b ^ 2) * Real.sqrt (1 - c ^ 2))) ≤
      Real.arcsin a + Real.arcsin b + Real.arcsin c + Real.arcsin d := by
  let A := Real.sqrt (1 - b ^ 2)
  let D := Real.sqrt (1 - c ^ 2)
  let R := Real.sqrt (b ^ 2 + u ^ 2)
  let B := Real.arcsin b
  let C := Real.arcsin c
  let U := Real.arccos (a / A)
  let V := Real.arccos (d / D)
  let T := Real.arccos (b / R)
  have hA2 : A ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith only [hleft, sq_nonneg a, sq_nonneg u])
  have hD2 : D ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith only [hright, sq_nonneg d, sq_nonneg v])
  have hR2 : R ^ 2 = b ^ 2 + u ^ 2 := Real.sq_sqrt (by positivity)
  have hA2' : A ^ 2 = a ^ 2 + u ^ 2 := by nlinarith only [hA2, hleft]
  have hD2' : D ^ 2 = d ^ 2 + v ^ 2 := by nlinarith only [hD2, hright]
  have hApos : 0 < A := by
    have hA0 := Real.sqrt_nonneg (1 - b ^ 2)
    nlinarith only [hA0, hA2', ha0, sq_nonneg u]
  have hDpos : 0 < D := by
    have hD0 := Real.sqrt_nonneg (1 - c ^ 2)
    nlinarith only [hD0, hD2', hd0, sq_nonneg v]
  have hRpos : 0 < R := by
    have hR0 := Real.sqrt_nonneg (b ^ 2 + u ^ 2)
    nlinarith only [hR0, hR2, hb0, sq_nonneg u]
  have hb1 : b ≤ 1 := by nlinarith only [hleft, hb0, ha0, hu0]
  have hc1 : c ≤ 1 := by nlinarith only [hright, hc0, hd0, hv0]
  have hBsin : Real.sin B = b := Real.sin_arcsin (by linarith) hb1
  have hCsin : Real.sin C = c := Real.sin_arcsin (by linarith) hc1
  have hBcos : Real.cos B = A := Real.cos_arcsin b
  have hCcos : Real.cos C = D := Real.cos_arcsin c
  have hB0 : 0 ≤ B := Real.arcsin_nonneg.mpr hb0.le
  have hC0 : 0 ≤ C := Real.arcsin_nonneg.mpr hc0.le
  have hB1 : B ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hC1 : C ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hU := arccos_ratio_data ha0.le hu0.le hApos hA2'
  have hV := arccos_ratio_data hd0.le hv0.le hDpos hD2'
  have hT := arccos_ratio_data hb0.le hu0.le hRpos hR2
  have hrel1 : Real.sin B * Real.sin T = Real.cos B * Real.sin U * Real.cos T := by
    rw [hBsin, hT.2.1, hBcos, hU.2.1, hT.1]
    field_simp
  have hrel2 : Real.sin C * Real.cos T = Real.cos C * Real.sin V * Real.sin T := by
    rw [hCsin, hT.1, hCcos, hV.2.1, hT.2.1]
    field_simp
    nlinarith only [hcross]
  have hproj := C4Pentagon.local_projection_inequality
    hT.2.2.1 hT.2.2.2 hB0 hB1 hC0 hC1
    hU.2.2.1 hU.2.2.2 hV.2.2.1 hV.2.2.2 hrel1 hrel2
  have hsinUV : Real.sin U * Real.sin V = b * c / (A * D) := by
    rw [hU.2.1, hV.2.1, ← hcross]
    ring
  have hcosBU : Real.cos B * Real.cos U = a := by
    rw [hBcos, hU.1]
    field_simp
  have hcosCV : Real.cos C * Real.cos V = d := by
    rw [hCcos, hV.1]
    field_simp
  rw [hsinUV, hcosBU, hcosCV] at hproj
  simp only [Real.arccos_eq_pi_div_two_sub_arcsin] at hproj
  change Real.arcsin (a / A) + Real.arcsin (d / D) +
    Real.arcsin (b * c / (A * D)) ≤
    Real.arcsin a + Real.arcsin b + Real.arcsin c + Real.arcsin d
  dsimp [B, C] at hproj
  linarith

#print axioms raw_projection_inequality
end C4SixCycle
