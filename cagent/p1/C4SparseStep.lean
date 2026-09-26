import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Max
import C4Extremum
import C4Rotation

namespace C4SparseStep

/-- A positive initial inner product determines a cosine phase whose positive
semicircle contains the initial configuration strictly in its interior. -/
theorem cosine_phase {a b : ℝ} (ha : 0 < a) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ∃ r p : ℝ, 0 < r ∧ r ≤ 1 ∧ -(Real.pi / 2) < p ∧ p < Real.pi / 2 ∧
      ∀ t : ℝ, a * Real.cos t + b * Real.sin t = r * Real.cos (t - p) := by
  let r := Real.sqrt (a ^ 2 + b ^ 2)
  have hrad : 0 < a ^ 2 + b ^ 2 := by positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hrad.le
  have hr1 : r ≤ 1 := by nlinarith
  have hblo : -r < b := by nlinarith [sq_pos_of_pos ha]
  have hbhi : b < r := by nlinarith [sq_pos_of_pos ha]
  have hratio0 : -1 < b / r := by
    apply (lt_div_iff₀ hr).2
    linarith
  have hratio1 : b / r < 1 := (div_lt_one hr).2 hbhi
  let p := Real.arcsin (b / r)
  have hp0 : -(Real.pi / 2) < p := Real.neg_pi_div_two_lt_arcsin.mpr hratio0
  have hp1 : p < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hratio1
  have hsin : Real.sin p = b / r := Real.sin_arcsin hratio0.le hratio1.le
  have hcos : Real.cos p = a / r := by
    have hcos0 : 0 ≤ Real.cos p := Real.cos_arcsin_nonneg _
    have hsquare : (Real.cos p) ^ 2 = (a / r) ^ 2 := by
      have hid := Real.sin_sq_add_cos_sq p
      rw [hsin] at hid
      have hrat : (a / r) ^ 2 + (b / r) ^ 2 = 1 := by
        field_simp
        nlinarith only [hr2]
      nlinarith only [hid, hrat]
    nlinarith only [hsquare, hcos0, div_pos ha hr]
  refine ⟨r, p, hr, hr1, hp0, hp1, ?_⟩
  intro t
  rw [Real.cos_sub, hcos, hsin]
  field_simp

/-- A finite nonempty family of positive cosine arcs has a common closed
interval around zero, and one arc vanishes at its left endpoint. -/
theorem common_positive_segment {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, -(Real.pi / 2) < p i ∧ p i < Real.pi / 2) :
    ∃ l u : ℝ, l < 0 ∧ 0 < u ∧
      (∀ i t, t ∈ Set.Icc l u → t - p i ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
      ∃ i, Real.cos (l - p i) = 0 := by
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  refine ⟨p imax - Real.pi / 2, p imin + Real.pi / 2, by linarith [(hp imax).2],
    by linarith [(hp imin).1], ?_, ?_⟩
  · intro i t ht
    have hi0 := hmax i (Finset.mem_univ i)
    have hi1 := hmin i (Finset.mem_univ i)
    constructor <;> linarith [ht.1, ht.2]
  · refine ⟨imax, ?_⟩
    rw [show p imax - Real.pi / 2 - p imax = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two]

/-- The finite-family part of the first-zero rotation argument. The individual
arc convexity hypothesis is discharged by the analytic rotation theorem. -/
theorem phase_family_endpoint {ι : Type*} [Fintype ι] [Nonempty ι]
    (r p : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hp : ∀ i, -(Real.pi / 2) < p i ∧ p i < Real.pi / 2)
    (hconv : ∀ i, ConvexOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
      (fun t => Real.arccos (r i * Real.cos t)))
    (hmax : ∀ t : ℝ,
      (∑ i, Real.arccos |r i * Real.cos (t - p i)|) ≤
      ∑ i, Real.arccos |r i * Real.cos (0 - p i)|) :
    ∃ t : ℝ,
      (∑ i, Real.arccos |r i * Real.cos (t - p i)|) =
        (∑ i, Real.arccos |r i * Real.cos (0 - p i)|) ∧
      ∃ i, r i * Real.cos (t - p i) = 0 := by
  obtain ⟨l, u, hl, hu, hseg, izero, hzero⟩ := common_positive_segment p hp
  let f : ℝ → ℝ := fun t => ∑ i, Real.arccos |r i * Real.cos (t - p i)|
  have heach (i : ι) : ConvexOn ℝ (Set.Icc l u)
      (fun t => Real.arccos |r i * Real.cos (t - p i)|) := by
    have hsub : Set.Icc l u ⊆
        (fun t => -p i + t) ⁻¹' Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      intro t ht
      simpa only [Set.mem_preimage, sub_eq_add_neg, add_comm] using hseg i t ht
    have hshift := ((hconv i).translate_right (-p i)).subset hsub (convex_Icc l u)
    apply hshift.congr
    intro t ht
    have hnonneg : 0 ≤ r i * Real.cos (t - p i) :=
      mul_nonneg (hr i) (Real.cos_nonneg_of_mem_Icc (hseg i t ht))
    change Real.arccos (r i * Real.cos (-p i + t)) =
      Real.arccos |r i * Real.cos (t - p i)|
    rw [show -p i + t = t - p i by ring, abs_of_nonneg hnonneg]
  have hsum : ConvexOn ℝ (Set.Icc l u) f := by
    refine ⟨convex_Icc l u, ?_⟩
    intro x hx y hy a b ha hb hab
    change (∑ i, Real.arccos |r i * Real.cos (a * x + b * y - p i)|) ≤
      a * (∑ i, Real.arccos |r i * Real.cos (x - p i)|) +
        b * (∑ i, Real.arccos |r i * Real.cos (y - p i)|)
    calc
      _ ≤ ∑ i, (a * Real.arccos |r i * Real.cos (x - p i)| +
          b * Real.arccos |r i * Real.cos (y - p i)|) := by
        apply Finset.sum_le_sum
        intro i _
        exact (heach i).2 hx hy ha hb hab
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hend := (C4Extremum.convex_max_endpoints hl hu hsum (fun t _ => hmax t)).1
  exact ⟨l, hend, izero, by rw [hzero, mul_zero]⟩

/-- A maximal finite sum of line angles can be rotated until one positive
initial inner product vanishes, without changing the sum. -/
theorem positive_coefficient_endpoint {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, (a i) ^ 2 + (b i) ^ 2 ≤ 1)
    (hmax : ∀ t : ℝ,
      (∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t|) ≤
      ∑ i, Real.arccos |a i|) :
    ∃ t : ℝ,
      (∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t|) =
        (∑ i, Real.arccos |a i|) ∧
      ∃ i, a i * Real.cos t + b i * Real.sin t = 0 := by
  classical
  choose r p hr0 hr1 hp0 hp1 heq using fun i => cosine_phase (ha i) (hab i)
  have hsum (t : ℝ) :
      (∑ i, Real.arccos |r i * Real.cos (t - p i)|) =
      ∑ i, Real.arccos |a i * Real.cos t + b i * Real.sin t| := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← heq i t]
  have hsum0 : (∑ i, Real.arccos |r i * Real.cos (0 - p i)|) =
      ∑ i, Real.arccos |a i| := by
    simpa only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero] using hsum 0
  obtain ⟨t, ht, i, hi⟩ := phase_family_endpoint r p (fun i => (hr0 i).le)
    (fun i => ⟨hp0 i, hp1 i⟩) (fun i => C4Rotation.convexOn_angle (hr0 i).le (hr1 i))
    (fun t => by rw [hsum t, hsum0]; exact hmax t)
  refine ⟨t, ?_, i, ?_⟩
  · rwa [hsum t, hsum0] at ht
  · rwa [heq i t]

#print axioms cosine_phase
#print axioms common_positive_segment
#print axioms phase_family_endpoint
#print axioms positive_coefficient_endpoint
end C4SparseStep
