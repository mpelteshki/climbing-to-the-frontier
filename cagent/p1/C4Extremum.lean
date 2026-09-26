import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace C4Extremum

/-- An interior maximum of a convex function forces both endpoint values to equal it. -/
theorem convex_max_endpoints {f : ℝ → ℝ} {l r : ℝ}
    (hl : l < 0) (hr : 0 < r) (hconv : ConvexOn ℝ (Set.Icc l r) f)
    (hmax : ∀ t ∈ Set.Icc l r, f t ≤ f 0) :
    f l = f 0 ∧ f r = f 0 := by
  have hd : 0 < r - l := by linarith
  let a : ℝ := r / (r - l)
  let b : ℝ := -l / (r - l)
  have ha : 0 < a := div_pos hr hd
  have hb : 0 < b := div_pos (neg_pos.mpr hl) hd
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div]
    have hnum : r + -l = r - l := by ring
    rw [hnum]
    exact div_self (ne_of_gt hd)
  have hzero : a • l + b • r = (0 : ℝ) := by
    dsimp [a, b]
    field_simp [ne_of_gt hd]
    ring
  have hlin : l ∈ Set.Icc l r := ⟨le_rfl, by linarith⟩
  have hrin : r ∈ Set.Icc l r := ⟨by linarith, le_rfl⟩
  have hweighted := hconv.2 hlin hrin ha.le hb.le hab
  rw [hzero] at hweighted
  simp only [smul_eq_mul] at hweighted
  have hfl : f l ≤ f 0 := hmax l hlin
  have hfr : f r ≤ f 0 := hmax r hrin
  have hsum : a * f 0 + b * f 0 = f 0 := by
    calc
      a * f 0 + b * f 0 = (a + b) * f 0 := by ring
      _ = f 0 := by rw [hab]; ring
  constructor
  · apply le_antisymm hfl
    by_contra h
    have hlt : f l < f 0 := lt_of_not_ge h
    have hltmul : a * f l < a * f 0 := mul_lt_mul_of_pos_left hlt ha
    have hlemul : b * f r ≤ b * f 0 := mul_le_mul_of_nonneg_left hfr hb.le
    linarith
  · apply le_antisymm hfr
    by_contra h
    have hlt : f r < f 0 := lt_of_not_ge h
    have hltmul : b * f r < b * f 0 := mul_lt_mul_of_pos_left hlt hb
    have hlemul : a * f l ≤ a * f 0 := mul_le_mul_of_nonneg_left hfl ha.le
    linarith

/-- Abstract endpoint contradiction used after a rotation is shown to preserve constraints. -/
theorem rotation_endpoint_contradiction {α : Type*} (rotation : ℝ → α)
    (objective : α → ℝ) (complexity : α → ℕ) {x : α} {l r : ℝ}
    (hl : l < 0) (hr : 0 < r)
    (hconv : ConvexOn ℝ (Set.Icc l r) (objective ∘ rotation))
    (hzero : rotation 0 = x)
    (hmax : ∀ y, objective y ≤ objective x)
    (hselect : ∀ y, objective y = objective x → complexity y ≤ complexity x)
    (hgain : complexity x < complexity (rotation l) ∨
      complexity x < complexity (rotation r)) : False := by
  have hmax' : ∀ t ∈ Set.Icc l r,
      (objective ∘ rotation) t ≤ (objective ∘ rotation) 0 := by
    intro t _
    simpa only [Function.comp_apply, hzero] using hmax (rotation t)
  obtain ⟨hle, hre⟩ := convex_max_endpoints hl hr hconv hmax'
  rcases hgain with hgain | hgain
  · have heq : objective (rotation l) = objective x := by
      simpa only [Function.comp_apply, hzero] using hle
    exact (not_lt_of_ge (hselect (rotation l) heq)) hgain
  · have heq : objective (rotation r) = objective x := by
      simpa only [Function.comp_apply, hzero] using hre
    exact (not_lt_of_ge (hselect (rotation r) heq)) hgain

#print axioms convex_max_endpoints
#print axioms rotation_endpoint_contradiction

end C4Extremum
