import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Genuine Euclidean cases of P1. Vectors use Cartesian coordinates;
`unit2` is exactly squared Euclidean norm = 1. No general cell claimed here. -/
namespace Angles

abbrev Vec2 := ℝ × ℝ

def dot2 (x y : Vec2) : ℝ := x.1 * y.1 + x.2 * y.2
def unit2 (x : Vec2) : Prop := dot2 x x = 1
noncomputable def angle2 (x y : Vec2) : ℝ := Real.arccos |dot2 x y|

 theorem angle2_nonneg (x y : Vec2) : 0 ≤ angle2 x y := Real.arccos_nonneg _
 theorem angle2_le (x y : Vec2) : angle2 x y ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.mpr (abs_nonneg _)

 theorem dot2_bound {x y : Vec2} (hx : unit2 x) (hy : unit2 y) :
    |dot2 x y| ≤ 1 := by
  dsimp [unit2, dot2] at *
  have h := sq_nonneg (x.1 * y.2 - x.2 * y.1)
  have hid : (x.1*y.1+x.2*y.2)^2 + (x.1*y.2-x.2*y.1)^2 =
      (x.1*x.1+x.2*x.2)*(y.1*y.1+y.2*y.2) := by ring
  rw [hx, hy] at hid
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x.1*y.1+x.2*y.2+1),
    sq_nonneg (x.1*y.1+x.2*y.2-1)]

 theorem gram2 (x y z : Vec2) :
    dot2 x x * dot2 y y * dot2 z z + 2 * dot2 x y * dot2 y z * dot2 x z -
    dot2 x x * (dot2 y z)^2 - dot2 y y * (dot2 x z)^2 -
    dot2 z z * (dot2 x y)^2 = 0 := by
  dsimp [dot2]
  ring

 theorem arccos_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a^2 + b^2 = 1) : Real.arccos a + Real.arccos b = Real.pi / 2 := by
  have hs : Real.sqrt (1 - a^2) = b := by
    rw [show 1-a^2 = b^2 by nlinarith, Real.sqrt_sq hb]
  rw [Real.arccos_eq_arcsin ha, hs, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

/-- C2, full geometric case m=3 (not arbitrary m). -/
 theorem c2_m3 {x y z : Vec2} (hx : unit2 x) (hy : unit2 y) (hz : unit2 z)
    (hxz : dot2 x z = 0) : angle2 x y + angle2 y z = Real.pi / 2 := by
  have hg := gram2 x y z
  change dot2 x x = 1 at hx
  change dot2 y y = 1 at hy
  change dot2 z z = 1 at hz
  rw [hx, hy, hz, hxz] at hg
  apply arccos_pair (abs_nonneg _) (abs_nonneg _)
  simpa only [sq_abs] using (show (dot2 x y)^2 + (dot2 y z)^2 = 1 by nlinarith [hg])

/-- Analytic certificate used for three arbitrary planar lines. -/
 theorem arccos_triple {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (_hc1 : c ≤ 1)
    (h : 1 ≤ a^2 + b^2 + c^2 + 2*a*b*c) :
    Real.arccos a + Real.arccos b + Real.arccos c ≤ Real.pi := by
  have hsa : (Real.sqrt (1-a^2))^2 = 1-a^2 :=
    Real.sq_sqrt (by nlinarith)
  have hsb : (Real.sqrt (1-b^2))^2 = 1-b^2 :=
    Real.sq_sqrt (by nlinarith)
  have hsab : Real.sqrt (1-a^2) * Real.sqrt (1-b^2) ≤ c+a*b := by
    have hprod : (Real.sqrt (1-a^2) * Real.sqrt (1-b^2))^2 =
        (1-a^2)*(1-b^2) := by rw [mul_pow, hsa, hsb]
    have hnn := mul_nonneg ha hb
    have hsn := mul_nonneg (Real.sqrt_nonneg (1-a^2)) (Real.sqrt_nonneg (1-b^2))
    nlinarith [sq_nonneg (c+a*b-Real.sqrt (1-a^2)*Real.sqrt (1-b^2))]
  have hcosa : Real.cos (Real.arccos a) = a := Real.cos_arccos (by linarith) ha1
  have hcosb : Real.cos (Real.arccos b) = b := Real.cos_arccos (by linarith) hb1
  have hcos : -Real.cos (Real.arccos a + Real.arccos b) ≤ c := by
    rw [Real.cos_add, hcosa, hcosb, Real.sin_arccos, Real.sin_arccos]
    linarith
  have hsum0 : 0 ≤ Real.arccos a + Real.arccos b :=
    add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _)
  have hsump : Real.arccos a + Real.arccos b ≤ Real.pi := by
    linarith [Real.arccos_le_pi_div_two.mpr ha, Real.arccos_le_pi_div_two.mpr hb]
  have hc' := Real.arccos_le_arccos hcos
  rw [Real.arccos_neg, Real.arccos_cos hsum0 hsump] at hc'
  linarith

/-- C1 with N=3: all real unit vectors, no finite grid restriction. -/
 theorem c1_n3 {x y z : Vec2} (hx : unit2 x) (hy : unit2 y) (hz : unit2 z) :
    angle2 x y + angle2 x z + angle2 y z ≤ Real.pi := by
  have hg := gram2 x y z
  change dot2 x x = 1 at hx
  change dot2 y y = 1 at hy
  change dot2 z z = 1 at hz
  rw [hx, hy, hz] at hg
  have hp : -(dot2 x y * dot2 x z * dot2 y z) ≤
      |dot2 x y| * |dot2 x z| * |dot2 y z| := by
    calc
      _ ≤ |dot2 x y * dot2 x z * dot2 y z| := neg_le_abs _
      _ = _ := by simp only [abs_mul]
  apply arccos_triple (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (dot2_bound hx hy) (dot2_bound hx hz) (dot2_bound hy hz)
  simp only [sq_abs]
  nlinarith [hg, hp]

/-- C1, N=4, obtained by adding the four three-line inequalities. -/
 theorem c1_n4 {w x y z : Vec2} (hw : unit2 w) (hx : unit2 x)
    (hy : unit2 y) (hz : unit2 z) :
    angle2 w x + angle2 w y + angle2 w z + angle2 x y + angle2 x z + angle2 y z ≤
      2 * Real.pi := by
  linarith [c1_n3 hw hx hy, c1_n3 hw hx hz, c1_n3 hw hy hz, c1_n3 hx hy hz]

/-- C2, m=2, in R¹. This also supplies C3, d=1. -/
 theorem c2_m2 {x y : ℝ} (hx : x*x=1) (hy : y*y=1) :
    Real.arccos |x*y| = 0 := by
  have hs : (x*y)^2=1 := by
    calc
      (x*y)^2 = (x*x)*(y*y) := by ring
      _ = 1 := by rw [hx, hy]; norm_num
  have hab : |x*y|=1 := by
    have := sq_abs (x*y)
    have := abs_nonneg (x*y)
    nlinarith
  rw [hab, Real.arccos_one]

/-- C3, d=2, is the three-line planar case. -/
 theorem c3_d2 {x y z : Vec2} (hx : unit2 x) (hy : unit2 y) (hz : unit2 z) :
    angle2 x y + angle2 x z + angle2 y z ≤ Real.pi := c1_n3 hx hy hz

/-- C5, d=2, is the four-line planar case. -/
 theorem c5_d2 {w x y z : Vec2} (hw : unit2 w) (hx : unit2 x)
    (hy : unit2 y) (hz : unit2 z) :
    angle2 w x + angle2 w y + angle2 w z + angle2 x y + angle2 x z + angle2 y z ≤
      2 * Real.pi := c1_n4 hw hx hy hz

#print axioms c2_m2
#print axioms c1_n4
#print axioms c3_d2
#print axioms c5_d2
#print axioms c2_m3
#print axioms c1_n3
end Angles
