import C4Selection
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped InnerProductSpace

namespace C4Configuration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev UnitVector (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

abbrev Configuration (E : Type*) [NormedAddCommGroup E] (n : ℕ) :=
  Fin n → UnitVector E

/-- Each unordered pair of indices appears once. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

noncomputable def totalAngle {n : ℕ} (v : Configuration E n) : ℝ :=
  ∑ p ∈ pairs n, Real.arccos |⟪(v p.1).1, (v p.2).1⟫_ℝ|

noncomputable def orthogonalityCount {n : ℕ} (v : Configuration E n) : ℕ :=
  ((pairs n).filter (fun p => ⟪(v p.1).1, (v p.2).1⟫_ℝ = 0)).card

theorem continuous_totalAngle (n : ℕ) :
    Continuous (totalAngle (E := E) (n := n)) := by
  classical
  unfold totalAngle
  apply continuous_finsetSum
  intro p _
  have hfirst : Continuous (fun v : Configuration E n => (v p.1).1) :=
    continuous_subtype_val.comp (continuous_apply p.1)
  have hsecond : Continuous (fun v : Configuration E n => (v p.2).1) :=
    continuous_subtype_val.comp (continuous_apply p.2)
  exact Real.continuous_arccos.comp ((hfirst.inner hsecond).abs)

theorem orthogonalityCount_le {n : ℕ} (v : Configuration E n) :
    orthogonalityCount v ≤ (pairs n).card := by
  classical
  exact Finset.card_filter_le _ _

/-- A geometric angle maximizer with the most orthogonal pairs among all ties. -/
theorem exists_lex_max {n : ℕ} [ProperSpace E] (u : UnitVector E) :
    ∃ v : Configuration E n,
      (∀ w : Configuration E n, totalAngle w ≤ totalAngle v) ∧
      (∀ w : Configuration E n, totalAngle w = totalAngle v →
        orthogonalityCount w ≤ orthogonalityCount v) := by
  have hne : (Set.univ : Set (Configuration E n)).Nonempty :=
    ⟨fun _ => u, Set.mem_univ _⟩
  obtain ⟨v, _, hmax, hselect⟩ :=
    C4Selection.compact_lex_max (K := Set.univ)
      (S := totalAngle (E := E) (n := n)) (C := orthogonalityCount)
      (M := (pairs n).card) isCompact_univ hne
      (continuous_totalAngle n).continuousOn
      (by intro w _; exact orthogonalityCount_le w)
  refine ⟨v, ?_, ?_⟩
  · intro w
    exact hmax w (Set.mem_univ w)
  · intro w hw
    exact hselect w (Set.mem_univ w) hw

#print axioms continuous_totalAngle
#print axioms orthogonalityCount_le
#print axioms exists_lex_max

end C4Configuration
