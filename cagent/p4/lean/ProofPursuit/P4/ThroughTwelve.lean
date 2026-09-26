import ProofPursuit.P4.Ten
import ProofPursuit.P4.Eleven
import ProofPursuit.P4.Twelve

namespace ProofPursuit.P4.ThroughTwelve

theorem through_ten : ∀ k : Nat, 2 ≤ k → k ≤ 10 → Statement k := by
  intro k hlo hhi
  by_cases h : k ≤ 9
  · exact ThroughNine.solution k hlo h
  · have : k = 10 := by omega
    subst k
    exact Ten.solution

theorem eleven : Statement 11 :=
  Eleven.step (fun k hlo hhi => through_ten k hlo (by omega))

theorem through_eleven : ∀ k : Nat, 2 ≤ k → k ≤ 11 → Statement k := by
  intro k hlo hhi
  by_cases h : k ≤ 10
  · exact through_ten k hlo h
  · have : k = 11 := by omega
    subst k
    exact eleven

/-- Every positive-modulus disjoint family with 2 through 12 classes has a
pair of moduli with gcd at least the number of classes. -/
theorem solution : ∀ k : Nat, 2 ≤ k → k ≤ 12 → Statement k := by
  intro k hlo hhi
  by_cases h : k ≤ 11
  · exact through_eleven k hlo h
  · have : k = 12 := by omega
    subst k
    exact Twelve.step (fun t htlo hthi => through_eleven t htlo (by omega))

#print axioms solution
end ProofPursuit.P4.ThroughTwelve
