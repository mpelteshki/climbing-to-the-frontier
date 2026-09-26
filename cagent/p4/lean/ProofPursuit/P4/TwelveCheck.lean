import ProofPursuit.P4.FiniteSearch
namespace ProofPursuit.P4.TwelveCheck
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
/-- All non-prime-power divisors of lcm(1,...,11), with multiples of 11 first. -/
def values : List Nat := [22, 33, 44, 55, 66, 77, 88, 99, 110, 132, 154, 165, 198, 220, 231, 264, 308, 330, 385, 396, 440, 462, 495, 616, 660, 693, 770, 792, 924, 990, 1155, 1320, 1386, 1540, 1848, 1980, 2310, 2772, 3080, 3465, 3960, 4620, 5544, 6930, 9240, 13860, 27720, 6, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45, 56, 60, 63, 70, 72, 84, 90, 105, 120, 126, 140, 168, 180, 210, 252, 280, 315, 360, 420, 504, 630, 840, 1260, 2520]
def modulus (rank : Nat) : Nat := values.getD rank 0
def good (ranks : List Nat) : Bool :=
  (ranks.take 3).all (fun x => x < 47) &&
  decide ((ranks.map modulus).Pairwise (fun x y => 1 < Nat.gcd x y ∧ Nat.gcd x y < 12))
/-- Arithmetic certificate only; the semantic normal-form bridge is separate. -/
theorem checked : FiniteSearch.search (List.range 87) good 12 [] = false := by decide

theorem no_sorted_candidate : ¬ ∃ xs : List Nat,
    xs.length = 12 ∧ xs.Pairwise (· ≤ ·) ∧
    (∀ x ∈ xs, x ∈ List.range 87) ∧ FiniteSearch.EveryPrefixPasses good xs :=
  FiniteSearch.no_sorted_good_of_false _ _ _ checked
#print axioms no_sorted_candidate
end ProofPursuit.P4.TwelveCheck
