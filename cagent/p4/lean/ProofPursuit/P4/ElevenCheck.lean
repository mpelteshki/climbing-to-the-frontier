import ProofPursuit.P4.FiniteSearch

namespace ProofPursuit.P4.ElevenCheck

/-- Rank order puts the 18 multiples of 10 before the remaining 22 moduli.
The values are precisely the non-prime-power divisors of 2520. -/
def values : List Nat :=
  [10, 20, 30, 40, 60, 70, 90, 120, 140, 180, 210, 280, 360, 420,
   630, 840, 1260, 2520,
   6, 12, 14, 15, 18, 21, 24, 28, 35, 36, 42, 45, 56, 63, 72,
   84, 105, 126, 168, 252, 315, 504]

def modulus (rank : Nat) : Nat := values.getD rank 0

def ranks : List Nat := List.range 40

private def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairs xs

private def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs =>
      let ss := subsets xs
      ss ++ ss.map (x :: ·)

private def pairOK (xs : List Nat) : Bool :=
  match xs.reverse with
  | [] => true
  | x :: earlier => earlier.all fun y =>
      let g := Nat.gcd (modulus x) (modulus y)
      decide (1 < g ∧ g < 11)

private def period (xs : List Nat) : Nat :=
  (pairs xs).foldl (fun acc (x, y) => Nat.lcm acc (Nat.gcd (modulus x) (modulus y))) 1

private def densityOK (xs : List Nat) : Bool :=
  let m := period xs
  decide ((xs.map (fun x => m / Nat.gcd (modulus x) m)).sum ≤ m)

private def newSubsets (xs : List Nat) : List (List Nat) :=
  match xs.reverse with
  | [] => []
  | x :: earlier => (subsets earlier).map (x :: ·)

/-- The rank test forces three multiples of 10 first. The pair and density
tests inspect only conditions involving the newly appended value; earlier
prefixes were checked on the preceding recursion levels. -/
def good (xs : List Nat) : Bool :=
  (if xs.length ≤ 3 then xs.all (fun x => x < 18) else true) &&
  pairOK xs && (newSubsets xs).all densityOK

theorem values_length : values.length = 40 := by decide

theorem values_nodup : values.Nodup := by decide

/-- This is the exact finite proposition that still requires a kernel proof.
It is kept explicit so a failed diagnostic evaluation is never promoted to a
theorem about `Statement 11`. -/
def exhausted : Prop := FiniteSearch.search ranks good 11 [] = false

/-- If `exhausted` is certified, the generic checker rules out every sorted
length-11 rank list in the declared 40-element domain that passes each prefix. -/
theorem no_rank_candidate_of_exhausted (h : exhausted) :
    ¬ ∃ xs, xs.length = 11 ∧ xs.Pairwise (· ≤ ·) ∧
      (∀ x ∈ xs, x ∈ ranks) ∧ FiniteSearch.EveryPrefixPasses good xs :=
  FiniteSearch.no_sorted_good_of_false ranks good 11 h

#print axioms no_rank_candidate_of_exhausted

end ProofPursuit.P4.ElevenCheck
