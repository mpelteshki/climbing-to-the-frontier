import Std

namespace ProofPursuit.P4.DensityAudit13
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Distinct subsequences, retaining repeated entries within each subsequence. -/
def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let ss := sublists xs; (ss ++ ss.map (x :: ·)).eraseDups

theorem mem_sublists {xs ys : List Nat} (h : xs.Sublist ys) : xs ∈ sublists ys := by
  induction h with
  | slnil => simp [sublists]
  | @cons l₁ l₂ a h ih => simp only [sublists, List.mem_eraseDups, List.mem_append]; exact Or.inl ih
  | @cons_cons l₁ l₂ a h ih =>
    simp only [sublists, List.mem_eraseDups, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨l₁, ih, rfl⟩)

/-- Least common multiple of gcds over distinct positions. -/
def pairLCM : List Nat → Nat
  | [] => 1
  | x :: xs => xs.foldl (fun n y => Nat.lcm n (Nat.gcd x y)) (pairLCM xs)

def passes (xs : List Nat) : Bool :=
  xs.length < 2 || (xs.map (fun x => pairLCM xs / Nat.gcd x (pairLCM xs))).sum ≤ pairLCM xs

def candidate : List Nat := [10,10,10,10,10,12,12,12,12,24,36,40,45]

theorem checked : (sublists candidate).all passes = true := by decide

theorem every_sublist_passes (xs : List Nat) (h : xs.Sublist candidate) : passes xs = true := by
  exact List.all_eq_true.mp checked xs (mem_sublists h)

#print axioms every_sublist_passes
end ProofPursuit.P4.DensityAudit13
