import Std

namespace ProofPursuit.P4.FiniteSearch

/-- A continuation passes when each chosen value belongs to the finite domain,
is at least every earlier value, and passes the Boolean test on the new prefix. -/
def Admissible (D : List Nat) (good : List Nat → Bool) (pre : List Nat) :
    List Nat → Prop
  | [] => True
  | x :: xs =>
      x ∈ D ∧ (∀ y ∈ pre, y ≤ x) ∧ good (pre ++ [x]) = true ∧
        Admissible D good (pre ++ [x]) xs

/-- A finite, prefix-pruned search for a continuation of exactly `remaining` values.
The domain can contain duplicates, and selected values may repeat. -/
def search (D : List Nat) (good : List Nat → Bool) : Nat → List Nat → Bool
  | 0, _ => true
  | remaining + 1, pre =>
      D.any fun x =>
        pre.all (fun y => decide (y ≤ x)) &&
          good (pre ++ [x]) &&
            search D good remaining (pre ++ [x])

/-- The executable search detects exactly the admissible continuations. -/
theorem search_true_iff (D : List Nat) (good : List Nat → Bool)
    (remaining : Nat) (pre : List Nat) :
    search D good remaining pre = true ↔
      ∃ xs, xs.length = remaining ∧ Admissible D good pre xs := by
  induction remaining generalizing pre with
  | zero =>
      simp [search, Admissible]
  | succ n ih =>
      change (D.any fun x =>
        pre.all (fun y => decide (y ≤ x)) && good (pre ++ [x]) &&
          search D good n (pre ++ [x])) = true ↔ _
      rw [List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hcheck⟩
        obtain ⟨hall, hgood, hrec⟩ :
            pre.all (fun y => decide (y ≤ x)) = true ∧
            good (pre ++ [x]) = true ∧
            search D good n (pre ++ [x]) = true := by
          simpa [Bool.and_eq_true, and_assoc] using hcheck
        obtain ⟨xs, hlen, hadm⟩ := (ih (pre ++ [x])).mp hrec
        refine ⟨x :: xs, by simp [hlen], ?_⟩
        exact ⟨hx, (fun y hy => of_decide_eq_true ((List.all_eq_true.mp hall) y hy)),
          hgood, hadm⟩
      · rintro ⟨xs, hlen, hadm⟩
        cases xs with
        | nil => simp at hlen
        | cons x ys =>
          obtain ⟨hx, horder, hgood, htail⟩ := hadm
          have hlen' : ys.length = n := by simpa using hlen
          refine ⟨x, hx, ?_⟩
          have hall : pre.all (fun y => decide (y ≤ x)) = true :=
            List.all_eq_true.mpr (fun y hy => decide_eq_true (horder y hy))
          have hrec := (ih (pre ++ [x])).mpr ⟨ys, hlen', htail⟩
          simpa [Bool.and_eq_true, and_assoc] using
            (show pre.all (fun y => decide (y ≤ x)) = true ∧
              good (pre ++ [x]) = true ∧
              search D good n (pre ++ [x]) = true from ⟨hall, hgood, hrec⟩)

/-- A negative search result rules out every admissible continuation. -/
theorem no_admissible_of_false (D : List Nat) (good : List Nat → Bool)
    (remaining : Nat) (pre : List Nat)
    (hfalse : search D good remaining pre = false) :
    ¬ ∃ xs, xs.length = remaining ∧ Admissible D good pre xs := by
  intro h
  have htrue := (search_true_iff D good remaining pre).mpr h
  simp [hfalse] at htrue

/-- The usual meaning of passing every nonempty initial segment. -/
def EveryPrefixPasses (good : List Nat → Bool) (xs : List Nat) : Prop :=
  ∀ pre, pre <+: xs → pre ≠ [] → good pre = true

private theorem admissible_of_sorted (D : List Nat) (good : List Nat → Bool)
    (pre xs : List Nat)
    (hsorted : (pre ++ xs).Pairwise (· ≤ ·))
    (hdomain : ∀ x ∈ xs, x ∈ D)
    (hgood : ∀ q, q <+: pre ++ xs → pre.length < q.length → good q = true) :
    Admissible D good pre xs := by
  induction xs generalizing pre with
  | nil => exact trivial
  | cons x rest ih =>
      have hcross := (List.pairwise_append.mp hsorted).2.2
      have hord (y : Nat) (hy : y ∈ pre) : y ≤ x :=
        hcross y hy x (by simp)
      have hstep : good (pre ++ [x]) = true := by
        apply hgood (pre ++ [x])
        · exact ⟨rest, by simp [List.append_assoc]⟩
        · simp
      refine ⟨hdomain x (by simp), hord, hstep, ?_⟩
      apply ih (pre ++ [x])
      · simpa [List.append_assoc] using hsorted
      · intro y hy
        exact hdomain y (by simp [hy])
      · intro q hq hlen
        apply hgood q
        · simpa [List.append_assoc] using hq
        · simp only [List.length_append, List.length_singleton] at hlen
          omega

/-- A negative result rules out every sorted length-`k` list drawn from `D`
whose every nonempty prefix passes `good`. -/
theorem no_sorted_good_of_false (D : List Nat) (good : List Nat → Bool)
    (k : Nat) (hfalse : search D good k [] = false) :
    ¬ ∃ xs, xs.length = k ∧ xs.Pairwise (· ≤ ·) ∧
      (∀ x ∈ xs, x ∈ D) ∧ EveryPrefixPasses good xs := by
  rintro ⟨xs, hlen, hsorted, hdomain, hgood⟩
  apply no_admissible_of_false D good k [] hfalse
  refine ⟨xs, hlen, ?_⟩
  apply admissible_of_sorted D good [] xs (by simpa using hsorted) hdomain
  intro q hq hqpos
  apply hgood q hq
  intro hnil
  subst q
  simp at hqpos

#print axioms search_true_iff
#print axioms no_sorted_good_of_false

end ProofPursuit.P4.FiniteSearch
