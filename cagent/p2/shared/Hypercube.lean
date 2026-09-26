import Std

namespace Hypercube

/-- Natural numbers below 2^d encode d-bit vertices; XOR with a power of two flips one bit. -/
def adjacent (d u v : Nat) : Bool :=
  (List.range d).any (fun k => u ^^^ v == 2 ^ k)

/-- A labelling is its list of vertices in strictly increasing label order. -/
def IsLabelling (d : Nat) (order : List Nat) : Prop :=
  order.Perm (List.range (2 ^ d))

/-- All vertices before v have lower labels. -/
def before (order : List Nat) (v : Nat) : List Nat :=
  order.takeWhile (fun w => w != v)

def after (order : List Nat) (v : Nat) : List Nat :=
  (order.dropWhile (fun w => w != v)).drop 1

def valley (d : Nat) (order : List Nat) (v : Nat) : Bool :=
  !(before order v).any (adjacent d v)

/-- The suffix follows hypercube edges, starting at v. -/
def ChainFrom (d v : Nat) : List Nat → Prop
  | [] => True
  | w :: ws => adjacent d v w = true ∧ ChainFrom d w ws

/-- Exact task semantics: start at a valley and follow adjacent vertices in label order.
A sublist of the strictly ordered suffix expresses strictly increasing labels. -/
def Uphill (d : Nat) (order p : List Nat) : Prop :=
  ∃ v tail, p = v :: tail ∧ v ∈ order ∧ valley d order v = true ∧
    tail.Sublist (after order v) ∧ ChainFrom d v tail

/-- Enumerates every possible increasing continuation, including the empty one. -/
def extensions (d v : Nat) : List Nat → List (List Nat)
  | [] => [[]]
  | w :: ws => extensions d v ws ++
      if adjacent d v w then (extensions d w ws).map (w :: ·) else []

theorem mem_extensions (d v : Nat) (order p : List Nat) :
    p ∈ extensions d v order ↔ p.Sublist order ∧ ChainFrom d v p := by
  induction order generalizing v p with
  | nil =>
    cases p <;> simp [extensions, ChainFrom]
  | cons w ws ih =>
    simp only [extensions, List.mem_append]
    by_cases h : adjacent d v w = true
    · simp only [h, ↓reduceIte, List.mem_map, ih]
      constructor
      · intro hp
        rcases hp with hp | ⟨tail, ⟨hs, hc⟩, rfl⟩
        · exact ⟨List.sublist_cons_iff.mpr (Or.inl hp.1), hp.2⟩
        · exact ⟨List.sublist_cons_iff.mpr (Or.inr ⟨tail, rfl, hs⟩), h, hc⟩
      · rintro ⟨hs, hc⟩
        rcases List.sublist_cons_iff.mp hs with hs | ⟨tail, rfl, hs⟩
        · exact Or.inl ⟨hs, hc⟩
        · exact Or.inr ⟨tail, ⟨List.cons_sublist_cons.mp hs, hc.2⟩, rfl⟩
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, or_false, ih]
      constructor
      · rintro ⟨hs, hc⟩
        exact ⟨List.sublist_cons_iff.mpr (Or.inl hs), hc⟩
      · rintro ⟨hs, hc⟩
        rcases List.sublist_cons_iff.mp hs with hs | ⟨tail, rfl, hs⟩
        · exact ⟨hs, hc⟩
        · exact False.elim (h hc.1)

/-- Exhaustive enumeration of the paths in the task, with duplicates removed. -/
def paths (d : Nat) (order : List Nat) : List (List Nat) :=
  (order.flatMap fun v =>
    if valley d order v then (extensions d v (after order v)).map (v :: ·)
    else []).eraseDups

theorem mem_paths (d : Nat) (order p : List Nat) :
    p ∈ paths d order ↔ Uphill d order p := by
  simp only [paths, List.mem_eraseDups, List.mem_flatMap, Uphill]
  constructor
  · rintro ⟨v, hv, hp⟩
    split at hp
    next h =>
      obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hp
      exact ⟨v, tail, rfl, hv, h, (mem_extensions ..).mp ht⟩
    next h => simp at hp
  · rintro ⟨v, tail, rfl, hv, h, hs, hc⟩
    refine ⟨v, hv, ?_⟩
    simp only [h, ↓reduceIte, List.mem_map]
    exact ⟨tail, (mem_extensions ..).mpr ⟨hs, hc⟩, rfl⟩

theorem eraseDups_nodup (xs : List (List Nat)) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_eraseDups]
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by
  have h := List.length_filter_le (fun b : List Nat => !b == x) xs
  simp only [List.length_cons]
  omega

theorem paths_nodup (d : Nat) (order : List Nat) : (paths d order).Nodup :=
  eraseDups_nodup _

def pathCount (d : Nat) (order : List Nat) : Nat := (paths d order).length

#print axioms paths_nodup
#print axioms mem_extensions
#print axioms mem_paths
end Hypercube
