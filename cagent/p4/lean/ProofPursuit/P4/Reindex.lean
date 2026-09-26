import ProofPursuit.P4.ListDensity

namespace ProofPursuit.P4.ListDensity

/-- Any list of distinct original positions preserves actual realizability.
The selected moduli themselves may repeat. -/
theorem realizable_map_indices {k : Nat} (a : Fin k → Int) (m : Fin k → Nat)
    (hd : DisjointClasses a m) (indices : List (Fin k)) (hn : indices.Nodup) :
    Realizable (indices.map m) := by
  let f : Fin (indices.map m).length → Fin k := fun i => indices[i.val]'(by simpa using i.isLt)
  refine ⟨fun i => a (f i), ?_⟩
  intro i j hij hmeet
  have hne : f i ≠ f j := by
    intro he
    apply hij
    apply Fin.ext
    exact hn.eq_of_getElem_eq (by simpa using i.isLt) (by simpa using j.isLt) he
  apply hd (f i) (f j) hne
  simpa [f] using hmeet

/-- Sorting positions by any natural-number rank preserves every class. -/
def sortedIndices {k : Nat} (rank : Fin k → Nat) : List (Fin k) :=
  (List.finRange k).mergeSort (fun i j => decide (rank i ≤ rank j))

theorem sortedIndices_nodup {k : Nat} (rank : Fin k → Nat) :
    (sortedIndices rank).Nodup := by
  exact (List.mergeSort_perm _ _).symm.nodup (List.nodup_finRange k)

theorem sortedIndices_order {k : Nat} (rank : Fin k → Nat) :
    ((sortedIndices rank).map rank).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  have h := List.pairwise_mergeSort
    (le := fun i j : Fin k => decide (rank i ≤ rank j))
    (fun i j l hij hjl => by simp_all; omega)
    (fun i j => by simp; omega) (List.finRange k)
  simpa [sortedIndices] using h

/-- In a sorted list, sufficiently many entries below a cutoff force the
whole requested initial segment below that cutoff. -/
theorem take_lt_of_filter_length (xs : List Nat) (hs : xs.Pairwise (· ≤ ·))
    (cutoff n : Nat) (hc : n ≤ (xs.filter (fun x => x < cutoff)).length) :
    ∀ x ∈ xs.take n, x < cutoff := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp at hc
    | cons a rest =>
      obtain ⟨ha, hr⟩ := List.pairwise_cons.mp hs
      have hal : a < cutoff := by
        apply Classical.byContradiction
        intro h
        have hf : rest.filter (fun x => x < cutoff) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have := ha x hx
          simp
          omega
        simp [h, hf] at hc
      have hn : n ≤ (rest.filter (fun x => x < cutoff)).length := by
        simpa [List.filter_cons, hal] using hc
      intro x hx
      simp only [List.take_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hal
      · exact ih rest hr hn x hx

#print axioms realizable_map_indices
end ProofPursuit.P4.ListDensity
