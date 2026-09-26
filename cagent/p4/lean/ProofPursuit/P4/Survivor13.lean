import ProofPursuit.P4.Basic

namespace ProofPursuit.P4.Survivor13

/-- Seven moduli inside the surviving thirteen-modulus configuration. -/
def moduli (i : Fin 7) : Nat := if i.val < 5 then 10 else if i.val = 5 then 12 else 45

/-- Density inequalities alone miss this residue obstruction. -/
theorem impossible (a : Fin 7 → Int) : ¬ DisjointClasses a moduli := by
  intro hd
  have parity (i : Fin 7) (hi : i.val < 5) : a i % 2 ≠ a 5 % 2 := by
    apply residues_ne hd (by omega)
    simp [moduli, hi]
    decide
  have first (i j : Fin 7) (hi : i.val < 5) (hj : j.val < 5) (hne : i ≠ j) :
      a i % 5 ≠ a j % 5 := by
    have h10 : a i % 10 ≠ a j % 10 := by
      apply residues_ne hd hne
      simp [moduli, hi, hj]
    have pi := parity i hi
    have pj := parity j hj
    omega
  have last (i : Fin 7) (hi : i.val < 5) : a i % 5 ≠ a 6 % 5 := by
    apply residues_ne hd (by omega)
    simp [moduli, hi]
    decide
  let xs : List Int := [a 0 % 5, a 1 % 5, a 2 % 5, a 3 % 5, a 4 % 5, a 6 % 5]
  have hn : xs.Nodup := by
    simp only [xs, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    repeat' constructor
    all_goals first
      | simp
      | exact first 0 1 (by decide) (by decide) (by decide)
      | exact first 0 2 (by decide) (by decide) (by decide)
      | exact first 0 3 (by decide) (by decide) (by decide)
      | exact first 0 4 (by decide) (by decide) (by decide)
      | exact first 1 2 (by decide) (by decide) (by decide)
      | exact first 1 3 (by decide) (by decide) (by decide)
      | exact first 1 4 (by decide) (by decide) (by decide)
      | exact first 2 3 (by decide) (by decide) (by decide)
      | exact first 2 4 (by decide) (by decide) (by decide)
      | exact first 3 4 (by decide) (by decide) (by decide)
      | exact last 0 (by decide)
      | exact last 1 (by decide)
      | exact last 2 (by decide)
      | exact last 3 (by decide)
      | exact last 4 (by decide)
  have hs : xs ⊆ ([0, 1, 2, 3, 4] : List Int) := by
    intro x hx
    simp [xs] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  have := hn.length_le_of_subset hs
  simp [xs] at this

/-- The explicit k=13 modulus list examined by this audit. -/
def candidate (i : Fin 13) : Nat :=
  if i.val < 5 then 10 else if i.val < 9 then 12 else
  if i.val = 9 then 24 else if i.val = 10 then 36 else if i.val = 11 then 40 else 45

private def inclusion (i : Fin 7) : Fin 13 :=
  ⟨if i.val < 6 then i.val else 12, by split <;> omega⟩

/-- This modulus list admits no pairwise disjoint choice of integer residues. -/
theorem candidate_impossible (a : Fin 13 → Int) : ¬ DisjointClasses a candidate := by
  intro hd
  apply impossible (fun i => a (inclusion i))
  have hm : ∀ i : Fin 7, candidate (inclusion i) = moduli i := by decide
  intro i j hij hmeet
  have hne : inclusion i ≠ inclusion j := by
    intro he
    have he' := congrArg Fin.val he
    simp only [inclusion] at he'
    have : i.val = j.val := by split at he' <;> split at he' <;> omega
    exact hij (Fin.ext this)
  apply hd (inclusion i) (inclusion j) hne
  simpa only [hm] using hmeet

#print axioms impossible
#print axioms candidate_impossible
end ProofPursuit.P4.Survivor13
