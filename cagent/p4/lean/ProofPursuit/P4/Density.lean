import ProofPursuit.P4.Reduction

namespace ProofPursuit.P4

private def residue (a : Int) (r : Nat) : Nat := (a % (r : Int)).toNat

private theorem residue_lt (a : Int) (r : Nat) (hr : 0 < r) : residue a r < r := by
  have hp : (0 : Int) < (r : Int) := by exact_mod_cast hr
  have hlo : (0 : Int) ≤ a % (r : Int) := Int.emod_nonneg a (by omega)
  have hhi : a % (r : Int) < (r : Int) := Int.emod_lt_of_pos a hp
  have he : (residue a r : Int) = a % (r : Int) := Int.toNat_of_nonneg hlo
  omega

private theorem point_in_class (a : Int) (r j : Nat) (hr : 0 < r) :
    InClass a r ((residue a r + j * r : Nat) : Int) := by
  have hlo : (0 : Int) ≤ a % (r : Int) :=
    Int.emod_nonneg a (by exact_mod_cast (Nat.ne_of_gt hr))
  have he : (residue a r : Int) = a % (r : Int) := Int.toNat_of_nonneg hlo
  apply Int.dvd_iff_emod_eq_zero.mpr
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  push_cast
  rw [he, Int.add_mul_emod_self_right, Int.emod_emod]

private theorem point_lt (a : Int) (r M j : Nat) (hr : 0 < r)
    (hdiv : r ∣ M) (hj : j < M / r) : residue a r + j * r < M := by
  have hM : M / r * r = M := Nat.div_mul_cancel hdiv
  have hmul := Nat.mul_le_mul_right r (show j + 1 ≤ M / r by omega)
  simp [Nat.add_mul] at hmul
  have hres := residue_lt a r hr
  omega

private theorem point_injective (a : Int) (r : Nat) (hr : 0 < r) {j t : Nat}
    (h : residue a r + j * r = residue a r + t * r) : j = t := by
  have hmul : j * r = t * r := by omega
  exact Nat.mul_right_cancel hr hmul

/-- Pairwise disjoint classes whose positive moduli divide M occupy at most M
residues modulo M. The sum uses the canonical list of Fin k indices. -/
theorem density_bound {k M : Nat} (a : Fin k → Int) (r : Fin k → Nat)
    (_hM : 0 < M) (hr : ∀ i, 0 < r i ∧ r i ∣ M)
    (hd : DisjointClasses a r) :
    ((List.finRange k).map (fun i => M / r i)).sum ≤ M := by
  let points : Fin k → List Nat := fun i =>
    (List.range (M / r i)).map (fun j => residue (a i) (r i) + j * r i)
  let allPoints : List Nat := (List.finRange k).flatMap points
  have hndPoint (i : Fin k) : (points i).Nodup := by
    dsimp [points]
    apply List.pairwise_map.mpr
    apply (List.nodup_range).imp_of_mem
    intro j t _ _ hne he
    exact hne (point_injective (a i) (r i) (hr i).1 he)
  have hnd : allPoints.Nodup := by
    dsimp [allPoints]
    apply List.pairwise_flatMap.mpr
    constructor
    · intro i _
      exact hndPoint i
    · apply (List.nodup_finRange k).imp_of_mem
      intro i j _ _ hij x hx y hy hxy
      simp only [points, List.mem_map, List.mem_range] at hx hy
      obtain ⟨s, _, rfl⟩ := hx
      obtain ⟨t, _, rfl⟩ := hy
      apply hd i j hij
      refine ⟨((residue (a i) (r i) + s * r i : Nat) : Int), ?_, ?_⟩
      · exact point_in_class (a i) (r i) s (hr i).1
      · rw [hxy]
        exact point_in_class (a j) (r j) t (hr j).1
  have hsub : allPoints ⊆ List.range M := by
    intro x hx
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < M / r i ∧
        residue (a i) (r i) + j * r i = x := by
      simpa [points, List.mem_map, List.mem_range] using hi
    exact List.mem_range.mpr (point_lt (a i) (r i) M j (hr i).1 (hr i).2 hj)
  have hlen := hnd.length_le_of_subset hsub
  simpa [allPoints, points, List.length_flatMap] using hlen

/-- If every pairwise gcd divides M, reducing each modulus to its gcd with M
preserves disjointness and yields the same density bound. -/
theorem density_bound_compressed {k M : Nat} (a : Fin k → Int) (m : Fin k → Nat)
    (hM : 0 < M) (hd : DisjointClasses a m)
    (hpair : ∀ i j : Fin k, i ≠ j → Nat.gcd (m i) (m j) ∣ M) :
    ((List.finRange k).map (fun i => M / Nat.gcd (m i) M)).sum ≤ M := by
  exact density_bound a (fun i => Nat.gcd (m i) M) hM
    (fun i => compressed_modulus_bounds m M hM i)
    (disjoint_compressed a m M hd hpair)

#print axioms density_bound
#print axioms density_bound_compressed

end ProofPursuit.P4
