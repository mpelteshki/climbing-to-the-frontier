import ProofPursuit.P4.TwelveCheck
import ProofPursuit.P4.Reindex
import ProofPursuit.P4.NormalForm12

namespace ProofPursuit.P4.Twelve

open ProofPursuit.P4.ListDensity

/-- A ranked twelve-class configuration meeting the checked restrictions
would give the forbidden sorted search candidate. -/
theorem no_ranked_candidate (r : Fin 12 → Nat) (rank : Fin 12 → Nat)
    (hrange : ∀ i, rank i < 87)
    (hdecode : ∀ i, TwelveCheck.modulus (rank i) = r i)
    (hpair : ∀ i j : Fin 12, i ≠ j →
      1 < Nat.gcd (r i) (r j) ∧ Nat.gcd (r i) (r j) < 12)
    (hanchors : 3 ≤ (((sortedIndices rank).map rank).filter (fun x => x < 47)).length) :
    False := by
  let indices := sortedIndices rank
  let xs := indices.map rank
  have hlen : xs.length = 12 := by
    simp [xs, indices, sortedIndices]
  have hsorted : xs.Pairwise (· ≤ ·) := sortedIndices_order rank
  have hnd : indices.Nodup := sortedIndices_nodup rank
  have hdomain : ∀ x ∈ xs, x ∈ List.range 87 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (hrange i)
  have hmod : (xs.map TwelveCheck.modulus).Pairwise
      (fun x y => 1 < Nat.gcd x y ∧ Nat.gcd x y < 12) := by
    have hpidx : indices.Pairwise (fun i j =>
        1 < Nat.gcd (r i) (r j) ∧ Nat.gcd (r i) (r j) < 12) :=
      hnd.imp_of_mem (fun {i j} _ _ hij => hpair i j hij)
    have hpmod : (indices.map r).Pairwise
        (fun x y => 1 < Nat.gcd x y ∧ Nat.gcd x y < 12) :=
      List.pairwise_map.mpr hpidx
    have he : xs.map TwelveCheck.modulus = indices.map r := by
      simp [xs, List.map_map, hdecode]
    rw [he]
    exact hpmod
  have hfirst : ∀ x ∈ xs.take 3, x < 47 :=
    take_lt_of_filter_length xs hsorted 47 3 hanchors
  have hgood : FiniteSearch.EveryPrefixPasses TwelveCheck.good xs := by
    intro pre hpre _
    have hp : pre = xs.take pre.length := List.prefix_iff_eq_take.mp hpre
    have hsub : List.Sublist (pre.take 3) (xs.take 3) := by
      rw [hp, List.take_take]
      exact List.take_sublist_take_left (Nat.min_le_left 3 pre.length)
    have hsmall : (pre.take 3).all (fun x => x < 47) = true := by
      apply List.all_eq_true.mpr
      intro x hx
      exact decide_eq_true (hfirst x (hsub.subset hx))
    have hpairpre : (pre.map TwelveCheck.modulus).Pairwise
        (fun x y => 1 < Nat.gcd x y ∧ Nat.gcd x y < 12) :=
      hmod.sublist ((hpre.map TwelveCheck.modulus).sublist)
    simp [TwelveCheck.good, hsmall, hpairpre]
  exact TwelveCheck.no_sorted_candidate ⟨xs, hlen, hsorted, hdomain, hgood⟩

private theorem domain_rank_facts (x : Nat) (hx : x ∈ Domain12) :
    x ∈ TwelveCheck.values ∧
      (11 ∣ x → TwelveCheck.values.idxOf x < 47) := by
  have hc : Domain12.all (fun d =>
      decide (d ∈ TwelveCheck.values) &&
        decide (11 ∣ d → TwelveCheck.values.idxOf d < 47)) = true := by decide
  have h := (List.all_eq_true.mp hc) x hx
  simp [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro h11
  rcases h.2 with hnot | hlt
  · exact False.elim (hnot h11)
  · exact hlt

theorem step (hprev : ∀ t : Nat, 2 ≤ t → t < 12 → Statement t) : Statement 12 := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  obtain ⟨r, hdomain, _, _, hrgcd, ⟨i, j, l, hij, hil, hjl, hi11, hj11, hl11⟩⟩ :=
    normal_form_12 hprev a m hm hd hn
  let rank : Fin 12 → Nat := fun t => TwelveCheck.values.idxOf (r t)
  have hrange (t : Fin 12) : rank t < 87 := by
    have hmem := (domain_rank_facts (r t) (hdomain t)).1
    have hlt := List.idxOf_lt_length_of_mem hmem
    simpa [rank, TwelveCheck.values] using hlt
  have hdecode (t : Fin 12) : TwelveCheck.modulus (rank t) = r t := by
    have hmem := (domain_rank_facts (r t) (hdomain t)).1
    have hlt := List.idxOf_lt_length_of_mem hmem
    calc
      TwelveCheck.modulus (rank t) =
          TwelveCheck.values[TwelveCheck.values.idxOf (r t)] := by
        exact (List.getElem_eq_getD 0).symm
      _ = r t := List.getElem_idxOf hlt
  have hpair (u v : Fin 12) (huv : u ≠ v) :
      1 < Nat.gcd (r u) (r v) ∧ Nat.gcd (r u) (r v) < 12 := by
    rw [hrgcd u v huv]
    exact bounds hm hd hn huv
  have harank (t : Fin 12) (ht : 11 ∣ r t) : rank t < 47 :=
    (domain_rank_facts (r t) (hdomain t)).2 ht
  let indices := sortedIndices rank
  have hmem (t : Fin 12) : t ∈ indices := by
    simp [indices, sortedIndices]
  have hanchor_mem (t : Fin 12) (ht : 11 ∣ r t) :
      t ∈ indices.filter (fun u => rank u < 47) := by
    simp [hmem t, harank t ht]
  have hnd : ([i, j, l] : List (Fin 12)).Nodup := by
    simp [hij, hil, hjl]
  have hsub : ([i, j, l] : List (Fin 12)) ⊆
      indices.filter (fun t => rank t < 47) := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with hti | htj | htl
    · simpa [hti] using hanchor_mem i hi11
    · simpa [htj] using hanchor_mem j hj11
    · simpa [htl] using hanchor_mem l hl11
  have hthree : 3 ≤ (indices.filter (fun t => rank t < 47)).length := by
    simpa using hnd.length_le_of_subset hsub
  have hanchors : 3 ≤ (((sortedIndices rank).map rank).filter
      (fun x => x < 47)).length := by
    simpa [indices, List.filter_map, Function.comp_def] using hthree
  exact no_ranked_candidate r rank hrange hdecode hpair hanchors

end ProofPursuit.P4.Twelve
