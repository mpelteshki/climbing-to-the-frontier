import ProofPursuit.P4.ElevenCertificate
import ProofPursuit.P4.Reindex
import ProofPursuit.P4.NormalForm11

namespace ProofPursuit.P4.Eleven

open ProofPursuit.P4.ListDensity
open ProofPursuit.P4.ElevenCertificate

private theorem valid_prefix_of_full (full pre : List Nat)
    (hpre : List.IsPrefix pre full)
    (hreal : Realizable (full.map ElevenCheck.modulus))
    (hpos : ∀ x ∈ full.map ElevenCheck.modulus, 0 < x) :
    ValidPrefix pre := by
  change ∀ mask M : Nat, 0 < M →
    ((select mask pre).map ElevenCheck.modulus).Pairwise
      (fun x y => Nat.gcd x y ∣ M) →
    ((((select mask pre).map ElevenCheck.modulus).map
      (fun x => M / Nat.gcd x M)).sum ≤ M)
  intro mask M hM hpair
  have hsub : List.Sublist ((select mask pre).map ElevenCheck.modulus)
      (full.map ElevenCheck.modulus) :=
    ((select_sublist mask pre).trans hpre.sublist).map ElevenCheck.modulus
  exact ProofPursuit.P4.ListDensity.density_bound_compressed _ M hM
    (fun x hx => hpos x (hsub.subset hx))
    (realizable_sublist hsub hreal) hpair

private theorem candidate_of_properties (full pre rest : List Nat)
    (hfull : pre ++ rest = full)
    (hsorted : full.Pairwise (· ≤ ·))
    (hfirst : ∀ x ∈ full.take 3, x < 18)
    (hdomain : ∀ x ∈ full, x ∈ ElevenCheck.ranks)
    (hpair : (full.map ElevenCheck.modulus).Pairwise
      (fun x y => 1 < Nat.gcd x y ∧ Nat.gcd x y < 11))
    (hreal : Realizable (full.map ElevenCheck.modulus))
    (hpos : ∀ x ∈ full.map ElevenCheck.modulus, 0 < x) :
    Candidate pre rest.length rest := by
  induction rest generalizing pre with
  | nil =>
    have hp : List.IsPrefix pre full := ⟨[], by simpa using hfull⟩
    exact valid_prefix_of_full full pre hp hreal hpos
  | cons x tail ih =>
    change ValidPrefix pre ∧ x ∈ allowed pre ∧
      Candidate (pre ++ [x]) tail.length tail
    have hp : List.IsPrefix pre full :=
      ⟨x :: tail, hfull⟩
    have hpx : List.IsPrefix (pre ++ [x]) full := by
      refine ⟨tail, ?_⟩
      simpa [List.append_assoc] using hfull
    have hord : (pre ++ [x]).Pairwise (· ≤ ·) :=
      hsorted.sublist hpx.sublist
    have hcross := (List.pairwise_append.mp hord).2.2
    have hmpair : ((pre ++ [x]).map ElevenCheck.modulus).Pairwise
        (fun u v => 1 < Nat.gcd u v ∧ Nat.gcd u v < 11) :=
      hpair.sublist ((hpx.map ElevenCheck.modulus).sublist)
    have hmcross := (List.pairwise_append.mp
      (show (pre.map ElevenCheck.modulus ++ [ElevenCheck.modulus x]).Pairwise
        (fun u v => 1 < Nat.gcd u v ∧ Nat.gcd u v < 11) by
        simpa [List.map_append] using hmpair)).2.2
    have hall : pre.all (fun y => decide
        (y ≤ x ∧ 1 < Nat.gcd (ElevenCheck.modulus y) (ElevenCheck.modulus x) ∧
          Nat.gcd (ElevenCheck.modulus y) (ElevenCheck.modulus x) < 11)) = true := by
      apply List.all_eq_true.mpr
      intro y hy
      have ho := hcross y hy x (by simp)
      have hg := hmcross (ElevenCheck.modulus y)
        (List.mem_map.mpr ⟨y, hy, rfl⟩)
        (ElevenCheck.modulus x) (by simp)
      exact decide_eq_true ⟨ho, hg.1, hg.2⟩
    have hallP : ∀ y ∈ pre,
        y ≤ x ∧ 1 < Nat.gcd (ElevenCheck.modulus y) (ElevenCheck.modulus x) ∧
          Nat.gcd (ElevenCheck.modulus y) (ElevenCheck.modulus x) < 11 := by
      intro y hy
      exact of_decide_eq_true ((List.all_eq_true.mp hall) y hy)
    have hsmall (h : pre.length < 3) : x < 18 := by
      have hpx3 : List.IsPrefix (pre ++ [x]) (full.take 3) :=
        List.prefix_take_iff.mpr ⟨hpx, by simp; omega⟩
      exact hfirst x (hpx3.sublist.subset (by simp))
    have hallowed : x ∈ allowed pre := by
      apply List.mem_filter.mpr
      constructor
      · exact hdomain x (hpx.sublist.subset (by simp))
      · by_cases hs : pre.length < 3
        · simpa [hs, hsmall hs] using hallP
        · simpa [hs] using hallP
    refine ⟨valid_prefix_of_full full pre hp hreal hpos,
      hallowed, ?_⟩
    apply ih (pre ++ [x])
    simpa [List.append_assoc] using hfull

private theorem no_ranked_candidate_of_certificate
    (hcert : ¬ ∃ xs, Candidate [] 11 xs)
    (a : Fin 11 → Int) (r rank : Fin 11 → Nat)
    (hrange : ∀ i, rank i < 40)
    (hdecode : ∀ i, ElevenCheck.modulus (rank i) = r i)
    (hrpos : ∀ i, 0 < r i) (hrdis : DisjointClasses a r)
    (hpair : ∀ i j : Fin 11, i ≠ j →
      1 < Nat.gcd (r i) (r j) ∧ Nat.gcd (r i) (r j) < 11)
    (hanchors : 3 ≤ (((sortedIndices rank).map rank).filter (fun x => x < 18)).length) :
    False := by
  let indices := sortedIndices rank
  let xs := indices.map rank
  have hlen : xs.length = 11 := by simp [xs, indices, sortedIndices]
  have hsorted : xs.Pairwise (· ≤ ·) := sortedIndices_order rank
  have hfirst : ∀ x ∈ xs.take 3, x < 18 :=
    take_lt_of_filter_length xs hsorted 18 3 hanchors
  have hdomain : ∀ x ∈ xs, x ∈ ElevenCheck.ranks := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (hrange i)
  have hnd : indices.Nodup := sortedIndices_nodup rank
  have hmpair : (xs.map ElevenCheck.modulus).Pairwise
      (fun u v => 1 < Nat.gcd u v ∧ Nat.gcd u v < 11) := by
    have hpidx : indices.Pairwise (fun i j =>
        1 < Nat.gcd (r i) (r j) ∧ Nat.gcd (r i) (r j) < 11) :=
      hnd.imp_of_mem (fun {i j} _ _ hij => hpair i j hij)
    have hpmod : (indices.map r).Pairwise
        (fun u v => 1 < Nat.gcd u v ∧ Nat.gcd u v < 11) :=
      List.pairwise_map.mpr hpidx
    have he : xs.map ElevenCheck.modulus = indices.map r := by
      simp [xs, List.map_map, hdecode]
    rw [he]
    exact hpmod
  have hreal : Realizable (xs.map ElevenCheck.modulus) := by
    have hr := realizable_map_indices a r hrdis indices hnd
    have he : xs.map ElevenCheck.modulus = indices.map r := by
      simp [xs, List.map_map, hdecode]
    rw [he]
    exact hr
  have hpos : ∀ u ∈ xs.map ElevenCheck.modulus, 0 < u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    rw [hdecode i]
    exact hrpos i
  have hc : Candidate [] 11 xs := by
    have h := candidate_of_properties xs [] xs (by simp)
      hsorted hfirst hdomain hmpair hreal hpos
    simpa [hlen] using h
  exact hcert ⟨xs, hc⟩

private theorem domain_rank_facts (x : Nat) (hx : x ∈ Domain11) :
    x ∈ ElevenCheck.values ∧
      (10 ∣ x → ElevenCheck.values.idxOf x < 18) := by
  have hc : Domain11.all (fun d =>
      decide (d ∈ ElevenCheck.values) &&
        decide (10 ∣ d → ElevenCheck.values.idxOf d < 18)) = true := by decide
  have h := (List.all_eq_true.mp hc) x hx
  simp [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro h10
  rcases h.2 with hnot | hlt
  · exact False.elim (hnot h10)
  · exact hlt

theorem step_of_certificate (hcert : ¬ ∃ xs, Candidate [] 11 xs)
    (hprev : ∀ t : Nat, 2 ≤ t → t < 11 → Statement t) : Statement 11 := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  obtain ⟨r, hdomain, hrpos, hrdis, hrgcd,
    ⟨i, j, l, hij, hil, hjl, hi10, hj10, hl10⟩⟩ :=
    normal_form_11_with_anchors hprev a m hm hd hn
  let rank : Fin 11 → Nat := fun t => ElevenCheck.values.idxOf (r t)
  have hrange (t : Fin 11) : rank t < 40 := by
    have hmem := (domain_rank_facts (r t) (hdomain t)).1
    have hlt := List.idxOf_lt_length_of_mem hmem
    simpa [rank, ElevenCheck.values] using hlt
  have hdecode (t : Fin 11) : ElevenCheck.modulus (rank t) = r t := by
    have hmem := (domain_rank_facts (r t) (hdomain t)).1
    have hlt := List.idxOf_lt_length_of_mem hmem
    calc
      ElevenCheck.modulus (rank t) =
          ElevenCheck.values[ElevenCheck.values.idxOf (r t)] := by
        exact (List.getElem_eq_getD 0).symm
      _ = r t := List.getElem_idxOf hlt
  have hpair (u v : Fin 11) (huv : u ≠ v) :
      1 < Nat.gcd (r u) (r v) ∧ Nat.gcd (r u) (r v) < 11 := by
    rw [hrgcd u v huv]
    exact bounds hm hd hn huv
  have harank (t : Fin 11) (ht : 10 ∣ r t) : rank t < 18 :=
    (domain_rank_facts (r t) (hdomain t)).2 ht
  let indices := sortedIndices rank
  have hmem (t : Fin 11) : t ∈ indices := by
    simp [indices, sortedIndices]
  have hanchor_mem (t : Fin 11) (ht : 10 ∣ r t) :
      t ∈ indices.filter (fun u => rank u < 18) := by
    simp [hmem t, harank t ht]
  have hnd : ([i, j, l] : List (Fin 11)).Nodup := by
    simp [hij, hil, hjl]
  have hsub : ([i, j, l] : List (Fin 11)) ⊆
      indices.filter (fun t => rank t < 18) := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with hti | htj | htl
    · simpa [hti] using hanchor_mem i hi10
    · simpa [htj] using hanchor_mem j hj10
    · simpa [htl] using hanchor_mem l hl10
  have hthree : 3 ≤ (indices.filter (fun t => rank t < 18)).length := by
    simpa using hnd.length_le_of_subset hsub
  have hanchors : 3 ≤ (((sortedIndices rank).map rank).filter
      (fun x => x < 18)).length := by
    simpa [indices, List.filter_map, Function.comp_def] using hthree
  exact no_ranked_candidate_of_certificate hcert a r rank hrange hdecode
    (fun t => (hrpos t).1) hrdis hpair hanchors

/-- The eleven-class statement follows from every smaller nontrivial case. -/
theorem step (hprev : ∀ t : Nat, 2 ≤ t → t < 11 → Statement t) :
    Statement 11 :=
  step_of_certificate no_candidate hprev

end ProofPursuit.P4.Eleven
