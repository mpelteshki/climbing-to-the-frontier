import ProofPursuit.P4.Density

namespace ProofPursuit.P4.ListDensity

/-- A list of moduli is realizable when its positions can be assigned
pairwise disjoint integer congruence classes. Equal moduli remain distinct
positions. -/
def Realizable (xs : List Nat) : Prop :=
  ∃ a : Fin xs.length → Int,
    DisjointClasses a (fun i => xs[i.val])

/-- The compressed density inequality for a realizable list. -/
theorem density_bound_compressed (xs : List Nat) (M : Nat)
    (hM : 0 < M) (_hr : ∀ x ∈ xs, 0 < x)
    (hreal : Realizable xs)
    (hpair : xs.Pairwise (fun x y => Nat.gcd x y ∣ M)) :
    (xs.map (fun x => M / Nat.gcd x M)).sum ≤ M := by
  obtain ⟨a, hd⟩ := hreal
  have hp (i j : Fin xs.length) (hij : i ≠ j) :
      Nat.gcd xs[i.val] xs[j.val] ∣ M := by
    by_cases hlt : i.val < j.val
    · exact (List.pairwise_iff_getElem.mp hpair) i.val j.val i.isLt j.isLt hlt
    · have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
        omega
      rw [Nat.gcd_comm]
      exact (List.pairwise_iff_getElem.mp hpair) j.val i.val j.isLt i.isLt hgt
  have hb := ProofPursuit.P4.density_bound_compressed a (fun i => xs[i.val]) hM hd hp
  have he : (List.ofFn (fun i : Fin xs.length => M / Nat.gcd xs[i.val] M)) =
      xs.map (fun x => M / Nat.gcd x M) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simpa [List.finRange, List.map_ofFn, Function.comp_def, he] using hb

/-- Every pair of positions, with multiplicity, in increasing position order. -/
def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

/-- The least common multiple of the pairwise gcds. -/
def pairModulus (xs : List Nat) : Nat :=
  (pairs xs).foldl (fun acc p => Nat.lcm acc (Nat.gcd p.1 p.2)) 1

private theorem pairs_pos (xs : List Nat) (hxs : ∀ x ∈ xs, 0 < x) :
    ∀ p ∈ pairs xs, 0 < p.1 ∧ 0 < p.2 := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      exact ⟨hxs x (by simp), hxs y (by simp [hy])⟩
    · exact ih (fun y hy => hxs y (by simp [hy])) p hp

private theorem fold_pos (ps : List (Nat × Nat)) (acc : Nat)
    (hacc : 0 < acc) (hps : ∀ p ∈ ps, 0 < p.1 ∧ 0 < p.2) :
    0 < ps.foldl (fun n p => Nat.lcm n (Nat.gcd p.1 p.2)) acc := by
  induction ps generalizing acc with
  | nil => simpa using hacc
  | cons p ps ih =>
    have hp := (hps p (by simp)).1
    have hg : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hp
    exact ih (Nat.lcm acc (Nat.gcd p.1 p.2))
      (Nat.lcm_pos hacc hg) (fun q hq => hps q (by simp [hq]))

theorem pairModulus_pos (xs : List Nat) (hxs : ∀ x ∈ xs, 0 < x) :
    0 < pairModulus xs := by
  exact fold_pos (pairs xs) 1 (by decide) (pairs_pos xs hxs)

private theorem acc_dvd_fold (ps : List (Nat × Nat)) (acc : Nat) :
    acc ∣ ps.foldl (fun n p => Nat.lcm n (Nat.gcd p.1 p.2)) acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    exact Nat.dvd_trans (Nat.dvd_lcm_left acc (Nat.gcd p.1 p.2))
      (ih (Nat.lcm acc (Nat.gcd p.1 p.2)))

private theorem pair_dvd_fold (ps : List (Nat × Nat)) (acc : Nat)
    (p : Nat × Nat) (hp : p ∈ ps) :
    Nat.gcd p.1 p.2 ∣
      ps.foldl (fun n q => Nat.lcm n (Nat.gcd q.1 q.2)) acc := by
  induction ps generalizing acc with
  | nil => contradiction
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.dvd_trans (Nat.dvd_lcm_right acc (Nat.gcd p.1 p.2))
        (acc_dvd_fold ps (Nat.lcm acc (Nat.gcd p.1 p.2)))
    · exact ih (Nat.lcm acc (Nat.gcd q.1 q.2)) hp

theorem pair_dvd_pairModulus (xs : List Nat) (p : Nat × Nat)
    (hp : p ∈ pairs xs) : Nat.gcd p.1 p.2 ∣ pairModulus xs := by
  exact pair_dvd_fold (pairs xs) 1 p hp

private theorem pairwise_of_pairs (xs : List Nat) (M : Nat)
    (h : ∀ p ∈ pairs xs, Nat.gcd p.1 p.2 ∣ M) :
    xs.Pairwise (fun x y => Nat.gcd x y ∣ M) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro y hy
      exact h (x, y) (by simp [pairs, hy])
    · apply ih
      intro p hp
      exact h p (by simp [pairs, hp])

theorem pairwise_pairModulus (xs : List Nat) :
    xs.Pairwise (fun x y => Nat.gcd x y ∣ pairModulus xs) := by
  exact pairwise_of_pairs xs (pairModulus xs)
    (fun p hp => pair_dvd_pairModulus xs p hp)

theorem density_bound_pairModulus (xs : List Nat)
    (hxs : ∀ x ∈ xs, 0 < x) (hreal : Realizable xs) :
    (xs.map (fun x => pairModulus xs / Nat.gcd x (pairModulus xs))).sum ≤
      pairModulus xs := by
  exact density_bound_compressed xs (pairModulus xs)
    (pairModulus_pos xs hxs) hxs hreal (pairwise_pairModulus xs)

/-- Deleting positions preserves realizability, including when moduli repeat. -/
theorem realizable_sublist {ys xs : List Nat} (hsub : List.Sublist ys xs)
    (hreal : Realizable xs) : Realizable ys := by
  obtain ⟨a, hd⟩ := hreal
  obtain ⟨is, his, hinc⟩ := List.sublist_eq_map_getElem hsub
  have hlen : ys.length = is.length := by simp [his]
  let f : Fin ys.length → Fin xs.length := fun i => is[i.val]'(by omega)
  have hf : ∀ i j : Fin ys.length, f i = f j → i = j := by
    intro i j heq
    apply Fin.ext
    by_cases hne : i.val = j.val
    · exact hne
    exfalso
    have hij : i.val < j.val ∨ j.val < i.val := by omega
    rcases hij with hij | hji
    · have hlt := (List.pairwise_iff_getElem.mp hinc) i.val j.val
        (by omega) (by omega) hij
      have : (is[i.val]'(by omega)).val < (is[j.val]'(by omega)).val := hlt
      exact (Nat.ne_of_lt this) (congrArg Fin.val heq)
    · have hlt := (List.pairwise_iff_getElem.mp hinc) j.val i.val
        (by omega) (by omega) hji
      have : (is[j.val]'(by omega)).val < (is[i.val]'(by omega)).val := hlt
      exact (Nat.ne_of_gt this) (congrArg Fin.val heq)
  have hm (i : Fin ys.length) : ys[i.val] = xs[(f i).val] := by
    subst ys
    simp [f]
  refine ⟨fun i => a (f i), ?_⟩
  intro i j hij hmeet
  apply hd (f i) (f j) (fun heq => hij (hf i j heq))
  simpa [hm] using hmeet

end ProofPursuit.P4.ListDensity
