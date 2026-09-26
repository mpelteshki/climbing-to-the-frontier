import ProofPursuit.P4.Basic

namespace ProofPursuit.P4

/-- The reverse intersection criterion: any common point forces the gcd to divide
the difference between the residues. -/
theorem gcd_dvd_of_meet (a b : Int) (m n : Nat)
    (h : ∃ z : Int, InClass a m z ∧ InClass b n z) :
    (Nat.gcd m n : Int) ∣ b - a := by
  obtain ⟨z, hm, hn⟩ := h
  have hgm : (Nat.gcd m n : Int) ∣ (m : Int) := by
    exact_mod_cast Nat.gcd_dvd_left m n
  have hgn : (Nat.gcd m n : Int) ∣ (n : Int) := by
    exact_mod_cast Nat.gcd_dvd_right m n
  obtain ⟨u, hu⟩ := hgm
  obtain ⟨v, hv⟩ := hgn
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := hn
  refine ⟨u * s - v * t, ?_⟩
  grind

/-- Generalized CRT for two integer congruence classes. -/
theorem meet_iff_gcd_dvd (a b : Int) (m n : Nat) :
    (∃ z : Int, InClass a m z ∧ InClass b n z) ↔
      (Nat.gcd m n : Int) ∣ b - a := by
  constructor
  · exact gcd_dvd_of_meet a b m n
  · exact meet_of_gcd_dvd a b m n

/-- Intersecting both moduli with a common modulus preserves their gcd when
their original gcd divides that modulus. -/
theorem gcd_compressed (m n L : Nat) (hL : Nat.gcd m n ∣ L) :
    Nat.gcd (Nat.gcd m L) (Nat.gcd n L) = Nat.gcd m n := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd
      (Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
  · apply Nat.dvd_gcd
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hL
    · exact Nat.dvd_gcd (Nat.gcd_dvd_right _ _) hL

/-- The compressed modulus at each index is positive and divides L. -/
theorem compressed_modulus_bounds {k : Nat} (m : Fin k → Nat) (L : Nat)
    (hLpos : 0 < L) (i : Fin k) :
    0 < Nat.gcd (m i) L ∧ Nat.gcd (m i) L ∣ L := by
  exact ⟨Nat.gcd_pos_of_pos_right (m i) hLpos, Nat.gcd_dvd_right _ _⟩

/-- Compression preserves actual set-theoretic disjointness. -/
theorem disjoint_compressed {k : Nat} (a : Fin k → Int) (m : Fin k → Nat)
    (L : Nat) (hd : DisjointClasses a m)
    (hL : ∀ i j : Fin k, i ≠ j → Nat.gcd (m i) (m j) ∣ L) :
    DisjointClasses a (fun i => Nat.gcd (m i) L) := by
  intro i j hij hmeet
  have hg := gcd_compressed (m i) (m j) L (hL i j hij)
  apply incompatible hd hij
  rw [← hg]
  exact gcd_dvd_of_meet (a i) (a j) _ _ hmeet

/-- Any counterexample with all pairwise gcds below k compresses to moduli
dividing a positive common multiple of all positive integers below k. -/
theorem compress_counterexample {k : Nat} (a : Fin k → Int) (m : Fin k → Nat)
    (L : Nat) (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin k, i ≠ j → Nat.gcd (m i) (m j) < k)
    (hLpos : 0 < L)
    (hL : ∀ d : Nat, 0 < d → d < k → d ∣ L) :
    ∃ r : Fin k → Nat,
      (∀ i, 0 < r i ∧ r i ∣ L) ∧
      DisjointClasses a r ∧
      (∀ i j : Fin k, i ≠ j → Nat.gcd (r i) (r j) = Nat.gcd (m i) (m j)) := by
  let r : Fin k → Nat := fun i => Nat.gcd (m i) L
  have hpair (i j : Fin k) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ L :=
    hL _ (Nat.gcd_pos_of_pos_left (m j) (hm i)) (hsmall i j hij)
  exact ⟨r, fun i => compressed_modulus_bounds m L hLpos i,
    disjoint_compressed a m L hd hpair,
    fun i j hij => gcd_compressed (m i) (m j) L (hpair i j hij)⟩

end ProofPursuit.P4
