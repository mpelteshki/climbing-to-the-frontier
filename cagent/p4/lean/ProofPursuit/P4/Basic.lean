import Std

namespace ProofPursuit.P4

/-- Membership in the integer congruence class of a modulo the natural modulus m. -/
def InClass (a : Int) (m : Nat) (z : Int) : Prop := (m : Int) ∣ z - a

/-- The actual set-theoretic disjointness condition, not a CRT assumption. -/
def DisjointClasses {k : Nat} (a : Fin k → Int) (m : Fin k → Nat) : Prop :=
  ∀ i j, i ≠ j → ¬ ∃ z : Int, InClass (a i) (m i) z ∧ InClass (a j) (m j) z

def Statement (k : Nat) : Prop :=
  ∀ (a : Fin k → Int) (m : Fin k → Nat),
    (∀ i, 0 < m i) → DisjointClasses a m →
      ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (m i) (m j)

/-- Extended Euclid, proved from the standard library's gcd induction. -/
theorem bezout (m n : Nat) :
    ∃ x y : Int, (Nat.gcd m n : Int) = (m : Int) * x + (n : Int) * y := by
  induction m, n using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _ ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y - (n / m : Nat) * x, x, ?_⟩
    rw [Nat.gcd_rec]
    have he : (n % m : Nat) + (m : Int) * (n / m : Nat) = (n : Int) := by
      exact_mod_cast Nat.mod_add_div n m
    grind

/-- The intersection direction of the generalized Chinese remainder theorem. -/
theorem meet_of_gcd_dvd (a b : Int) (m n : Nat)
    (h : (Nat.gcd m n : Int) ∣ b - a) :
    ∃ z : Int, InClass a m z ∧ InClass b n z := by
  obtain ⟨x, y, hb⟩ := bezout m n
  obtain ⟨t, ht⟩ := h
  refine ⟨a + (m : Int) * x * t, ?_, ?_⟩
  · exact ⟨x * t, by grind⟩
  · exact ⟨-y * t, by grind⟩

theorem incompatible {k : Nat} {a : Fin k → Int} {m : Fin k → Nat}
    (h : DisjointClasses a m) {i j : Fin k} (hij : i ≠ j) :
    ¬ (Nat.gcd (m i) (m j) : Int) ∣ a j - a i := by
  intro hd
  exact h i j hij (meet_of_gcd_dvd _ _ _ _ hd)

end ProofPursuit.P4

namespace ProofPursuit.P4

theorem bounds {k : Nat} {a : Fin k → Int} {m : Fin k → Nat}
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (m i) (m j))
    {i j : Fin k} (hij : i ≠ j) :
    2 ≤ Nat.gcd (m i) (m j) ∧ Nat.gcd (m i) (m j) < k := by
  have hp := Nat.gcd_pos_of_pos_left (m j) (hm i)
  have hne : Nat.gcd (m i) (m j) ≠ 1 := by
    intro h
    have hi := incompatible hd hij
    rw [h] at hi
    exact hi (by simp)
  have hu : Nat.gcd (m i) (m j) < k := by
    apply Classical.byContradiction
    intro h
    have hl : k ≤ Nat.gcd (m i) (m j) := by omega
    by_cases hlt : i < j
    · exact hn ⟨i, j, hlt, hl⟩
    · exact hn ⟨j, i, by omega, by simpa [Nat.gcd_comm] using hl⟩
  omega

theorem residues_ne {k : Nat} {a : Fin k → Int} {m : Fin k → Nat}
    (hd : DisjointClasses a m) {i j : Fin k} (hij : i ≠ j) {d : Nat}
    (hg : Nat.gcd (m i) (m j) = d) : a i % (d : Int) ≠ a j % (d : Int) := by
  intro h
  apply incompatible hd hij
  rw [hg, Int.dvd_iff_emod_eq_zero]
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h.symm

end ProofPursuit.P4

namespace ProofPursuit.P4

theorem residues_ne_of_gcd_dvd {k : Nat} {a : Fin k → Int} {m : Fin k → Nat}
    (hd : DisjointClasses a m) {i j : Fin k} (hij : i ≠ j) {d : Nat}
    (hg : Nat.gcd (m i) (m j) ∣ d) : a i % (d : Int) ≠ a j % (d : Int) := by
  intro h
  apply incompatible hd hij
  have hg' : (Nat.gcd (m i) (m j) : Int) ∣ (d : Int) := by exact_mod_cast hg
  exact Int.dvd_trans hg' (Int.dvd_iff_emod_eq_zero.mpr
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h.symm))

end ProofPursuit.P4
