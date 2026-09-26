import ProofPursuit.P4.Basic

namespace ProofPursuit.P4.Five

def target : Prop := Statement 5

theorem solution : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hb {i j : Fin 5} (hij : i ≠ j) := bounds hm hd hn hij
  by_cases he : ∀ i, 2 ∣ m i
  · have hg (i j : Fin 5) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 4 := by
      have h := hb hij
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (he i) (he j))
      have hh : Nat.gcd (m i) (m j) = 2 ∨ Nat.gcd (m i) (m j) = 4 := by omega
      rcases hh with hh | hh <;> simp [hh]
    have h01 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 5) ≠ 1) (hg 0 1 (by decide))
    have h02 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 5) ≠ 2) (hg 0 2 (by decide))
    have h03 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 5) ≠ 3) (hg 0 3 (by decide))
    have h04 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 5) ≠ 4) (hg 0 4 (by decide))
    have h12 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 5) ≠ 2) (hg 1 2 (by decide))
    have h13 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 5) ≠ 3) (hg 1 3 (by decide))
    have h14 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 5) ≠ 4) (hg 1 4 (by decide))
    have h23 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 5) ≠ 3) (hg 2 3 (by decide))
    have h24 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 5) ≠ 4) (hg 2 4 (by decide))
    have h34 := residues_ne_of_gcd_dvd hd (by decide : (3 : Fin 5) ≠ 4) (hg 3 4 (by decide))
    omega
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp he
    have hg (j : Fin 5) (hij : i ≠ j) : Nat.gcd (m i) (m j) = 3 := by
      have h := hb hij
      have hn2 : ¬ 2 ∣ Nat.gcd (m i) (m j) := by
        intro hh
        exact hi (Nat.dvd_trans hh (Nat.gcd_dvd_left _ _))
      have hz : Nat.gcd (m i) (m j) % 2 ≠ 0 := by
        intro hh
        exact hn2 (Nat.dvd_of_mod_eq_zero hh)
      omega
    have hthree : ∀ j, 3 ∣ m j := by
      intro j
      by_cases hij : i = j
      · subst j
        have hj : ∃ j : Fin 5, i ≠ j := by
          by_cases h : i = 0
          · exact ⟨1, by omega⟩
          · exact ⟨0, h⟩
        obtain ⟨j, hj⟩ := hj
        have hx := Nat.gcd_dvd_left (m i) (m j)
        rwa [hg j hj] at hx
      · have hx := Nat.gcd_dvd_right (m i) (m j)
        rwa [hg j hij] at hx
    have hall (i j : Fin 5) (hij : i ≠ j) : Nat.gcd (m i) (m j) = 3 := by
      have h := hb hij
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (hthree i) (hthree j))
      omega
    have h01 := residues_ne hd (by decide : (0 : Fin 5) ≠ 1) (hall 0 1 (by decide))
    have h02 := residues_ne hd (by decide : (0 : Fin 5) ≠ 2) (hall 0 2 (by decide))
    have h03 := residues_ne hd (by decide : (0 : Fin 5) ≠ 3) (hall 0 3 (by decide))
    have h12 := residues_ne hd (by decide : (1 : Fin 5) ≠ 2) (hall 1 2 (by decide))
    have h13 := residues_ne hd (by decide : (1 : Fin 5) ≠ 3) (hall 1 3 (by decide))
    have h23 := residues_ne hd (by decide : (2 : Fin 5) ≠ 3) (hall 2 3 (by decide))
    omega

end ProofPursuit.P4.Five
