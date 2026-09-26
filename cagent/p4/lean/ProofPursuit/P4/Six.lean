import ProofPursuit.P4.Basic

set_option maxHeartbeats 4000000

namespace ProofPursuit.P4.Six

def target : Prop := Statement 6

theorem solution : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hb {i j : Fin 6} (hij : i ≠ j) := bounds hm hd hn hij
  have ncommon (p : Nat) (hp : p = 2 ∨ p = 3 ∨ p = 5) : ¬ ∀ i, p ∣ m i := by
    intro hc
    have hg (i j : Fin 6) (hij : i ≠ j) := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (hc i) (hc j))
    rcases hp with rfl | rfl | rfl
    · have hh (i j : Fin 6) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 4 := by
        have h := hb hij
        have hz := hg i j hij
        have hx : Nat.gcd (m i) (m j) = 2 ∨ Nat.gcd (m i) (m j) = 4 := by omega
        rcases hx with hx | hx <;> simp [hx]
      have h01 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 1) (hh 0 1 (by decide))
      have h02 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 2) (hh 0 2 (by decide))
      have h03 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 3) (hh 0 3 (by decide))
      have h04 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 4) (hh 0 4 (by decide))
      have h12 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 2) (hh 1 2 (by decide))
      have h13 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 3) (hh 1 3 (by decide))
      have h14 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 4) (hh 1 4 (by decide))
      have h23 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 3) (hh 2 3 (by decide))
      have h24 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 4) (hh 2 4 (by decide))
      have h34 := residues_ne_of_gcd_dvd hd (by decide : (3 : Fin 6) ≠ 4) (hh 3 4 (by decide))
      omega
    · have hh (i j : Fin 6) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 3 := by
        have h := hb hij
        have hz := hg i j hij
        have hx : Nat.gcd (m i) (m j) = 3 := by omega
        simp [hx]
      have h01 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 1) (hh 0 1 (by decide))
      have h02 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 2) (hh 0 2 (by decide))
      have h03 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 3) (hh 0 3 (by decide))
      have h12 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 2) (hh 1 2 (by decide))
      have h13 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 3) (hh 1 3 (by decide))
      have h23 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 3) (hh 2 3 (by decide))
      omega
    · have hh (i j : Fin 6) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 5 := by
        have h := hb hij
        have hz := hg i j hij
        have hx : Nat.gcd (m i) (m j) = 5 := by omega
        simp [hx]
      have h01 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 1) (hh 0 1 (by decide))
      have h02 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 2) (hh 0 2 (by decide))
      have h03 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 3) (hh 0 3 (by decide))
      have h04 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 4) (hh 0 4 (by decide))
      have h05 := residues_ne_of_gcd_dvd hd (by decide : (0 : Fin 6) ≠ 5) (hh 0 5 (by decide))
      have h12 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 2) (hh 1 2 (by decide))
      have h13 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 3) (hh 1 3 (by decide))
      have h14 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 4) (hh 1 4 (by decide))
      have h15 := residues_ne_of_gcd_dvd hd (by decide : (1 : Fin 6) ≠ 5) (hh 1 5 (by decide))
      have h23 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 3) (hh 2 3 (by decide))
      have h24 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 4) (hh 2 4 (by decide))
      have h25 := residues_ne_of_gcd_dvd hd (by decide : (2 : Fin 6) ≠ 5) (hh 2 5 (by decide))
      have h34 := residues_ne_of_gcd_dvd hd (by decide : (3 : Fin 6) ≠ 4) (hh 3 4 (by decide))
      have h35 := residues_ne_of_gcd_dvd hd (by decide : (3 : Fin 6) ≠ 5) (hh 3 5 (by decide))
      have h45 := residues_ne_of_gcd_dvd hd (by decide : (4 : Fin 6) ≠ 5) (hh 4 5 (by decide))
      omega
  have supports (i j : Fin 6) (hij : i ≠ j) :
      (2 ∣ m i ∧ 2 ∣ m j) ∨ (3 ∣ m i ∧ 3 ∣ m j) ∨ (5 ∣ m i ∧ 5 ∣ m j) := by
    have h := hb hij
    have hl := Nat.gcd_dvd_left (m i) (m j)
    have hr := Nat.gcd_dvd_right (m i) (m j)
    have hx : Nat.gcd (m i) (m j) = 2 ∨ Nat.gcd (m i) (m j) = 3 ∨
        Nat.gcd (m i) (m j) = 4 ∨ Nat.gcd (m i) (m j) = 5 := by omega
    rcases hx with hx | hx | hx | hx
    · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
    · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hr)⟩
    · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
  have two (i : Fin 6) : (2 ∣ m i ∧ 3 ∣ m i) ∨ (2 ∣ m i ∧ 5 ∣ m i) ∨
      (3 ∣ m i ∧ 5 ∣ m i) := by
    have nc2 := ncommon 2 (by simp)
    have nc3 := ncommon 3 (by simp)
    have nc5 := ncommon 5 (by simp)
    by_cases h2 : 2 ∣ m i <;> by_cases h3 : 3 ∣ m i <;> by_cases h5 : 5 ∣ m i
    all_goals first
      | exact Or.inl ⟨h2, h3⟩
      | exact Or.inr (Or.inl ⟨h2, h5⟩)
      | exact Or.inr (Or.inr ⟨h3, h5⟩)
      | (exfalso; apply nc2; intro j; by_cases hij : i = j
         · simpa [← hij] using h2
         · rcases supports i j hij with h | h | h
           · exact h.2
           · exact False.elim (h3 h.1)
           · exact False.elim (h5 h.1))
      | (exfalso; apply nc3; intro j; by_cases hij : i = j
         · simpa [← hij] using h3
         · rcases supports i j hij with h | h | h
           · exact False.elim (h2 h.1)
           · exact h.2
           · exact False.elim (h5 h.1))
      | (exfalso; apply nc5; intro j; by_cases hij : i = j
         · simpa [← hij] using h5
         · rcases supports i j hij with h | h | h
           · exact False.elim (h2 h.1)
           · exact False.elim (h3 h.1)
           · exact h.2)
      | (have hx : ∃ j : Fin 6, i ≠ j := by
           by_cases h : i = 0
           · exact ⟨1, by omega⟩
           · exact ⟨0, h⟩
         obtain ⟨j, hj⟩ := hx
         rcases supports i j hj with h | h | h
         · exact False.elim (h2 h.1)
         · exact False.elim (h3 h.1)
         · exact False.elim (h5 h.1))
  have clash (i j : Fin 6) (hij : i ≠ j)
      (h : (2 ∣ m i ∧ 3 ∣ m i ∧ 2 ∣ m j ∧ 3 ∣ m j) ∨
           (2 ∣ m i ∧ 5 ∣ m i ∧ 2 ∣ m j ∧ 5 ∣ m j) ∨
           (3 ∣ m i ∧ 5 ∣ m i ∧ 3 ∣ m j ∧ 5 ∣ m j)) : False := by
    have hb' := hb hij
    rcases h with h | h | h
    all_goals
      have hx := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h.1 h.2.2.1)
      have hy := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h.2.1 h.2.2.2)
      omega
  have h0 := two 0
  have h1 := two 1
  have h2 := two 2
  have h3 := two 3
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3
  all_goals first
    | exact clash 0 1 (by decide) ((Or.inl) ⟨h0.1, h0.2, h1.1, h1.2⟩)
    | exact clash 0 1 (by decide) ((Or.inr ∘ Or.inl) ⟨h0.1, h0.2, h1.1, h1.2⟩)
    | exact clash 0 1 (by decide) ((Or.inr ∘ Or.inr) ⟨h0.1, h0.2, h1.1, h1.2⟩)
    | exact clash 0 2 (by decide) ((Or.inl) ⟨h0.1, h0.2, h2.1, h2.2⟩)
    | exact clash 0 2 (by decide) ((Or.inr ∘ Or.inl) ⟨h0.1, h0.2, h2.1, h2.2⟩)
    | exact clash 0 2 (by decide) ((Or.inr ∘ Or.inr) ⟨h0.1, h0.2, h2.1, h2.2⟩)
    | exact clash 0 3 (by decide) ((Or.inl) ⟨h0.1, h0.2, h3.1, h3.2⟩)
    | exact clash 0 3 (by decide) ((Or.inr ∘ Or.inl) ⟨h0.1, h0.2, h3.1, h3.2⟩)
    | exact clash 0 3 (by decide) ((Or.inr ∘ Or.inr) ⟨h0.1, h0.2, h3.1, h3.2⟩)
    | exact clash 1 2 (by decide) ((Or.inl) ⟨h1.1, h1.2, h2.1, h2.2⟩)
    | exact clash 1 2 (by decide) ((Or.inr ∘ Or.inl) ⟨h1.1, h1.2, h2.1, h2.2⟩)
    | exact clash 1 2 (by decide) ((Or.inr ∘ Or.inr) ⟨h1.1, h1.2, h2.1, h2.2⟩)
    | exact clash 1 3 (by decide) ((Or.inl) ⟨h1.1, h1.2, h3.1, h3.2⟩)
    | exact clash 1 3 (by decide) ((Or.inr ∘ Or.inl) ⟨h1.1, h1.2, h3.1, h3.2⟩)
    | exact clash 1 3 (by decide) ((Or.inr ∘ Or.inr) ⟨h1.1, h1.2, h3.1, h3.2⟩)
    | exact clash 2 3 (by decide) ((Or.inl) ⟨h2.1, h2.2, h3.1, h3.2⟩)
    | exact clash 2 3 (by decide) ((Or.inr ∘ Or.inl) ⟨h2.1, h2.2, h3.1, h3.2⟩)
    | exact clash 2 3 (by decide) ((Or.inr ∘ Or.inr) ⟨h2.1, h2.2, h3.1, h3.2⟩)

end ProofPursuit.P4.Six
