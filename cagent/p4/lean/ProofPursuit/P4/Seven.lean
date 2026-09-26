import ProofPursuit.P4.Parity

namespace ProofPursuit.P4.Seven
set_option maxHeartbeats 12000000

private theorem mod3_cases (b : Int) :
    b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega

private theorem allowed0 (b x : Int) (hb : b % 3 = 0) (ha : x % 3 ≠ b % 3) :
    x % 6 ∈ ([1, 2, 4, 5] : List Int) := by simp; omega

private theorem allowed1 (b x : Int) (hb : b % 3 = 1) (ha : x % 3 ≠ b % 3) :
    x % 6 ∈ ([0, 2, 3, 5] : List Int) := by simp; omega

private theorem allowed2 (b x : Int) (hb : b % 3 = 2) (ha : x % 3 ≠ b % 3) :
    x % 6 ∈ ([0, 1, 3, 4] : List Int) := by simp; omega

private theorem mod6_range (x : Int) :
    x % 6 ∈ ([0, 1, 2, 3, 4, 5] : List Int) := by simp; omega

private theorem mod5_range (x : Int) :
    x % 5 ∈ ([0, 1, 2, 3, 4] : List Int) := by simp; omega

private theorem seven_mod6_impossible (a : Fin 7 → Int)
    (h : ∀ i j : Fin 7, i ≠ j → a i % 6 ≠ a j % 6) : False := by
  let l : List Int := [a 0 % 6, a 1 % 6, a 2 % 6, a 3 % 6,
    a 4 % 6, a 5 % 6, a 6 % 6]
  have hnd : l.Nodup := by
    simp only [l, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
      or_false, not_or]
    repeat' constructor
    all_goals first
      | simp
      | exact h 0 1 (by decide)
      | exact h 0 2 (by decide)
      | exact h 0 3 (by decide)
      | exact h 0 4 (by decide)
      | exact h 0 5 (by decide)
      | exact h 0 6 (by decide)
      | exact h 1 2 (by decide)
      | exact h 1 3 (by decide)
      | exact h 1 4 (by decide)
      | exact h 1 5 (by decide)
      | exact h 1 6 (by decide)
      | exact h 2 3 (by decide)
      | exact h 2 4 (by decide)
      | exact h 2 5 (by decide)
      | exact h 2 6 (by decide)
      | exact h 3 4 (by decide)
      | exact h 3 5 (by decide)
      | exact h 3 6 (by decide)
      | exact h 4 5 (by decide)
      | exact h 4 6 (by decide)
      | exact h 5 6 (by decide)
  have hs : l ⊆ ([0, 1, 2, 3, 4, 5] : List Int) := by
    intro x hx
    simp [l] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mod6_range _
  have := hnd.length_le_of_subset hs
  simp [l] at this

private theorem six_mod5_impossible (a : Fin 7 → Int)
    (h : ∀ i j : Fin 7, i ≠ j → a i % 5 ≠ a j % 5) : False := by
  let l : List Int := [a 0 % 5, a 1 % 5, a 2 % 5,
    a 3 % 5, a 4 % 5, a 5 % 5]
  have hnd : l.Nodup := by
    simp only [l, List.nodup_cons, List.mem_cons, List.mem_nil_iff,
      or_false, not_or]
    repeat' constructor
    all_goals first
      | simp
      | exact h 0 1 (by decide)
      | exact h 0 2 (by decide)
      | exact h 0 3 (by decide)
      | exact h 0 4 (by decide)
      | exact h 0 5 (by decide)
      | exact h 1 2 (by decide)
      | exact h 1 3 (by decide)
      | exact h 1 4 (by decide)
      | exact h 1 5 (by decide)
      | exact h 2 3 (by decide)
      | exact h 2 4 (by decide)
      | exact h 2 5 (by decide)
      | exact h 3 4 (by decide)
      | exact h 3 5 (by decide)
      | exact h 4 5 (by decide)
  have hs : l ⊆ ([0, 1, 2, 3, 4] : List Int) := by
    intro x hx
    simp [l] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mod5_range _
  have := hnd.length_le_of_subset hs
  simp [l] at this

theorem five_avoid (b x0 x1 x2 x3 x4 : Int)
    (ha0 : x0 % 3 ≠ b % 3)
    (ha1 : x1 % 3 ≠ b % 3)
    (ha2 : x2 % 3 ≠ b % 3)
    (ha3 : x3 % 3 ≠ b % 3)
    (ha4 : x4 % 3 ≠ b % 3)
    (hd01 : x0 % 6 ≠ x1 % 6)
    (hd02 : x0 % 6 ≠ x2 % 6)
    (hd03 : x0 % 6 ≠ x3 % 6)
    (hd04 : x0 % 6 ≠ x4 % 6)
    (hd12 : x1 % 6 ≠ x2 % 6)
    (hd13 : x1 % 6 ≠ x3 % 6)
    (hd14 : x1 % 6 ≠ x4 % 6)
    (hd23 : x2 % 6 ≠ x3 % 6)
    (hd24 : x2 % 6 ≠ x4 % 6)
    (hd34 : x3 % 6 ≠ x4 % 6)
    : False := by
  let l : List Int := [x0 % 6, x1 % 6, x2 % 6, x3 % 6, x4 % 6]
  have hnd : l.Nodup := by
    simp [l, List.nodup_cons, hd01, hd02, hd03, hd04,
      hd12, hd13, hd14, hd23, hd24, hd34]
  have hb := mod3_cases b
  rcases hb with hb | hb | hb
  · have hs : l ⊆ ([1, 2, 4, 5] : List Int) := by
      intro y hy
      simp [l] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact allowed0 b x0 hb ha0
      · exact allowed0 b x1 hb ha1
      · exact allowed0 b x2 hb ha2
      · exact allowed0 b x3 hb ha3
      · exact allowed0 b x4 hb ha4
    have := hnd.length_le_of_subset hs
    simp [l] at this
  · have hs : l ⊆ ([0, 2, 3, 5] : List Int) := by
      intro y hy
      simp [l] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact allowed1 b x0 hb ha0
      · exact allowed1 b x1 hb ha1
      · exact allowed1 b x2 hb ha2
      · exact allowed1 b x3 hb ha3
      · exact allowed1 b x4 hb ha4
    have := hnd.length_le_of_subset hs
    simp [l] at this
  · have hs : l ⊆ ([0, 1, 3, 4] : List Int) := by
      intro y hy
      simp [l] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact allowed2 b x0 hb ha0
      · exact allowed2 b x1 hb ha1
      · exact allowed2 b x2 hb ha2
      · exact allowed2 b x3 hb ha3
      · exact allowed2 b x4 hb ha4
    have := hnd.length_le_of_subset hs
    simp [l] at this

def target : Prop := Statement 7

theorem solution : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hb {i j : Fin 7} (hij : i ≠ j) := bounds hm hd hn hij
  have ncommon (p : Nat) (hp : p = 2 ∨ p = 3 ∨ p = 5) : ¬ ∀ i, p ∣ m i := by
    rcases hp with rfl | rfl | rfl
    · exact seven_not_all_even a m hm hd hn
    · intro hc
      have hh (i j : Fin 7) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 6 := by
        have h := hb hij
        have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (hc i) (hc j))
        have hx : Nat.gcd (m i) (m j) = 3 ∨ Nat.gcd (m i) (m j) = 6 := by omega
        rcases hx with hx | hx <;> simp [hx]
      exact seven_mod6_impossible a (fun i j hij =>
        residues_ne_of_gcd_dvd hd hij (hh i j hij))
    · intro hc
      have hh (i j : Fin 7) (hij : i ≠ j) : Nat.gcd (m i) (m j) ∣ 5 := by
        have h := hb hij
        have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd (hc i) (hc j))
        have hx : Nat.gcd (m i) (m j) = 5 := by omega
        simp [hx]
      exact six_mod5_impossible a (fun i j hij =>
        residues_ne_of_gcd_dvd hd hij (hh i j hij))
  have supports (i j : Fin 7) (hij : i ≠ j) :
      (2 ∣ m i ∧ 2 ∣ m j) ∨ (3 ∣ m i ∧ 3 ∣ m j) ∨ (5 ∣ m i ∧ 5 ∣ m j) := by
    have h := hb hij
    have hl := Nat.gcd_dvd_left (m i) (m j)
    have hr := Nat.gcd_dvd_right (m i) (m j)
    have hx : Nat.gcd (m i) (m j) = 2 ∨ Nat.gcd (m i) (m j) = 3 ∨
        Nat.gcd (m i) (m j) = 4 ∨ Nat.gcd (m i) (m j) = 5 ∨ Nat.gcd (m i) (m j) = 6 := by omega
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
    · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hr)⟩
    · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [hx] using hr)⟩
  have two (i : Fin 7) : (2 ∣ m i ∧ 3 ∣ m i) ∨ (2 ∣ m i ∧ 5 ∣ m i) ∨
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
      | (have hx : ∃ j : Fin 7, i ≠ j := by
           by_cases h : i = 0
           · exact ⟨1, by omega⟩
           · exact ⟨0, h⟩
         obtain ⟨j, hj⟩ := hx
         rcases supports i j hj with h | h | h
         · exact False.elim (h2 h.1)
         · exact False.elim (h3 h.1)
         · exact False.elim (h5 h.1))
  obtain ⟨i, hi⟩ := Classical.not_forall.mp (ncommon 2 (by simp))
  obtain ⟨j, hj⟩ := Classical.not_forall.mp (ncommon 3 (by simp))
  have hi35 : 3 ∣ m i ∧ 5 ∣ m i := by
    rcases two i with h | h | h
    · exact False.elim (hi h.1)
    · exact False.elim (hi h.1)
    · exact h
  have hj25 : 2 ∣ m j ∧ 5 ∣ m j := by
    rcases two j with h | h | h
    · exact False.elim (hj h.2)
    · exact h
    · exact False.elim (hj h.1)
  have ht23 (t : Fin 7) (hti : t ≠ i) (htj : t ≠ j) : 2 ∣ m t ∧ 3 ∣ m t := by
    have h5 : ¬ 5 ∣ m t := by
      intro h5
      rcases two t with h | h | h
      · have b := hb htj
        have x := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h.1 hj25.1)
        have y := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h5 hj25.2)
        omega
      · have b := hb htj
        have x := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h.1 hj25.1)
        have y := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h5 hj25.2)
        omega
      · have b := hb hti
        have x := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h.1 hi35.1)
        have y := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd h5 hi35.2)
        omega
    rcases two t with h | h | h
    · exact h
    · exact False.elim (h5 h.2)
    · exact False.elim (h5 h.2)
  have avoid (t : Fin 7) (hti : t ≠ i) (htj : t ≠ j) : a t % 3 ≠ a i % 3 := by
    have ht := ht23 t hti htj
    have b := hb hti
    have h3 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht.2 hi35.1)
    have h6 : Nat.gcd (m t) (m i) ≠ 6 := by
      intro h
      apply hi
      exact Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [h] using Nat.gcd_dvd_right (m t) (m i))
    have hg : Nat.gcd (m t) (m i) = 3 := by omega
    exact residues_ne hd hti hg
  have different (t u : Fin 7) (htu : t ≠ u) (hti : t ≠ i) (htj : t ≠ j)
      (hui : u ≠ i) (huj : u ≠ j) : a t % 6 ≠ a u % 6 := by
    have ht := ht23 t hti htj
    have hu := ht23 u hui huj
    have b := hb htu
    have h2 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht.1 hu.1)
    have h3 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht.2 hu.2)
    have hg : Nat.gcd (m t) (m u) = 6 := by omega
    exact residues_ne hd htu hg
  have hic : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hic with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hjc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hi hj25.1
  · exact five_avoid (a 0) (a 2) (a 3) (a 4) (a 5) (a 6)
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 0) (a 1) (a 3) (a 4) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 0) (a 1) (a 2) (a 4) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 0) (a 1) (a 2) (a 3) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 0) (a 1) (a 2) (a 3) (a 4) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1
  · exact five_avoid (a 1) (a 0) (a 3) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 1) (a 0) (a 2) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 1) (a 0) (a 2) (a 3) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 1) (a 0) (a 2) (a 3) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 1) (a 0) (a 2) (a 3) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 2) (a 1) (a 3) (a 4) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 2) (a 0) (a 3) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1
  · exact five_avoid (a 2) (a 0) (a 1) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 2) (a 0) (a 1) (a 3) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 2) (a 0) (a 1) (a 3) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 2) (a 0) (a 1) (a 3) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 3) (a 1) (a 2) (a 4) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 3) (a 0) (a 2) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 3) (a 0) (a 1) (a 4) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1
  · exact five_avoid (a 3) (a 0) (a 1) (a 2) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 3) (a 0) (a 1) (a 2) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 3) (a 0) (a 1) (a 2) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 4) (a 1) (a 2) (a 3) (a 5) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 4) (a 0) (a 2) (a 3) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 4) (a 0) (a 1) (a 3) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 4) (a 0) (a 1) (a 2) (a 5) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 5 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1
  · exact five_avoid (a 4) (a 0) (a 1) (a 2) (a 3) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 4) (a 0) (a 1) (a 2) (a 3) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 5) (a 1) (a 2) (a 3) (a 4) (a 6)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 5) (a 0) (a 2) (a 3) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 5) (a 0) (a 1) (a 3) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 5) (a 0) (a 1) (a 2) (a 4) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 5) (a 0) (a 1) (a 2) (a 3) (a 6)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 6 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 6 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 6 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1
  · exact five_avoid (a 5) (a 0) (a 1) (a 2) (a 3) (a 4)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 1) (a 2) (a 3) (a 4) (a 5)
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 0) (a 2) (a 3) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 0) (a 1) (a 3) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 0) (a 1) (a 2) (a 4) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 4 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 0) (a 1) (a 2) (a 3) (a 5)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 5 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 5 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 5 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact five_avoid (a 6) (a 0) (a 1) (a 2) (a 3) (a 4)
      (avoid 0 (by decide) (by decide))
      (avoid 1 (by decide) (by decide))
      (avoid 2 (by decide) (by decide))
      (avoid 3 (by decide) (by decide))
      (avoid 4 (by decide) (by decide))
      (different 0 1 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 0 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 1 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 3 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 2 4 (by decide) (by decide) (by decide) (by decide) (by decide))
      (different 3 4 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact hi hj25.1

end ProofPursuit.P4.Seven
