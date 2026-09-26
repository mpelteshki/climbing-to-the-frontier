import ProofPursuit.P4.Density
import ProofPursuit.P4.ThroughNine

namespace ProofPursuit.P4.Ten

set_option maxHeartbeats 12000000

private def omitIndex {n : Nat} (t : Fin (n + 1)) (s : Fin n) : Fin (n + 1) :=
  ⟨if s.val < t.val then s.val else s.val + 1, by
    by_cases h : s.val < t.val <;> simp [h] <;> omega⟩

private theorem omitIndex_ne {n : Nat} (t : Fin (n + 1)) (s : Fin n) :
    omitIndex t s ≠ t := by
  intro h
  have hv := congrArg Fin.val h
  simp only [omitIndex] at hv
  by_cases hs : s.val < t.val <;> simp [hs] at hv <;> omega

private theorem omitIndex_injective {n : Nat} (t : Fin (n + 1)) {s u : Fin n}
    (h : omitIndex t s = omitIndex t u) : s = u := by
  have hv := congrArg Fin.val h
  simp only [omitIndex] at hv
  by_cases hs : s.val < t.val <;> by_cases hu : u.val < t.val <;>
    simp [hs, hu] at hv <;> apply Fin.ext <;> omega

private theorem omitIndex_surjective {n : Nat} (t i : Fin (n + 1)) (hit : i ≠ t) :
    ∃ s : Fin n, omitIndex t s = i := by
  have hv : i.val ≠ t.val := by intro h; exact hit (Fin.ext h)
  by_cases h : i.val < t.val
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [omitIndex, h]
  · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [omitIndex, show ¬ i.val - 1 < t.val by omega]
    omega

/-- Every counterexample at ten, conditional on Statement 9, has at least
three distinct moduli divisible by 9. -/
theorem three_multiples_nine (h9 : Statement 9)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j)) :
    ∃ i j k : Fin 10, i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
      9 ∣ m i ∧ 9 ∣ m j ∧ 9 ∣ m k := by
  have hb {i j : Fin 10} (hij : i ≠ j) := bounds hm hd hn hij
  have ninePair (v : Fin 10) :
      ∃ i j : Fin 10, i ≠ j ∧ i ≠ v ∧ j ≠ v ∧ Nat.gcd (m i) (m j) = 9 := by
    let a' : Fin 9 → Int := fun s => a (omitIndex v s)
    let m' : Fin 9 → Nat := fun s => m (omitIndex v s)
    have hm' : ∀ s, 0 < m' s := by intro s; exact hm _
    have hd' : DisjointClasses a' m' := by
      intro s u hsu
      exact hd (omitIndex v s) (omitIndex v u)
        (fun h => hsu (omitIndex_injective v h))
    obtain ⟨s, u, hsu, hge⟩ := h9 a' m' hm' hd'
    have hne : omitIndex v s ≠ omitIndex v u := by
      intro h
      have := omitIndex_injective v h
      omega
    refine ⟨omitIndex v s, omitIndex v u, hne, omitIndex_ne v s,
      omitIndex_ne v u, ?_⟩
    have hlt := (hb hne).2
    dsimp [m'] at hge
    omega
  obtain ⟨i, j, hij, _, _, hij9⟩ := ninePair 0
  have hi9 : 9 ∣ m i := by
    rw [← hij9]; exact Nat.gcd_dvd_left _ _
  have hj9 : 9 ∣ m j := by
    rw [← hij9]; exact Nat.gcd_dvd_right _ _
  obtain ⟨p, q, hpq, hpi, hqi, hpq9⟩ := ninePair i
  by_cases hpj : p = j
  · refine ⟨i, j, q, hij, hqi, ?_, hi9, hj9, ?_⟩
    · exact fun h => hpq (hpj.trans h.symm)
    · rw [← hpq9]; exact Nat.gcd_dvd_right _ _
  · refine ⟨i, j, p, hij, hpi, hpj, hi9, hj9, ?_⟩
    rw [← hpq9]; exact Nat.gcd_dvd_left _ _

/-- With one modulus outside 3, the three 9-multiples exhaust the primes
2, 5, and 7. There can be no fourth 9-multiple. -/
theorem nine_anchor_support (h9 : Statement 9)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (hthree : ∃ t : Fin 10, ¬ 3 ∣ m t) :
    ∃ i j k : Fin 10,
      i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
      9 ∣ m i ∧ 9 ∣ m j ∧ 9 ∣ m k ∧
      (∀ u : Fin 10, 9 ∣ m u → u = i ∨ u = j ∨ u = k) ∧
      (2 ∣ m i ∨ 5 ∣ m i ∨ 7 ∣ m i) ∧
      (2 ∣ m j ∨ 5 ∣ m j ∨ 7 ∣ m j) ∧
      (2 ∣ m k ∨ 5 ∣ m k ∨ 7 ∣ m k) ∧
      (2 ∣ m i ∨ 2 ∣ m j ∨ 2 ∣ m k) ∧
      (5 ∣ m i ∨ 5 ∣ m j ∨ 5 ∣ m k) ∧
      (7 ∣ m i ∨ 7 ∣ m j ∨ 7 ∣ m k) := by
  obtain ⟨i, j, k, hij, hki, hkj, hi9, hj9, hk9⟩ :=
    three_multiples_nine h9 a m hm hd hn
  obtain ⟨t, ht3⟩ := hthree
  have hb {x y : Fin 10} (hxy : x ≠ y) := bounds hm hd hn hxy
  have gcdNine (x y : Fin 10) (hxy : x ≠ y)
      (hx : 9 ∣ m x) (hy : 9 ∣ m y) : Nat.gcd (m x) (m y) = 9 := by
    have h := hb hxy
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx hy)
    omega
  have noCommon (x y : Fin 10) (hxy : x ≠ y)
      (hx : 9 ∣ m x) (hy : 9 ∣ m y) (p : Nat)
      (hp : p = 2 ∨ p = 5 ∨ p = 7) : ¬(p ∣ m x ∧ p ∣ m y) := by
    intro h
    have hdvd : p ∣ 9 := by
      rw [← gcdNine x y hxy hx hy]
      exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  have shared (x y : Fin 10) (hxy : x ≠ y) (hy : ¬ 3 ∣ m y) :
      (2 ∣ m x ∧ 2 ∣ m y) ∨
      (5 ∣ m x ∧ 5 ∣ m y) ∨
      (7 ∣ m x ∧ 7 ∣ m y) := by
    have h := hb hxy
    have hl := Nat.gcd_dvd_left (m x) (m y)
    have hr := Nat.gcd_dvd_right (m x) (m y)
    have hne : ¬ 3 ∣ Nat.gcd (m x) (m y) := by
      intro he
      exact hy (Nat.dvd_trans he hr)
    have hmod : Nat.gcd (m x) (m y) % 3 ≠ 0 := by
      intro he
      exact hne (Nat.dvd_of_mod_eq_zero he)
    have hx : Nat.gcd (m x) (m y) = 2 ∨ Nat.gcd (m x) (m y) = 4 ∨
        Nat.gcd (m x) (m y) = 5 ∨ Nat.gcd (m x) (m y) = 7 ∨
        Nat.gcd (m x) (m y) = 8 := by omega
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hr)⟩
    · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 8) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 8) (by simpa [hx] using hr)⟩
  have hti : t ≠ i := by
    intro h
    exact ht3 (Nat.dvd_trans (by decide : 3 ∣ 9) (h ▸ hi9))
  have htj : t ≠ j := by
    intro h
    exact ht3 (Nat.dvd_trans (by decide : 3 ∣ 9) (h ▸ hj9))
  have htk : t ≠ k := by
    intro h
    exact ht3 (Nat.dvd_trans (by decide : 3 ∣ 9) (h ▸ hk9))
  have h_it := shared i t hti.symm ht3
  have h_jt := shared j t htj.symm ht3
  have h_kt := shared k t htk.symm ht3
  have h_ij2 := noCommon i j hij hi9 hj9 2 (Or.inl rfl)
  have h_ij5 := noCommon i j hij hi9 hj9 5 (Or.inr (Or.inl rfl))
  have h_ij7 := noCommon i j hij hi9 hj9 7 (Or.inr (Or.inr rfl))
  have h_ik2 := noCommon i k hki.symm hi9 hk9 2 (Or.inl rfl)
  have h_ik5 := noCommon i k hki.symm hi9 hk9 5 (Or.inr (Or.inl rfl))
  have h_ik7 := noCommon i k hki.symm hi9 hk9 7 (Or.inr (Or.inr rfl))
  have h_jk2 := noCommon j k hkj.symm hj9 hk9 2 (Or.inl rfl)
  have h_jk5 := noCommon j k hkj.symm hj9 hk9 5 (Or.inr (Or.inl rfl))
  have h_jk7 := noCommon j k hkj.symm hj9 hk9 7 (Or.inr (Or.inr rfl))
  have atMost (u : Fin 10) (hu9 : 9 ∣ m u) : u = i ∨ u = j ∨ u = k := by
    apply Classical.byContradiction
    intro hnot
    have hui : u ≠ i := by intro h; exact hnot (Or.inl h)
    have huj : u ≠ j := by intro h; exact hnot (Or.inr (Or.inl h))
    have huk : u ≠ k := by intro h; exact hnot (Or.inr (Or.inr h))
    have hut : u ≠ t := by
      intro h
      exact ht3 (Nat.dvd_trans (by decide : 3 ∣ 9) (h ▸ hu9))
    have h_ut := shared u t hut ht3
    have h_ui2 := noCommon u i hui hu9 hi9 2 (Or.inl rfl)
    have h_ui5 := noCommon u i hui hu9 hi9 5 (Or.inr (Or.inl rfl))
    have h_ui7 := noCommon u i hui hu9 hi9 7 (Or.inr (Or.inr rfl))
    have h_uj2 := noCommon u j huj hu9 hj9 2 (Or.inl rfl)
    have h_uj5 := noCommon u j huj hu9 hj9 5 (Or.inr (Or.inl rfl))
    have h_uj7 := noCommon u j huj hu9 hj9 7 (Or.inr (Or.inr rfl))
    have h_uk2 := noCommon u k huk hu9 hk9 2 (Or.inl rfl)
    have h_uk5 := noCommon u k huk hu9 hk9 5 (Or.inr (Or.inl rfl))
    have h_uk7 := noCommon u k huk hu9 hk9 7 (Or.inr (Or.inr rfl))
    grind
  refine ⟨i, j, k, hij, hki, hkj, hi9, hj9, hk9, atMost,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals grind

/-- Deleting two 9-anchors leaves an eight-class family. If its remaining
9-anchor is odd, Statement 8 forces two new multiples of 8. -/
theorem two_eight_outside (h8 : Statement 8)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (i j k : Fin 10) (hij : i ≠ j)
    (hatMost : ∀ u : Fin 10, 9 ∣ m u → u = i ∨ u = j ∨ u = k)
    (hkodd : ¬ 2 ∣ m k) :
    ∃ u v : Fin 10, u ≠ v ∧ u ≠ i ∧ u ≠ j ∧ u ≠ k ∧
      v ≠ i ∧ v ≠ j ∧ v ≠ k ∧ 8 ∣ m u ∧ 8 ∣ m v := by
  obtain ⟨w, hw⟩ := omitIndex_surjective i j hij.symm
  let e : Fin 8 → Fin 10 := fun r => omitIndex i (omitIndex w r)
  have e_ne_i (r : Fin 8) : e r ≠ i := omitIndex_ne i _
  have e_ne_j (r : Fin 8) : e r ≠ j := by
    intro he
    apply omitIndex_ne w r
    apply omitIndex_injective i
    exact he.trans hw.symm
  have e_injective {r s : Fin 8} (he : e r = e s) : r = s := by
    apply omitIndex_injective w
    apply omitIndex_injective i
    exact he
  let a' : Fin 8 → Int := fun r => a (e r)
  let m' : Fin 8 → Nat := fun r => m (e r)
  have hm' : ∀ r, 0 < m' r := by intro r; exact hm _
  have hd' : DisjointClasses a' m' := by
    intro r s hrs
    exact hd (e r) (e s) (fun he => hrs (e_injective he))
  obtain ⟨r, s, hrs, hge⟩ := h8 a' m' hm' hd'
  have hne : e r ≠ e s := by
    intro he
    have := e_injective he
    omega
  have hlt := (bounds hm hd hn hne).2
  have hg8 : Nat.gcd (m (e r)) (m (e s)) = 8 := by
    dsimp [m'] at hge
    have hposs : Nat.gcd (m (e r)) (m (e s)) = 8 ∨
        Nat.gcd (m (e r)) (m (e s)) = 9 := by omega
    rcases hposs with h | h
    · exact h
    · have hr9 : 9 ∣ m (e r) := by
        rw [← h]; exact Nat.gcd_dvd_left _ _
      have hs9 : 9 ∣ m (e s) := by
        rw [← h]; exact Nat.gcd_dvd_right _ _
      have hrr := hatMost (e r) hr9
      have hss := hatMost (e s) hs9
      have hrne_i := e_ne_i r
      have hsne_i := e_ne_i s
      have hrne_j := e_ne_j r
      have hsne_j := e_ne_j s
      grind
  have hr8 : 8 ∣ m (e r) := by
    rw [← hg8]; exact Nat.gcd_dvd_left _ _
  have hs8 : 8 ∣ m (e s) := by
    rw [← hg8]; exact Nat.gcd_dvd_right _ _
  have hrne_k : e r ≠ k := by
    intro h
    apply hkodd
    exact Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hr8)
  have hsne_k : e s ≠ k := by
    intro h
    apply hkodd
    exact Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hs8)
  exact ⟨e r, e s, hne, e_ne_i r, e_ne_j r, hrne_k,
    e_ne_i s, e_ne_j s, hsne_k, hr8, hs8⟩

/-- The smaller statements and absence of a common factor 3 force three
distinct 9-anchors and two further 8-multiples. -/
theorem five_anchor_structure (h8 : Statement 8) (h9 : Statement 9)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (hthree : ∃ t : Fin 10, ¬ 3 ∣ m t) :
    ∃ x2 x5 x7 u v : Fin 10,
      x2 ≠ x5 ∧ x2 ≠ x7 ∧ x5 ≠ x7 ∧
      9 ∣ m x2 ∧ 9 ∣ m x5 ∧ 9 ∣ m x7 ∧
      2 ∣ m x2 ∧ 5 ∣ m x5 ∧ 7 ∣ m x7 ∧
      (∀ w : Fin 10, 9 ∣ m w → w = x2 ∨ w = x5 ∨ w = x7) ∧
      u ≠ v ∧ u ≠ x2 ∧ u ≠ x5 ∧ u ≠ x7 ∧
      v ≠ x2 ∧ v ≠ x5 ∧ v ≠ x7 ∧
      8 ∣ m u ∧ 8 ∣ m v := by
  obtain ⟨i, j, k, hij, hki, hkj, hi9, hj9, hk9, hatMost,
    hsup_i, hsup_j, hsup_k, htwo, hfiv, hsev⟩ :=
    nine_anchor_support h9 a m hm hd hn hthree
  have hpair (x y : Fin 10) (hxy : x ≠ y)
      (hx : 9 ∣ m x) (hy : 9 ∣ m y) : Nat.gcd (m x) (m y) = 9 := by
    have h := bounds hm hd hn hxy
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx hy)
    omega
  have noCommon (x y : Fin 10) (hxy : x ≠ y)
      (hx : 9 ∣ m x) (hy : 9 ∣ m y) (p : Nat)
      (hp : p = 2 ∨ p = 5 ∨ p = 7) : ¬(p ∣ m x ∧ p ∣ m y) := by
    intro h
    have hdvd : p ∣ 9 := by
      rw [← hpair x y hxy hx hy]
      exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  obtain ⟨x2, hx29, hx22, hx2which⟩ :
      ∃ x : Fin 10, 9 ∣ m x ∧ 2 ∣ m x ∧ (x = i ∨ x = j ∨ x = k) := by grind
  obtain ⟨x5, hx59, hx55, hx5which⟩ :
      ∃ x : Fin 10, 9 ∣ m x ∧ 5 ∣ m x ∧ (x = i ∨ x = j ∨ x = k) := by grind
  obtain ⟨x7, hx79, hx77, hx7which⟩ :
      ∃ x : Fin 10, 9 ∣ m x ∧ 7 ∣ m x ∧ (x = i ∨ x = j ∨ x = k) := by grind
  have hx25 : x2 ≠ x5 := by grind
  have hx27 : x2 ≠ x7 := by grind
  have hx57 : x5 ≠ x7 := by grind
  have hx5odd : ¬ 2 ∣ m x5 := by
    exact fun h => noCommon x2 x5 hx25 hx29 hx59 2 (Or.inl rfl) ⟨hx22, h⟩
  have hx7odd : ¬ 2 ∣ m x7 := by
    exact fun h => noCommon x2 x7 hx27 hx29 hx79 2 (Or.inl rfl) ⟨hx22, h⟩
  have atMostNamed (w : Fin 10) (hw9 : 9 ∣ m w) :
      w = x2 ∨ w = x5 ∨ w = x7 := by
    have hw := hatMost w hw9
    grind
  obtain ⟨u, v, huv, hu2, hu5, hu7, hv2, hv5, hv7, hu8, hv8⟩ :=
    two_eight_outside h8 a m hm hd hn x2 x5 x7 hx25 atMostNamed hx7odd
  exact ⟨x2, x5, x7, u, v, hx25, hx27, hx57,
    hx29, hx59, hx79, hx22, hx55, hx77, atMostNamed,
    huv, hu2, hu5, hu7, hv2, hv5, hv7, hu8, hv8⟩

private theorem shared_odd {a : Fin 10 → Int} {m : Fin 10 → Nat}
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (x y : Fin 10) (hxy : x ≠ y) (hy : ¬ 2 ∣ m y) :
    (3 ∣ m x ∧ 3 ∣ m y) ∨
    (5 ∣ m x ∧ 5 ∣ m y) ∨
    (7 ∣ m x ∧ 7 ∣ m y) := by
  have hb := bounds hm hd hn hxy
  have hl := Nat.gcd_dvd_left (m x) (m y)
  have hr := Nat.gcd_dvd_right (m x) (m y)
  have hne : ¬ 2 ∣ Nat.gcd (m x) (m y) := by
    intro he
    exact hy (Nat.dvd_trans he hr)
  have hmod : Nat.gcd (m x) (m y) % 2 ≠ 0 := by
    intro he
    exact hne (Nat.dvd_of_mod_eq_zero he)
  have hx : Nat.gcd (m x) (m y) = 3 ∨ Nat.gcd (m x) (m y) = 5 ∨
      Nat.gcd (m x) (m y) = 7 ∨ Nat.gcd (m x) (m y) = 9 := by omega
  rcases hx with hx | hx | hx | hx
  · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
  · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
  · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
  · exact Or.inl ⟨Nat.dvd_trans (by decide : 3 ∣ 9) (by simpa [hx] using hl),
      Nat.dvd_trans (by decide : 3 ∣ 9) (by simpa [hx] using hr)⟩

/-- The two 8-multiples split: one contains 3, the other contains both 5 and 7. -/
theorem forced_prime_pattern (h8 : Statement 8) (h9 : Statement 9)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (hthree : ∃ t : Fin 10, ¬ 3 ∣ m t) :
    ∃ x2 x5 x7 u v : Fin 10,
      x2 ≠ x5 ∧ x2 ≠ x7 ∧ x5 ≠ x7 ∧
      9 ∣ m x2 ∧ 9 ∣ m x5 ∧ 9 ∣ m x7 ∧
      2 ∣ m x2 ∧ 5 ∣ m x5 ∧ 7 ∣ m x7 ∧
      (∀ w : Fin 10, 9 ∣ m w → w = x2 ∨ w = x5 ∨ w = x7) ∧
      u ≠ v ∧ u ≠ x2 ∧ u ≠ x5 ∧ u ≠ x7 ∧
      v ≠ x2 ∧ v ≠ x5 ∧ v ≠ x7 ∧
      8 ∣ m u ∧ 8 ∣ m v ∧
      3 ∣ m u ∧ ¬ 3 ∣ m v ∧ 5 ∣ m v ∧ 7 ∣ m v ∧
      ¬ 5 ∣ m u ∧ ¬ 7 ∣ m u := by
  obtain ⟨x2, x5, x7, u, v, hx25, hx27, hx57,
    hx29, hx59, hx79, hx22, hx55, hx77, hatMost,
    huv, hu2, hu5, hu7, hv2, hv5, hv7, hu8, hv8⟩ :=
    five_anchor_structure h8 h9 a m hm hd hn hthree
  have hn25 (p : Nat) (hp : p = 2 ∨ p = 5 ∨ p = 7) :
      ¬(p ∣ m x2 ∧ p ∣ m x5) := by
    intro h
    have hg : Nat.gcd (m x2) (m x5) = 9 := by
      have hb := bounds hm hd hn hx25
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx29 hx59)
      omega
    have hdvd : p ∣ 9 := by
      rw [← hg]; exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  have hn27 (p : Nat) (hp : p = 2 ∨ p = 5 ∨ p = 7) :
      ¬(p ∣ m x2 ∧ p ∣ m x7) := by
    intro h
    have hg : Nat.gcd (m x2) (m x7) = 9 := by
      have hb := bounds hm hd hn hx27
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx29 hx79)
      omega
    have hdvd : p ∣ 9 := by
      rw [← hg]; exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  have hn57 (p : Nat) (hp : p = 2 ∨ p = 5 ∨ p = 7) :
      ¬(p ∣ m x5 ∧ p ∣ m x7) := by
    intro h
    have hg : Nat.gcd (m x5) (m x7) = 9 := by
      have hb := bounds hm hd hn hx57
      have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx59 hx79)
      omega
    have hdvd : p ∣ 9 := by
      rw [← hg]; exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  have hx5odd : ¬ 2 ∣ m x5 := by
    exact fun h => hn25 2 (Or.inl rfl) ⟨hx22, h⟩
  have hx7odd : ¬ 2 ∣ m x7 := by
    exact fun h => hn27 2 (Or.inl rfl) ⟨hx22, h⟩
  have hx5not7 : ¬ 7 ∣ m x5 := by
    exact fun h => hn57 7 (Or.inr (Or.inr rfl)) ⟨h, hx77⟩
  have hx7not5 : ¬ 5 ∣ m x7 := by
    exact fun h => hn57 5 (Or.inr (Or.inl rfl)) ⟨hx55, h⟩
  have hu5shared := shared_odd hm hd hn u x5 hu5 hx5odd
  have hu7shared := shared_odd hm hd hn u x7 hu7 hx7odd
  have hv5shared := shared_odd hm hd hn v x5 hv5 hx5odd
  have hv7shared := shared_odd hm hd hn v x7 hv7 hx7odd
  have hguv : Nat.gcd (m u) (m v) = 8 := by
    have hb := bounds hm hd hn huv
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hu8 hv8)
    omega
  have noCommon8 (p : Nat) (hp : p = 3 ∨ p = 5 ∨ p = 7) :
      ¬(p ∣ m u ∧ p ∣ m v) := by
    intro h
    have hdvd : p ∣ 8 := by
      rw [← hguv]; exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 3 ∣ 8) hdvd
    · exact (by decide : ¬ 5 ∣ 8) hdvd
    · exact (by decide : ¬ 7 ∣ 8) hdvd
  have hpattern :
      (3 ∣ m u ∧ ¬ 3 ∣ m v ∧ 5 ∣ m v ∧ 7 ∣ m v ∧
        ¬ 5 ∣ m u ∧ ¬ 7 ∣ m u) ∨
      (3 ∣ m v ∧ ¬ 3 ∣ m u ∧ 5 ∣ m u ∧ 7 ∣ m u ∧
        ¬ 5 ∣ m v ∧ ¬ 7 ∣ m v) := by
    have hn3 := noCommon8 3 (Or.inl rfl)
    have hn5 := noCommon8 5 (Or.inr (Or.inl rfl))
    have hn7 := noCommon8 7 (Or.inr (Or.inr rfl))
    grind
  rcases hpattern with hp | hp
  · exact ⟨x2, x5, x7, u, v, hx25, hx27, hx57,
      hx29, hx59, hx79, hx22, hx55, hx77, hatMost,
      huv, hu2, hu5, hu7, hv2, hv5, hv7, hu8, hv8,
      hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  · exact ⟨x2, x5, x7, v, u, hx25, hx27, hx57,
      hx29, hx59, hx79, hx22, hx55, hx77, hatMost,
      huv.symm, hv2, hv5, hv7, hu2, hu5, hu7, hv8, hu8,
      hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

private theorem large_pair {a : Fin 10 → Int} {m : Fin 10 → Nat}
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (x y : Fin 10) (hxy : x ≠ y) (p q : Nat)
    (hpq : Nat.Coprime p q) (hlarge : 10 ≤ p * q)
    (hpx : p ∣ m x) (hpy : p ∣ m y)
    (hqx : q ∣ m x) (hqy : q ∣ m y) : False := by
  have hp := Nat.dvd_gcd hpx hpy
  have hq := Nat.dvd_gcd hqx hqy
  have hpqg := hpq.mul_dvd_of_dvd_of_dvd hp hq
  have hgpos : 0 < Nat.gcd (m x) (m y) :=
    Nat.gcd_pos_of_pos_left (m y) (hm x)
  have hge := Nat.le_of_dvd hgpos hpqg
  have hlt := (bounds hm hd hn hxy).2
  omega

private theorem div8_cases (g : Nat) (hp : 0 < g) (hd : g ∣ 8) :
    g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 8 := by
  have hl := Nat.le_of_dvd (by decide : 0 < 8) hd
  have hc : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨
      g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 := by omega
  rcases hc with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact False.elim ((by decide : ¬ 3 ∣ 8) (h ▸ hd))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact False.elim ((by decide : ¬ 5 ∣ 8) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 6 ∣ 8) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 7 ∣ 8) (h ▸ hd))
  · exact Or.inr (Or.inr (Or.inr h))

private theorem div9_cases (g : Nat) (hp : 0 < g) (hd : g ∣ 9) :
    g = 1 ∨ g = 3 ∨ g = 9 := by
  have hl := Nat.le_of_dvd (by decide : 0 < 9) hd
  have hc : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨
      g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact False.elim ((by decide : ¬ 2 ∣ 9) (h ▸ hd))
  · exact Or.inr (Or.inl h)
  · exact False.elim ((by decide : ¬ 4 ∣ 9) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 5 ∣ 9) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 6 ∣ 9) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 7 ∣ 9) (h ▸ hd))
  · exact False.elim ((by decide : ¬ 8 ∣ 9) (h ▸ hd))
  · exact Or.inr (Or.inr h)

private theorem gcd72_small (n : Nat)
    (h8 : ¬ 8 ∣ n) (h9 : ¬ 9 ∣ n) (h12 : ¬ 12 ∣ n) :
    Nat.gcd n 72 ≤ 6 := by
  have hc : Nat.Coprime 8 9 := by decide
  have hprod : Nat.gcd n 72 = Nat.gcd n 8 * Nat.gcd n 9 := by
    simpa using hc.gcd_mul n
  have h8pos : 0 < Nat.gcd n 8 := Nat.gcd_pos_of_pos_right n (by decide)
  have h9pos : 0 < Nat.gcd n 9 := Nat.gcd_pos_of_pos_right n (by decide)
  have c8 := div8_cases _ h8pos (Nat.gcd_dvd_right n 8)
  have c9 := div9_cases _ h9pos (Nat.gcd_dvd_right n 9)
  have hn8 : Nat.gcd n 8 ≠ 8 := by
    intro h; exact h8 (by rw [←h]; exact Nat.gcd_dvd_left _ _)
  have hn9 : Nat.gcd n 9 ≠ 9 := by
    intro h; exact h9 (by rw [←h]; exact Nat.gcd_dvd_left _ _)
  have hn12 : ¬(Nat.gcd n 8 = 4 ∧ Nat.gcd n 9 = 3) := by
    intro h
    have h4 : 4 ∣ n := by rw [←h.1]; exact Nat.gcd_dvd_left _ _
    have h3 : 3 ∣ n := by rw [←h.2]; exact Nat.gcd_dvd_left _ _
    exact h12 ((by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4 h3)
  rcases c8 with h | h | h | h <;> rcases c9 with h' | h' | h' <;>
    simp [hprod, h, h'] at * <;> omega

private theorem gcd8_two (n : Nat) (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    Nat.gcd n 8 = 2 := by
  have hpos : 0 < Nat.gcd n 8 := Nat.gcd_pos_of_pos_right n (by decide)
  have hc := div8_cases _ hpos (Nat.gcd_dvd_right n 8)
  have h2g : 2 ∣ Nat.gcd n 8 :=
    Nat.dvd_gcd h2 (by decide : 2 ∣ 8)
  rcases hc with h | h | h | h
  · exact False.elim ((by decide : ¬ 2 ∣ 1) (h ▸ h2g))
  · exact h
  · exact False.elim (h4 (by rw [← h]; exact Nat.gcd_dvd_left _ _))
  · exact False.elim (h4 (Nat.dvd_trans (by decide : 4 ∣ 8)
      (by rw [← h]; exact Nat.gcd_dvd_left _ _)))

private theorem gcd8_one (n : Nat) (h2 : ¬ 2 ∣ n) : Nat.gcd n 8 = 1 := by
  have hpos : 0 < Nat.gcd n 8 := Nat.gcd_pos_of_pos_right n (by decide)
  have hc := div8_cases _ hpos (Nat.gcd_dvd_right n 8)
  rcases hc with h | h | h | h
  · exact h
  · exact False.elim (h2 (by rw [← h]; exact Nat.gcd_dvd_left _ _))
  · exact False.elim (h2 (Nat.dvd_trans (by decide : 2 ∣ 4)
      (by rw [← h]; exact Nat.gcd_dvd_left _ _)))
  · exact False.elim (h2 (Nat.dvd_trans (by decide : 2 ∣ 8)
      (by rw [← h]; exact Nat.gcd_dvd_left _ _)))

private theorem gcd9_three (n : Nat) (h3 : 3 ∣ n) (h9 : ¬ 9 ∣ n) :
    Nat.gcd n 9 = 3 := by
  have hpos : 0 < Nat.gcd n 9 := Nat.gcd_pos_of_pos_right n (by decide)
  have hc := div9_cases _ hpos (Nat.gcd_dvd_right n 9)
  have h3g : 3 ∣ Nat.gcd n 9 :=
    Nat.dvd_gcd h3 (by decide : 3 ∣ 9)
  rcases hc with h | h | h
  · exact False.elim ((by decide : ¬ 3 ∣ 1) (h ▸ h3g))
  · exact h
  · exact False.elim (h9 (by rw [← h]; exact Nat.gcd_dvd_left _ _))

private theorem gcd72_special (x2 x5 x7 u : Nat)
    (hx29 : 9 ∣ x2) (hx22 : 2 ∣ x2) (hx24 : ¬ 4 ∣ x2)
    (hx59 : 9 ∣ x5) (hx52 : ¬ 2 ∣ x5)
    (hx79 : 9 ∣ x7) (hx72 : ¬ 2 ∣ x7)
    (hu8 : 8 ∣ u) (hu3 : 3 ∣ u) (hu9 : ¬ 9 ∣ u) :
    Nat.gcd x2 72 = 18 ∧ Nat.gcd x5 72 = 9 ∧
      Nat.gcd x7 72 = 9 ∧ Nat.gcd u 72 = 24 := by
  have hc : Nat.Coprime 8 9 := by decide
  have hprod (n : Nat) : Nat.gcd n 72 = Nat.gcd n 8 * Nat.gcd n 9 := by
    simpa using hc.gcd_mul n
  constructor
  · rw [hprod, gcd8_two x2 hx22 hx24, Nat.gcd_eq_right hx29]
  constructor
  · rw [hprod, gcd8_one x5 hx52, Nat.gcd_eq_right hx59]
  constructor
  · rw [hprod, gcd8_one x7 hx72, Nat.gcd_eq_right hx79]
  · rw [hprod, Nat.gcd_eq_right hu8, gcd9_three u hu3 hu9]

private theorem bounded_non57_div72 (g : Nat)
    (hlo : 2 ≤ g) (hhi : g < 10) (h5 : g ≠ 5) (h7 : g ≠ 7) : g ∣ 72 := by
  have hc : g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 6 ∨ g = 8 ∨ g = 9 := by omega
  rcases hc with h | h | h | h | h | h <;> simp [h]

private theorem other_small {a : Fin 10 → Int} {m : Fin 10 → Nat}
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (x2 x5 x7 u v w : Fin 10)
    (hx59 : 9 ∣ m x5) (hx55 : 5 ∣ m x5)
    (hx79 : 9 ∣ m x7) (hx77 : 7 ∣ m x7)
    (hx5odd : ¬ 2 ∣ m x5) (hx5not7 : ¬ 7 ∣ m x5)
    (hx2not5 : ¬ 5 ∣ m x2) (hx2not7 : ¬ 7 ∣ m x2)
    (hu8 : 8 ∣ m u) (hu3 : 3 ∣ m u)
    (hv8 : 8 ∣ m v) (hv5 : 5 ∣ m v) (hv7 : 7 ∣ m v)
    (hatMost9 : ∀ z : Fin 10, 9 ∣ m z → z = x2 ∨ z = x5 ∨ z = x7)
    (hw2 : w ≠ x2) (hw5 : w ≠ x5) (hw7 : w ≠ x7)
    (hwu : w ≠ u) (hwv : w ≠ v) :
    ¬ 5 ∣ m w ∧ ¬ 7 ∣ m w ∧ Nat.gcd (m w) 72 ≤ 6 := by
  have hw9 : ¬ 9 ∣ m w := by
    intro h
    rcases hatMost9 w h with h | h | h
    · exact hw2 h
    · exact hw5 h
    · exact hw7 h
  have hw8 : ¬ 8 ∣ m w := by
    intro h
    have hn3 : ¬ 3 ∣ m w := by
      intro h3
      exact large_pair hm hd hn w u hwu 8 3 (by decide) (by decide)
        h hu8 h3 hu3
    have hn5 : ¬ 5 ∣ m w := by
      intro h5
      exact large_pair hm hd hn w v hwv 8 5 (by decide) (by decide)
        h hv8 h5 hv5
    rcases shared_odd hm hd hn w x5 hw5 hx5odd with hs | hs | hs
    · exact hn3 hs.1
    · exact hn5 hs.1
    · exact hx5not7 hs.2
  have hw23 : 2 ∣ m w ∨ 3 ∣ m w := by
    have hb := bounds hm hd hn hw2
    have hl := Nat.gcd_dvd_left (m w) (m x2)
    have hr := Nat.gcd_dvd_right (m w) (m x2)
    have hnot5 : Nat.gcd (m w) (m x2) ≠ 5 := by
      intro h
      apply hx2not5
      rw [← h]
      exact hr
    have hnot7 : Nat.gcd (m w) (m x2) ≠ 7 := by
      intro h
      apply hx2not7
      rw [← h]
      exact hr
    have hp : Nat.gcd (m w) (m x2) = 2 ∨
        Nat.gcd (m w) (m x2) = 3 ∨
        Nat.gcd (m w) (m x2) = 4 ∨
        Nat.gcd (m w) (m x2) = 6 ∨
        Nat.gcd (m w) (m x2) = 8 ∨
        Nat.gcd (m w) (m x2) = 9 := by omega
    rcases hp with h | h | h | h | h | h
    · exact Or.inl (by simpa [h] using hl)
    · exact Or.inr (by simpa [h] using hl)
    · exact Or.inl (Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [h] using hl))
    · exact Or.inl (Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [h] using hl))
    · exact Or.inl (Nat.dvd_trans (by decide : 2 ∣ 8) (by simpa [h] using hl))
    · exact Or.inr (Nat.dvd_trans (by decide : 3 ∣ 9) (by simpa [h] using hl))
  have hw5not : ¬ 5 ∣ m w := by
    intro h5
    rcases hw23 with h2 | h3
    · exact large_pair hm hd hn w v hwv 2 5 (by decide) (by decide)
        h2 (Nat.dvd_trans (by decide : 2 ∣ 8) hv8) h5 hv5
    · exact large_pair hm hd hn w x5 hw5 3 5 (by decide) (by decide)
        h3 (Nat.dvd_trans (by decide : 3 ∣ 9) hx59) h5 hx55
  have hw7not : ¬ 7 ∣ m w := by
    intro h7
    rcases hw23 with h2 | h3
    · exact large_pair hm hd hn w v hwv 2 7 (by decide) (by decide)
        h2 (Nat.dvd_trans (by decide : 2 ∣ 8) hv8) h7 hv7
    · exact large_pair hm hd hn w x7 hw7 3 7 (by decide) (by decide)
        h3 (Nat.dvd_trans (by decide : 3 ∣ 9) hx79) h7 hx77
  have hw12 : ¬ 12 ∣ m w := by
    intro h12
    exact large_pair hm hd hn w u hwu 4 3 (by decide) (by decide)
      (Nat.dvd_trans (by decide : 4 ∣ 12) h12)
      (Nat.dvd_trans (by decide : 4 ∣ 8) hu8)
      (Nat.dvd_trans (by decide : 3 ∣ 12) h12) hu3
  exact ⟨hw5not, hw7not, gcd72_small (m w) hw8 hw9 hw12⟩

/-- All gcd information needed for the final nine-class density count;
this concerns compressed gcds, not exact original moduli. -/
theorem gcd72_profile (h8 : Statement 8) (h9 : Statement 9)
    (a : Fin 10 → Int) (m : Fin 10 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j))
    (hthree : ∃ t : Fin 10, ¬ 3 ∣ m t) :
    ∃ x2 x5 x7 u v : Fin 10,
      x2 ≠ x5 ∧ x2 ≠ x7 ∧ x2 ≠ u ∧ x2 ≠ v ∧
      x5 ≠ x7 ∧ x5 ≠ u ∧ x5 ≠ v ∧
      x7 ≠ u ∧ x7 ≠ v ∧ u ≠ v ∧
      Nat.gcd (m x2) 72 = 18 ∧ Nat.gcd (m x5) 72 = 9 ∧
      Nat.gcd (m x7) 72 = 9 ∧ Nat.gcd (m u) 72 = 24 ∧
      (∀ w : Fin 10, w ≠ x2 → w ≠ x5 → w ≠ x7 → w ≠ u → w ≠ v →
        Nat.gcd (m w) 72 ≤ 6) ∧
      (∀ x y : Fin 10, x ≠ y → x ≠ v → y ≠ v →
        Nat.gcd (m x) (m y) ∣ 72) := by
  obtain ⟨x2, x5, x7, u, v, hx25, hx27, hx57,
    hx29, hx59, hx79, hx22, hx55, hx77, hatMost,
    huv, hu2, hu5, hu7, hv2, hv5, hv7, hu8, hv8,
    hu3, hv3not, hv5p, hv7p, hu5not, hu7not⟩ :=
    forced_prime_pattern h8 h9 a m hm hd hn hthree
  have noCommon9 (x y : Fin 10) (hxy : x ≠ y)
      (hx : 9 ∣ m x) (hy : 9 ∣ m y) (p : Nat)
      (hp : p = 2 ∨ p = 5 ∨ p = 7) : ¬(p ∣ m x ∧ p ∣ m y) := by
    intro h
    have hb := bounds hm hd hn hxy
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx hy)
    have hg : Nat.gcd (m x) (m y) = 9 := by omega
    have hdvd : p ∣ 9 := by
      rw [← hg]; exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 9) hdvd
    · exact (by decide : ¬ 5 ∣ 9) hdvd
    · exact (by decide : ¬ 7 ∣ 9) hdvd
  have hx2not5 : ¬ 5 ∣ m x2 := by
    exact fun h => noCommon9 x2 x5 hx25 hx29 hx59 5 (Or.inr (Or.inl rfl)) ⟨h, hx55⟩
  have hx2not7 : ¬ 7 ∣ m x2 := by
    exact fun h => noCommon9 x2 x7 hx27 hx29 hx79 7 (Or.inr (Or.inr rfl)) ⟨h, hx77⟩
  have hx5odd : ¬ 2 ∣ m x5 := by
    exact fun h => noCommon9 x2 x5 hx25 hx29 hx59 2 (Or.inl rfl) ⟨hx22, h⟩
  have hx7odd : ¬ 2 ∣ m x7 := by
    exact fun h => noCommon9 x2 x7 hx27 hx29 hx79 2 (Or.inl rfl) ⟨hx22, h⟩
  have hx5not7 : ¬ 7 ∣ m x5 := by
    exact fun h => noCommon9 x5 x7 hx57 hx59 hx79 7 (Or.inr (Or.inr rfl)) ⟨h, hx77⟩
  have hx7not5 : ¬ 5 ∣ m x7 := by
    exact fun h => noCommon9 x5 x7 hx57 hx59 hx79 5 (Or.inr (Or.inl rfl)) ⟨hx55, h⟩
  have hx24not : ¬ 4 ∣ m x2 := by
    intro h4
    exact large_pair hm hd hn x2 u hu2.symm 4 3 (by decide) (by decide)
      h4 (Nat.dvd_trans (by decide : 4 ∣ 8) hu8)
      (Nat.dvd_trans (by decide : 3 ∣ 9) hx29) hu3
  have hu9not : ¬ 9 ∣ m u := by
    intro h
    rcases hatMost u h with h | h | h
    · exact hu2 h
    · exact hu5 h
    · exact hu7 h
  have hs := gcd72_special (m x2) (m x5) (m x7) (m u)
    hx29 hx22 hx24not hx59 hx5odd hx79 hx7odd hu8 hu3 hu9not
  have hother (w : Fin 10) (hw2 : w ≠ x2) (hw5 : w ≠ x5)
      (hw7 : w ≠ x7) (hwu : w ≠ u) (hwv : w ≠ v) :
      ¬ 5 ∣ m w ∧ ¬ 7 ∣ m w ∧ Nat.gcd (m w) 72 ≤ 6 :=
    other_small hm hd hn x2 x5 x7 u v w hx59 hx55 hx79 hx77
      hx5odd hx5not7 hx2not5 hx2not7 hu8 hu3 hv8 hv5p hv7p
      hatMost hw2 hw5 hw7 hwu hwv
  have five_only (w : Fin 10) (hwv : w ≠ v) (hw5 : 5 ∣ m w) : w = x5 := by
    by_cases h : w = x2
    · exact False.elim (hx2not5 (h ▸ hw5))
    by_cases h' : w = x5
    · exact h'
    by_cases h'' : w = x7
    · exact False.elim (hx7not5 (h'' ▸ hw5))
    by_cases h''' : w = u
    · exact False.elim (hu5not (h''' ▸ hw5))
    exact False.elim ((hother w h h' h'' h''' hwv).1 hw5)
  have seven_only (w : Fin 10) (hwv : w ≠ v) (hw7 : 7 ∣ m w) : w = x7 := by
    by_cases h : w = x2
    · exact False.elim (hx2not7 (h ▸ hw7))
    by_cases h' : w = x5
    · exact False.elim (hx5not7 (h' ▸ hw7))
    by_cases h'' : w = x7
    · exact h''
    by_cases h''' : w = u
    · exact False.elim (hu7not (h''' ▸ hw7))
    exact False.elim ((hother w h h' h'' h''' hwv).2.1 hw7)
  have hpair (x y : Fin 10) (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v) :
      Nat.gcd (m x) (m y) ∣ 72 := by
    have hb := bounds hm hd hn hxy
    have hnot5 : Nat.gcd (m x) (m y) ≠ 5 := by
      intro hg
      have h5x : 5 ∣ m x := by rw [← hg]; exact Nat.gcd_dvd_left _ _
      have h5y : 5 ∣ m y := by rw [← hg]; exact Nat.gcd_dvd_right _ _
      exact hxy ((five_only x hxv h5x).trans (five_only y hyv h5y).symm)
    have hnot7 : Nat.gcd (m x) (m y) ≠ 7 := by
      intro hg
      have h7x : 7 ∣ m x := by rw [← hg]; exact Nat.gcd_dvd_left _ _
      have h7y : 7 ∣ m y := by rw [← hg]; exact Nat.gcd_dvd_right _ _
      exact hxy ((seven_only x hxv h7x).trans (seven_only y hyv h7y).symm)
    exact bounded_non57_div72 _ hb.1 hb.2 hnot5 hnot7
  exact ⟨x2, x5, x7, u, v, hx25, hx27, hu2.symm, hv2.symm,
    hx57, hu5.symm, hv5.symm, hu7.symm, hv7.symm, huv,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
    fun w hw2 hw5 hw7 hwu hwv => (hother w hw2 hw5 hw7 hwu hwv).2.2,
    hpair⟩

private theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

private theorem sum_pointwise {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : f x ≤ g x := h x (by simp)
    have ht : ∀ y ∈ xs, f y ≤ g y := by
      intro y hy; exact h y (by simp [hy])
    have hh := ih ht
    simpa using Nat.add_le_add hx hh

private theorem indicator_sum (i : Fin 9) (n : Nat) :
    ((List.finRange 9).map (fun r => if r = i then n else 0)).sum = n := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
    omega
  rcases hi with h | h | h | h | h | h | h | h | h <;> subst i <;>
    simp [List.finRange_succ]

private theorem weighted (b : Fin 9 → Nat) (i j k l : Fin 9)
    (hi : 4 ≤ b i) (hj : 8 ≤ b j) (hk : 8 ≤ b k) (hl : 3 ≤ b l)
    (hrest : ∀ r : Fin 9, r ≠ i → r ≠ j → r ≠ k → r ≠ l → 12 ≤ b r) :
    83 ≤ ((List.finRange 9).map b).sum := by
  let p : Fin 9 → Nat := fun r =>
    (if r = i then 8 else 0) + (if r = j then 4 else 0) +
    (if r = k then 4 else 0) + (if r = l then 9 else 0)
  have hp (r : Fin 9) : 12 ≤ b r + p r := by
    by_cases hri : r = i
    · have hb : 4 ≤ b r := by simpa [hri] using hi
      have hp8 : 8 ≤ p r := by simp [p, hri]; omega
      omega
    by_cases hrj : r = j
    · have hb : 8 ≤ b r := by simpa [hrj] using hj
      have hp4 : 4 ≤ p r := by simp [p, hrj]; omega
      omega
    by_cases hrk : r = k
    · have hb : 8 ≤ b r := by simpa [hrk] using hk
      have hp4 : 4 ≤ p r := by simp [p, hrk]; omega
      omega
    by_cases hrl : r = l
    · have hb : 3 ≤ b r := by simpa [hrl] using hl
      have hp9 : 9 ≤ p r := by simp [p, hrl]
      omega
    have hb := hrest r hri hrj hrk hrl
    simp [p, hri, hrj, hrk, hrl]
    omega
  have hpsum : ((List.finRange 9).map p).sum = 25 := by
    simp [p, sum_map_add, indicator_sum]
  have hconst : ((List.finRange 9).map (fun _ => 12)).sum = 108 := by
    simp [List.finRange_succ]
  have hs := sum_pointwise (List.finRange 9) (fun _ => 12)
    (fun r => b r + p r) (fun r _ => hp r)
  rw [hconst, sum_map_add, hpsum] at hs
  omega

/-- Statement 10 follows from Statements 8 and 9 and the absence of a
common factor 3 in any hypothetical ten-class counterexample. -/
theorem step_of_no_common_three (h8 : Statement 8) (h9 : Statement 9)
    (hthree : ∀ (a : Fin 10 → Int) (m : Fin 10 → Nat),
      (∀ i, 0 < m i) → DisjointClasses a m →
      (¬ ∃ i j : Fin 10, i < j ∧ 10 ≤ Nat.gcd (m i) (m j)) →
      ∃ t : Fin 10, ¬ 3 ∣ m t) : Statement 10 := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  obtain ⟨x2, x5, x7, u, v, hx25, hx27, hx2u, hx2v,
    hx57, hx5u, hx5v, hx7u, hx7v, huv,
    hg2, hg5, hg7, hgu, hsmall, hpair⟩ :=
    gcd72_profile h8 h9 a m hm hd hn (hthree a m hm hd hn)
  let e : Fin 9 → Fin 10 := omitIndex v
  have heinj : Function.Injective e := by
    intro r s hrs
    exact omitIndex_injective v hrs
  have hene (r : Fin 9) : e r ≠ v := omitIndex_ne v r
  obtain ⟨r2, hr2⟩ := omitIndex_surjective v x2 hx2v
  obtain ⟨r5, hr5⟩ := omitIndex_surjective v x5 hx5v
  obtain ⟨r7, hr7⟩ := omitIndex_surjective v x7 hx7v
  obtain ⟨ru, hru⟩ := omitIndex_surjective v u huv
  let aa : Fin 9 → Int := a ∘ e
  let mm : Fin 9 → Nat := m ∘ e
  have hdis : DisjointClasses aa mm := by
    intro r s hrs
    exact hd (e r) (e s) (fun h => hrs (heinj h))
  have hpairs : ∀ r s : Fin 9, r ≠ s → Nat.gcd (mm r) (mm s) ∣ 72 := by
    intro r s hrs
    exact hpair (e r) (e s) (fun h => hrs (heinj h)) (hene r) (hene s)
  have hden := density_bound_compressed aa mm (by decide : 0 < 72) hdis hpairs
  let b : Fin 9 → Nat := fun r => 72 / Nat.gcd (m (e r)) 72
  have hb2 : 4 ≤ b r2 := by change 4 ≤ 72 / Nat.gcd (m (omitIndex v r2)) 72; rw [hr2, hg2]; decide
  have hb5 : 8 ≤ b r5 := by change 8 ≤ 72 / Nat.gcd (m (omitIndex v r5)) 72; rw [hr5, hg5]; decide
  have hb7 : 8 ≤ b r7 := by change 8 ≤ 72 / Nat.gcd (m (omitIndex v r7)) 72; rw [hr7, hg7]; decide
  have hbu : 3 ≤ b ru := by change 3 ≤ 72 / Nat.gcd (m (omitIndex v ru)) 72; rw [hru, hgu]; decide
  have hbrest (r : Fin 9) (hr2' : r ≠ r2) (hr5' : r ≠ r5)
      (hr7' : r ≠ r7) (hru' : r ≠ ru) : 12 ≤ b r := by
    have he2 : e r ≠ x2 := by
      intro h; exact hr2' (heinj (h.trans hr2.symm))
    have he5 : e r ≠ x5 := by
      intro h; exact hr5' (heinj (h.trans hr5.symm))
    have he7 : e r ≠ x7 := by
      intro h; exact hr7' (heinj (h.trans hr7.symm))
    have heu : e r ≠ u := by
      intro h; exact hru' (heinj (h.trans hru.symm))
    have hle := hsmall (e r) he2 he5 he7 heu (hene r)
    have hpos : 0 < Nat.gcd (m (e r)) 72 :=
      Nat.gcd_pos_of_pos_right _ (by decide)
    dsimp [b]
    apply (Nat.le_div_iff_mul_le hpos).2
    omega
  have hlo := weighted b r2 r5 r7 ru hb2 hb5 hb7 hbu hbrest
  change ((List.finRange 9).map b).sum ≤ 72 at hden
  omega

/-- The ten-class statement. All smaller cases and the no-common-divisor
obstruction are supplied by the previously certified range. -/
theorem solution : Statement 10 := by
  apply step_of_no_common_three
    (ThroughNine.solution 8 (by decide) (by decide))
    ThroughNine.nine
  intro a m hm hd hn
  exact no_common_divisor_of_smaller_statements (k := 10) (p := 3)
    (by decide) (by decide)
    (by intro t ht hlt; exact ThroughNine.solution t ht (by omega))
    a m hm hd (by intro i j hij; exact (bounds hm hd hn hij).2)


#print axioms step_of_no_common_three
#print axioms solution

end ProofPursuit.P4.Ten
