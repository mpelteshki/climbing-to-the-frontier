import ProofPursuit.P4.Basic

namespace ProofPursuit.P4.Eight

set_option maxHeartbeats 12000000

private def omitIndex (t : Fin 8) (s : Fin 7) : Fin 8 :=
  ⟨if s.val < t.val then s.val else s.val + 1, by
    by_cases h : s.val < t.val <;> simp [h] <;> omega⟩

private theorem omitIndex_ne (t : Fin 8) (s : Fin 7) : omitIndex t s ≠ t := by
  intro h
  have hv := congrArg Fin.val h
  simp only [omitIndex] at hv
  by_cases hs : s.val < t.val <;> simp [hs] at hv <;> omega

private theorem omitIndex_injective (t : Fin 8) {s u : Fin 7}
    (h : omitIndex t s = omitIndex t u) : s = u := by
  have hv := congrArg Fin.val h
  simp only [omitIndex] at hv
  by_cases hs : s.val < t.val <;> by_cases hu : u.val < t.val <;>
    simp [hs, hu] at hv <;> apply Fin.ext <;> omega

private theorem omitIndex_surjective (t i : Fin 8) (hit : i ≠ t) :
    ∃ s : Fin 7, omitIndex t s = i := by
  have hv : i.val ≠ t.val := by intro h; exact hit (Fin.ext h)
  by_cases h : i.val < t.val
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [omitIndex, h]
  · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [omitIndex, show ¬ i.val - 1 < t.val by omega]
    omega

def target : Prop := Statement 8

theorem step (h7 : Statement 7) : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hb {i j : Fin 8} (hij : i ≠ j) := bounds hm hd hn hij
  have sevenPair (t : Fin 8) :
      ∃ i j : Fin 8, i ≠ j ∧ i ≠ t ∧ j ≠ t ∧ Nat.gcd (m i) (m j) = 7 := by
    let a' : Fin 7 → Int := fun s => a (omitIndex t s)
    let m' : Fin 7 → Nat := fun s => m (omitIndex t s)
    have hm' : ∀ s, 0 < m' s := by intro s; exact hm _
    have hd' : DisjointClasses a' m' := by
      intro s u hsu
      exact hd (omitIndex t s) (omitIndex t u)
        (fun h => hsu (omitIndex_injective t h))
    obtain ⟨s, u, hsu, hge⟩ := h7 a' m' hm' hd'
    have hne : omitIndex t s ≠ omitIndex t u := by
      intro h
      have := omitIndex_injective t h
      omega
    refine ⟨omitIndex t s, omitIndex t u, hne, omitIndex_ne t s,
      omitIndex_ne t u, ?_⟩
    have hlt := (hb hne).2
    dsimp [m'] at hge
    omega
  have gcdSeven (x y : Fin 8) (hxy : x ≠ y)
      (hx : 7 ∣ m x) (hy : 7 ∣ m y) : Nat.gcd (m x) (m y) = 7 := by
    have h := hb hxy
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx hy)
    omega
  have noAllSeven : ¬ ∀ x : Fin 8, 7 ∣ m x := by
    intro hall
    have hres (x y : Fin 8) (hxy : x ≠ y) : a x % 7 ≠ a y % 7 :=
      residues_ne hd hxy (gcdSeven x y hxy (hall x) (hall y))
    let l : List Int := List.ofFn (fun x : Fin 8 => a x % 7)
    have hnodup : l.Nodup := by
      rw [List.nodup_iff_eq_of_getElem_eq]
      intro x y hx hy heq
      have hx8 : x < 8 := by simpa [l] using hx
      have hy8 : y < 8 := by simpa [l] using hy
      apply Classical.byContradiction
      intro hxy
      have hfi : (⟨x, hx8⟩ : Fin 8) ≠ ⟨y, hy8⟩ := by
        intro h
        apply hxy
        exact congrArg Fin.val h
      have hne := hres ⟨x, hx8⟩ ⟨y, hy8⟩ hfi
      apply hne
      simpa only [l, List.getElem_ofFn] using heq
    have hsub : l ⊆ ([0, 1, 2, 3, 4, 5, 6] : List Int) := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      have h0 := Int.emod_nonneg (a i) (by decide : (7 : Int) ≠ 0)
      have h1 := Int.emod_lt_of_pos (a i) (by decide : (0 : Int) < 7)
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      omega
    have hc := hnodup.length_le_of_subset hsub
    simp [l] at hc
  obtain ⟨i, j, hij, _, _, hij7⟩ := sevenPair 0
  have hi7 : 7 ∣ m i := by
    rw [← hij7]
    exact Nat.gcd_dvd_left (m i) (m j)
  have hj7 : 7 ∣ m j := by
    rw [← hij7]
    exact Nat.gcd_dvd_right (m i) (m j)
  have third : ∃ k : Fin 8, k ≠ i ∧ k ≠ j ∧ 7 ∣ m k := by
    obtain ⟨p, q, hpq, hpi, hqi, hpq7⟩ := sevenPair i
    by_cases hpj : p = j
    · refine ⟨q, hqi, ?_, ?_⟩
      · exact fun h => hpq (hpj.trans h.symm)
      · rw [← hpq7]
        exact Nat.gcd_dvd_right (m p) (m q)
    · refine ⟨p, hpi, hpj, ?_⟩
      rw [← hpq7]
      exact Nat.gcd_dvd_left (m p) (m q)
  obtain ⟨k, hki, hkj, hk7⟩ := third
  obtain ⟨t, ht7⟩ := Classical.not_forall.mp noAllSeven
  have hti : t ≠ i := by intro h; exact ht7 (h ▸ hi7)
  have htj : t ≠ j := by intro h; exact ht7 (h ▸ hj7)
  have htk : t ≠ k := by intro h; exact ht7 (h ▸ hk7)
  have noCommon (x y : Fin 8) (hxy : x ≠ y)
      (hx : 7 ∣ m x) (hy : 7 ∣ m y) (p : Nat)
      (hp : p = 2 ∨ p = 3 ∨ p = 5) : ¬(p ∣ m x ∧ p ∣ m y) := by
    intro h
    have hdvd : p ∣ 7 := by
      rw [← gcdSeven x y hxy hx hy]
      exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 2 ∣ 7) hdvd
    · exact (by decide : ¬ 3 ∣ 7) hdvd
    · exact (by decide : ¬ 5 ∣ 7) hdvd
  have sharedSmall (x y : Fin 8) (hxy : x ≠ y) (hy : ¬ 7 ∣ m y) :
      (2 ∣ m x ∧ 2 ∣ m y) ∨
      (3 ∣ m x ∧ 3 ∣ m y) ∨
      (5 ∣ m x ∧ 5 ∣ m y) := by
    have h := hb hxy
    have hl := Nat.gcd_dvd_left (m x) (m y)
    have hr := Nat.gcd_dvd_right (m x) (m y)
    have hne : Nat.gcd (m x) (m y) ≠ 7 := by
      intro heq
      apply hy
      rw [← heq]
      exact hr
    have hx : Nat.gcd (m x) (m y) = 2 ∨ Nat.gcd (m x) (m y) = 3 ∨
        Nat.gcd (m x) (m y) = 4 ∨ Nat.gcd (m x) (m y) = 5 ∨
        Nat.gcd (m x) (m y) = 6 := by omega
    rcases hx with hx | hx | hx | hx | hx
    · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
    · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 4) (by simpa [hx] using hr)⟩
    · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inl ⟨Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [hx] using hl),
        Nat.dvd_trans (by decide : 2 ∣ 6) (by simpa [hx] using hr)⟩
  have h_it := sharedSmall i t hti.symm ht7
  have h_jt := sharedSmall j t htj.symm ht7
  have h_kt := sharedSmall k t htk.symm ht7
  have h_ij2 := noCommon i j hij hi7 hj7 2 (Or.inl rfl)
  have h_ij3 := noCommon i j hij hi7 hj7 3 (Or.inr (Or.inl rfl))
  have h_ij5 := noCommon i j hij hi7 hj7 5 (Or.inr (Or.inr rfl))
  have h_ik2 := noCommon i k hki.symm hi7 hk7 2 (Or.inl rfl)
  have h_ik3 := noCommon i k hki.symm hi7 hk7 3 (Or.inr (Or.inl rfl))
  have h_ik5 := noCommon i k hki.symm hi7 hk7 5 (Or.inr (Or.inr rfl))
  have h_jk2 := noCommon j k hkj.symm hj7 hk7 2 (Or.inl rfl)
  have h_jk3 := noCommon j k hkj.symm hj7 hk7 3 (Or.inr (Or.inl rfl))
  have h_jk5 := noCommon j k hkj.symm hj7 hk7 5 (Or.inr (Or.inr rfl))
  have ht235 : 2 ∣ m t ∧ 3 ∣ m t ∧ 5 ∣ m t := by grind
  have fifth : ∃ u : Fin 8, u ≠ i ∧ u ≠ j ∧ u ≠ k ∧ u ≠ t := by
    apply Classical.byContradiction
    intro h
    have h0 : ¬ ((0 : Fin 8) ≠ i ∧ 0 ≠ j ∧ 0 ≠ k ∧ 0 ≠ t) := by
      intro hh; exact h ⟨0, hh⟩
    have h1 : ¬ ((1 : Fin 8) ≠ i ∧ 1 ≠ j ∧ 1 ≠ k ∧ 1 ≠ t) := by
      intro hh; exact h ⟨1, hh⟩
    have h2 : ¬ ((2 : Fin 8) ≠ i ∧ 2 ≠ j ∧ 2 ≠ k ∧ 2 ≠ t) := by
      intro hh; exact h ⟨2, hh⟩
    have h3 : ¬ ((3 : Fin 8) ≠ i ∧ 3 ≠ j ∧ 3 ≠ k ∧ 3 ≠ t) := by
      intro hh; exact h ⟨3, hh⟩
    have h4 : ¬ ((4 : Fin 8) ≠ i ∧ 4 ≠ j ∧ 4 ≠ k ∧ 4 ≠ t) := by
      intro hh; exact h ⟨4, hh⟩
    omega
  obtain ⟨u, hui, huj, huk, hut⟩ := fifth
  have hu7 : ¬ 7 ∣ m u := by
    intro hu7
    have h_ut := sharedSmall u t hut ht7
    have h_ui2 := noCommon u i hui hu7 hi7 2 (Or.inl rfl)
    have h_ui3 := noCommon u i hui hu7 hi7 3 (Or.inr (Or.inl rfl))
    have h_ui5 := noCommon u i hui hu7 hi7 5 (Or.inr (Or.inr rfl))
    have h_uj2 := noCommon u j huj hu7 hj7 2 (Or.inl rfl)
    have h_uj3 := noCommon u j huj hu7 hj7 3 (Or.inr (Or.inl rfl))
    have h_uj5 := noCommon u j huj hu7 hj7 5 (Or.inr (Or.inr rfl))
    have h_uk2 := noCommon u k huk hu7 hk7 2 (Or.inl rfl)
    have h_uk3 := noCommon u k huk hu7 hk7 3 (Or.inr (Or.inl rfl))
    have h_uk5 := noCommon u k huk hu7 hk7 5 (Or.inr (Or.inr rfl))
    grind
  have h_iu := sharedSmall i u hui.symm hu7
  have h_ju := sharedSmall j u huj.symm hu7
  have h_ku := sharedSmall k u huk.symm hu7
  have hu235 : 2 ∣ m u ∧ 3 ∣ m u ∧ 5 ∣ m u := by grind
  have hbound := hb hut.symm
  have hg2 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht235.1 hu235.1)
  have hg3 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht235.2.1 hu235.2.1)
  have hg5 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd ht235.2.2 hu235.2.2)
  omega

end ProofPursuit.P4.Eight
