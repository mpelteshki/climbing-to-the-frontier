import ProofPursuit.P4.Basic

namespace ProofPursuit.P4.Nine

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

/-- The only external obstruction needed by this argument. -/
def NoCommonTwo9 : Prop :=
  ∀ (a : Fin 9 → Int) (m : Fin 9 → Nat),
    (∀ i, 0 < m i) → DisjointClasses a m →
    (¬ ∃ i j : Fin 9, i < j ∧ 9 ≤ Nat.gcd (m i) (m j)) →
    ∃ t : Fin 9, ¬ 2 ∣ m t

def target : Prop := Statement 9

theorem step (h7 : Statement 7) (h8 : Statement 8)
    (hodd : NoCommonTwo9) : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hb {i j : Fin 9} (hij : i ≠ j) := bounds hm hd hn hij
  obtain ⟨t, htodd⟩ := hodd a m hm hd hn
  have eightPair (v : Fin 9) :
      ∃ i j : Fin 9, i ≠ j ∧ i ≠ v ∧ j ≠ v ∧ Nat.gcd (m i) (m j) = 8 := by
    let a' : Fin 8 → Int := fun s => a (omitIndex v s)
    let m' : Fin 8 → Nat := fun s => m (omitIndex v s)
    have hm' : ∀ s, 0 < m' s := by intro s; exact hm _
    have hd' : DisjointClasses a' m' := by
      intro s u hsu
      exact hd (omitIndex v s) (omitIndex v u)
        (fun h => hsu (omitIndex_injective v h))
    obtain ⟨s, u, hsu, hge⟩ := h8 a' m' hm' hd'
    have hne : omitIndex v s ≠ omitIndex v u := by
      intro h
      have := omitIndex_injective v h
      omega
    refine ⟨omitIndex v s, omitIndex v u, hne, omitIndex_ne v s,
      omitIndex_ne v u, ?_⟩
    have hlt := (hb hne).2
    dsimp [m'] at hge
    omega
  have gcdEight (x y : Fin 9) (hxy : x ≠ y)
      (hx : 8 ∣ m x) (hy : 8 ∣ m y) : Nat.gcd (m x) (m y) = 8 := by
    have h := hb hxy
    have hz := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx hy)
    omega
  obtain ⟨i, j, hij, _, _, hij8⟩ := eightPair t
  have hi8 : 8 ∣ m i := by
    rw [← hij8]
    exact Nat.gcd_dvd_left (m i) (m j)
  have hj8 : 8 ∣ m j := by
    rw [← hij8]
    exact Nat.gcd_dvd_right (m i) (m j)
  have third : ∃ k : Fin 9, k ≠ i ∧ k ≠ j ∧ 8 ∣ m k := by
    obtain ⟨p, q, hpq, hpi, hqi, hpq8⟩ := eightPair i
    by_cases hpj : p = j
    · refine ⟨q, hqi, ?_, ?_⟩
      · exact fun h => hpq (hpj.trans h.symm)
      · rw [← hpq8]
        exact Nat.gcd_dvd_right (m p) (m q)
    · refine ⟨p, hpi, hpj, ?_⟩
      rw [← hpq8]
      exact Nat.gcd_dvd_left (m p) (m q)
  obtain ⟨k, hki, hkj, hk8⟩ := third
  have hti : t ≠ i := by intro h; exact htodd (Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hi8))
  have htj : t ≠ j := by intro h; exact htodd (Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hj8))
  have htk : t ≠ k := by intro h; exact htodd (Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hk8))
  have noCommon (x y : Fin 9) (hxy : x ≠ y)
      (hx : 8 ∣ m x) (hy : 8 ∣ m y) (p : Nat)
      (hp : p = 3 ∨ p = 5 ∨ p = 7) : ¬(p ∣ m x ∧ p ∣ m y) := by
    intro h
    have hdvd : p ∣ 8 := by
      rw [← gcdEight x y hxy hx hy]
      exact Nat.dvd_gcd h.1 h.2
    rcases hp with rfl | rfl | rfl
    · exact (by decide : ¬ 3 ∣ 8) hdvd
    · exact (by decide : ¬ 5 ∣ 8) hdvd
    · exact (by decide : ¬ 7 ∣ 8) hdvd
  have sharedOdd (x y : Fin 9) (hxy : x ≠ y) (hy : ¬ 2 ∣ m y) :
      (3 ∣ m x ∧ 3 ∣ m y) ∨
      (5 ∣ m x ∧ 5 ∣ m y) ∨
      (7 ∣ m x ∧ 7 ∣ m y) := by
    have h := hb hxy
    have hl := Nat.gcd_dvd_left (m x) (m y)
    have hr := Nat.gcd_dvd_right (m x) (m y)
    have hne : ¬ 2 ∣ Nat.gcd (m x) (m y) := by
      intro he
      exact hy (Nat.dvd_trans he hr)
    have hmod : Nat.gcd (m x) (m y) % 2 ≠ 0 := by
      intro he
      exact hne (Nat.dvd_of_mod_eq_zero he)
    have hx : Nat.gcd (m x) (m y) = 3 ∨ Nat.gcd (m x) (m y) = 5 ∨
        Nat.gcd (m x) (m y) = 7 := by omega
    rcases hx with hx | hx | hx
    · exact Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩
    · exact Or.inr (Or.inl ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
    · exact Or.inr (Or.inr ⟨by simpa [hx] using hl, by simpa [hx] using hr⟩)
  have h_it := sharedOdd i t hti.symm htodd
  have h_jt := sharedOdd j t htj.symm htodd
  have h_kt := sharedOdd k t htk.symm htodd
  have h_ij3 := noCommon i j hij hi8 hj8 3 (Or.inl rfl)
  have h_ij5 := noCommon i j hij hi8 hj8 5 (Or.inr (Or.inl rfl))
  have h_ij7 := noCommon i j hij hi8 hj8 7 (Or.inr (Or.inr rfl))
  have h_ik3 := noCommon i k hki.symm hi8 hk8 3 (Or.inl rfl)
  have h_ik5 := noCommon i k hki.symm hi8 hk8 5 (Or.inr (Or.inl rfl))
  have h_ik7 := noCommon i k hki.symm hi8 hk8 7 (Or.inr (Or.inr rfl))
  have h_jk3 := noCommon j k hkj.symm hj8 hk8 3 (Or.inl rfl)
  have h_jk5 := noCommon j k hkj.symm hj8 hk8 5 (Or.inr (Or.inl rfl))
  have h_jk7 := noCommon j k hkj.symm hj8 hk8 7 (Or.inr (Or.inr rfl))
  have ht357 : 3 ∣ m t ∧ 5 ∣ m t ∧ 7 ∣ m t := by grind
  have atMostThree (u : Fin 9) (hu8 : 8 ∣ m u) : u = i ∨ u = j ∨ u = k := by
    apply Classical.byContradiction
    intro hnot
    have hui : u ≠ i := by intro h; exact hnot (Or.inl h)
    have huj : u ≠ j := by intro h; exact hnot (Or.inr (Or.inl h))
    have huk : u ≠ k := by intro h; exact hnot (Or.inr (Or.inr h))
    have hut : u ≠ t := by
      intro h
      exact htodd (Nat.dvd_trans (by decide : 2 ∣ 8) (h ▸ hu8))
    have h_ut := sharedOdd u t hut htodd
    have h_ui3 := noCommon u i hui hu8 hi8 3 (Or.inl rfl)
    have h_ui5 := noCommon u i hui hu8 hi8 5 (Or.inr (Or.inl rfl))
    have h_ui7 := noCommon u i hui hu8 hi8 7 (Or.inr (Or.inr rfl))
    have h_uj3 := noCommon u j huj hu8 hj8 3 (Or.inl rfl)
    have h_uj5 := noCommon u j huj hu8 hj8 5 (Or.inr (Or.inl rfl))
    have h_uj7 := noCommon u j huj hu8 hj8 7 (Or.inr (Or.inr rfl))
    have h_uk3 := noCommon u k huk hu8 hk8 3 (Or.inl rfl)
    have h_uk5 := noCommon u k huk hu8 hk8 5 (Or.inr (Or.inl rfl))
    have h_uk7 := noCommon u k huk hu8 hk8 7 (Or.inr (Or.inr rfl))
    grind
  have anchor3 : ∃ s : Fin 9, 8 ∣ m s ∧ 3 ∣ m s ∧ (s = i ∨ s = j ∨ s = k) := by
    grind
  have anchor5 : ∃ s : Fin 9, 8 ∣ m s ∧ 5 ∣ m s ∧ (s = i ∨ s = j ∨ s = k) := by
    grind
  have anchor7 : ∃ s : Fin 9, 8 ∣ m s ∧ 7 ∣ m s ∧ (s = i ∨ s = j ∨ s = k) := by
    grind
  obtain ⟨s3, hs38, hs33, hs3which⟩ := anchor3
  obtain ⟨s5, hs58, hs55, hs5which⟩ := anchor5
  obtain ⟨s7, hs78, hs77, hs7which⟩ := anchor7
  have hs35 : s3 ≠ s5 := by grind
  have hs37 : s3 ≠ s7 := by grind
  have hs57 : s5 ≠ s7 := by grind
  have hs5not3 : ¬ 3 ∣ m s5 := by
    exact fun h => noCommon s3 s5 hs35 hs38 hs58 3 (Or.inl rfl) ⟨hs33, h⟩
  have hs5not7 : ¬ 7 ∣ m s5 := by
    exact fun h => noCommon s7 s5 hs57.symm hs78 hs58 7 (Or.inr (Or.inr rfl)) ⟨hs77, h⟩
  have atMostNamed (u : Fin 9) (hu8 : 8 ∣ m u) :
      u = s3 ∨ u = s5 ∨ u = s7 := by
    have hu := atMostThree u hu8
    grind
  obtain ⟨w, hw⟩ := omitIndex_surjective s7 s5 hs57
  let e : Fin 7 → Fin 9 := fun r => omitIndex s7 (omitIndex w r)
  have e_ne7 (r : Fin 7) : e r ≠ s7 := omitIndex_ne s7 _
  have e_ne5 (r : Fin 7) : e r ≠ s5 := by
    intro he
    apply omitIndex_ne w r
    apply omitIndex_injective s7
    exact he.trans hw.symm
  have e_injective {r s : Fin 7} (h : e r = e s) : r = s := by
    apply omitIndex_injective w
    apply omitIndex_injective s7
    exact h
  let a' : Fin 7 → Int := fun r => a (e r)
  let m' : Fin 7 → Nat := fun r => m (e r)
  have hm' : ∀ r, 0 < m' r := by intro r; exact hm _
  have hd' : DisjointClasses a' m' := by
    intro r s hrs
    exact hd (e r) (e s) (fun he => hrs (e_injective he))
  obtain ⟨r, s, hrs, hge⟩ := h7 a' m' hm' hd'
  have hne : e r ≠ e s := by
    intro he
    have := e_injective he
    omega
  have hlt := (hb hne).2
  have hg7 : Nat.gcd (m (e r)) (m (e s)) = 7 := by
    dsimp [m'] at hge
    have hposs : Nat.gcd (m (e r)) (m (e s)) = 7 ∨
        Nat.gcd (m (e r)) (m (e s)) = 8 := by omega
    rcases hposs with h | h
    · exact h
    · have hr8 : 8 ∣ m (e r) := by
        rw [← h]; exact Nat.gcd_dvd_left _ _
      have hs8 : 8 ∣ m (e s) := by
        rw [← h]; exact Nat.gcd_dvd_right _ _
      have hrr := atMostNamed (e r) hr8
      have hss := atMostNamed (e s) hs8
      have hrne5 := e_ne5 r
      have hsne5 := e_ne5 s
      have hrne7 := e_ne7 r
      have hsne7 := e_ne7 s
      grind
  have hr7 : 7 ∣ m (e r) := by
    rw [← hg7]; exact Nat.gcd_dvd_left _ _
  have hs7 : 7 ∣ m (e s) := by
    rw [← hg7]; exact Nat.gcd_dvd_right _ _
  have odd_of_seven (x : Fin 9) (hx7 : 7 ∣ m x) (hxne : x ≠ s7) :
      ¬ 2 ∣ m x := by
    intro hx2
    have hg := hb hxne
    have h7 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hx7 hs77)
    have h2 := Nat.mod_eq_zero_of_dvd
      (Nat.dvd_gcd hx2 (Nat.dvd_trans (by decide : 2 ∣ 8) hs78))
    omega
  have hrodd := odd_of_seven (e r) hr7 (e_ne7 r)
  have hsodd := odd_of_seven (e s) hs7 (e_ne7 s)
  have hrshared := sharedOdd s5 (e r) (e_ne5 r).symm hrodd
  have hsshared := sharedOdd s5 (e s) (e_ne5 s).symm hsodd
  have hr5 : 5 ∣ m (e r) := by grind
  have hs5 : 5 ∣ m (e s) := by grind
  have hbound := hb hne
  have hg5 := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hr5 hs5)
  have hg7' := Nat.mod_eq_zero_of_dvd (Nat.dvd_gcd hr7 hs7)
  omega

end ProofPursuit.P4.Nine
