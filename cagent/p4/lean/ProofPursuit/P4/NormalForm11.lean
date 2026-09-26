import ProofPursuit.P4.Reduction
import ProofPursuit.P4.CommonPrime

namespace ProofPursuit.P4

/-- The forty divisors of 2520 with at least two distinct prime factors. -/
def Domain11 : List Nat :=
  [6, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 35, 36, 40, 42, 45,
   56, 60, 63, 70, 72, 84, 90, 105, 120, 126, 140, 168, 180, 210,
   252, 280, 315, 360, 420, 504, 630, 840, 1260, 2520]

private def PrimePower11 : List Nat := [1, 2, 3, 4, 5, 7, 8, 9]

private def basePrime11 (x : Nat) : Nat :=
  if x = 2 ∨ x = 4 ∨ x = 8 then 2
  else if x = 3 ∨ x = 9 then 3
  else if x = 5 then 5
  else if x = 7 then 7
  else 0

private theorem prime_power_lt_ten (x : Nat) (hx : x ∈ PrimePower11) : x < 10 := by
  simp [PrimePower11] at hx
  omega

private theorem prime_power_factor_aux :
    ∀ x g : Fin 10, x.val ∈ PrimePower11 → 2 ≤ g.val → g.val ∣ x.val →
      2 ≤ basePrime11 x.val ∧ basePrime11 x.val ∣ x.val ∧
        basePrime11 x.val ∣ g.val := by
  decide

private theorem prime_power_forces_common_factor (x : Nat)
    (hx : x ∈ PrimePower11) (hex : ∃ y : Nat, 2 ≤ Nat.gcd x y) :
    ∃ p : Nat, 2 ≤ p ∧ p ∣ x ∧
      ∀ y : Nat, 2 ≤ Nat.gcd x y → p ∣ y := by
  let p := basePrime11 x
  have hxt : x < 10 := prime_power_lt_ten x hx
  have hxp : 0 < x := by
    simp [PrimePower11] at hx
    omega
  obtain ⟨y0, hg0⟩ := hex
  have hgt0 : Nat.gcd x y0 < 10 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hxp (Nat.gcd_dvd_left x y0)) hxt
  have hcore := prime_power_factor_aux ⟨x, hxt⟩ ⟨Nat.gcd x y0, hgt0⟩
    hx hg0 (Nat.gcd_dvd_left x y0)
  refine ⟨p, hcore.1, hcore.2.1, ?_⟩
  intro y hgy
  have hgt : Nat.gcd x y < 10 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hxp (Nat.gcd_dvd_left x y)) hxt
  have hfac := (prime_power_factor_aux ⟨x, hxt⟩ ⟨Nat.gcd x y, hgt⟩
    hx hgy (Nat.gcd_dvd_left x y)).2.2
  exact Nat.dvd_trans hfac (Nat.gcd_dvd_right x y)

set_option maxRecDepth 8192 in
private theorem divisor_2520_classification :
    ∀ n : Fin 2521, n.val ∣ 2520 →
      n.val ∈ PrimePower11 ∨ n.val ∈ Domain11 := by
  decide

private theorem small_divides_2520 (d : Nat) (hd : 0 < d) (hk : d < 11) :
    d ∣ 2520 := by
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨
      d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def omitIndexForAnchors {n : Nat} (v : Fin (n + 1)) (s : Fin n) : Fin (n + 1) :=
  ⟨if s.val < v.val then s.val else s.val + 1, by
    by_cases h : s.val < v.val <;> simp [h] <;> omega⟩

private theorem omitIndexForAnchors_ne {n : Nat} (v : Fin (n + 1)) (s : Fin n) :
    omitIndexForAnchors v s ≠ v := by
  intro h
  have hv := congrArg Fin.val h
  simp only [omitIndexForAnchors] at hv
  by_cases hs : s.val < v.val <;> simp [hs] at hv <;> omega

private theorem omitIndexForAnchors_injective {n : Nat} (v : Fin (n + 1))
    {s u : Fin n} (h : omitIndexForAnchors v s = omitIndexForAnchors v u) : s = u := by
  have hv := congrArg Fin.val h
  simp only [omitIndexForAnchors] at hv
  by_cases hs : s.val < v.val <;> by_cases hu : u.val < v.val <;>
    simp [hs, hu] at hv <;> apply Fin.ext <;> omega

private theorem anchor_pair_avoiding {n : Nat}
    (a : Fin (n + 1) → Int) (m : Fin (n + 1) → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin (n + 1), i ≠ j → Nat.gcd (m i) (m j) < n + 1)
    (hprev : Statement n) (v : Fin (n + 1)) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ i ≠ v ∧ j ≠ v ∧
      Nat.gcd (m i) (m j) = n := by
  let b : Fin n → Int := fun s => a (omitIndexForAnchors v s)
  let q : Fin n → Nat := fun s => m (omitIndexForAnchors v s)
  have hq : ∀ s, 0 < q s := by intro s; exact hm _
  have hb : DisjointClasses b q := by
    intro s u hsu
    exact hd (omitIndexForAnchors v s) (omitIndexForAnchors v u)
      (fun h => hsu (omitIndexForAnchors_injective v h))
  obtain ⟨s, u, hsu, hge⟩ := hprev b q hq hb
  have hne : omitIndexForAnchors v s ≠ omitIndexForAnchors v u := by
    intro h
    have he := omitIndexForAnchors_injective v h
    omega
  have hlt := hsmall (omitIndexForAnchors v s) (omitIndexForAnchors v u) hne
  refine ⟨omitIndexForAnchors v s, omitIndexForAnchors v u, hne,
    omitIndexForAnchors_ne v s, omitIndexForAnchors_ne v u, ?_⟩
  dsimp [q] at hge
  omega

/-- The previous statement forces three distinct moduli divisible by n in a
counterexample with n+1 classes. -/
theorem three_anchors_from_previous {n : Nat} (_hn : 2 ≤ n)
    (hprev : Statement n)
    (a : Fin (n + 1) → Int) (m : Fin (n + 1) → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin (n + 1), i ≠ j → Nat.gcd (m i) (m j) < n + 1) :
    ∃ i j l : Fin (n + 1), i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      n ∣ m i ∧ n ∣ m j ∧ n ∣ m l := by
  obtain ⟨i, j, hij, _, _, hg⟩ := anchor_pair_avoiding a m hm hd hsmall hprev 0
  have hi : n ∣ m i := by
    rw [← hg]
    exact Nat.gcd_dvd_left _ _
  have hj : n ∣ m j := by
    rw [← hg]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨x, y, hxy, hxi, hyi, hxyN⟩ := anchor_pair_avoiding a m hm hd hsmall hprev i
  by_cases hxj : x = j
  · refine ⟨i, j, y, hij, ?_, ?_, hi, hj, ?_⟩
    · exact Ne.symm hyi
    · intro h
      exact hxy (hxj.trans h)
    · rw [← hxyN]
      exact Nat.gcd_dvd_right _ _
  · refine ⟨i, j, x, hij, Ne.symm hxi, ?_, hi, hj, ?_⟩
    · exact Ne.symm hxj
    · rw [← hxyN]
      exact Nat.gcd_dvd_left _ _

/-- A hypothetical eleven-class counterexample compresses into the exact
forty-value domain used by the finite enumerator. This is only a necessary
condition; it does not certify that the finite domain has no survivors. -/
theorem normal_form_11
    (hprev : ∀ t : Nat, 2 ≤ t → t < 11 → Statement t)
    (a : Fin 11 → Int) (m : Fin 11 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 11, i < j ∧ 11 ≤ Nat.gcd (m i) (m j)) :
    ∃ r : Fin 11 → Nat,
      (∀ i, r i ∈ Domain11) ∧
      (∀ i, 0 < r i ∧ r i ∣ 2520) ∧
      DisjointClasses a r ∧
      (∀ i j : Fin 11, i ≠ j →
        Nat.gcd (r i) (r j) = Nat.gcd (m i) (m j)) := by
  have hsmall (i j : Fin 11) (hij : i ≠ j) : Nat.gcd (m i) (m j) < 11 :=
    (bounds hm hd hn hij).2
  obtain ⟨r, hrpos, hrdis, hrgcd⟩ :=
    compress_counterexample a m 2520 hm hd hsmall (by decide) small_divides_2520
  have hsmallr (i j : Fin 11) (hij : i ≠ j) : Nat.gcd (r i) (r j) < 11 := by
    rw [hrgcd i j hij]
    exact hsmall i j hij
  have htwo (i j : Fin 11) (hij : i ≠ j) : 2 ≤ Nat.gcd (r i) (r j) := by
    rw [hrgcd i j hij]
    exact (bounds hm hd hn hij).1
  have hnotbad (i : Fin 11) : r i ∉ PrimePower11 := by
    intro hbad
    let j : Fin 11 := if i = 0 then 1 else 0
    have hij : i ≠ j := by
      dsimp [j]
      split <;> omega
    obtain ⟨p, hp, hpri, hforce⟩ :=
      prime_power_forces_common_factor (r i) hbad ⟨r j, htwo i j hij⟩
    have hall : ∀ u : Fin 11, p ∣ r u := by
      intro u
      by_cases hui : u = i
      · simpa [hui] using hpri
      · exact hforce (r u) (htwo i u (Ne.symm hui))
    obtain ⟨u, hu⟩ := no_common_divisor_of_smaller_statements
      (by decide : 3 ≤ 11) hp hprev a r (fun u => (hrpos u).1)
      hrdis hsmallr
    exact hu (hall u)
  have hdomain (i : Fin 11) : r i ∈ Domain11 := by
    have hle : r i ≤ 2520 := Nat.le_of_dvd (by decide) (hrpos i).2
    have hclass := divisor_2520_classification ⟨r i, by omega⟩ (hrpos i).2
    exact hclass.resolve_left (hnotbad i)
  exact ⟨r, hdomain, hrpos, hrdis, hrgcd⟩

/-- The eleven-class normal form also has three distinct ten-divisible
moduli, using the ten-class statement. -/
theorem normal_form_11_with_anchors
    (hprev : ∀ t : Nat, 2 ≤ t → t < 11 → Statement t)
    (a : Fin 11 → Int) (m : Fin 11 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 11, i < j ∧ 11 ≤ Nat.gcd (m i) (m j)) :
    ∃ r : Fin 11 → Nat,
      (∀ i, r i ∈ Domain11) ∧
      (∀ i, 0 < r i ∧ r i ∣ 2520) ∧
      DisjointClasses a r ∧
      (∀ i j : Fin 11, i ≠ j →
        Nat.gcd (r i) (r j) = Nat.gcd (m i) (m j)) ∧
      (∃ i j l : Fin 11, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
        10 ∣ r i ∧ 10 ∣ r j ∧ 10 ∣ r l) := by
  obtain ⟨r, hrdom, hrpos, hrdis, hrgcd⟩ := normal_form_11 hprev a m hm hd hn
  have hsmallr (i j : Fin 11) (hij : i ≠ j) : Nat.gcd (r i) (r j) < 11 := by
    rw [hrgcd i j hij]
    exact (bounds hm hd hn hij).2
  have hanchors := three_anchors_from_previous (by decide : 2 ≤ 10)
    (hprev 10 (by decide) (by decide)) a r (fun i => (hrpos i).1)
    hrdis hsmallr
  exact ⟨r, hrdom, hrpos, hrdis, hrgcd, hanchors⟩

end ProofPursuit.P4
