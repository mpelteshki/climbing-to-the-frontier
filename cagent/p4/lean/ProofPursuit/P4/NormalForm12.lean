import ProofPursuit.P4.NormalForm11

namespace ProofPursuit.P4

/-- The eighty-seven divisors of 27720 with at least two distinct prime factors. -/
def Domain12 : List Nat :=
  [6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 28, 30, 33, 35, 36, 40,
   42, 44, 45, 55, 56, 60, 63, 66, 70, 72, 77, 84, 88, 90, 99, 105,
   110, 120, 126, 132, 140, 154, 165, 168, 180, 198, 210, 220, 231,
   252, 264, 280, 308, 315, 330, 360, 385, 396, 420, 440, 462, 495,
   504, 616, 630, 660, 693, 770, 792, 840, 924, 990, 1155, 1260,
   1320, 1386, 1540, 1848, 1980, 2310, 2520, 2772, 3080, 3465,
   3960, 4620, 5544, 6930, 9240, 13860, 27720]

private def PrimePower12 : List Nat := [1, 2, 3, 4, 5, 7, 8, 9, 11]

private def basePrime12 (x : Nat) : Nat :=
  if x = 2 ∨ x = 4 ∨ x = 8 then 2
  else if x = 3 ∨ x = 9 then 3
  else if x = 5 then 5
  else if x = 7 then 7
  else if x = 11 then 11
  else 0

private theorem prime_power_lt_twelve (x : Nat) (hx : x ∈ PrimePower12) : x < 12 := by
  simp [PrimePower12] at hx
  omega

private theorem prime_power_factor_aux_12 :
    ∀ x g : Fin 12, x.val ∈ PrimePower12 → 2 ≤ g.val → g.val ∣ x.val →
      2 ≤ basePrime12 x.val ∧ basePrime12 x.val ∣ x.val ∧
        basePrime12 x.val ∣ g.val := by
  decide

private theorem prime_power_forces_common_factor_12 (x : Nat)
    (hx : x ∈ PrimePower12) (hex : ∃ y : Nat, 2 ≤ Nat.gcd x y) :
    ∃ p : Nat, 2 ≤ p ∧ p ∣ x ∧
      ∀ y : Nat, 2 ≤ Nat.gcd x y → p ∣ y := by
  let p := basePrime12 x
  have hxt : x < 12 := prime_power_lt_twelve x hx
  have hxp : 0 < x := by
    simp [PrimePower12] at hx
    omega
  obtain ⟨y0, hg0⟩ := hex
  have hgt0 : Nat.gcd x y0 < 12 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hxp (Nat.gcd_dvd_left x y0)) hxt
  have hcore := prime_power_factor_aux_12 ⟨x, hxt⟩ ⟨Nat.gcd x y0, hgt0⟩
    hx hg0 (Nat.gcd_dvd_left x y0)
  refine ⟨p, hcore.1, hcore.2.1, ?_⟩
  intro y hgy
  have hgt : Nat.gcd x y < 12 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd hxp (Nat.gcd_dvd_left x y)) hxt
  have hfac := (prime_power_factor_aux_12 ⟨x, hxt⟩ ⟨Nat.gcd x y, hgt⟩
    hx hgy (Nat.gcd_dvd_left x y)).2.2
  exact Nat.dvd_trans hfac (Nat.gcd_dvd_right x y)

set_option maxRecDepth 8192 in
private theorem divisor_chunk_0 :
    ∀ x : Fin 2521, 0 + x.val ∣ 27720 →
      0 + x.val ∈ PrimePower12 ∨ 0 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_1 :
    ∀ x : Fin 2521, 2520 + x.val ∣ 27720 →
      2520 + x.val ∈ PrimePower12 ∨ 2520 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_2 :
    ∀ x : Fin 2521, 5040 + x.val ∣ 27720 →
      5040 + x.val ∈ PrimePower12 ∨ 5040 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_3 :
    ∀ x : Fin 2521, 7560 + x.val ∣ 27720 →
      7560 + x.val ∈ PrimePower12 ∨ 7560 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_4 :
    ∀ x : Fin 2521, 10080 + x.val ∣ 27720 →
      10080 + x.val ∈ PrimePower12 ∨ 10080 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_5 :
    ∀ x : Fin 2521, 12600 + x.val ∣ 27720 →
      12600 + x.val ∈ PrimePower12 ∨ 12600 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_6 :
    ∀ x : Fin 2521, 15120 + x.val ∣ 27720 →
      15120 + x.val ∈ PrimePower12 ∨ 15120 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_7 :
    ∀ x : Fin 2521, 17640 + x.val ∣ 27720 →
      17640 + x.val ∈ PrimePower12 ∨ 17640 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_8 :
    ∀ x : Fin 2521, 20160 + x.val ∣ 27720 →
      20160 + x.val ∈ PrimePower12 ∨ 20160 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_9 :
    ∀ x : Fin 2521, 22680 + x.val ∣ 27720 →
      22680 + x.val ∈ PrimePower12 ∨ 22680 + x.val ∈ Domain12 := by
  decide

set_option maxRecDepth 8192 in
private theorem divisor_chunk_10 :
    ∀ x : Fin 2521, 25200 + x.val ∣ 27720 →
      25200 + x.val ∈ PrimePower12 ∨ 25200 + x.val ∈ Domain12 := by
  decide

private theorem divisor_from_chunk (n offset : Nat)
    (hlo : offset ≤ n) (hhi : n ≤ offset + 2520)
    (hc : ∀ x : Fin 2521, offset + x.val ∣ 27720 →
      offset + x.val ∈ PrimePower12 ∨ offset + x.val ∈ Domain12)
    (hd : n ∣ 27720) : n ∈ PrimePower12 ∨ n ∈ Domain12 := by
  let x : Fin 2521 := ⟨n - offset, by omega⟩
  have heq : offset + x.val = n := by dsimp [x]; omega
  simpa [heq] using hc x (by simpa [heq] using hd)

private theorem divisor_27720_classification (n : Nat) (hd : n ∣ 27720) :
    n ∈ PrimePower12 ∨ n ∈ Domain12 := by
  have hle : n ≤ 27720 := Nat.le_of_dvd (by decide) hd

  have hcases : n ≤ 2520 ∨
      (2520 ≤ n ∧ n ≤ 5040) ∨
      (5040 ≤ n ∧ n ≤ 7560) ∨
      (7560 ≤ n ∧ n ≤ 10080) ∨
      (10080 ≤ n ∧ n ≤ 12600) ∨
      (12600 ≤ n ∧ n ≤ 15120) ∨
      (15120 ≤ n ∧ n ≤ 17640) ∨
      (17640 ≤ n ∧ n ≤ 20160) ∨
      (20160 ≤ n ∧ n ≤ 22680) ∨
      (22680 ≤ n ∧ n ≤ 25200) ∨
      (25200 ≤ n ∧ n ≤ 27720) := by omega

  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10

  · exact divisor_from_chunk n 0 (by omega) h0 divisor_chunk_0 hd

  · exact divisor_from_chunk n 2520 h1.1 h1.2 divisor_chunk_1 hd

  · exact divisor_from_chunk n 5040 h2.1 h2.2 divisor_chunk_2 hd

  · exact divisor_from_chunk n 7560 h3.1 h3.2 divisor_chunk_3 hd

  · exact divisor_from_chunk n 10080 h4.1 h4.2 divisor_chunk_4 hd

  · exact divisor_from_chunk n 12600 h5.1 h5.2 divisor_chunk_5 hd

  · exact divisor_from_chunk n 15120 h6.1 h6.2 divisor_chunk_6 hd

  · exact divisor_from_chunk n 17640 h7.1 h7.2 divisor_chunk_7 hd

  · exact divisor_from_chunk n 20160 h8.1 h8.2 divisor_chunk_8 hd

  · exact divisor_from_chunk n 22680 h9.1 h9.2 divisor_chunk_9 hd

  · exact divisor_from_chunk n 25200 h10.1 h10.2 divisor_chunk_10 hd

private theorem small_divides_27720 (d : Nat) (hd : 0 < d) (hk : d < 12) :
    d ∣ 27720 := by
  have hcheck : ∀ x : Fin 12, x.val = 0 ∨ x.val ∣ 27720 := by decide
  exact (hcheck ⟨d, hk⟩).resolve_left (by simpa using (Nat.ne_of_gt hd))

/-- Every hypothetical twelve-class counterexample compresses to the exact
87-value domain. The three-anchor clause follows from Statement 11. -/
theorem normal_form_12
    (hprev : ∀ t : Nat, 2 ≤ t → t < 12 → Statement t)
    (a : Fin 12 → Int) (m : Fin 12 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 12, i < j ∧ 12 ≤ Nat.gcd (m i) (m j)) :
    ∃ r : Fin 12 → Nat,
      (∀ i, r i ∈ Domain12) ∧
      (∀ i, 0 < r i ∧ r i ∣ 27720) ∧
      DisjointClasses a r ∧
      (∀ i j : Fin 12, i ≠ j →
        Nat.gcd (r i) (r j) = Nat.gcd (m i) (m j)) ∧
      (∃ i j l : Fin 12, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
        11 ∣ r i ∧ 11 ∣ r j ∧ 11 ∣ r l) := by
  have hsmall (i j : Fin 12) (hij : i ≠ j) : Nat.gcd (m i) (m j) < 12 :=
    (bounds hm hd hn hij).2
  obtain ⟨r, hrpos, hrdis, hrgcd⟩ :=
    compress_counterexample a m 27720 hm hd hsmall (by decide) small_divides_27720
  have hsmallr (i j : Fin 12) (hij : i ≠ j) : Nat.gcd (r i) (r j) < 12 := by
    rw [hrgcd i j hij]
    exact hsmall i j hij
  have htwo (i j : Fin 12) (hij : i ≠ j) : 2 ≤ Nat.gcd (r i) (r j) := by
    rw [hrgcd i j hij]
    exact (bounds hm hd hn hij).1
  have hnotbad (i : Fin 12) : r i ∉ PrimePower12 := by
    intro hbad
    let j : Fin 12 := if i = 0 then 1 else 0
    have hij : i ≠ j := by
      dsimp [j]
      split <;> omega
    obtain ⟨p, hp, hpri, hforce⟩ :=
      prime_power_forces_common_factor_12 (r i) hbad ⟨r j, htwo i j hij⟩
    have hall : ∀ u : Fin 12, p ∣ r u := by
      intro u
      by_cases hui : u = i
      · simpa [hui] using hpri
      · exact hforce (r u) (htwo i u (Ne.symm hui))
    obtain ⟨u, hu⟩ := no_common_divisor_of_smaller_statements
      (by decide : 3 ≤ 12) hp hprev a r (fun u => (hrpos u).1)
      hrdis hsmallr
    exact hu (hall u)
  have hdomain (i : Fin 12) : r i ∈ Domain12 :=
    (divisor_27720_classification (r i) (hrpos i).2).resolve_left (hnotbad i)
  have hanchors : ∃ i j l : Fin 12, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      11 ∣ r i ∧ 11 ∣ r j ∧ 11 ∣ r l :=
    three_anchors_from_previous (by decide : 2 ≤ 11)
      (hprev 11 (by decide) (by decide)) a r (fun u => (hrpos u).1)
      hrdis hsmallr
  exact ⟨r, hdomain, hrpos, hrdis, hrgcd, hanchors⟩

end ProofPursuit.P4
