import ProofPursuit.P4.C2

namespace ProofPursuit.P4

set_option maxHeartbeats 4000000

theorem four_same_parity (a : Fin 7 → Int) :
    ∃ i j l r : Fin 7, i < j ∧ j < l ∧ l < r ∧
      a i % 2 = a j % 2 ∧ a i % 2 = a l % 2 ∧ a i % 2 = a r % 2 := by
  by_cases h0 : a 0 % 2 = 0 <;>
    by_cases h1 : a 1 % 2 = 0 <;>
    by_cases h2 : a 2 % 2 = 0 <;>
    by_cases h3 : a 3 % 2 = 0 <;>
    by_cases h4 : a 4 % 2 = 0 <;>
    by_cases h5 : a 5 % 2 = 0 <;>
    by_cases h6 : a 6 % 2 = 0
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨3, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 2, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨1, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 2, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 3, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 4, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨2, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 3, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨3, 4, 5, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 6, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 5, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 4, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩
  · exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by omega, by omega, by omega⟩

theorem seven_not_all_even (a : Fin 7 → Int) (m : Fin 7 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hn : ¬ ∃ i j : Fin 7, i < j ∧ 7 ≤ Nat.gcd (m i) (m j)) :
    ¬ ∀ i, 2 ∣ m i := by
  intro he
  obtain ⟨i, j, l, r, hij, hjl, hlr, haj, hal, har⟩ := four_same_parity a
  let f : Fin 4 → Fin 7 := fun t => [i, j, l, r][t.val]'(by simp)
  have hf : ∀ x y : Fin 4, f x = f y → x = y := by
    simp [Fin.forall_fin_succ, f]
    omega
  have ha : ∀ t, a (f t) % 2 = a i % 2 := by
    simp [Fin.forall_fin_succ, f]
    exact ⟨haj.symm, hal.symm, har.symm⟩
  let b : Fin 4 → Int := fun t => (a (f t) - a i % 2) / 2
  let n : Fin 4 → Nat := fun t => m (f t) / 2
  have hmEq (t : Fin 4) : 2 * n t = m (f t) := Nat.mul_div_cancel' (he (f t))
  have haEq (t : Fin 4) : a (f t) = 2 * b t + a i % 2 := by
    have := ha t
    dsimp [b]
    omega
  have hnp : ∀ t, 0 < n t := by
    intro t
    have := hmEq t
    have := hm (f t)
    omega
  have hdis : DisjointClasses b n := by
    intro x y hxy hmeet
    obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hmeet
    apply hd (f x) (f y) (fun h => hxy (hf x y h))
    refine ⟨2 * z + a i % 2, ?_, ?_⟩
    · refine ⟨u, ?_⟩
      have hmx : (m (f x) : Int) = 2 * (n x : Int) := by exact_mod_cast (hmEq x).symm
      have hax := haEq x
      grind
    · refine ⟨v, ?_⟩
      have hmy : (m (f y) : Int) = 2 * (n y : Int) := by exact_mod_cast (hmEq y).symm
      have hay := haEq y
      grind
  obtain ⟨x, y, hxy, hg⟩ := C2.solution b n hnp hdis
  have hxyn : f x ≠ f y := by intro h; have := hf x y h; omega
  have hb := bounds hm hd hn hxyn
  have hdiv : Nat.gcd (n x) (n y) = Nat.gcd (m (f x)) (m (f y)) / 2 :=
    Nat.gcd_div (he (f x)) (he (f y))
  omega

end ProofPursuit.P4
