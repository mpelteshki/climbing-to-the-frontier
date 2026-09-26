import ProofPursuit.P4.Basic

namespace ProofPursuit.P4

private theorem sum_map_add (cs : List α) (f g : α → Nat) :
    ((cs.map fun c => f c + g c).sum) = (cs.map f).sum + (cs.map g).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [List.map_cons, List.sum_cons, ih, Nat.add_assoc,
      Nat.add_left_comm]

private theorem beq_comm' [BEq α] [LawfulBEq α] (x y : α) : (x == y) = (y == x) := by
  by_cases h : x = y
  · subst y
    rfl
  · have hxy : (x == y) = false := by simp [h]
    have hyx : (y == x) = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      exact h (beq_iff_eq.mp he).symm
    rw [hxy, hyx]

private theorem sum_indicator_count [BEq α] [LawfulBEq α] (cs : List α) (x : α) :
    ((cs.map fun c => if (c == x) = true then 1 else 0).sum) = cs.count x := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons]
    rw [ih]
    simp [Nat.add_comm]

private theorem sum_fiber_counts [BEq α] [LawfulBEq α] (cs : List α)
    (xs : List α) (hcover : ∀ x ∈ xs, x ∈ cs) (hnodup : cs.Nodup) :
    (cs.map fun c => xs.count c).sum = xs.length := by
  induction xs with
  | nil =>
    change (cs.map fun _ => (0 : Nat)).sum = 0
    induction cs <;> simp_all
  | cons x xs ih =>
    have hx : x ∈ cs := hcover x (by simp)
    have hxs : ∀ y ∈ xs, y ∈ cs := by
      intro y hy
      exact hcover y (by simp [hy])
    have hc : cs.count x = 1 := (List.nodup_iff_count_of_mem.mp hnodup) x hx
    calc
      (cs.map fun c => (x :: xs).count c).sum =
          (cs.map fun c => xs.count c + if (c == x) = true then 1 else 0).sum := by
            congr 1
            apply List.map_congr_left
            intro c hc'
            rw [List.count_cons, beq_comm']
      _ = (cs.map fun c => xs.count c).sum +
          (cs.map fun c => if (c == x) = true then 1 else 0).sum :=
            sum_map_add cs _ _
      _ = (x :: xs).length := by
            rw [ih hxs, sum_indicator_count, hc]
            simp

private theorem exists_large_fiber {k p : Nat} (hp : 0 < p) (color : Fin k → Fin p) :
    ∃ c : Fin p, k ≤ p * ((List.finRange k).filter (fun i => color i == c)).length := by
  let cs := List.finRange p
  let xs := (List.finRange k).map color
  let ys := cs.map (fun c => xs.count c)
  have hsum : ys.sum = k := by
    have h := sum_fiber_counts cs xs
      (fun c hc => List.mem_finRange c) (List.nodup_finRange p)
    simpa [ys, xs, cs] using h
  have hlen : ys.length = p := by simp [ys, cs]
  have hne : ys ≠ [] := by
    intro h
    have := hlen
    simp [h] at this
    omega
  have hmax := List.sum_le_max_mul_length_nat hne
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp (List.max_mem hne)
  refine ⟨c, ?_⟩
  have hcount : xs.count c = ((List.finRange k).filter (fun i => color i == c)).length := by
    simp [xs, List.count_eq_length_filter, List.filter_map, Function.comp_def]
  have hbound : k ≤ xs.count c * p := by
    calc
      k = ys.sum := hsum.symm
      _ ≤ ys.max hne * ys.length := hmax
      _ = xs.count c * p := by rw [← heq, hlen]
  rw [hcount] at hbound
  simpa [Nat.mul_comm] using hbound

/-- A large group of classes with residues congruent modulo a common divisor
would contradict the corresponding smaller instance of the statement. -/
theorem no_large_common_residue_subfamily {k t p : Nat}
    (a : Fin k → Int) (m : Fin k → Nat) (c : Int)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin k, i ≠ j → Nat.gcd (m i) (m j) < k)
    (hdiv : ∀ i, p ∣ m i)
    (hpt : k ≤ p * t)
    (hst : Statement t)
    (f : Fin t → Fin k) (hf : Function.Injective f)
    (hres : ∀ u, (p : Int) ∣ a (f u) - c) : False := by
  let b : Fin t → Int := fun u => Classical.choose (hres u)
  let n : Fin t → Nat := fun u => m (f u) / p
  have hmEq (u : Fin t) : p * n u = m (f u) := Nat.mul_div_cancel' (hdiv (f u))
  have haEq (u : Fin t) : a (f u) = (p : Int) * b u + c := by
    have hs := Classical.choose_spec (hres u)
    dsimp [b]
    grind
  have hnp : ∀ u, 0 < n u := by
    intro u
    by_cases h : n u = 0
    · have he := hmEq u
      rw [h] at he
      have hpos := hm (f u)
      simp at he
      omega
    · omega
  have hdis : DisjointClasses b n := by
    intro x y hxy hmeet
    obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hmeet
    apply hd (f x) (f y) (fun h => hxy (hf h))
    refine ⟨(p : Int) * z + c, ?_, ?_⟩
    · refine ⟨u, ?_⟩
      have hmx : (m (f x) : Int) = (p : Int) * (n x : Int) := by
        exact_mod_cast (hmEq x).symm
      have hax := haEq x
      grind
    · refine ⟨v, ?_⟩
      have hmy : (m (f y) : Int) = (p : Int) * (n y : Int) := by
        exact_mod_cast (hmEq y).symm
      have hay := haEq y
      grind
  obtain ⟨x, y, hxy, hbig⟩ := hst b n hnp hdis
  have hxy' : f x ≠ f y := by
    intro h
    have := hf h
    omega
  have hg : Nat.gcd (n x) (n y) = Nat.gcd (m (f x)) (m (f y)) / p :=
    Nat.gcd_div (hdiv (f x)) (hdiv (f y))
  have hpdiv : p ∣ Nat.gcd (m (f x)) (m (f y)) :=
    Nat.dvd_gcd (hdiv (f x)) (hdiv (f y))
  have hmul : p * Nat.gcd (n x) (n y) = Nat.gcd (m (f x)) (m (f y)) := by
    rw [hg]
    exact Nat.mul_div_cancel' hpdiv
  have hlarge : p * t ≤ Nat.gcd (m (f x)) (m (f y)) := by
    rw [← hmul]
    exact Nat.mul_le_mul_left p hbig
  have hcontr := hsmall (f x) (f y) hxy'
  omega

/-- A counterexample cannot have any common divisor at least two when all
smaller instances of the statement hold. In particular, no prime divides
every modulus. -/
theorem no_common_divisor_of_smaller_statements {k p : Nat}
    (hk : 3 ≤ k) (hp : 2 ≤ p)
    (hprev : ∀ t : Nat, 2 ≤ t → t < k → Statement t)
    (a : Fin k → Int) (m : Fin k → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin k, i ≠ j → Nat.gcd (m i) (m j) < k) :
    ∃ i : Fin k, ¬ p ∣ m i := by
  apply Classical.byContradiction
  intro hnone
  have hdiv : ∀ i, p ∣ m i := by
    intro i
    by_cases h : p ∣ m i
    · exact h
    · exact False.elim (hnone ⟨i, h⟩)
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv
  have hpk : p < k := by
    have hgd : p ∣ Nat.gcd (m i0) (m i1) := Nat.dvd_gcd (hdiv i0) (hdiv i1)
    have hgp : 0 < Nat.gcd (m i0) (m i1) :=
      Nat.gcd_pos_of_pos_left (m i1) (hm i0)
    have hle := Nat.le_of_dvd hgp hgd
    have hlt := hsmall i0 i1 h01
    omega
  let color (i : Fin k) : Fin p :=
    ⟨(a i % (p : Int)).toNat, by
      have hn : 0 ≤ a i % (p : Int) := Int.emod_nonneg (a i) (by omega)
      have hu : a i % (p : Int) < (p : Int) :=
        Int.emod_lt_of_pos (a i) (by omega)
      have he := Int.toNat_of_nonneg hn
      omega⟩
  obtain ⟨c, hc⟩ := exists_large_fiber (by omega : 0 < p) color
  let s := (List.finRange k).filter (fun i => color i == c)
  have hlen : s.length ≤ k := by
    have := List.length_filter_le (fun i => color i == c) (List.finRange k)
    simpa [s] using this
  have htwo : 2 ≤ s.length := by
    by_cases h0 : s.length = 0
    · simp [s, h0] at hc
      omega
    by_cases h1 : s.length = 1
    · simp [s, h1] at hc
      omega
    · omega
  have hnodup : s.Nodup := (List.filter_sublist).nodup (List.nodup_finRange k)
  have hsres (i : Fin k) (hi : i ∈ s) : (p : Int) ∣ a i - (c.val : Int) := by
    have hcolor : color i = c := beq_iff_eq.mp (List.mem_filter.mp hi).2
    have hmod : a i % (p : Int) = (c.val : Int) := by
      have hv := congrArg Fin.val hcolor
      dsimp [color] at hv
      have hn : 0 ≤ a i % (p : Int) := Int.emod_nonneg (a i) (by omega)
      have he := Int.toNat_of_nonneg hn
      omega
    have hcmod : (c.val : Int) % (p : Int) = c.val := by
      apply Int.emod_eq_of_lt (by omega)
      exact_mod_cast c.isLt
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by rw [hmod, hcmod])
  have noLarge (t : Nat) (htlen : t ≤ s.length) (ht : 2 ≤ t)
      (htk : t < k) (hpt : k ≤ p * t) : False := by
    let f : Fin t → Fin k := fun u => s[u.val]'(by have := u.isLt; omega)
    have hf : Function.Injective f := by
      intro u v huv
      apply Fin.ext
      exact (List.Nodup.getElem_inj hnodup).mp huv
    have hr (u : Fin t) : (p : Int) ∣ a (f u) - (c.val : Int) :=
      hsres (f u) (List.getElem_mem _)
    exact no_large_common_residue_subfamily a m (c.val : Int) hm hd hsmall hdiv
      hpt (hprev t ht htk) f hf hr
  by_cases hlt : s.length < k
  · exact noLarge s.length (Nat.le_refl _) htwo hlt hc
  · have heq : s.length = k := by omega
    have hpt : k ≤ p * (k - 1) := by
      have hbase : k ≤ 2 * (k - 1) := by omega
      have hmul := Nat.mul_le_mul_right (k - 1) hp
      omega
    exact noLarge (k - 1) (by omega) (by omega) (by omega) hpt

end ProofPursuit.P4

namespace ProofPursuit.P4

private theorem five_same_parity_impossible
    (a : Fin 9 → Int) (m : Fin 9 → Nat) (c : Int)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin 9, i ≠ j → Nat.gcd (m i) (m j) < 9)
    (heven : ∀ i, 2 ∣ m i) (h5 : Statement 5)
    (xs : List (Fin 9)) (hnodup : xs.Nodup) (hlen : 5 ≤ xs.length)
    (hres : ∀ i ∈ xs, (2 : Int) ∣ a i - c) : False := by
  let f : Fin 5 → Fin 9 := fun u => xs[u.val]'(by have := u.isLt; omega)
  have hf : Function.Injective f := by
    intro u v huv
    apply Fin.ext
    exact (List.Nodup.getElem_inj hnodup).mp huv
  have hr (u : Fin 5) : (2 : Int) ∣ a (f u) - c :=
    hres (f u) (List.getElem_mem _)
  exact no_large_common_residue_subfamily a m c hm hd hsmall heven
    (by decide) h5 f hf hr

/-- For nine classes, the five-class theorem rules out a common factor 2 in
all moduli of a counterexample. -/
theorem no_common_two_nine (h5 : Statement 5)
    (a : Fin 9 → Int) (m : Fin 9 → Nat)
    (hm : ∀ i, 0 < m i) (hd : DisjointClasses a m)
    (hsmall : ∀ i j : Fin 9, i ≠ j → Nat.gcd (m i) (m j) < 9) :
    ∃ t : Fin 9, ¬ 2 ∣ m t := by
  apply Classical.byContradiction
  intro hn
  have heven : ∀ i, 2 ∣ m i := by
    intro i
    by_cases h : 2 ∣ m i
    · exact h
    · exact False.elim (hn ⟨i, h⟩)
  let all := List.finRange 9
  let pos := all.filter (fun i => decide (a i % 2 = 0))
  let neg := all.filter (fun i => !(decide (a i % 2 = 0)))
  have hp : pos.Nodup := (List.filter_sublist).nodup (List.nodup_finRange 9)
  have hn' : neg.Nodup := (List.filter_sublist).nodup (List.nodup_finRange 9)
  have hlen : pos.length + neg.length = 9 := by
    have hc := List.length_eq_countP_add_countP
      (p := fun i : Fin 9 => decide (a i % 2 = 0)) (l := all)
    simpa [all, pos, neg, List.countP_eq_length_filter] using hc.symm
  by_cases hpos : 5 ≤ pos.length
  · apply five_same_parity_impossible a m 0 hm hd hsmall heven h5 pos hp hpos
    intro i hi
    have hzero : a i % 2 = 0 := by
      have hh := (List.mem_filter.mp hi).2
      exact of_decide_eq_true hh
    exact Int.dvd_iff_emod_eq_zero.mpr (by simpa using hzero)
  · have hneg : 5 ≤ neg.length := by omega
    apply five_same_parity_impossible a m 1 hm hd hsmall heven h5 neg hn' hneg
    intro i hi
    have hne : a i % 2 ≠ 0 := by
      have hh := (List.mem_filter.mp hi).2
      simp at hh
      exact hh
    have hmod : a i % 2 = 1 := by
      have hlow := Int.emod_nonneg (a i) (by decide : (2 : Int) ≠ 0)
      have hupp := Int.emod_lt_of_pos (a i) (by decide : (0 : Int) < 2)
      omega
    apply Int.dvd_iff_emod_eq_zero.mpr
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by simpa using hmod)

end ProofPursuit.P4
