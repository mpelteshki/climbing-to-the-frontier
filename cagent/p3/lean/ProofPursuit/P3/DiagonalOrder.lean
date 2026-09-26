import ProofPursuit.P3.Diagonal

namespace ProofPursuit.P3

/-- A nonnegative time that simultaneously sends column `j` on diagonal `w`
to its final column and column `q` on diagonal `w+1` to column zero. -/
theorem adjacent_diagonal_alignment {w j q : Nat} (hw : 0 < w)
    (hj : j < w) (_hq : q < w+1) :
    ∃ t : Nat, (j+t) % w = w-1 ∧ (q+t) % (w+1) = 0 := by
  let a := w-1-j
  let t := (w+1)*a + w*q
  have ha : j+a = w-1 := by dsimp [a]; omega
  have hfirst : j+t = (j+a) + w*(a+q) := by
    dsimp [t]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  have hsecond : q+t = (w+1)*(a+q) := by
    dsimp [t]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega
  refine ⟨t, ?_, ?_⟩
  · rw [hfirst, ha]
    simp [Nat.mod_eq_of_lt (by omega : w-1 < w)]
  · rw [hsecond]
    simp

/-- An occupied cell on diagonal `w+1` forces every cell on diagonal `w`
to be occupied on a periodic orbit. -/
theorem lower_diagonal_filled_of_upper_cell {n : Nat} {s : State}
    (hp : IsPartition n s) (hc : Cyclic s) {w q : Nat}
    (hw : 0 < w) (hq : q < w+1)
    (hcard : diagonalCell s (w+1) q) :
    ∀ j, j < w → diagonalCell s w j := by
  intro j hj
  apply Classical.byContradiction
  intro hhole
  obtain ⟨t, hlast, hfirst⟩ := adjacent_diagonal_alignment hw hj hq
  let u := run t s
  have hup : IsPartition n u := run_isPartition hp t
  have huc : Cyclic u := cyclic_run hc t
  have hholeLast : ¬ diagonalCell u w (w-1) := by
    rw [← hlast]
    intro h
    exact hhole ((diagonal_run hp hc hw hj t).mpr h)
  have hcardFirst : diagonalCell u (w+1) 0 := by
    rw [← hfirst]
    exact (diagonal_run hp hc (by omega : 0 < w+1) hq t).mp hcard
  have hlen : u.length < w := by
    have hpos := height_pos_iff hup.2.1 (w-1)
    have hzero : ¬ 0 < height u (w-1) := by
      intro h
      apply hholeLast
      unfold diagonalCell
      omega
    omega
  have hhead : w+1 ≤ height u 0 := by
    simpa only [diagonalCell, Nat.sub_zero] using hcardFirst
  cases hu : u with
  | nil =>
    rw [hu] at hhead
    simp [height] at hhead
  | cons a tail =>
    have hup' := hup
    have huc' := huc
    rw [hu] at hup' huc' hhead hlen
    have hbound := cyclic_head_bound hup' huc'
    simp only [height, List.length_cons] at hhead hlen hbound
    omega

#print axioms lower_diagonal_filled_of_upper_cell

end ProofPursuit.P3
