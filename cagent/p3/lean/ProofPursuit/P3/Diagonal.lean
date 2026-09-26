import ProofPursuit.P3.CyclicStep

namespace ProofPursuit.P3

/-- Whether column `j` has a card on the diagonal of weight `w`. -/
def diagonalCell (s : State) (w j : Nat) : Prop :=
  w - j ≤ height s j

/-- For a cyclic partition, one move rotates every positive diagonal by one column. -/
theorem diagonal_step {n : Nat} {s : State} (hp : IsPartition n s)
    (hc : Cyclic s) {w j : Nat} (_hw : 0 < w) (hj : j < w) :
    diagonalCell s w j ↔ diagonalCell (step s) w ((j+1) % w) := by
  by_cases hn : j+1 < w
  · rw [Nat.mod_eq_of_lt hn]
    simp only [diagonalCell, height_step_succ hp hc j]
    omega
  · have he : j+1 = w := by omega
    rw [he, Nat.mod_self]
    simp only [diagonalCell, Nat.sub_zero, height_step_zero hp hc]
    have hpos := height_pos_iff hp.2.1 j
    omega

theorem run_succ_eq_step_run (t : Nat) (s : State) :
    run (t+1) s = step (run t s) := by
  rw [run_add]
  rfl

/-- After `t` moves, a cell on a positive diagonal has moved `t` columns. -/
theorem diagonal_run {n : Nat} {s : State} (hp : IsPartition n s)
    (hc : Cyclic s) {w j : Nat} (hw : 0 < w) (hj : j < w) (t : Nat) :
    diagonalCell s w j ↔ diagonalCell (run t s) w ((j+t) % w) := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt hj, run]
  | succ t ih =>
    have hidx : (j+t) % w < w := Nat.mod_lt _ hw
    have hs := diagonal_step (run_isPartition hp t) (cyclic_run hc t) hw hidx
    have hmod : (((j+t) % w)+1) % w = (j+(t+1)) % w := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [run_succ_eq_step_run, ← hmod]
    exact ih.trans hs

theorem diagonal_periodic {n : Nat} {s : State} (hp : IsPartition n s)
    (hc : Cyclic s) {w j p : Nat} (hw : 0 < w) (hj : j < w)
    (hperiod : run p s = s) :
    diagonalCell s w j ↔ diagonalCell s w ((j+p) % w) := by
  simpa [hperiod] using diagonal_run hp hc hw hj p

#print axioms diagonal_step
#print axioms diagonal_run
#print axioms diagonal_periodic

end ProofPursuit.P3
