import ProofPursuit.P3.Enumeration
import ProofPursuit.P3.Staircase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ProofPursuit.P3

def convergesCheck (n d : Nat) (target : State) : Bool :=
  (partitions n).all fun s => decide (run d s = target)

theorem converges_of_check {n d : Nat} {target : State}
    (h : convergesCheck n d target = true) :
    ∀ s, IsPartition n s → run d s = target := by
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp h s (partitions_complete hs))

theorem cyclic_eq_target_of_convergence {n d : Nat} {target : State}
    (hfixed : step target = target)
    (hconverges : ∀ s, IsPartition n s → run d s = target) :
    ∀ s, IsPartition n s → Cyclic s → s = target := by
  intro s hs hc
  have hr := hconverges s hs
  have hperiod : run 1 (run d s) = run d s := by
    rw [hr]
    exact hfixed
  have hsfix : run 1 s = s := period_backwards hc hperiod
  have hrepeat : run d s = s := by
    simpa using run_multiple hsfix d
  exact hrepeat.symm.trans hr

def TriangularConverges (k d : Nat) : Prop :=
  (∀ s, IsPartition (k*(k+1)/2) s → run d s = staircase k) ∧
  (∀ s, IsPartition (k*(k+1)/2) s → Cyclic s → s = staircase k)

theorem triangular_of_check {k d : Nat}
    (h : convergesCheck (k*(k+1)/2) d (staircase k) = true) :
    TriangularConverges k d := by
  have hc := converges_of_check h
  exact ⟨hc, cyclic_eq_target_of_convergence (staircase_fixed k) hc⟩

theorem triangular_1 : TriangularConverges 1 0 := triangular_of_check (by cbv)
theorem triangular_2 : TriangularConverges 2 2 := triangular_of_check (by cbv)
theorem triangular_3 : TriangularConverges 3 6 := triangular_of_check (by cbv)
theorem triangular_4 : TriangularConverges 4 12 := triangular_of_check (by cbv)
theorem triangular_5 : TriangularConverges 5 20 := triangular_of_check (by cbv)
theorem triangular_6 : TriangularConverges 6 30 := triangular_of_check (by cbv)

#print axioms triangular_1
#print axioms triangular_2
#print axioms triangular_3
#print axioms triangular_4
#print axioms triangular_5
#print axioms triangular_6

end ProofPursuit.P3
