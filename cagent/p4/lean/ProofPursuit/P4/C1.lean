import ProofPursuit.P4.Basic

namespace ProofPursuit.P4.C1

def target : Prop := Statement 3

theorem solution : target := by
  intro a m hm hd
  apply Classical.byContradiction
  intro hn
  have hg (i j : Fin 3) (hij : i ≠ j) : Nat.gcd (m i) (m j) = 2 := by
    have := bounds hm hd hn hij
    omega
  have h01 := residues_ne hd (by decide : (0 : Fin 3) ≠ 1) (hg 0 1 (by decide))
  have h02 := residues_ne hd (by decide : (0 : Fin 3) ≠ 2) (hg 0 2 (by decide))
  have h12 := residues_ne hd (by decide : (1 : Fin 3) ≠ 2) (hg 1 2 (by decide))
  omega

end ProofPursuit.P4.C1
