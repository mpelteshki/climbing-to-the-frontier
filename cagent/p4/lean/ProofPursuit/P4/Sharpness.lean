import ProofPursuit.P4.Reduction
namespace ProofPursuit.P4

/-- The k canonical residues modulo k are pairwise disjoint, even with repeated
moduli. This also supplies exact positive controls for certificate machinery. -/
theorem canonical_classes_disjoint (k : Nat) :
    DisjointClasses (fun i : Fin k => (i.val : Int)) (fun _ => k) := by
  intro i j hij hmeet
  have hdiv := gcd_dvd_of_meet (i.val : Int) (j.val : Int) k k hmeet
  simp only [Nat.gcd_self] at hdiv
  have he : (j.val : Int) % (k : Int) = (i.val : Int) % (k : Int) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hdiv)
  have hi : (i.val : Int) % (k : Int) = (i.val : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hj : (j.val : Int) % (k : Int) = (j.val : Int) :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  apply hij
  apply Fin.ext
  omega

/-- Every pair in the canonical construction attains exactly the proposed bound. -/
theorem canonical_gcd (k : Nat) : Nat.gcd k k = k := Nat.gcd_self k

#print axioms canonical_classes_disjoint
end ProofPursuit.P4
