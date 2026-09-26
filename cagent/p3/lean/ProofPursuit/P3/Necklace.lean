import ProofPursuit.P3.Classification

namespace ProofPursuit.P3

theorem height_ext {s t : State} (hs : ∀ a ∈ s, 0 < a) (ht : ∀ a ∈ t, 0 < a)
    (he : ∀ j, height s j = height t j) : s = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons a t =>
      have hp := ht a (by simp)
      have hz := he 0
      simp [height] at hz
      omega
  | cons a s ih =>
    cases t with
    | nil =>
      have hp := hs a (by simp)
      have hz := he 0
      simp [height] at hz
      omega
    | cons b t =>
      have hab : a = b := he 0
      have hst : s = t := ih
        (by intro x hx; exact hs x (by simp [hx]))
        (by intro x hx; exact ht x (by simp [hx])) (fun j => he (j+1))
      simp [hab, hst]

theorem height_boundary (bits : List Bool) (j : Nat) :
    height (boundary bits) j = height (boundaryRaw bits) j :=
  height_filter_positive (boundaryRaw_sorted bits) j

theorem boundary_injective_of_length {a b : List Bool} (hlen : a.length = b.length)
    (he : boundary a = boundary b) : a = b := by
  induction a generalizing b with
  | nil => simpa using hlen.symm
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have htail : a.length = b.length := by simpa using hlen
      have hhead := congrArg (fun s => height s 0) he
      rw [height_boundary, height_boundary] at hhead
      have hxy : x = y := by
        cases x <;> cases y <;> simp_all [boundaryRaw, height]
        all_goals cases hhead
      have hheights : ∀ j, height (boundary a) j = height (boundary b) j := by
        intro j
        have hh := congrArg (fun s => height s (j+1)) he
        rw [height_boundary, height_boundary] at hh
        simpa only [boundaryRaw, height, ← height_boundary] using hh
      have heTail := height_ext (boundary_partition a).2.1 (boundary_partition b).2.1 hheights
      simp [hxy, ih htail heTail]

def rotateWord (bits : List Bool) (t : Nat) : List Bool :=
  bits.drop (bits.length - t % bits.length) ++ bits.take (bits.length - t % bits.length)

theorem rotateWord_length (bits : List Bool) (t : Nat) :
    (rotateWord bits t).length = bits.length := by
  simp only [rotateWord, List.length_append, List.length_drop, List.length_take]
  omega

theorem run_mod_period {s : State} {p : Nat} (he : run p s = s) (t : Nat) :
    run t s = run (t % p) s := by
  have hdecomp : t = p * (t / p) + t % p := by
    have := Nat.mod_add_div t p
    omega
  conv => lhs; rw [hdecomp]
  rw [run_add, run_multiple he]

theorem run_boundary_eq_rotation (bits : List Bool) (t : Nat) :
    run t (boundary bits) = boundary (rotateWord bits t) := by
  cases bits with
  | nil =>
    have hf : step (boundary []) = boundary [] := by rfl
    induction t with
    | zero => rfl
    | succ t ih => simpa [run, hf, rotateWord] using ih
  | cons b bits =>
    let word := b :: bits
    let cut := word.length - t % word.length
    have hpos : 0 < word.length := by simp [word]
    have hr := Nat.mod_lt t hpos
    have hsuffix : (word.drop cut).length = t % word.length := by
      simp only [List.length_drop]
      dsimp [cut]
      omega
    have hrot := run_boundary_rotate (word.take cut) (word.drop cut)
    rw [List.take_append_drop, hsuffix] at hrot
    change run t (boundary word) = _
    rw [run_mod_period (boundary_period word) t]
    exact hrot

/-- Equal-width binary words describe the same dynamical cycle exactly when
one is a rotation of the other. -/
theorem boundary_same_cycle_iff {a b : List Bool} (hlen : a.length = b.length) :
    (∃ t, run t (boundary a) = boundary b) ↔ ∃ t, rotateWord a t = b := by
  constructor
  · rintro ⟨t, he⟩
    refine ⟨t, boundary_injective_of_length ?_ ?_⟩
    · rw [rotateWord_length, hlen]
    · rw [← run_boundary_eq_rotation]
      exact he
  · rintro ⟨t, he⟩
    exact ⟨t, by rw [run_boundary_eq_rotation, he]⟩

#print axioms boundary_injective_of_length
#print axioms boundary_same_cycle_iff
end ProofPursuit.P3
