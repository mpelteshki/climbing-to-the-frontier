import ProofPursuit.P3.Basic

namespace ProofPursuit.P3

/-- Enumerate positive decreasing partitions, with length and largest-part bounds. -/
def enumerate : Nat → Nat → Nat → List State
  | 0, n, _ => if n = 0 then [[]] else []
  | fuel+1, n, cap =>
    if n = 0 then [[]]
    else (List.range (min n cap)).flatMap fun a =>
      (enumerate fuel (n-(a+1)) (a+1)).map ((a+1) :: ·)

theorem length_le_sum {s : State} (h : ∀ a ∈ s, 0 < a) : s.length ≤ s.sum := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have ha := h a (by simp)
    have hs : ∀ b ∈ s, 0 < b := by intro b hb; exact h b (by simp [hb])
    have hi := ih hs
    simp only [List.length_cons, List.sum_cons]
    omega

theorem enumerate_complete {fuel n cap : Nat} {s : State}
    (hp : IsPartition n s) (hl : s.length ≤ fuel) (hc : ∀ a ∈ s, a ≤ cap) :
    s ∈ enumerate fuel n cap := by
  induction fuel generalizing n cap s with
  | zero =>
    have hs : s = [] := by cases s <;> simp_all
    subst s
    simp [IsPartition] at hp
    simp [enumerate, hp]
  | succ fuel ih =>
    rcases hp with ⟨hsum, hpos, hsort⟩
    cases s with
    | nil => simp only [List.sum_nil] at hsum; subst n; simp [enumerate]
    | cons a tail =>
      have ha : 0 < a := hpos a (by simp)
      have hac : a ≤ cap := hc a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      have hn : n ≠ 0 := by omega
      have htSum : tail.sum = n-a := by simp only [List.sum_cons] at hsum; omega
      have htPos : ∀ b ∈ tail, 0 < b := by intro b hb; exact hpos b (by simp [hb])
      have hpair := List.pairwise_cons.mp hsort
      have hlen : tail.length ≤ fuel := by simp only [List.length_cons] at hl; omega
      have htail := ih ⟨htSum, htPos, hpair.2⟩ hlen hpair.1
      simp only [enumerate, ite_eq_right hn, List.mem_flatMap, List.mem_map]
      refine ⟨a-1, ?_, tail, ?_, ?_⟩
      · simp only [List.mem_range]; omega
      · simpa [Nat.sub_add_cancel ha] using htail
      · simp [Nat.sub_add_cancel ha]

def partitions (n : Nat) : List State := enumerate n n n

theorem partitions_complete {n : Nat} {s : State} (hp : IsPartition n s) :
    s ∈ partitions n := by
  have hsum := hp.1
  apply enumerate_complete hp
  · have h := length_le_sum hp.2.1; omega
  · intro a ha
    have h : a ≤ s.sum := by
      clear hp hsum
      induction s with
      | nil => simp at ha
      | cons b tail ih =>
        simp only [List.mem_cons] at ha
        simp only [List.sum_cons]
        rcases ha with rfl | ht
        · omega
        · have := ih ht; omega
    omega

/-- Executable certificate condition; the kernel reduces it, not native code. -/
def upperCheck (n d p : Nat) : Bool :=
  (partitions n).all fun s => decide (run p (run d s) = run d s)

def exactCheck (s : State) (d p : Nat) : Bool :=
  decide (run p (run d s) = run d s) &&
  (List.range d).all fun t => decide (run p (run t s) ≠ run t s)

theorem upper_of_check {n d p : Nat} (hp : 0 < p) (h : upperCheck n d p = true) :
    ∀ s, IsPartition n s → ∃ t, t ≤ d ∧ DepthExactly s t := by
  intro s hs
  have he := List.all_eq_true.mp h s (partitions_complete hs)
  apply depth_exists_of_cyclic_run
  exact ⟨p, hp, of_decide_eq_true he⟩

theorem exact_of_check {s : State} {d p : Nat} (hp : 0 < p) (h : exactCheck s d p = true) :
    DepthExactly s d := by
  simp only [exactCheck, Bool.and_eq_true] at h
  apply depth_of_period_checks hp (of_decide_eq_true h.1)
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h.2 t (List.mem_range.mpr ht))

end ProofPursuit.P3
