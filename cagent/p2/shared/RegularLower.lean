import Hypercube

namespace Hypercube

/-- Number of paths ending at each vertex, expressed independently of path enumeration. -/
def endpointRecurrence (d : Nat) (order : List Nat) (p : Nat → Nat) : Prop :=
  ∀ v ∈ order,
    p v = max 1 (((before order v).filter (adjacent d v)).map p).sum

def indegree (d : Nat) (order : List Nat) (v : Nat) : Nat :=
  ((before order v).filter (adjacent d v)).length

def outdegree (d : Nat) (order : List Nat) (v : Nat) : Nat :=
  ((after order v).filter (adjacent d v)).length

private theorem sum_map_ge_length (xs : List Nat) (p : Nat → Nat)
    (h : ∀ x ∈ xs, 1 ≤ p x) : xs.length ≤ (xs.map p).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, 1 ≤ p y := by
      intro y hy
      exact h y (by simp [hy])
    have hs := ih hxs
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem sum_map_le (xs : List Nat) (f g : Nat → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, f y ≤ g y := by
      intro y hy
      exact h y (by simp [hy])
    have hs := ih hxs
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_map_eq_pointwise (xs : List Nat) (f g : Nat → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x)
    (heq : (xs.map f).sum = (xs.map g).sum) :
    ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hys : ∀ x ∈ ys, f x ≤ g x := by
      intro x hx
      exact h x (by simp [hx])
    have hs := sum_map_le ys f g hys
    simp only [List.map_cons, List.sum_cons] at heq
    have hyeq : f y = g y := by omega
    have hseq : (ys.map f).sum = (ys.map g).sum := by omega
    intro x hx
    rcases List.mem_cons.mp hx with hxy | hxy
    · simpa [hxy] using hyeq
    · exact ih hys hseq x hxy

private theorem sum_map_one (xs : List Nat) :
    (xs.map (fun _ => 1)).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.add_comm]

theorem endpoint_positive (d : Nat) (order : List Nat) (p : Nat → Nat)
    (h : endpointRecurrence d order p) (v : Nat) (hv : v ∈ order) :
    1 ≤ p v := by
  rw [h v hv]
  exact Nat.le_max_left ..

theorem endpoint_ge_indegree (d : Nat) (order : List Nat) (p : Nat → Nat)
    (h : endpointRecurrence d order p) (v : Nat) (hv : v ∈ order) :
    indegree d order v ≤ p v := by
  have hmem : ∀ x ∈ (before order v).filter (adjacent d v), x ∈ order := by
    intro x hx
    exact (List.takeWhile_sublist (fun w : Nat => w != v)).mem
      (List.mem_filter.mp hx).1
  have hs := sum_map_ge_length ((before order v).filter (adjacent d v)) p
    (by intro x hx; exact endpoint_positive d order p h x (hmem x hx))
  rw [h v hv]
  exact Nat.le_trans hs (Nat.le_max_right ..)

private theorem regularAdjacentSymm (d u v : Nat) :
    adjacent d u v = adjacent d v u := by
  simp only [adjacent, Nat.xor_comm]

private theorem regularAdjacentSelfFalse (d v : Nat) : adjacent d v v = false := by
  simp [adjacent]
  intro k _
  exact Nat.ne_of_lt (Nat.two_pow_pos k)

private theorem regularSplitAtVertex (order : List Nat) (v : Nat)
    (hv : v ∈ order) : order = before order v ++ v :: after order v := by
  induction order with
  | nil => simp at hv
  | cons w ws ih =>
    by_cases h : w = v
    · subst w
      simp [before, after]
    · have hne : (w != v) = true := by simp [h]
      have hmem : v ∈ ws :=
        (List.mem_cons.mp hv).resolve_left (fun he => h he.symm)
      simpa [before, after, hne] using congrArg (w :: ·) (ih hmem)

private theorem after_mem_before (order : List Nat) (src v : Nat)
    (hn : order.Nodup) (hv : v ∈ after order src) :
    src ∈ before order v := by
  induction order with
  | nil => simp [after] at hv
  | cons head rest ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
    by_cases h : head = src
    · subst head
      have hvrest : v ∈ rest := by simpa [after] using hv
      have hneq : src ≠ v := by
        intro he
        exact hnot (he ▸ hvrest)
      have hne : (src != v) = true := by simp [hneq]
      simp [before, hne]
    · have hne : (head != src) = true := by simp [h]
      have hv' : v ∈ after rest src := by simpa [after, hne] using hv
      have hvrest : v ∈ rest := by
        have hsub : (after rest src).Sublist rest := by
          unfold after
          exact (List.drop_sublist 1 _).trans (List.dropWhile_sublist _)
        exact hsub.mem hv'
      have hneq : head ≠ v := by
        intro he
        exact hnot (he ▸ hvrest)
      have hnev : (head != v) = true := by simp [hneq]
      simp only [before, List.takeWhile_cons, hnev, ↓reduceIte,
        List.mem_cons]
      exact Or.inr (ih hnodup hv')

theorem indegree_add_outdegree (d : Nat) (order : List Nat) (v : Nat)
    (hv : v ∈ order) :
    indegree d order v + outdegree d order v =
      (order.filter (adjacent d v)).length := by
  have hf : (order.filter (adjacent d v)).length =
      ((before order v).filter (adjacent d v)).length +
      ((after order v).filter (adjacent d v)).length := by
    have hs := congrArg (fun xs => (xs.filter (adjacent d v)).length)
      (regularSplitAtVertex order v hv)
    simpa [List.filter_append, regularAdjacentSelfFalse] using hs
  exact hf.symm

theorem cube3_degree (order : List Nat) (h : IsLabelling 3 order)
    (v : Nat) (hv : v ∈ order) :
    indegree 3 order v + outdegree 3 order v = 3 := by
  rw [indegree_add_outdegree 3 order v hv]
  have hr : v ∈ List.range 8 := (List.Perm.mem_iff h).mp hv
  have hd : ∀ v ∈ List.range 8,
      ((List.range 8).filter (adjacent 3 v)).length = 3 := by decide
  exact (List.Perm.length_eq (h.filter (adjacent 3 v))).trans (hd v hr)

theorem cube4_degree (order : List Nat) (h : IsLabelling 4 order)
    (v : Nat) (hv : v ∈ order) :
    indegree 4 order v + outdegree 4 order v = 4 := by
  rw [indegree_add_outdegree 4 order v hv]
  have hr : v ∈ List.range 16 := (List.Perm.mem_iff h).mp hv
  have hd : ∀ v ∈ List.range 16,
      ((List.range 16).filter (adjacent 4 v)).length = 4 := by decide
  exact (List.Perm.length_eq (h.filter (adjacent 4 v))).trans (hd v hr)

/-- Count edges once, from each vertex to vertices later in an ordering. -/
def edgeCount (d : Nat) : List Nat → Nat
  | [] => 0
  | v :: rest => rest.countP (adjacent d v) + edgeCount d rest

def totalIndegree (d : Nat) (order : List Nat) : Nat :=
  (order.map (indegree d order)).sum

private theorem sum_map_add (xs : List Nat) (f g : Nat → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_adj_indicator (d u : Nat) (xs : List Nat) :
    (xs.map (fun x => if adjacent d u x then 1 else 0)).sum =
      xs.countP (adjacent d u) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    cases adjacent d u x <;> simp [Nat.add_comm]

private theorem indegree_cons_of_mem (d u w : Nat) (rest : List Nat)
    (hn : (u :: rest).Nodup) (hw : w ∈ rest) :
    indegree d (u :: rest) w =
      (if adjacent d u w then 1 else 0) + indegree d rest w := by
  have hu : u ∉ rest := (List.nodup_cons.mp hn).1
  have hneq : u ≠ w := by
    intro he
    exact hu (he ▸ hw)
  have hne : (u != w) = true := by simp [hneq]
  simp only [indegree, before, List.takeWhile_cons, hne, ↓reduceIte,
    List.filter_cons]
  rw [regularAdjacentSymm d w u]
  cases adjacent d u w <;> simp [Nat.add_comm]

theorem totalIndegree_eq_edgeCount (d : Nat) (order : List Nat)
    (hn : order.Nodup) : totalIndegree d order = edgeCount d order := by
  induction order with
  | nil => rfl
  | cons u rest ih =>
    have hr : rest.Nodup := (List.nodup_cons.mp hn).2
    have hfirst : indegree d (u :: rest) u = 0 := by
      simp [indegree, before]
    have hmap : (rest.map (indegree d (u :: rest))).sum =
        (rest.map (fun w =>
          (if adjacent d u w then 1 else 0) + indegree d rest w)).sum := by
      congr 1
      apply List.map_congr_left
      intro w hw
      exact indegree_cons_of_mem d u w rest hn hw
    have hrest : (rest.map (indegree d rest)).sum = edgeCount d rest :=
      ih hr
    simp only [totalIndegree, List.map_cons, List.sum_cons, hfirst,
      Nat.zero_add, edgeCount]
    rw [hmap, sum_map_add, sum_adj_indicator, hrest]

private theorem edgeCount_swap (d u v : Nat) (rest : List Nat) :
    edgeCount d (u :: v :: rest) = edgeCount d (v :: u :: rest) := by
  simp only [edgeCount, List.countP_cons]
  rw [regularAdjacentSymm d u v]
  omega

theorem edgeCount_perm (d : Nat) {xs ys : List Nat} (h : xs.Perm ys) :
    edgeCount d xs = edgeCount d ys := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    simp only [edgeCount]
    have hc : l₁.countP (adjacent d x) = l₂.countP (adjacent d x) :=
      List.Perm.countP_eq _ ‹l₁.Perm l₂›
    omega
  | @swap x y l => exact (edgeCount_swap d x y l).symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem edgeCount_cube3 (order : List Nat) (h : IsLabelling 3 order) :
    edgeCount 3 order = 12 := by
  rw [edgeCount_perm 3 h]
  decide

theorem edgeCount_cube4 (order : List Nat) (h : IsLabelling 4 order) :
    edgeCount 4 order = 32 := by
  rw [edgeCount_perm 4 h]
  decide

theorem endpoint_eq_indegree_tail (d u : Nat) (rest : List Nat) (p : Nat → Nat)
    (hn : (u :: rest).Nodup)
    (hrec : endpointRecurrence d (u :: rest) p)
    (hbound : ((u :: rest).map p).sum ≤ edgeCount d (u :: rest) + 1) :
    ∀ v ∈ rest, p v = indegree d (u :: rest) v := by
  have hu : p u = 1 := by
    have h := hrec u (by simp)
    simpa [endpointRecurrence, before] using h
  have hdeg : indegree d (u :: rest) u = 0 := by simp [indegree, before]
  have hle : ∀ v ∈ rest, indegree d (u :: rest) v ≤ p v := by
    intro v hv
    exact endpoint_ge_indegree d (u :: rest) p hrec v (by simp [hv])
  have hsum := sum_map_le rest (indegree d (u :: rest)) p hle
  have htotal := totalIndegree_eq_edgeCount d (u :: rest) hn
  have heq : (rest.map (indegree d (u :: rest))).sum = (rest.map p).sum := by
    simp only [totalIndegree, List.map_cons, List.sum_cons, hdeg,
      Nat.zero_add] at htotal
    simp only [List.map_cons, List.sum_cons, hu] at hbound
    omega
  intro v hv
  exact (sum_map_eq_pointwise rest (indegree d (u :: rest)) p hle heq v hv).symm

theorem predecessor_endpoint_one (d head : Nat) (rest : List Nat) (p : Nat → Nat)
    (hn : (head :: rest).Nodup)
    (hrec : endpointRecurrence d (head :: rest) p)
    (hbound : ((head :: rest).map p).sum ≤ edgeCount d (head :: rest) + 1)
    (v : Nat) (hv : v ∈ rest) (src : Nat)
    (hsrc : src ∈ before (head :: rest) v)
    (hadj : adjacent d v src = true) : p src = 1 := by
  let incoming := (before (head :: rest) v).filter (adjacent d v)
  have hmem : src ∈ incoming := List.mem_filter.mpr ⟨hsrc, hadj⟩
  have hpositive : ∀ x ∈ incoming, 1 ≤ p x := by
    intro x hx
    have hbefore := (List.mem_filter.mp hx).1
    exact endpoint_positive d (head :: rest) p hrec x
      ((List.takeWhile_sublist (fun w : Nat => w != v)).mem hbefore)
  have hsumge := sum_map_ge_length incoming p hpositive
  have hlength : 1 ≤ incoming.length := List.length_pos_of_mem hmem
  have htail := endpoint_eq_indegree_tail d head rest p hn hrec hbound v hv
  have hrv := hrec v (by simp [hv])
  have hsum : (incoming.map p).sum = incoming.length := by
    change p v = max 1 (incoming.map p).sum at hrv
    change p v = incoming.length at htail
    omega
  have hones : (incoming.map (fun _ => 1)).sum = (incoming.map p).sum := by
    rw [sum_map_one, hsum]
  have hpoint := sum_map_eq_pointwise incoming (fun _ => 1) p hpositive hones src hmem
  exact hpoint.symm

theorem bad_endpoint_is_sink (d head : Nat) (rest : List Nat) (p : Nat → Nat)
    (hn : (head :: rest).Nodup)
    (hrec : endpointRecurrence d (head :: rest) p)
    (hbound : ((head :: rest).map p).sum ≤ edgeCount d (head :: rest) + 1)
    (src : Nat) (hbad : 1 < p src) :
    outdegree d (head :: rest) src = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hex : ∃ v, v ∈ (after (head :: rest) src).filter (adjacent d src) :=
    List.length_pos_iff_exists_mem.mp hpos
  obtain ⟨v, hv⟩ := hex
  have hvafter : v ∈ after (head :: rest) src := (List.mem_filter.mp hv).1
  have hadj : adjacent d v src = true := by
    rw [← regularAdjacentSymm d src v]
    exact (List.mem_filter.mp hv).2
  have hbefore := after_mem_before (head :: rest) src v hn hvafter
  have hvorder : v ∈ head :: rest := by
    have hsub : (after (head :: rest) src).Sublist (head :: rest) := by
      unfold after
      exact (List.drop_sublist 1 _).trans (List.dropWhile_sublist _)
    exact hsub.mem hvafter
  have hneq : v ≠ head := by
    intro he
    subst v
    simp [before] at hbefore
  have hvrest : v ∈ rest :=
    (List.mem_cons.mp hvorder).resolve_left hneq
  have hone := predecessor_endpoint_one d head rest p hn hrec hbound v hvrest src
    hbefore hadj
  omega

private theorem sum_two_class (xs : List Nat) (f : Nat → Nat) (bad : Nat → Bool)
    (k : Nat) (h : ∀ x ∈ xs, f x = if bad x then k + 1 else 1) :
    (xs.map f).sum = xs.length + k * xs.countP bad := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, f y = if bad y then k + 1 else 1 := by
      intro y hy
      exact h y (by simp [hy])
    have hs := ih hxs
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      List.countP_cons, hx]
    cases bad x <;> simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] at * <;> omega

private theorem regular_profile_impossible (d m n : Nat)
    (order : List Nat) (p : Nat → Nat)
    (hn : order.Nodup) (hlen : order.length = n)
    (hm : edgeCount d order = m)
    (hdpos : 1 ≤ d)
    (hdegree : ∀ v ∈ order,
      indegree d order v + outdegree d order v = d)
    (harith : ∀ b : Nat, m ≠ n - 1 + (d - 1) * b)
    (hrec : endpointRecurrence d order p) :
    m + 2 ≤ (order.map p).sum := by
  by_cases hgoal : m + 2 ≤ (order.map p).sum
  · exact hgoal
  have hbound : (order.map p).sum ≤ edgeCount d order + 1 := by omega
  cases order with
  | nil =>
    have hmzero : m = 0 := by simpa [edgeCount] using hm.symm
    have hnzero : n = 0 := by simpa using hlen.symm
    have hc := harith 0
    simp [hmzero, hnzero] at hc
  | cons head rest =>
    have htail := endpoint_eq_indegree_tail d head rest p hn hrec hbound
    have hclass : ∀ v ∈ rest,
        indegree d (head :: rest) v =
          if decide (1 < p v) then d else 1 := by
      intro v hv
      have hvorder : v ∈ head :: rest := by simp [hv]
      have hpge := endpoint_positive d (head :: rest) p hrec v hvorder
      have heq := htail v hv
      by_cases hb : 1 < p v
      · have hsink := bad_endpoint_is_sink d head rest p hn hrec hbound v hb
        have hd := hdegree v hvorder
        simp [hb]
        omega
      · simp [hb]
        omega
    have hsum := sum_two_class rest (indegree d (head :: rest))
      (fun v => decide (1 < p v)) (d - 1) (by
        intro v hv
        have hc := hclass v hv
        by_cases hb : 1 < p v
        · simpa [hb, Nat.sub_add_cancel hdpos] using hc
        · simpa [hb] using hc)
    have htotal := totalIndegree_eq_edgeCount d (head :: rest) hn
    have hhead : indegree d (head :: rest) head = 0 := by
      simp [indegree, before]
    simp only [totalIndegree, List.map_cons, List.sum_cons, hhead,
      Nat.zero_add] at htotal
    have hrestlen : rest.length = n - 1 := by simp at hlen; omega
    have hformula : m = n - 1 + (d - 1) *
        rest.countP (fun v => decide (1 < p v)) := by
      omega
    exact (harith _ hformula).elim

theorem regularLower3 (order : List Nat) (p : Nat → Nat)
    (h : IsLabelling 3 order) (hrec : endpointRecurrence 3 order p) :
    14 ≤ (order.map p).sum := by
  have hn : order.Nodup := (List.Perm.nodup_iff h).mpr List.nodup_range
  have hlen : order.length = 8 := by
    simpa using List.Perm.length_eq h
  exact regular_profile_impossible 3 12 8 order p hn hlen
    (edgeCount_cube3 order h) (by omega)
    (by intro v hv; exact cube3_degree order h v hv)
    (by intro b hb; omega) hrec

theorem regularLower4 (order : List Nat) (p : Nat → Nat)
    (h : IsLabelling 4 order) (hrec : endpointRecurrence 4 order p) :
    34 ≤ (order.map p).sum := by
  have hn : order.Nodup := (List.Perm.nodup_iff h).mpr List.nodup_range
  have hlen : order.length = 16 := by
    simpa using List.Perm.length_eq h
  exact regular_profile_impossible 4 32 16 order p hn hlen
    (edgeCount_cube4 order h) (by omega)
    (by intro v hv; exact cube4_degree order h v hv)
    (by intro b hb; omega) hrec

#print axioms endpoint_ge_indegree
#print axioms totalIndegree_eq_edgeCount
#print axioms edgeCount_cube3
#print axioms edgeCount_cube4
#print axioms regularLower3
#print axioms regularLower4

end Hypercube
