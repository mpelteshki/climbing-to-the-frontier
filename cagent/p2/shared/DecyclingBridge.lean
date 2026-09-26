import LowerBound

namespace Hypercube

def badFlag (p : Nat → Nat) (v : Nat) : Bool := decide (1 < p v)

def badVertices (order : List Nat) (p : Nat → Nat) : List Nat :=
  order.filter (badFlag p)

theorem good_endpoint_eq_one (d : Nat) (order : List Nat) (p : Nat → Nat)
    (hrec : endpointRecurrence d order p) (v : Nat) (hv : v ∈ order)
    (hgood : badFlag p v = false) : p v = 1 := by
  have hpos := endpoint_positive d order p hrec v hv
  simp only [badFlag, decide_eq_false_iff_not] at hgood
  omega

private theorem mem_le_sum_nat (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp
    · have h := ih ht
      simp only [List.sum_cons]
      omega

theorem bad_predecessor_forces_bad (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hrec : endpointRecurrence d order p)
    (u v : Nat) (hv : v ∈ order) (hu : u ∈ before order v)
    (hadj : adjacent d v u = true) (hbad : badFlag p u = true) :
    badFlag p v = true := by
  have hin : u ∈ (before order v).filter (adjacent d v) :=
    List.mem_filter.mpr ⟨hu, hadj⟩
  have hmap : p u ∈ (((before order v).filter (adjacent d v)).map p) :=
    List.mem_map_of_mem hin
  have hle := mem_le_sum_nat _ (p u) hmap
  have hrec' := hrec v hv
  have hb : 1 < p u := by simpa [badFlag] using hbad
  simp only [badFlag, decide_eq_true_iff]
  rw [hrec']
  omega

theorem before_filter_of_kept (order : List Nat) (keep : Nat → Bool)
    (v : Nat) (hv : keep v = true) :
    before (order.filter keep) v = (before order v).filter keep := by
  induction order with
  | nil => rfl
  | cons w ws ih =>
    by_cases heq : w = v
    · subst w
      simp [before, hv]
    · have hne : (w != v) = true := by simp [heq]
      cases hkeep : keep w <;>
        simpa [before, hne, hkeep] using ih

theorem after_filter_of_kept (order : List Nat) (keep : Nat → Bool)
    (v : Nat) (hv : keep v = true) :
    after (order.filter keep) v = (after order v).filter keep := by
  induction order with
  | nil => rfl
  | cons w ws ih =>
    by_cases heq : w = v
    · subst w
      simp [after, hv]
    · have hne : (w != v) = true := by simp [heq]
      cases hkeep : keep w <;>
        simpa [after, hne, hkeep] using ih

theorem after_mem_before_bridge (order : List Nat) (u v : Nat)
    (hn : order.Nodup) (hu : u ∈ order) (hv : v ∈ after order u) :
    u ∈ before order v := by
  have hpair : ([u, v]).Sublist order := by
    have hvsub : ([v]).Sublist (after order u) := List.singleton_sublist.mpr hv
    have hsub : (u :: after order u).Sublist order := by
      have hbase : (u :: after order u).Sublist
          (before order u ++ u :: after order u) :=
        List.sublist_append_right _ _
      simpa only [← split_at_vertex order u hu] using hbase
    exact (hvsub.cons_cons u).trans hsub
  exact ((append_vertex_sublist_iff_before order v [u] hn).mp hpair).2
    |>.mem (by simp)

theorem bad_successor (d : Nat) (order : List Nat) (p : Nat → Nat)
    (hn : order.Nodup) (hrec : endpointRecurrence d order p)
    (u v : Nat) (hu : u ∈ order) (hv : v ∈ after order u)
    (hadj : adjacent d u v = true) (hbad : badFlag p u = true) :
    badFlag p v = true := by
  have hvorder : v ∈ order := by
    have hsub : (after order u).Sublist order :=
      (List.drop_sublist 1 _).trans (List.dropWhile_sublist _)
    exact hsub.mem hv
  have hbefore := after_mem_before_bridge order u v hn hu hv
  exact bad_predecessor_forces_bad d order p hrec u v hvorder hbefore
    (by simpa [adjacent_symm] using hadj) hbad

private theorem sum_map_ge_length_add_bad_count (xs : List Nat)
    (p : Nat → Nat) (hpos : ∀ x ∈ xs, 1 ≤ p x) :
    xs.length + xs.countP (badFlag p) ≤ (xs.map p).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := hpos x (by simp)
    have hr : ∀ y ∈ rest, 1 ≤ p y := by
      intro y hy
      exact hpos y (by simp [hy])
    have hrest := ih hr
    simp only [List.length_cons, List.countP_cons, List.map_cons, List.sum_cons]
    by_cases hb : badFlag p x = true
    · have hpx : 2 ≤ p x := by
        have : 1 < p x := by simpa [badFlag] using hb
        omega
      simp [hb]
      omega
    · have hfalse : badFlag p x = false := by
        cases h : badFlag p x <;> simp_all
      simp [hfalse]
      omega

def badIncoming (d : Nat) (order : List Nat) (p : Nat → Nat) (v : Nat) : Nat :=
  ((before order v).filter (adjacent d v)).countP (badFlag p)

theorem bad_endpoint_local_bound (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hrec : endpointRecurrence d order p)
    (v : Nat) (hv : v ∈ order) (hb : badFlag p v = true) :
    indegree d order v + badIncoming d order p v ≤ p v := by
  have hmem : ∀ x ∈ (before order v).filter (adjacent d v), x ∈ order := by
    intro x hx
    exact (List.takeWhile_sublist (fun w : Nat => w != v)).mem
      (List.mem_filter.mp hx).1
  have hpos : ∀ x ∈ (before order v).filter (adjacent d v), 1 ≤ p x := by
    intro x hx
    exact endpoint_positive d order p hrec x (hmem x hx)
  have hsum := sum_map_ge_length_add_bad_count
    ((before order v).filter (adjacent d v)) p hpos
  have hr := hrec v hv
  have hbad : 1 < p v := by simpa [badFlag] using hb
  unfold indegree badIncoming
  omega

theorem badIncoming_eq_indegree_bad (d : Nat) (order : List Nat)
    (p : Nat → Nat) (v : Nat) (hb : badFlag p v = true) :
    badIncoming d order p v = indegree d (badVertices order p) v := by
  simp only [badIncoming, indegree, badVertices, List.countP_eq_length_filter,
    before_filter_of_kept order (badFlag p) v hb, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  exact Bool.and_comm ..

theorem bad_outdegree_eq_filtered (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p) (v : Nat)
    (hv : v ∈ order) (hb : badFlag p v = true) :
    outdegree d order v = outdegree d (badVertices order p) v := by
  simp only [outdegree, badVertices,
    after_filter_of_kept order (badFlag p) v hb, List.filter_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro w hw
  cases h : adjacent d v w with
  | false => simp
  | true =>
    have hbw := bad_successor d order p hn hrec v w hv hw h hb
    simp [hbw]

def totalOutdegree (d : Nat) (order : List Nat) : Nat :=
  (order.map (outdegree d order)).sum

theorem totalOutdegree_eq_edgeCount (d : Nat) (order : List Nat)
    (hn : order.Nodup) : totalOutdegree d order = edgeCount d order := by
  induction order with
  | nil => rfl
  | cons u rest ih =>
    have hu : u ∉ rest := (List.nodup_cons.mp hn).1
    have hr : rest.Nodup := (List.nodup_cons.mp hn).2
    have hfirst : outdegree d (u :: rest) u = rest.countP (adjacent d u) := by
      simp [outdegree, after, List.countP_eq_length_filter]
    have hrest : (rest.map (outdegree d (u :: rest))).sum =
        (rest.map (outdegree d rest)).sum := by
      congr 1
      apply List.map_congr_left
      intro w hw
      have hneq : u ≠ w := by
        intro he
        exact hu (he ▸ hw)
      have hne : (u != w) = true := by simp [hneq]
      simp [outdegree, after, hne]
    simp only [totalOutdegree, List.map_cons, List.sum_cons, hfirst, edgeCount]
    rw [hrest]
    have hih := ih hr
    change (rest.map (outdegree d rest)).sum = edgeCount d rest at hih
    rw [hih]

theorem badIncoming_total_eq_badOutdegree (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p) :
    ((badVertices order p).map (badIncoming d order p)).sum =
      ((badVertices order p).map (outdegree d order)).sum := by
  let bad := badVertices order p
  have hnodup : bad.Nodup := by
    exact (List.filter_sublist).nodup hn
  have hin : (bad.map (badIncoming d order p)).sum =
      totalIndegree d bad := by
    unfold totalIndegree
    congr 1
    apply List.map_congr_left
    intro v hv
    have hb : badFlag p v = true := (List.mem_filter.mp hv).2
    exact badIncoming_eq_indegree_bad d order p v hb
  have hout : (bad.map (outdegree d order)).sum =
      totalOutdegree d bad := by
    unfold totalOutdegree
    congr 1
    apply List.map_congr_left
    intro v hv
    obtain ⟨hvorder, hb⟩ := List.mem_filter.mp hv
    exact bad_outdegree_eq_filtered d order p hn hrec v hvorder hb
  rw [hin, hout, totalIndegree_eq_edgeCount d bad hnodup,
    totalOutdegree_eq_edgeCount d bad hnodup]

private theorem sum_map_le_nat (xs : List Nat) (f g : Nat → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    have hx := h x (by simp)
    have hr : ∀ y ∈ rest, f y ≤ g y := by
      intro y hy
      exact h y (by simp [hy])
    have hrest := ih hr
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_map_const_nat (xs : List Nat) (d : Nat) :
    (xs.map (fun _ => d)).sum = d * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Nat.mul_succ]
    omega

theorem bad_endpoints_ge_degree_budget (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p)
    (hdegree : ∀ v ∈ order,
      indegree d order v + outdegree d order v = d) :
    d * (badVertices order p).length ≤
      ((badVertices order p).map p).sum := by
  let bad := badVertices order p
  have hlocal : (bad.map (fun v =>
      indegree d order v + badIncoming d order p v)).sum ≤
      (bad.map p).sum := by
    apply sum_map_le_nat
    intro v hv
    obtain ⟨hvorder, hb⟩ := List.mem_filter.mp hv
    exact bad_endpoint_local_bound d order p hrec v hvorder hb
  rw [sum_map_add_nat] at hlocal
  have hbalance := badIncoming_total_eq_badOutdegree d order p hn hrec
  change (bad.map (badIncoming d order p)).sum =
    (bad.map (outdegree d order)).sum at hbalance
  rw [hbalance] at hlocal
  have hdegrees : (bad.map (fun v =>
      indegree d order v + outdegree d order v)).sum = d * bad.length := by
    have hmap : bad.map (fun v =>
        indegree d order v + outdegree d order v) = bad.map (fun _ => d) := by
      apply List.map_congr_left
      intro v hv
      exact hdegree v (List.filter_sublist.mem hv)
    rw [hmap]
    exact sum_map_const_nat bad d
  rw [sum_map_add_nat] at hdegrees
  change d * bad.length ≤ (bad.map p).sum
  omega

theorem regular_path_budget (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p) (hd : 1 ≤ d)
    (hdegree : ∀ v ∈ order,
      indegree d order v + outdegree d order v = d) :
    order.length + (d - 1) * (badVertices order p).length ≤
      (order.map p).sum := by
  let bad := badVertices order p
  let good := order.filter (fun v => !badFlag p v)
  have hbad := bad_endpoints_ge_degree_budget d order p hn hrec hdegree
  change d * bad.length ≤ (bad.map p).sum at hbad
  have hgood : (good.map p).sum = good.length := by
    have hmap : good.map p = good.map (fun _ => 1) := by
      apply List.map_congr_left
      intro v hv
      obtain ⟨hvorder, hg⟩ := List.mem_filter.mp hv
      have hgfalse : badFlag p v = false := by
        cases h : badFlag p v <;> simp_all
      exact good_endpoint_eq_one d order p hrec v hvorder hgfalse
    rw [hmap]
    induction good with
    | nil => rfl
    | cons x xs ih => simp [ih, Nat.add_comm]
  have hperm := List.filter_append_perm (badFlag p) order
  have hlen : bad.length + good.length = order.length := by
    simpa [bad, good, badVertices] using hperm.length_eq
  have hsum : (bad.map p).sum + (good.map p).sum =
      (order.map p).sum := by
    simpa [bad, good, badVertices, List.map_append, List.sum_append] using
      (hperm.map p).sum_nat
  have hd' : d = (d - 1) + 1 := by omega
  rw [hd', Nat.add_mul, Nat.one_mul] at hbad
  change order.length + (d - 1) * bad.length ≤ (order.map p).sum
  omega

theorem pathCount_regular_budget (d : Nat) (order : List Nat)
    (hn : order.Nodup) (hd : 1 ≤ d)
    (hdegree : ∀ v ∈ order,
      indegree d order v + outdegree d order v = d) :
    order.length + (d - 1) *
      (badVertices order (endCount d order)).length ≤ pathCount d order := by
  have hrec : endpointRecurrence d order (endCount d order) := by
    intro v hv
    exact endCount_recurrence d order v hn hv
  rw [pathCount_eq_sum_endCount d order hn]
  exact regular_path_budget d order (endCount d order) hn hrec hd hdegree

#print axioms bad_predecessor_forces_bad
#print axioms regular_path_budget
#print axioms pathCount_regular_budget

end Hypercube
