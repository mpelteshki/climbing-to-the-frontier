import LowerBound
import Decycling5

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

theorem good_indegree_budget (d : Nat) (order : List Nat)
    (p : Nat → Nat) (horder : order ≠ [])
    (hrec : endpointRecurrence d order p) :
    ((order.filter (fun v => !badFlag p v)).map (indegree d order)).sum + 1 ≤
      (order.filter (fun v => !badFlag p v)).length := by
  obtain ⟨head, rest, rfl⟩ := List.exists_cons_of_ne_nil horder
  have hhead : p head = 1 := by
    rw [hrec head (by simp)]
    simp [before]
  have hheadgood : badFlag p head = false := by
    simp [badFlag, hhead]
  have hheadin : indegree d (head :: rest) head = 0 := by
    simp [indegree, before]
  simp only [List.filter_cons, hheadgood, Bool.not_false, ↓reduceIte,
    List.map_cons, List.sum_cons, List.length_cons, hheadin, Nat.zero_add]
  have htail : ∀ v ∈ rest.filter (fun v => !badFlag p v),
      indegree d (head :: rest) v ≤ 1 := by
    intro v hv
    obtain ⟨hvr, hgv⟩ := List.mem_filter.mp hv
    have hvorder : v ∈ head :: rest := by simp [hvr]
    have hg : badFlag p v = false := by
      cases h : badFlag p v <;> simp_all
    have hpe := good_endpoint_eq_one d (head :: rest) p hrec v hvorder hg
    exact hpe ▸ endpoint_ge_indegree d (head :: rest) p hrec v hvorder
  have hsum := sum_map_le_nat (rest.filter (fun v => !badFlag p v))
    (indegree d (head :: rest)) (fun _ => 1) htail
  have hone : ((rest.filter (fun v => !badFlag p v)).map (fun _ => 1)).sum =
      (rest.filter (fun v => !badFlag p v)).length := by
    induction rest.filter (fun v => !badFlag p v) with
    | nil => rfl
    | cons v vs ih => simp [ih, Nat.add_comm]
  omega

theorem regular_edge_budget (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup) (horder : order ≠ [])
    (hrec : endpointRecurrence d order p) (hd : 1 ≤ d)
    (hdegree : ∀ v ∈ order,
      indegree d order v + outdegree d order v = d) :
    edgeCount d order + 1 + edgeCount d (badVertices order p) ≤
      order.length + (d - 1) * (badVertices order p).length := by
  let bad := badVertices order p
  let good := order.filter (fun v => !badFlag p v)
  have hbadout : (bad.map (outdegree d order)).sum = edgeCount d bad := by
    have hfiltered : (bad.map (outdegree d order)).sum =
        totalOutdegree d bad := by
      unfold totalOutdegree
      congr 1
      apply List.map_congr_left
      intro v hv
      obtain ⟨hvorder, hb⟩ := List.mem_filter.mp hv
      exact bad_outdegree_eq_filtered d order p hn hrec v hvorder hb
    rw [hfiltered]
    exact totalOutdegree_eq_edgeCount d bad
      ((List.filter_sublist).nodup hn)
  have hbaddegree : d * bad.length =
      (bad.map (indegree d order)).sum + edgeCount d bad := by
    have hmap : bad.map (fun v =>
        indegree d order v + outdegree d order v) =
        bad.map (fun _ => d) := by
      apply List.map_congr_left
      intro v hv
      exact hdegree v (List.filter_sublist.mem hv)
    have hsum := congrArg List.sum hmap
    rw [sum_map_add_nat, sum_map_const_nat, hbadout] at hsum
    exact hsum.symm
  have hperm := List.filter_append_perm (badFlag p) order
  have hlen : bad.length + good.length = order.length := by
    simpa [bad, good, badVertices] using hperm.length_eq
  have hsum : (bad.map (indegree d order)).sum +
      (good.map (indegree d order)).sum = edgeCount d order := by
    have hsum' : (bad.map (indegree d order)).sum +
        (good.map (indegree d order)).sum =
        (order.map (indegree d order)).sum := by
      simpa [bad, good, badVertices, List.map_append, List.sum_append] using
        (hperm.map (indegree d order)).sum_nat
    rw [hsum']
    exact totalIndegree_eq_edgeCount d order hn
  have hgood : (good.map (indegree d order)).sum + 1 ≤ good.length := by
    exact good_indegree_budget d order p horder hrec
  have hd' : d = (d - 1) + 1 := by omega
  have hmul : d * bad.length = (d - 1) * bad.length + bad.length := by
    calc
      d * bad.length = ((d - 1) + 1) * bad.length := by rw [← hd']
      _ = (d - 1) * bad.length + bad.length := by simp [Nat.add_mul]
  change edgeCount d order + 1 + edgeCount d bad ≤
    order.length + (d - 1) * bad.length
  omega

theorem cube5_degree (order : List Nat) (h : IsLabelling 5 order)
    (v : Nat) (hv : v ∈ order) :
    indegree 5 order v + outdegree 5 order v = 5 := by
  rw [indegree_add_outdegree 5 order v hv]
  have hr : v ∈ List.range 32 := (List.Perm.mem_iff h).mp hv
  have hd : ∀ v ∈ List.range 32,
      ((List.range 32).filter (adjacent 5 v)).length = 5 := by decide
  exact (List.Perm.length_eq (h.filter (adjacent 5 v))).trans (hd v hr)

theorem edgeCount_cube5 (order : List Nat) (h : IsLabelling 5 order) :
    edgeCount 5 order = 80 := by
  rw [edgeCount_perm 5 h]
  decide

theorem q5_bad_profile (order : List Nat) (p : Nat → Nat)
    (h : IsLabelling 5 order) (hrec : endpointRecurrence 5 order p)
    (hsmall : (badVertices order p).length ≤ 13) :
    (badVertices order p).length = 13 ∧
    edgeCount 5 (badVertices order p) ≤ 3 := by
  have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
  have hlen : order.length = 32 := by simpa using h.length_eq
  have hnonempty : order ≠ [] := by
    intro he
    simp [he] at hlen
  have hbudget := regular_edge_budget 5 order p hn hnonempty hrec
    (by omega) (by intro v hv; exact cube5_degree order h v hv)
  rw [edgeCount_cube5 order h, hlen] at hbudget
  constructor <;> omega

theorem one_indegree_edge_budget (d : Nat) (vertices : List Nat)
    (hn : vertices.Nodup) (hne : vertices ≠ [])
    (hdegree : ∀ v ∈ vertices, indegree d vertices v ≤ 1) :
    edgeCount d vertices + 1 ≤ vertices.length := by
  obtain ⟨head, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hzero : indegree d (head :: rest) head = 0 := by
    simp [indegree, before]
  have hrest : ∀ v ∈ rest, indegree d (head :: rest) v ≤ 1 := by
    intro v hv
    exact hdegree v (by simp [hv])
  have hsum := sum_map_le_nat rest (indegree d (head :: rest))
    (fun _ => 1) hrest
  have hone : (rest.map (fun _ => 1)).sum = rest.length := by
    simpa using sum_map_const_nat rest 1
  have heq := totalIndegree_eq_edgeCount d (head :: rest) hn
  simp only [totalIndegree, List.map_cons, List.sum_cons, hzero, Nat.zero_add]
    at heq
  simp only [List.length_cons]
  omega

theorem indegree_filter_le (d : Nat) (order : List Nat)
    (keep : Nat → Bool) (v : Nat) (hv : keep v = true) :
    indegree d (order.filter keep) v ≤ indegree d order v := by
  unfold indegree
  rw [before_filter_of_kept order keep v hv]
  have hs : ((before order v).filter keep).Sublist (before order v) :=
    List.filter_sublist
  exact (hs.filter (adjacent d v)).length_le

theorem edgeCount_good_subset (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p)
    (c : List Nat) (hc : c.Nodup) (hcne : c ≠ [])
    (hsubset : c ⊆ order)
    (hgood : ∀ v ∈ c, badFlag p v = false) :
    edgeCount d c + 1 ≤ c.length := by
  let selected := order.filter (fun v => decide (v ∈ c))
  have hnselected : selected.Nodup := by
    exact List.filter_sublist.nodup hn
  have hperm : selected.Perm c := by
    apply (List.perm_ext_iff_of_nodup hnselected hc).mpr
    intro v
    simp only [selected, List.mem_filter, decide_eq_true_iff]
    exact ⟨fun h => h.2, fun h => ⟨hsubset h, h⟩⟩
  have hselne : selected ≠ [] := by
    intro he
    exact hcne ((he ▸ hperm).nil_eq.symm)
  have hdegree : ∀ v ∈ selected, indegree d selected v ≤ 1 := by
    intro v hv
    have hvorder : v ∈ order := (List.mem_filter.mp hv).1
    have hvc : v ∈ c := by simpa [selected] using (List.mem_filter.mp hv).2
    have hpe := good_endpoint_eq_one d order p hrec v hvorder (hgood v hvc)
    have hle := indegree_filter_le d order (fun x => decide (x ∈ c)) v
      (by simpa [selected] using (List.mem_filter.mp hv).2)
    change indegree d selected v ≤ indegree d order v at hle
    have hrecdeg := endpoint_ge_indegree d order p hrec v hvorder
    omega
  have hbudget := one_indegree_edge_budget d selected hnselected hselne hdegree
  rw [edgeCount_perm d hperm, hperm.length_eq] at hbudget
  exact hbudget

theorem edge_rich_subset_hits_bad (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p)
    (c : List Nat) (hc : c.Nodup) (hcne : c ≠ [])
    (hsubset : c ⊆ order)
    (hedges : c.length ≤ edgeCount d c) :
    ∃ v ∈ c, badFlag p v = true := by
  by_cases hex : ∃ v ∈ c, badFlag p v = true
  · exact hex
  have hnone := hex
  have hgood : ∀ v ∈ c, badFlag p v = false := by
    intro v hv
    cases hb : badFlag p v with
    | false => rfl
    | true => exact False.elim (hnone ⟨v, hv, hb⟩)
  have hbudget := edgeCount_good_subset d order p hn hrec c hc hcne
    hsubset hgood
  omega

theorem edge_rich_family_hits_bad (d : Nat) (order : List Nat)
    (p : Nat → Nat) (hn : order.Nodup)
    (hrec : endpointRecurrence d order p)
    (cycles : List (List Nat))
    (hvalid : ∀ c ∈ cycles,
      c.Nodup ∧ c ≠ [] ∧ c ⊆ order ∧ c.length ≤ edgeCount d c) :
    cycles.all (fun c => c.any (badVertices order p).contains) = true := by
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨hcn, hcne, hsub, hedge⟩ := hvalid c hc
  obtain ⟨v, hvc, hb⟩ := edge_rich_subset_hits_bad d order p hn hrec
    c hcn hcne hsub hedge
  apply List.any_eq_true.mpr
  refine ⟨v, hvc, ?_⟩
  exact List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨hsub hvc, hb⟩)

theorem q5_shortCycles_hit (order : List Nat) (p : Nat → Nat)
    (h : IsLabelling 5 order) (hrec : endpointRecurrence 5 order p) :
    Decycling5.shortCyclesHit (badVertices order p) = true := by
  have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
  have hrange : ∀ c ∈ Decycling5.shortCycles,
      c ⊆ List.range 32 := Decycling5.shortCycles_subset_range
  have hvalid : ∀ c ∈ Decycling5.shortCycles,
      c.Nodup ∧ c ≠ [] ∧ c ⊆ order ∧ c.length ≤ edgeCount 5 c := by
    intro c hc
    obtain ⟨hcn, hcne, hedge⟩ := Decycling5.shortCycles_edge_rich c hc
    refine ⟨hcn, hcne, ?_, hedge⟩
    intro v hv
    exact (List.Perm.mem_iff h).mpr (hrange c hc hv)
  exact edge_rich_family_hits_bad 5 order p hn hrec
    Decycling5.shortCycles hvalid

theorem pathCount_lower5_of_search_and_edges (order : List Nat)
    (h : IsLabelling 5 order)
    (hcheck : Decycling5.search 13 [] = true)
    (hedgeBridge : ∀ bad : List Nat, bad.Nodup →
      bad ⊆ List.range 32 →
      Decycling5.internalEdges bad ≤ edgeCount 5 bad) :
    88 ≤ pathCount 5 order := by
  have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
  let p := endCount 5 order
  let bad := badVertices order p
  have hrec : endpointRecurrence 5 order p := by
    intro v hv
    exact endCount_recurrence 5 order v hn hv
  have hbudget := pathCount_regular_budget 5 order hn (by omega)
    (by intro v hv; exact cube5_degree order h v hv)
  have hlen : order.length = 32 := by simpa using h.length_eq
  rw [hlen] at hbudget
  by_cases hmany : 14 ≤ bad.length
  · change 32 + (5 - 1) * bad.length ≤ pathCount 5 order at hbudget
    omega
  · have hsmall : bad.length ≤ 13 := by omega
    have ⟨_, heB⟩ := q5_bad_profile order p h hrec hsmall
    change edgeCount 5 bad ≤ 3 at heB
    have hbn : bad.Nodup := List.filter_sublist.nodup hn
    have hbr : bad ⊆ List.range 32 := by
      intro v hv
      exact (List.Perm.mem_iff h).mp (List.filter_sublist.mem hv)
    have hedge : Decycling5.internalEdges bad ≤ 3 := by
      have hle := hedgeBridge bad hbn hbr
      omega
    have hhit := q5_shortCycles_hit order p h hrec
    exact False.elim (Decycling5.no_thirteen_of_search
      hcheck bad hbn hsmall hedge hhit)

#print axioms bad_predecessor_forces_bad
#print axioms regular_path_budget
#print axioms pathCount_regular_budget
#print axioms regular_edge_budget
#print axioms q5_bad_profile
#print axioms edge_rich_subset_hits_bad
#print axioms q5_shortCycles_hit
#print axioms pathCount_lower5_of_search_and_edges

end Hypercube
