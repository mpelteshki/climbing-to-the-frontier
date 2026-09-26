import Fast
import RegularLower

namespace Hypercube

theorem adjacent_symm (d u v : Nat) : adjacent d u v = adjacent d v u := by
  simp only [adjacent, Nat.xor_comm]

theorem adjacent_self_false (d v : Nat) : adjacent d v v = false := by
  simp [adjacent]
  intro x _
  exact Nat.ne_of_lt (Nat.two_pow_pos x)

theorem singleton_mem_paths (d : Nat) (order : List Nat) (v : Nat)
    (hv : v ∈ order) (hvalley : valley d order v = true) :
    [v] ∈ paths d order := by
  apply (mem_paths d order [v]).mpr
  exact ⟨v, [], rfl, hv, hvalley, List.nil_sublist _, trivial⟩

theorem split_at_vertex (order : List Nat) (v : Nat) (hv : v ∈ order) :
    order = before order v ++ v :: after order v := by
  induction order with
  | nil => simp at hv
  | cons w ws ih =>
    by_cases h : w = v
    · subst w
      simp [before, after]
    · have hne : (w != v) = true := by simp [h]
      have hmem : v ∈ ws := (List.mem_cons.mp hv).resolve_left (fun he => h he.symm)
      simpa [before, after, hne] using congrArg (w :: ·) (ih hmem)

def lastFrom (v : Nat) : List Nat → Nat
  | [] => v
  | w :: ws => lastFrom w ws

theorem lastFrom_append_vertex (v u : Nat) (tail : List Nat) :
    lastFrom v (tail ++ [u]) = u := by
  induction tail generalizing v with
  | nil => rfl
  | cons w ws ih => exact ih w

theorem chain_append_vertex (d u v : Nat) (tail : List Nat) :
    ChainFrom d u (tail ++ [v]) ↔
      ChainFrom d u tail ∧ adjacent d (lastFrom u tail) v = true := by
  induction tail generalizing u with
  | nil => simp [ChainFrom, lastFrom]
  | cons w ws ih =>
    simp only [List.cons_append, ChainFrom, lastFrom, ih, and_assoc]

theorem cons_sublist_iff_after (order : List Nat) (v : Nat) (tail : List Nat)
    (hn : order.Nodup) :
    (v :: tail).Sublist order ↔ v ∈ order ∧ tail.Sublist (after order v) := by
  induction order with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hw, hws⟩ := List.nodup_cons.mp hn
    by_cases h : w = v
    · subst w
      constructor
      · intro hs
        have ht : tail.Sublist ws := by
          rcases List.sublist_cons_iff.mp hs with hskip | ⟨t, heq, ht⟩
          · exact False.elim (hw (hskip.mem (by simp)))
          · exact (List.cons.inj heq).2 ▸ ht
        exact ⟨by simp, by simpa [after] using ht⟩
      · rintro ⟨_, ht⟩
        exact List.Sublist.cons_cons _ (by simpa [after] using ht)
    · have hne : (w != v) = true := by simp [h]
      have hvnot : v ≠ w := Ne.symm h
      constructor
      · intro hs
        have hs' : (v :: tail).Sublist ws := by
          rcases List.sublist_cons_iff.mp hs with hs' | ⟨t, heq, ht⟩
          · exact hs'
          · exact False.elim (hvnot (List.cons.inj heq).1)
        obtain ⟨hv, ht⟩ := ih hws |>.mp hs'
        exact ⟨by simp [hv], by simpa [after, hne] using ht⟩
      · rintro ⟨hv, ht⟩
        have hv' : v ∈ ws := (List.mem_cons.mp hv).resolve_left hvnot
        have hs' := (ih hws).mpr ⟨hv', by simpa [after, hne] using ht⟩
        exact hs'.cons w

theorem cons_mem_paths_iff (d : Nat) (order : List Nat) (v : Nat)
    (tail : List Nat) (hn : order.Nodup) :
    v :: tail ∈ paths d order ↔
      (v :: tail).Sublist order ∧ valley d order v = true ∧ ChainFrom d v tail := by
  rw [mem_paths]
  constructor
  · rintro ⟨w, rest, heq, hw, hval, hs, hc⟩
    have hhead := (List.cons.inj heq).1
    have htail := (List.cons.inj heq).2
    subst w
    subst rest
    exact ⟨(cons_sublist_iff_after order v tail hn).mpr ⟨hw, hs⟩, hval, hc⟩
  · rintro ⟨hs, hval, hc⟩
    obtain ⟨hv, ht⟩ := (cons_sublist_iff_after order v tail hn).mp hs
    exact ⟨v, tail, rfl, hv, hval, ht, hc⟩

theorem append_vertex_sublist_iff_before (order : List Nat) (v : Nat)
    (xs : List Nat) (hn : order.Nodup) :
    (xs ++ [v]).Sublist order ↔
      v ∈ order ∧ xs.Sublist (before order v) := by
  constructor
  · intro hs
    obtain ⟨r₁, r₂, heq, hp, hv⟩ := List.append_sublist_iff.mp hs
    have hmem : v ∈ r₂ := hv.mem (by simp)
    have hnot : v ∉ r₁ := by
      intro hin
      have hdisj := (List.nodup_append.mp (heq ▸ hn)).2.2
      exact hdisj v hin v hmem rfl
    have hpos : ∀ x ∈ r₁, (x != v) = true := by
      intro x hx
      have hne : x ≠ v := by
        intro he
        subst x
        exact hnot hx
      simp [hne]
    have hbefore : before order v = r₁ ++ before r₂ v := by
      rw [heq]
      exact List.takeWhile_append_of_pos hpos
    exact ⟨hs.mem (by simp), hbefore ▸ List.sublist_append_of_sublist_left hp⟩
  · rintro ⟨hv, hp⟩
    rw [split_at_vertex order v hv]
    have h : (xs ++ [v]).Sublist (before order v ++ [v]) :=
      hp.append (List.Sublist.refl [v])
    simpa [List.append_assoc] using List.sublist_append_of_sublist_left (l₂ := after order v) h

theorem append_vertex_mem_paths_iff (d : Nat) (order : List Nat)
    (u : Nat) (tail : List Nat) (v : Nat) (hn : order.Nodup) :
    u :: (tail ++ [v]) ∈ paths d order ↔
      u :: tail ∈ paths d order ∧ v ∈ order ∧
      (u :: tail).Sublist (before order v) ∧
      adjacent d (lastFrom u tail) v = true := by
  rw [cons_mem_paths_iff d order u (tail ++ [v]) hn]
  constructor
  · rintro ⟨hs, hval, hc⟩
    have hs' : ((u :: tail) ++ [v]).Sublist order := by simpa using hs
    obtain ⟨hv, hp⟩ := (append_vertex_sublist_iff_before order v (u :: tail) hn).mp hs'
    have hshort : (u :: tail).Sublist order :=
      hp.trans (List.takeWhile_sublist (fun w : Nat => w != v))
    obtain ⟨hc', hedge⟩ := (chain_append_vertex d u v tail).mp hc
    exact ⟨(cons_mem_paths_iff d order u tail hn).mpr ⟨hshort, hval, hc'⟩,
      hv, hp, hedge⟩
  · rintro ⟨hpath, hv, hp, hedge⟩
    obtain ⟨_, hval, hc⟩ := (cons_mem_paths_iff d order u tail hn).mp hpath
    have hs : ((u :: tail) ++ [v]).Sublist order :=
      (append_vertex_sublist_iff_before order v (u :: tail) hn).mpr ⟨hv, hp⟩
    exact ⟨by simpa using hs, hval,
      (chain_append_vertex d u v tail).mpr ⟨hc, hedge⟩⟩

theorem before_append_of_mem (xs ys : List Nat) (v : Nat) (hv : v ∈ xs) :
    before (xs ++ ys) v = before xs v := by
  induction xs with
  | nil => simp at hv
  | cons w ws ih =>
    by_cases h : w = v
    · subst w
      simp [before]
    · have hmem : v ∈ ws := (List.mem_cons.mp hv).resolve_left (fun he => h he.symm)
      have hne : (w != v) = true := by simp [h]
      simpa [before, hne] using congrArg (w :: ·) (ih hmem)

theorem through_vertex_sublist_before (order : List Nat) (u v : Nat)
    (hv : v ∈ order) (hu : u ∈ before order v) :
    (before order u ++ [u]).Sublist (before order v) := by
  have hsplit := split_at_vertex order v hv
  have hbefore : before order u = before (before order v) u := by
    calc
      before order u = before (before order v ++ v :: after order v) u :=
        congrArg (fun xs => before xs u) hsplit
      _ = before (before order v) u :=
        before_append_of_mem (before order v) (v :: after order v) u hu
  have hsplit' := split_at_vertex (before order v) u hu
  have hsub : (before (before order v) u ++ [u]).Sublist
      (before (before order v) u ++ u :: after (before order v) u) := by
    simp
  rw [hbefore]
  simpa only [← hsplit'] using hsub

theorem path_sublist_order (d : Nat) (order p : List Nat)
    (hn : order.Nodup) (hp : p ∈ paths d order) : p.Sublist order := by
  obtain ⟨v, tail, rfl, hv, _, hs, _⟩ := (mem_paths d order p).mp hp
  exact (cons_sublist_iff_after order v tail hn).mpr ⟨hv, hs⟩

theorem path_ending_before_later (d : Nat) (order xs : List Nat)
    (u v : Nat) (hn : order.Nodup) (hv : v ∈ order)
    (hu : u ∈ before order v) (hp : xs ++ [u] ∈ paths d order) :
    (xs ++ [u]).Sublist (before order v) := by
  have hs := path_sublist_order d order (xs ++ [u]) hn hp
  obtain ⟨_, hxs⟩ := (append_vertex_sublist_iff_before order u xs hn).mp hs
  have hthrough := through_vertex_sublist_before order u v hv hu
  exact (hxs.append (List.Sublist.refl [u])).trans hthrough

theorem path_append_of_edge (d : Nat) (order p : List Nat) (u v : Nat)
    (hn : order.Nodup) (hv : v ∈ order) (hu : u ∈ before order v)
    (hedge : adjacent d u v = true) (hp : p ∈ paths d order)
    (hend : p.getLast? = some u) : p ++ [v] ∈ paths d order := by
  obtain ⟨xs, rfl⟩ := List.getLast?_eq_some_iff.mp hend
  have hbefore := path_ending_before_later d order xs u v hn hv hu hp
  cases xs with
  | nil =>
    exact (append_vertex_mem_paths_iff d order u [] v hn).mpr
      ⟨hp, hv, by simpa using hbefore, hedge⟩
  | cons w ws =>
    have hlast : lastFrom w (ws ++ [u]) = u := lastFrom_append_vertex w u ws
    apply (append_vertex_mem_paths_iff d order w (ws ++ [u]) v hn).mpr
    simpa [hlast, List.cons_append, List.append_assoc] using
      (show (w :: ws ++ [u]) ∈ paths d order ∧ v ∈ order ∧
        (w :: ws ++ [u]).Sublist (before order v) ∧
        adjacent d (lastFrom w (ws ++ [u])) v = true from
        ⟨hp, hv, by simpa using hbefore, by simpa [hlast] using hedge⟩)

theorem getLast?_cons_eq_lastFrom (u : Nat) (tail : List Nat) :
    (u :: tail).getLast? = some (lastFrom u tail) := by
  induction tail generalizing u with
  | nil => rfl
  | cons w ws ih =>
    simpa only [List.getLast?_cons_cons, lastFrom] using ih w

def endPaths (d : Nat) (order : List Nat) (v : Nat) : List (List Nat) :=
  (paths d order).filter (fun p => p.getLast? == some v)

def endCount (d : Nat) (order : List Nat) (v : Nat) : Nat :=
  (endPaths d order v).length

def incomingPaths (d : Nat) (order : List Nat) (v : Nat) : List (List Nat) :=
  (paths d order).filter (fun p =>
    (before order v).any (fun u => (p.getLast? == some u) && adjacent d u v))

theorem mem_endPaths_iff (d : Nat) (order : List Nat) (v : Nat) (p : List Nat) :
    p ∈ endPaths d order v ↔ p ∈ paths d order ∧ p.getLast? = some v := by
  simp [endPaths]

theorem mem_incomingPaths_iff (d : Nat) (order : List Nat) (v : Nat) (p : List Nat) :
    p ∈ incomingPaths d order v ↔
      p ∈ paths d order ∧ ∃ u ∈ before order v,
        p.getLast? = some u ∧ adjacent d u v = true := by
  simp [incomingPaths, List.any_eq_true]

theorem mem_endPaths_decompose (d : Nat) (order : List Nat) (v : Nat)
    (p : List Nat) (hn : order.Nodup) (hv : v ∈ order) :
    p ∈ endPaths d order v ↔
      (p = [v] ∧ valley d order v = true) ∨
      ∃ q ∈ incomingPaths d order v, p = q ++ [v] := by
  constructor
  · intro hp
    obtain ⟨hpath, hend⟩ := (mem_endPaths_iff d order v p).mp hp
    obtain ⟨xs, rfl⟩ := List.getLast?_eq_some_iff.mp hend
    cases xs with
    | nil =>
      left
      have hs := (cons_mem_paths_iff d order v [] hn).mp hpath
      exact ⟨rfl, hs.2.1⟩
    | cons w ws =>
      right
      obtain ⟨hq, _, hbefore, hedge⟩ :=
        (append_vertex_mem_paths_iff d order w ws v hn).mp (by simpa using hpath)
      have hendq : (w :: ws).getLast? = some (lastFrom w ws) :=
        getLast?_cons_eq_lastFrom w ws
      have hu : lastFrom w ws ∈ before order v := by
        obtain ⟨ys, heq⟩ := List.getLast?_eq_some_iff.mp hendq
        exact hbefore.mem (heq ▸ by simp)
      refine ⟨w :: ws, (mem_incomingPaths_iff d order v (w :: ws)).mpr ?_, ?_⟩
      · exact ⟨hq, lastFrom w ws, hu, hendq, hedge⟩
      · simp [List.cons_append]
  · rintro (⟨rfl, hval⟩ | ⟨q, hq, rfl⟩)
    · exact (mem_endPaths_iff d order v [v]).mpr
        ⟨singleton_mem_paths d order v hv hval, by simp⟩
    · obtain ⟨hpath, u, hu, hend, hedge⟩ :=
        (mem_incomingPaths_iff d order v q).mp hq
      exact (mem_endPaths_iff d order v (q ++ [v])).mpr
        ⟨path_append_of_edge d order q u v hn hv hu hedge hpath hend,
          by simp⟩

def nextEndPaths (d : Nat) (order : List Nat) (v : Nat) : List (List Nat) :=
  (if valley d order v then [[v]] else []) ++
    (incomingPaths d order v).map (· ++ [v])

theorem nextEndPaths_nodup (d : Nat) (order : List Nat) (v : Nat) :
    (nextEndPaths d order v).Nodup := by
  have hin : (incomingPaths d order v).Nodup :=
    (Hypercube.paths_nodup d order).filter _
  have hmap : ((incomingPaths d order v).map (· ++ [v])).Nodup := by
    apply List.Pairwise.map (R := (· ≠ ·)) (· ++ [v])
      (by intro a b hab he; exact hab (List.append_inj_left' he (by simp)))
    exact hin
  unfold nextEndPaths
  split
  · apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨q, hq, heq⟩ := List.mem_map.mp hm
      have hpath := (mem_incomingPaths_iff d order v q).mp hq |>.1
      obtain ⟨u, tail, rfl, _, _, _, _⟩ := (mem_paths d order q).mp hpath
      simp at heq
    · exact hmap
  · simpa using hmap

theorem endPaths_perm_next (d : Nat) (order : List Nat) (v : Nat)
    (hn : order.Nodup) (hv : v ∈ order) :
    (endPaths d order v).Perm (nextEndPaths d order v) := by
  apply (List.perm_ext_iff_of_nodup
    ((Hypercube.paths_nodup d order).filter _) (nextEndPaths_nodup d order v)).mpr
  intro p
  change p ∈ endPaths d order v ↔ p ∈ nextEndPaths d order v
  rw [mem_endPaths_decompose d order v p hn hv]
  unfold nextEndPaths
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨rfl, hval⟩ | ⟨q, hq, rfl⟩)
    · left
      simp [hval]
    · right
      exact ⟨q, hq, rfl⟩
  · rintro (hsource | ⟨q, hq, rfl⟩)
    · left
      by_cases hval : valley d order v = true
      · simp [hval] at hsource
        exact ⟨hsource, hval⟩
      · simp [hval] at hsource
    · exact Or.inr ⟨q, hq, rfl⟩

theorem endCount_eq_source_add_incoming (d : Nat) (order : List Nat)
    (v : Nat) (hn : order.Nodup) (hv : v ∈ order) :
    endCount d order v =
      (if valley d order v then 1 else 0) + (incomingPaths d order v).length := by
  have hlen := (endPaths_perm_next d order v hn hv).length_eq
  cases h : valley d order v <;>
    simpa [endCount, nextEndPaths, h, Nat.add_comm] using hlen

theorem sum_map_add_nat {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_unique_endpoint_indicator (vertices : List Nat) (hn : vertices.Nodup)
    (endpoint : Option Nat) (edge : Nat → Bool) :
    (vertices.map (fun u => if (endpoint == some u) && edge u then 1 else 0)).sum =
      if vertices.any (fun u => (endpoint == some u) && edge u) then 1 else 0 := by
  induction vertices with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
    by_cases h : (endpoint == some u) && edge u = true
    · have hend : endpoint = some u := by
        have hh : endpoint = some u ∧ edge u = true := by simpa using h
        exact hh.1
      have hrest : us.any (fun w => (endpoint == some w) && edge w) = false := by
        apply List.any_eq_false.mpr
        intro w hw hpred
        have hew : endpoint = some w := by
          have hh : endpoint = some w ∧ edge w = true := by simpa using hpred
          exact hh.1
        have he : u = w := Option.some.inj (hend.symm.trans hew)
        exact hnot (he ▸ hw)
      have hprop : endpoint = some u ∧ edge u = true := by simpa using h
      have hbool : ((endpoint == some u) && edge u) = true := by simpa using hprop
      simp only [List.map_cons, List.sum_cons]
      rw [ih hnodup]
      simp only [List.any_cons]
      simp [hbool, hrest]
    · have hprop : ¬(endpoint = some u ∧ edge u = true) := by simpa using h
      simp only [List.map_cons, List.sum_cons]
      rw [ih hnodup]
      simp [List.any_cons, hprop]

theorem countP_any_endpoint_eq_sum (ps : List (List Nat)) (vertices : List Nat)
    (hn : vertices.Nodup) (edge : Nat → Bool) :
    ps.countP (fun p => vertices.any (fun u => (p.getLast? == some u) && edge u)) =
      (vertices.map (fun u =>
        ps.countP (fun p => (p.getLast? == some u) && edge u))).sum := by
  induction ps with
  | nil => induction vertices with
    | nil => rfl
    | cons u us ih =>
      exact (by simpa using ih (List.nodup_cons.mp hn).2)
  | cons p ps ih =>
    simp only [List.countP_cons]
    rw [ih]
    rw [sum_map_add_nat vertices
      (fun u => ps.countP (fun p => (p.getLast? == some u) && edge u))
      (fun u => if (p.getLast? == some u) && edge u then 1 else 0)]
    rw [sum_unique_endpoint_indicator vertices hn p.getLast? edge]

theorem sum_filter_map_nat (vertices : List Nat) (edge : Nat → Bool)
    (f : Nat → Nat) :
    ((vertices.filter edge).map f).sum =
      (vertices.map (fun u => if edge u then f u else 0)).sum := by
  induction vertices with
  | nil => rfl
  | cons u us ih =>
    cases h : edge u <;> simp [h, ih]

theorem incomingPaths_length_eq_neighbor_sum (d : Nat) (order : List Nat)
    (v : Nat) (hn : order.Nodup) :
    (incomingPaths d order v).length =
      (((before order v).filter (adjacent d v)).map (endCount d order)).sum := by
  have hbefore : (before order v).Nodup :=
    (List.takeWhile_sublist (fun w : Nat => w != v)).nodup hn
  rw [incomingPaths, ← List.countP_eq_length_filter,
    countP_any_endpoint_eq_sum (paths d order) (before order v)
      hbefore (fun u => adjacent d u v)]
  rw [sum_filter_map_nat (before order v) (adjacent d v) (endCount d order)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [adjacent_symm d u v]
  cases h : adjacent d v u <;>
    simp [endCount, endPaths, List.countP_eq_length_filter]

theorem endCount_eq_source_add_neighbor_sum (d : Nat) (order : List Nat)
    (v : Nat) (hn : order.Nodup) (hv : v ∈ order) :
    endCount d order v = (if valley d order v then 1 else 0) +
      (((before order v).filter (adjacent d v)).map (endCount d order)).sum := by
  rw [endCount_eq_source_add_incoming d order v hn hv,
    incomingPaths_length_eq_neighbor_sum d order v hn]

theorem valley_false_iff_earlier_neighbor (d : Nat) (order : List Nat)
    (v : Nat) :
    valley d order v = false ↔
      ∃ u ∈ before order v, adjacent d v u = true := by
  simp [valley, List.any_eq_true]

theorem endCount_pos (d : Nat) (order : List Nat) (hn : order.Nodup)
    (v : Nat) (hv : v ∈ order) : 0 < endCount d order v := by
  have key : ∀ n (w : Nat), (before order w).length = n →
      w ∈ order → 0 < endCount d order w := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro w hlen hw
      by_cases hval : valley d order w = true
      · rw [endCount_eq_source_add_neighbor_sum d order w hn hw]
        simp only [hval, ↓reduceIte]
        omega
      · have hfalse : valley d order w = false := by
          cases h : valley d order w <;> simp_all
        obtain ⟨u, hu, hedge⟩ :=
          (valley_false_iff_earlier_neighbor d order w).mp hfalse
        have huorder : u ∈ order :=
          (List.takeWhile_sublist (fun x : Nat => x != w)).mem hu
        have hthrough := through_vertex_sublist_before order u w hw hu
        have hlt : (before order u).length < n := by
          have hle := hthrough.length_le
          simp only [List.length_append, List.length_singleton] at hle
          omega
        have hupos := ih (before order u).length hlt u rfl huorder
        have hfiltered : u ∈ (before order w).filter (adjacent d w) := by
          simp [hu, hedge]
        have hmapped : endCount d order u ∈
            (((before order w).filter (adjacent d w)).map (endCount d order)) :=
          List.mem_map_of_mem hfiltered
        have hsumpos : 0 <
            (((before order w).filter (adjacent d w)).map (endCount d order)).sum :=
          List.sum_pos_iff_exists_pos_nat.mpr
            ⟨endCount d order u, hmapped, hupos⟩
        rw [endCount_eq_source_add_neighbor_sum d order w hn hw]
        simpa [hfalse] using hsumpos
  exact key (before order v).length v rfl hv

theorem endCount_recurrence (d : Nat) (order : List Nat)
    (v : Nat) (hn : order.Nodup) (hv : v ∈ order) :
    endCount d order v = max 1
      (((before order v).filter (adjacent d v)).map (endCount d order)).sum := by
  have hcount := endCount_eq_source_add_neighbor_sum d order v hn hv
  by_cases hval : valley d order v = true
  · have hany : (before order v).any (adjacent d v) = false := by
      cases h : (before order v).any (adjacent d v) <;>
        simp [valley, h] at hval ⊢
    have hfilter : (before order v).filter (adjacent d v) = [] :=
      List.filter_eq_nil_iff.mpr (List.any_eq_false.mp hany)
    rw [hcount, hfilter]
    simp [hval]
  · have hfalse : valley d order v = false := by
      cases h : valley d order v <;> simp_all
    have hsumpos : 0 <
        (((before order v).filter (adjacent d v)).map (endCount d order)).sum := by
      have hpos := endCount_pos d order hn v hv
      rw [hcount] at hpos
      simpa [hfalse] using hpos
    rw [hcount]
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact (Nat.max_eq_right (by omega : 1 ≤
      (((before order v).filter (adjacent d v)).map (endCount d order)).sum)).symm

theorem path_has_endpoint_in_order (d : Nat) (order p : List Nat)
    (hn : order.Nodup) (hp : p ∈ paths d order) :
    ∃ v ∈ order, p.getLast? = some v := by
  have hnonempty : p ≠ [] := by
    obtain ⟨v, tail, rfl, _, _, _, _⟩ := (mem_paths d order p).mp hp
    simp
  let v := p.getLast hnonempty
  have hv : v ∈ order :=
    (path_sublist_order d order p hn hp).getLast_mem hnonempty
  exact ⟨v, hv, List.getLast?_eq_some_getLast hnonempty⟩

theorem pathCount_eq_sum_endCount (d : Nat) (order : List Nat)
    (hn : order.Nodup) :
    pathCount d order = (order.map (endCount d order)).sum := by
  have hall : ∀ p ∈ paths d order,
      order.any (fun v => p.getLast? == some v) = true := by
    intro p hp
    obtain ⟨v, hv, hend⟩ := path_has_endpoint_in_order d order p hn hp
    exact List.any_eq_true.mpr ⟨v, hv, by simp [hend]⟩
  have hcount := countP_any_endpoint_eq_sum (paths d order) order hn (fun _ => true)
  have hleft : (paths d order).countP
      (fun p => order.any (fun v => (p.getLast? == some v) && true)) =
      (paths d order).length := by
    rw [List.countP_eq_length_filter]
    apply congrArg List.length
    apply List.filter_eq_self.mpr
    intro p hp
    simpa using hall p hp
  rw [hleft] at hcount
  unfold pathCount
  rw [hcount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v hv
  simp [endCount, endPaths, List.countP_eq_length_filter]

theorem pathCount_lower3 (order : List Nat) (h : IsLabelling 3 order) :
    14 ≤ pathCount 3 order := by
  have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
  have hrec : endpointRecurrence 3 order (endCount 3 order) := by
    intro v hv
    exact endCount_recurrence 3 order v hn hv
  rw [pathCount_eq_sum_endCount 3 order hn]
  exact regularLower3 order (endCount 3 order) h hrec

theorem pathCount_lower4 (order : List Nat) (h : IsLabelling 4 order) :
    34 ≤ pathCount 4 order := by
  have hn : order.Nodup := h.nodup_iff.mpr List.nodup_range
  have hrec : endpointRecurrence 4 order (endCount 4 order) := by
    intro v hv
    exact endCount_recurrence 4 order v hn hv
  rw [pathCount_eq_sum_endCount 4 order hn]
  exact regularLower4 order (endCount 4 order) h hrec

#print axioms append_vertex_mem_paths_iff
#print axioms path_append_of_edge
#print axioms endPaths_perm_next
#print axioms endCount_recurrence
#print axioms pathCount_eq_sum_endCount
#print axioms pathCount_lower3
#print axioms pathCount_lower4

end Hypercube
