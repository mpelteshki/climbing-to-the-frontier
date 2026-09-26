import Hypercube
namespace Hypercube

theorem extensions_nodup (d v : Nat) (order : List Nat) (hn : order.Nodup) :
    (extensions d v order).Nodup := by
  induction order generalizing v with
  | nil => simp [extensions]
  | cons w ws ih =>
    obtain ⟨hw, hws⟩ := List.nodup_cons.mp hn
    simp only [extensions]
    split
    next ha =>
      apply List.nodup_append.mpr
      refine ⟨ih v hws, ?_, ?_⟩
      · exact List.Pairwise.map (w :: ·) (by intro a b hab he; exact hab (List.cons.inj he).2) (ih w hws)
      · intro a ham b hbm he
        obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hbm
        subst a
        have hs := ((mem_extensions ..).mp ham).1
        exact hw (hs.subset (by simp))
    next ha => simpa using ih v hws

def rawPaths (d : Nat) (order : List Nat) : List (List Nat) :=
  order.flatMap fun v =>
    if valley d order v then (extensions d v (after order v)).map (v :: ·)
    else []

theorem rawPaths_nodup (d : Nat) (order : List Nat) (hn : order.Nodup) :
    (rawPaths d order).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro v hv
    split
    next h =>
      apply List.Pairwise.map (R := (· ≠ ·)) (v :: ·)
        (by intro a b hab he; exact hab (List.cons.inj he).2)
      apply extensions_nodup
      exact ((List.drop_sublist 1 _).trans (List.dropWhile_sublist _)).nodup hn
    next h => simp
  · apply hn.imp
    intro v w hne a ha b hb he
    split at ha
    next hv =>
      split at hb
      next hw =>
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact hne (List.cons.inj he).1
      next hw => simp at hb
    next hv => simp at ha

theorem eraseDups_eq_of_nodup (xs : List (List Nat)) (hn : xs.Nodup) :
    xs.eraseDups = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hn⟩ := List.nodup_cons.mp hn
    rw [List.eraseDups_cons]
    have hf : xs.filter (fun b => !b == x) = xs := by
      apply List.filter_eq_self.mpr
      intro b hb
      simp
      intro he
      subst b
      exact hx hb
    rw [hf, ih hn]

theorem fast_count (d : Nat) (order : List Nat) (h : IsLabelling d order) :
    pathCount d order = (rawPaths d order).length := by
  have hn : order.Nodup := h.nodup_iff.mpr (List.nodup_range)
  exact congrArg List.length (eraseDups_eq_of_nodup _ (rawPaths_nodup d order hn))

#print axioms fast_count
end Hypercube
