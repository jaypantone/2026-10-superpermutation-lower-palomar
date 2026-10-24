module

public import Mathlib.Data.List.SplitBy
public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

def reflectList {α β : Type*} (f : α → β) (l : List α) : List β := l.reverse.map f

@[simp] theorem reflectList_length {α β : Type*} (f : α → β) (l : List α) :
    (reflectList f l).length = l.length := by simp [reflectList]

@[simp] theorem reflectList_eq_nil_iff {α β : Type*} (f : α → β) (l : List α) :
    reflectList f l = [] ↔ l = [] := by simp [reflectList]

@[simp] theorem reflectList_head {α β : Type*} (f : α → β) (l : List α)
    (h : reflectList f l ≠ []) :
    (reflectList f l).head h = f (l.getLast (by simpa using h)) := by
  simp [reflectList]

@[simp] theorem reflectList_getLast {α β : Type*} (f : α → β) (l : List α)
    (h : reflectList f l ≠ []) :
    (reflectList f l).getLast h = f (l.head (by simpa using h)) := by
  simp [reflectList]

theorem reflectList_flatten {α β : Type*} (f : α → β) (l : List (List α)) :
    reflectList f l.flatten = (reflectList (reflectList f) l).flatten := by
  induction l with
  | nil => simp [reflectList]
  | cons xs xss ih =>
      simpa [reflectList, List.map_append] using
        (congrArg (fun ys => ys ++ reflectList f xs) ih)

/-- Canonical splitting commutes with reflection whenever the boundary
predicate reverses with the entries. -/
theorem splitBy_reflectList {α β : Type*} (f : α → β)
    (r : α → α → Bool) (s : β → β → Bool)
    (hrel : ∀ x y, s (f y) (f x) = r x y) (l : List α) :
    (reflectList f l).splitBy s = reflectList (reflectList f) (l.splitBy r) := by
  rw [List.splitBy_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← reflectList_flatten, List.flatten_splitBy]
  · intro hnil
    rcases List.mem_map.mp hnil with ⟨xs, hxs, heq⟩
    have hx := (reflectList_eq_nil_iff f xs).mp heq
    have hmem : xs ∈ l.splitBy r := by simpa using hxs
    exact List.ne_nil_of_mem_splitBy hmem hx
  · intro xs hxs
    rcases List.mem_map.mp hxs with ⟨ys, hys, rfl⟩
    have hmem : ys ∈ l.splitBy r := by simpa using hys
    change (ys.reverse.map f).IsChain _
    rw [List.isChain_map, List.isChain_reverse]
    simpa only [hrel] using List.isChain_of_mem_splitBy hmem
  · change ((l.splitBy r).reverse.map (reflectList f)).IsChain _
    rw [List.isChain_map, List.isChain_reverse]
    apply (List.isChain_getLast_head_splitBy r l).imp
    intro xs ys hxy
    rcases hxy with ⟨hx, hy, hxy⟩
    refine ⟨by simpa using hy, by simpa using hx, ?_⟩
    simpa only [reflectList_getLast, reflectList_head, hrel] using hxy

end SuperpermutationLowerBound.Refinement
