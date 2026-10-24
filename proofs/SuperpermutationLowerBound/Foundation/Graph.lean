module

public import SuperpermutationLowerBound.Foundation.Words

@[expose] public section

namespace SuperpermutationLowerBound

open PermutationVertex

/-! The complete loopless directed overlap graph and its weights. -/

/-- Suffix-prefix overlap after appending `t` symbols. -/
def OverlapsAt {k : ℕ} (u v : PermutationVertex k) (t : ℕ) : Prop :=
  u.1.drop t = v.1.take (k - t)

/-- A positive overlap displacement always exists. -/
theorem positiveOverlap_exists {k : ℕ} (u v : PermutationVertex k) :
    ∃ t, 1 ≤ t ∧ OverlapsAt u v t := by
  refine ⟨k + 1, Nat.le_add_left 1 k, ?_⟩
  simp [OverlapsAt, PermutationVertex.length]

/-- The least positive suffix-prefix overlap displacement. -/
noncomputable def overlapWeight {k : ℕ} (u v : PermutationVertex k) : ℕ :=
  by
    classical
    exact Nat.find (positiveOverlap_exists u v)

/-- An edge of the complete loopless directed graph on permutation vertices. -/
structure DirectedOverlapEdge (k : ℕ) where
  source : PermutationVertex k
  target : PermutationVertex k
  ne : source ≠ target

namespace DirectedOverlapEdge

/-- The overlap weight carried by a directed edge. -/
noncomputable def weight {k : ℕ} (e : DirectedOverlapEdge k) : ℕ :=
  overlapWeight e.source e.target

end DirectedOverlapEdge

theorem overlapWeight_spec {k : ℕ} (u v : PermutationVertex k) :
    1 ≤ overlapWeight u v ∧ OverlapsAt u v (overlapWeight u v) :=
  by
    classical
    simpa [overlapWeight] using Nat.find_spec (positiveOverlap_exists u v)

theorem overlapWeight_min {k : ℕ} (u v : PermutationVertex k) {t : ℕ}
    (ht : 1 ≤ t) (hov : OverlapsAt u v t) : overlapWeight u v ≤ t := by
  classical
  simpa [overlapWeight] using
    (Nat.find_min' (positiveOverlap_exists u v) ⟨ht, hov⟩)

theorem overlapsAt_full {k : ℕ} (_hk : 1 ≤ k) (u v : PermutationVertex k) :
    OverlapsAt u v k := by
  simp [OverlapsAt, PermutationVertex.length]

theorem overlapWeight_le_length {k : ℕ} (hk : 1 ≤ k) (u v : PermutationVertex k) :
    overlapWeight u v ≤ k :=
  overlapWeight_min u v hk (overlapsAt_full hk u v)

/-- A weight is `t` exactly when overlap occurs at `t` and no smaller positive overlap occurs. -/
theorem overlapWeight_eq_iff_overlap_no_shorter {k : ℕ} (u v : PermutationVertex k)
    {t : ℕ} (ht : 1 ≤ t) :
    overlapWeight u v = t ↔
      OverlapsAt u v t ∧ ∀ s, 1 ≤ s → s < t → ¬ OverlapsAt u v s := by
  constructor
  · intro h
    subst t
    exact ⟨(overlapWeight_spec u v).2, fun s hs hlt hov ↦
      (Nat.not_lt_of_ge (overlapWeight_min u v hs hov)) hlt⟩
  · rintro ⟨hov, hshort⟩
    apply Nat.le_antisymm (overlapWeight_min u v ht hov)
    by_contra hnot
    have hlt : overlapWeight u v < t := Nat.lt_of_not_ge hnot
    exact hshort (overlapWeight u v) (overlapWeight_spec u v).1 hlt
      (overlapWeight_spec u v).2

end SuperpermutationLowerBound
