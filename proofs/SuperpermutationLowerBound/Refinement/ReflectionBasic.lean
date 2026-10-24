module

public import SuperpermutationLowerBound.Refinement.GeometryBasic

@[expose] public section

/-! Reversal of literal words and complete block entries. -/
namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

def reverseVertex (u : PermutationVertex k) : PermutationVertex k :=
  ⟨u.1.reverse, (List.reverse_perm _).trans u.2⟩

@[simp] theorem reverseVertex_word (u : PermutationVertex k) :
    (reverseVertex u).1 = u.1.reverse := rfl

@[simp] theorem reverseVertex_reverseVertex (u : PermutationVertex k) :
    reverseVertex (reverseVertex u) = u := by
  apply PermutationVertex.ext
  simp

theorem reverseVertex_injective : Function.Injective (reverseVertex : PermutationVertex k → _) :=
  Function.LeftInverse.injective reverseVertex_reverseVertex

theorem overlapsAt_reverse_iff (u v : PermutationVertex k) (t : ℕ) (ht : t ≤ k) :
    OverlapsAt (reverseVertex v) (reverseVertex u) t ↔ OverlapsAt u v t := by
  simp only [OverlapsAt, reverseVertex_word, List.drop_reverse, List.take_reverse,
    PermutationVertex.length, Nat.sub_sub_self ht, List.reverse_inj]
  exact eq_comm

theorem overlapWeight_reverse (hk : 1 ≤ k) (u v : PermutationVertex k) :
    overlapWeight (reverseVertex v) (reverseVertex u) = overlapWeight u v := by
  apply Nat.le_antisymm
  · exact overlapWeight_min _ _ (overlapWeight_spec u v).1
      ((overlapsAt_reverse_iff u v _ (overlapWeight_le_length hk u v)).2
        (overlapWeight_spec u v).2)
  · exact overlapWeight_min _ _ (overlapWeight_spec (reverseVertex v) (reverseVertex u)).1
      ((overlapsAt_reverse_iff u v _ (overlapWeight_le_length hk _ _)).1
        (overlapWeight_spec (reverseVertex v) (reverseVertex u)).2)

theorem rotationClass_eq_iff_words_rotated (hk : 1 ≤ k) (u v : PermutationVertex k) :
    rotationClass u = rotationClass v ↔ u.1.IsRotated v.1 := by
  rw [rotationClass_eq_iff_mem hk, mem_rotationClass_iff]
  constructor
  · rintro ⟨i, hi, heq⟩
    exact ⟨i, by simpa only [rotationPower_word hk] using congrArg Subtype.val heq⟩
  · rintro ⟨i, heq⟩
    refine ⟨i % k, Nat.mod_lt _ (by omega), ?_⟩
    rw [rotationPower_mod hk i u]
    apply PermutationVertex.ext
    simpa only [rotationPower_word hk] using heq

theorem rotationClass_reverse_iff (hk : 1 ≤ k) (u v : PermutationVertex k) :
    rotationClass (reverseVertex u) = rotationClass (reverseVertex v) ↔
      rotationClass u = rotationClass v := by
  simp only [rotationClass_eq_iff_words_rotated hk, reverseVertex_word,
    List.isRotated_reverse_iff]

theorem blockExit_reverseVertex (u : PermutationVertex k) :
    blockExit (reverseVertex u) = reverseVertex (rotation u) := by
  apply PermutationVertex.ext
  simp only [blockExit, inverseRotation_word, reverseVertex_word, rotation_word,
    List.reverse_append, List.reverse_take, List.reverse_drop, PermutationVertex.length]

/-- When traversal is reflected, the old block exit becomes the new entry. -/
def reflectEntry (u : PermutationVertex k) : PermutationVertex k := reverseVertex (blockExit u)

@[simp] theorem blockExit_reflectEntry (hk : 1 ≤ k) (u : PermutationVertex k) :
    blockExit (reflectEntry u) = reverseVertex u := by
  rw [reflectEntry, blockExit_reverseVertex, rotation_blockExit hk]

@[simp] theorem reflectEntry_involution (hk : 1 ≤ k) (u : PermutationVertex k) :
    reflectEntry (reflectEntry u) = u := by
  rw [reflectEntry, blockExit_reflectEntry hk, reverseVertex_reverseVertex]

theorem reflectEntry_class_iff (hk : 1 ≤ k) (u v : PermutationVertex k) :
    rotationClass (reflectEntry u) = rotationClass (reflectEntry v) ↔
      rotationClass u = rotationClass v := by
  rw [reflectEntry, reflectEntry, rotationClass_reverse_iff hk]
  rw [← rotationPower_pred_eq_blockExit hk u, ← rotationPower_pred_eq_blockExit hk v,
    rotationClass_rotationPower hk, rotationClass_rotationPower hk]

theorem reflectEntry_boundary_weight (hk : 1 ≤ k) (u v : PermutationVertex k) :
    overlapWeight (blockExit (reflectEntry v)) (reflectEntry u) =
      overlapWeight (blockExit u) v := by
  rw [blockExit_reflectEntry hk, reflectEntry, overlapWeight_reverse hk]

end SuperpermutationLowerBound.Refinement
