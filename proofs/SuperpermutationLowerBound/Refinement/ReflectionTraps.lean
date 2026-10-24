module

public import SuperpermutationLowerBound.Refinement.ReflectionPath
public import SuperpermutationLowerBound.Refinement.ChainPatterns

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

theorem regularPath_reverse (gaps : List ℕ) :
    (regularPath gaps).reverse = regularPath gaps.reverse := by
  induction gaps with
  | nil => simp [regularPath]
  | cons g gs ih =>
      rw [regularPath, List.reverse_cons, List.reverse_append, List.reverse_replicate, ih,
        List.reverse_cons, regularPath_eq_gapWord (gs.reverse ++ [g]), gapWord_append]
      rw [regularPath_eq_gapWord gs.reverse]
      simp [gapWord, List.append_assoc]

theorem zeroRegular_reverse (gaps : List ℕ) :
    (zeroRegular gaps).reverse = zeroRegular gaps.reverse := by
  simp [zeroRegular, regularPath_reverse]

theorem zeroCell_reverse (a : ℕ) (cells : List Bool) :
    (zeroCell a cells).reverse = zeroCell a cells.reverse := by
  simp only [zeroCell_eq_zeroRegular, zeroRegular_reverse, List.map_reverse]

theorem CellFactor.reverse {a : ℕ} {cells : List Bool} {d : List ℕ}
    (h : CellFactor a cells d) : CellFactor a cells.reverse d.reverse := by
  obtain ⟨pre, post, heq⟩ := h
  refine ⟨post.reverse, pre.reverse, ?_⟩
  simp only [heq, List.reverse_append, zeroCell_reverse, List.append_assoc]

@[simp] theorem chainWindow_reverse_empty (r s : ℕ) :
    (chainWindow r s []).reverse = chainWindow s r [] := by
  simp [chainWindow, List.append_assoc]

/-- An exclusion proved uniformly for genuine segments automatically holds
for the reflected literal cell pattern. -/
theorem actual_cellFactor_reverse_avoidance {k : ℕ} (hk : 7 ≤ k)
    (a : ℕ) (pattern : List Bool)
    (H : ∀ (p : OverlapPath k) (hp : IsBlockAligned p)
      (segment : BlockAlignedLightSegment hk p hp), ¬CellFactor a pattern segment.deficitString)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor a pattern.reverse segment.deficitString := by
  intro h
  apply H (reflectedPath hk p hp) (reflectedPath_aligned hk p hp)
    (reflectedSegment hk p hp segment)
  simpa only [reflectedSegment_deficitString, List.reverse_reverse] using h.reverse

/-- The left endpoint bound is the reflected right endpoint trap; both
bounding zeros remain literal factors throughout the construction. -/
theorem actual_basicLeft_of_basicRight {k : ℕ} (hk : 7 ≤ k)
    (a periodBound : ℕ)
    (H : ∀ (p : OverlapPath k) (hp : IsBlockAligned p)
      (segment : BlockAlignedLightSegment hk p hp),
        ¬CellFactor a (chainWindow 0 (periodBound - 1) []) segment.deficitString)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor a (chainWindow (periodBound - 1) 0 []) segment.deficitString := by
  simpa only [chainWindow_reverse_empty] using
    actual_cellFactor_reverse_avoidance hk a (chainWindow 0 (periodBound - 1) []) H p hp segment

end SuperpermutationLowerBound.Refinement
