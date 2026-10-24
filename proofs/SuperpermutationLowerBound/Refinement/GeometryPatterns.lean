module

public import SuperpermutationLowerBound.Refinement.GeometryCells
public import SuperpermutationLowerBound.Refinement.ChainEncoding

@[expose] public section

/-! Literal contiguous patterns retain their actual run positions. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ} {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}

def PatternAt (segment : BlockAlignedLightSegment hk p hp) (start : ℕ)
    (digits : List ℕ) : Prop :=
  start + digits.length ≤ segment.length ∧
    ∀ i, ∀ hi : i < digits.length,
      deficitAt segment.deficitString (start + i) = digits[i]

namespace PatternAt

variable {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}

theorem of_factor {before digits after : List ℕ}
    (h : segment.deficitString = before ++ digits ++ after) :
    PatternAt segment before.length digits := by
  have hlength := congrArg List.length h
  simp only [blockAlignedLightSegment_deficitString_length, List.length_append] at hlength
  refine ⟨by omega, ?_⟩
  intro i hi
  rw [deficitAt_eq_get _ _ (by rw [h]; simp only [List.length_append]; omega)]
  simp only [List.get_eq_getElem, h]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp

theorem append_left {xs ys : List ℕ} (h : PatternAt segment start (xs ++ ys)) :
    PatternAt segment start xs := by
  refine ⟨by have := h.1; simp only [List.length_append] at this; omega, ?_⟩
  intro i hi
  have heq := h.2 i (by simp only [List.length_append]; omega)
  simpa only [List.getElem_append_left hi] using heq

theorem append_right {xs ys : List ℕ} (h : PatternAt segment start (xs ++ ys)) :
    PatternAt segment (start + xs.length) ys := by
  refine ⟨by have := h.1; simp only [List.length_append] at this; omega, ?_⟩
  intro i hi
  have heq := h.2 (xs.length + i) (by simp only [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at heq
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using heq

theorem cons_head {d : ℕ} {tail : List ℕ} (h : PatternAt segment start (d :: tail)) :
    deficitAt segment.deficitString start = d := by
  have heq := h.2 0 (by simp)
  change deficitAt segment.deficitString (start + 0) = d at heq
  simpa using heq

theorem cons_tail {d : ℕ} {tail : List ℕ} (h : PatternAt segment start (d :: tail)) :
    PatternAt segment (start + 1) tail := by
  exact h.append_right (xs := [d])

theorem actual_length {digits : List ℕ} (h : PatternAt segment start digits)
    (i : ℕ) (hi : i < digits.length) :
    (segment.actualRun ⟨start + i, by have := h.1; omega⟩).length =
      k - 1 - digits[i] := by
  have heq := h.2 i hi
  rw [segment.deficitAt_deficitString_eq _ (by have := h.1; omega),
    segment.deficitString_get_eq ⟨start + i, by have := h.1; omega⟩] at heq
  have hb := segment.actualRun_length_bounds ⟨start + i, by have := h.1; omega⟩
  have hblocks := segment.actualRun_blocks ⟨start + i, by have := h.1; omega⟩
  change (segment.actualRun _).blocks.length = _
  rw [hblocks]
  omega

noncomputable def firstContext {tail : List ℕ} (h : PatternAt segment start (2 :: tail)) :
    SatelliteContext hk p hp segment := by
  have hs : start < segment.length := by
    have := h.1
    simp only [List.length_cons] at this
    omega
  refine segment.satelliteContextAt ⟨start, hs⟩ ?_
  change 0 < segment.deficitString.get ⟨start, by simpa using hs⟩
  rw [← segment.deficitAt_deficitString_eq start hs, h.cons_head]
  decide

@[simp] theorem firstContext_index {tail : List ℕ}
    (h : PatternAt segment start (2 :: tail)) : h.firstContext.localIndex.1 = start := rfl

@[simp] theorem firstContext_deficit {tail : List ℕ}
    (h : PatternAt segment start (2 :: tail)) : h.firstContext.deficit = 2 := by
  rw [firstContext, segment.satelliteContextAt_deficit]
  have heq := h.cons_head
  rw [segment.deficitAt_deficitString_eq start (by
    have := h.1
    simp only [List.length_cons] at this
    omega)] at heq
  exact heq

@[simp] theorem firstContext_entry {tail : List ℕ}
    (h : PatternAt segment start (2 :: tail)) :
    h.firstContext.entry = (segment.actualRun
      ⟨start, by have := h.1; simp only [List.length_cons] at this; omega⟩).entry := rfl

/-- The following zero digits become a genuine full-run prefix, without a
maximality assumption at the factor endpoint. -/
noncomputable def fullPrefix {g : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (2 :: List.replicate g 0 ++ tail)) (hg : 0 < g) :
    FullPrefix h.firstContext where
  count := g
  positive := hg
  inBounds := by
    have := h.1
    simp only [firstContext_index, List.length_cons, List.length_append,
      List.length_replicate] at *
    omega
  full j hj := by
    have hzero := h.2 (1 + j) (by
      simp only [List.length_cons, List.length_append, List.length_replicate]
      omega)
    simp only [List.cons_append, List.getElem_cons_succ,
      show 1 + j = j + 1 by omega] at hzero
    rw [List.getElem_append_left (by simpa using hj)] at hzero
    simp only [List.getElem_replicate] at hzero
    rw [segment.deficitAt_deficitString_eq _ (by
      have := h.1
      simp only [List.length_cons, List.length_append, List.length_replicate] at this
      omega)] at hzero
    apply (segment.deficitString_get_eq_zero_iff _).mp
    simpa only [firstContext_index, Nat.add_assoc, Nat.add_comm 1 j] using hzero

end PatternAt

end SuperpermutationLowerBound.Refinement
