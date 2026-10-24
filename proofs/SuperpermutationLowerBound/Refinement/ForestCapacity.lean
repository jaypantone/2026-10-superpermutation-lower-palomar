module

public import SuperpermutationLowerBound.Refinement.EndpointBounds
public import SuperpermutationLowerBound.Refinement.ForestFoundation
public import SuperpermutationLowerBound.Section10.SurplusRows

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open scoped BigOperators

theorem deficitAt_zero_eq_head (d : List ℕ) (hd : d ≠ []) :
    deficitAt d 0 = d.head hd := by
  rw [deficitAt_eq_get d 0 (List.length_pos_of_ne_nil hd)]
  exact (List.head_eq_getElem_zero hd).symm

theorem deficitAt_last_eq_getLast (d : List ℕ) (hd : d ≠ []) :
    deficitAt d (d.length - 1) = d.getLast hd := by
  rw [deficitAt_eq_get d (d.length - 1)
    (Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega))]
  exact (List.getLast_eq_getElem hd).symm

theorem ListAffineBound.mask {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) (hd : d ≠ []) (L R : Prop)
    [Decidable L] [Decidable R] (hlen : L → R → 2 ≤ d.length) :
    δ * (d.length : ℚ) - β +
      (if L then endpointCharge δ (deficitAt d 0) else 0) +
      (if R then endpointCharge δ (deficitAt d (d.length - 1)) else 0) ≤
        (d.sum : ℚ) := by
  rw [deficitAt_zero_eq_head d hd, deficitAt_last_eq_getLast d hd]
  by_cases hL : L <;> by_cases hR : R
  · simpa [hL, hR] using h.both (hlen hL hR) hd
  · simpa [hL, hR] using h.first hd
  · simpa [hL, hR] using h.last hd
  · simpa [hL, hR] using h.base

variable {k : ℕ}

/-- Summing hereditary segment bounds charges both actual endpoints whenever
the left endpoint is requested.  Only the coincident two-endpoint case needs
two runs. -/
theorem blockAligned_affine_endpoint_sum (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (p : OverlapPath k)
    (hp : IsBlockAligned p) (L : Prop) [Decidable L]
    (hq : L → 2 ≤ blockAlignedRunCount hk p hp) :
    δ * (blockAlignedRunCount hk p hp : ℚ) -
      ((blockAlignedLightSegments hk p hp).length : ℚ) * β +
      (if L then endpointCharge δ (blockAlignedFirstDeficit hk p hp) else 0) +
      endpointCharge δ (blockAlignedLastDeficit hk p hp) ≤
        (blockAlignedTotalDeficit hk p hp : ℚ) := by
  classical
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let first : Fin segments.length := ⟨0, hm⟩
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  have hfirstValue :
      deficitAt (blockAlignedLightSegmentAt hk p hp first).deficitString 0 =
        blockAlignedFirstDeficit hk p hp := by
    simpa [segments, first] using firstLightSegment_firstDeficit hk p hp
  have hlastValue :
      deficitAt (blockAlignedLightSegmentAt hk p hp last).deficitString
        ((blockAlignedLightSegmentAt hk p hp last).length - 1) =
        blockAlignedLastDeficit hk p hp := by
    simpa [segments, last] using lastLightSegment_lastDeficit hk p hp
  have hpoint (i : Fin segments.length) :
      δ * ((blockAlignedLightSegmentAt hk p hp i).length : ℚ) - β +
        (if i = first then
          (if L then endpointCharge δ (blockAlignedFirstDeficit hk p hp) else 0)
         else 0) +
        (if i = last then endpointCharge δ (blockAlignedLastDeficit hk p hp) else 0) ≤
          ((blockAlignedLightSegmentAt hk p hp i).totalDeficit : ℚ) := by
    let s := blockAlignedLightSegmentAt hk p hp i
    have hlen := blockAlignedLightSegment_deficitString_length hk p hp s
    have hspos := blockAlignedLightSegment_length_pos hk p hp s
    have hd : s.deficitString ≠ [] := by
      intro he
      rw [he] at hlen
      simp only [List.length_nil] at hlen
      omega
    have htwo : (i = first ∧ L) → i = last → 2 ≤ s.deficitString.length := by
      rintro ⟨hif, hL⟩ hil
      have hstart : s.globalStart = 0 := by
        simp [s, hif, segments, first]
      have hend : s.globalStart + s.length = blockAlignedRunCount hk p hp := by
        simpa [s, hil, segments, last] using lastLightSegment_end_eq_runCount hk p hp
      have := hq hL
      omega
    have he := (H p hp s).mask hd (i = first ∧ L) (i = last) htwo
    have hsum : (s.deficitString.sum : ℚ) = (s.totalDeficit : ℚ) := rfl
    rw [hlen, hsum] at he
    have hl : (if i = first ∧ L then endpointCharge δ (deficitAt s.deficitString 0) else 0) =
        (if i = first then (if L then endpointCharge δ (blockAlignedFirstDeficit hk p hp)
          else 0) else 0) := by
      by_cases hi : i = first <;> by_cases hL : L <;> simp [hi, hL, s, hfirstValue]
    have hr : (if i = last then endpointCharge δ
        (deficitAt s.deficitString (s.length - 1)) else 0) =
        (if i = last then endpointCharge δ (blockAlignedLastDeficit hk p hp) else 0) := by
      by_cases hi : i = last <;> simp [hi, s, hlastValue]
    rw [hl, hr] at he
    exact he
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  have hlengths :
      (∑ i : Fin segments.length,
        ((blockAlignedLightSegmentAt hk p hp i).length : ℚ)) =
        (blockAlignedRunCount hk p hp : ℚ) := by
    exact_mod_cast blockAlignedLightSegmentLengths_fin_sum hk p hp
  have hdeficits :
      (∑ i : Fin segments.length,
        ((blockAlignedLightSegmentAt hk p hp i).totalDeficit : ℚ)) =
        (blockAlignedTotalDeficit hk p hp : ℚ) := by
    exact_mod_cast (blockAlignedTotalDeficit_eq_sum_lightSegments hk p hp).symm
  rw [hlengths, hdeficits] at hsum
  exact hsum

/-- The rational component capacity is inherited by every actual aligned path,
with no terminal bonus or rounded deficit function. -/
theorem blockAligned_affine_capacity (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (L : Prop) [Decidable L] (hq : L → 2 ≤ blockAlignedRunCount hk p hp) :
    (pathBlockCount p : ℚ) - (((k - 1 : ℕ) : ℚ) - δ) * (blockAlignedZ p hp : ℚ) +
      (if L then endpointCharge δ (blockAlignedFirstDeficit hk p hp) else 0) +
      endpointCharge δ (blockAlignedLastDeficit hk p hp) ≤ β := by
  have hs := blockAligned_affine_endpoint_sum hk H p hp L hq
  have hm : 1 ≤ (blockAlignedLightSegments hk p hp).length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  have he := blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one hk p hp
  have heq : (((blockAlignedLightSegments hk p hp).length : ℚ) - 1) ≤
      (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by
    have : (blockAlignedLightSegments hk p hp).length ≤
        blockAlignedRunBoundaryExcess hk p hp + 1 := by omega
    have hc : ((blockAlignedLightSegments hk p hp).length : ℚ) ≤
        (blockAlignedRunBoundaryExcess hk p hp : ℚ) + 1 := by exact_mod_cast this
    linarith
  have hmul := mul_le_mul_of_nonneg_left heq hβ
  have hexcess : 0 ≤ (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by positivity
  have hmul' := mul_le_mul_of_nonneg_right hβα hexcess
  have hz : (blockAlignedZ p hp : ℚ) = (blockAlignedRunCount hk p hp : ℚ) +
      (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by
    exact_mod_cast blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp
  have hb : (pathBlockCount p : ℚ) =
      ((k - 1 : ℕ) : ℚ) * (blockAlignedRunCount hk p hp : ℚ) -
        (blockAlignedTotalDeficit hk p hp : ℚ) := by
    rw [pathBlockCount_eq_runCount_sub_totalDeficit hk p hp,
      Nat.cast_sub (blockAlignedTotalDeficit_le_capacity hk p hp), Nat.cast_mul]
  rw [hb, hz]
  nlinarith

noncomputable def rationalComponentSurplus (hk : 7 ≤ k) (P : HamiltonianPath k)
    (δ : ℚ) (C : WeakComponent (pathForest (by omega) P)) : ℚ :=
  (pathForestComponentBlockCount (by omega) P C : ℚ) -
    (((k - 1 : ℕ) : ℚ) - δ) * (pathForestComponentBudget (by omega) P C : ℚ)

theorem componentBudget_eq_z_of_mem_U (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentBudget (by omega) P p.1 =
      pathForestComponentZ (by omega) P p.1 := by
  have hminto := (mem_pathForestU hk P p).mp hpU
  rw [pathForestComponentBudget_nonroot_split (by omega) P p.1 p.2]
  change pathForestComponentZ (by omega) P p.1 +
      (pathForestNonrootMinto hk P p - 2) = _
  rw [hminto]
  simp

theorem component_affine_capacity (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockCount (by omega) P C : ℚ) -
      (((k - 1 : ℕ) : ℚ) - δ) * (pathForestComponentZ (by omega) P C : ℚ) +
      endpointCharge δ (pathForestComponentLastDeficit hk P C) ≤ β := by
  have h := blockAligned_affine_capacity hk H hβ hβα
    (pathForestComponentPath (by omega) P C)
    (pathForestComponentPath_blockAligned (by omega) P C) False (by simp)
  simp only [ite_false, add_zero] at h
  rw [pathForestComponentLastDeficit_eq_blockAlignedLastDeficit hk P C]
  exact h

theorem root_affine_capacity (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (P : HamiltonianPath k) :
    rationalComponentSurplus hk P δ (pathForestRootComponent (by omega) P) +
      endpointCharge δ (pathForestComponentLastDeficit hk P
        (pathForestRootComponent (by omega) P)) ≤ β := by
  unfold rationalComponentSurplus
  rw [pathForestComponentBudget_root]
  exact component_affine_capacity hk H hβ hβα P _

theorem expensive_affine_capacity (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) (hp : p ∉ pathForestU hk P) :
    rationalComponentSurplus hk P δ p.1 +
      endpointCharge δ (pathForestComponentLastDeficit hk P p.1) ≤
        β - (((k - 1 : ℕ) : ℚ) - δ) := by
  have hc := component_affine_capacity hk H hβ hβα P p.1
  have hm := (pathForestNonrootMinto_bounds hk P p).1
  have hne : pathForestNonrootMinto hk P p ≠ 2 := by
    simpa only [mem_pathForestU] using hp
  have hb : pathForestComponentZ (by omega) P p.1 + 1 ≤
      pathForestComponentBudget (by omega) P p.1 := by
    rw [pathForestComponentBudget_nonroot_split (by omega) P p.1 p.2]
    change pathForestComponentZ (by omega) P p.1 + 1 ≤
      pathForestComponentZ (by omega) P p.1 + (pathForestNonrootMinto hk P p - 2)
    omega
  have hbq : (pathForestComponentZ (by omega) P p.1 : ℚ) + 1 ≤
      (pathForestComponentBudget (by omega) P p.1 : ℚ) := by exact_mod_cast hb
  have hα : 0 ≤ ((k - 1 : ℕ) : ℚ) - δ := hβ.trans hβα
  have := mul_le_mul_of_nonneg_left hbq hα
  unfold rationalComponentSurplus
  nlinarith

/-- Literal prepending supplies the extra block in the cheap capacity. -/
theorem cheap_affine_capacity_two (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) (hp : p ∈ pathForestU hk P)
    (hq : 2 ≤ pathForestComponentRunCount hk P p.1) :
    rationalComponentSurplus hk P δ p.1 +
      endpointCharge δ (pathForestComponentFirstDeficit hk P p.1 - 1) +
      endpointCharge δ (pathForestComponentLastDeficit hk P p.1) ≤ β - 1 := by
  have hminto := (mem_pathForestU hk P p).mp hp
  have hd := pathForestComponentCheapDeficit hk P p.1 p.2 hminto
  let Q := cheapEntryPrependedPath hk P p.1 hd.1
  let hQ := cheapEntryPrependedPath_blockAligned hk P p.1 hd.1
  have hqQ : 2 ≤ blockAlignedRunCount hk Q hQ := by
    simpa [Q, hQ, cheapEntryPrependedPath_runCount] using hq
  have hc := blockAligned_affine_capacity hk H hβ hβα Q hQ True (by simpa)
  simp only [ite_true] at hc
  have hb := cheapEntryPrependedPath_blockCount hk P p.1 hd.1
  have hz := cheapEntryPrependedPath_z hk P p.1 hd.1
  have hf := (cheapEntryPrependedPath_deficitChanges hk P p.1 hd.1 hd.2.1).1
  have hl := cheapEntryPrependedPath_lastDeficit hk P p.1 hd.1 hq
  change (pathBlockCount Q : ℚ) - (((k - 1 : ℕ) : ℚ) - δ) *
    (blockAlignedZ Q hQ : ℚ) + endpointCharge δ (blockAlignedFirstDeficit hk Q hQ) +
      endpointCharge δ (blockAlignedLastDeficit hk Q hQ) ≤ β at hc
  rw [hb, hz, hf, hl, Nat.cast_add, Nat.cast_one] at hc
  unfold rationalComponentSurplus
  rw [componentBudget_eq_z_of_mem_U hk P p hp]
  linarith

/-- Clipping the entrance charge makes the cheap row valid also for one run. -/
theorem cheap_affine_capacity_clipped (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hδ : δ < 1) (hβ : 1 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) (hp : p ∈ pathForestU hk P) :
    rationalComponentSurplus hk P δ p.1 +
      min (endpointCharge δ (pathForestComponentFirstDeficit hk P p.1 - 1)) (β - 1) +
      endpointCharge δ (pathForestComponentLastDeficit hk P p.1) ≤ β - 1 := by
  by_cases hq : 2 ≤ pathForestComponentRunCount hk P p.1
  · have hc := cheap_affine_capacity_two hk H (by linarith) hβα P p hp hq
    have := min_le_left (endpointCharge δ (pathForestComponentFirstDeficit hk P p.1 - 1)) (β - 1)
    linarith
  · have hz : pathForestComponentZ (by omega) P p.1 = 1 := by
      have hzpos := pathForestComponentZ_pos (by omega) P p.1
      have hztwo := pathForestComponentZ_ge_two_iff_runCount_ge_two hk P p.1
      omega
    have hdata := pathForestComponentZOneData hk P p.1 hz
    have hminto := (mem_pathForestU hk P p).mp hp
    have hd := pathForestComponentCheapDeficit hk P p.1 p.2 hminto
    have hdq : 1 ≤ (pathForestComponentFirstDeficit hk P p.1 : ℚ) := by exact_mod_cast hd.2.1
    have hb : (pathForestComponentBlockCount (by omega) P p.1 : ℚ) =
        ((k - 1 : ℕ) : ℚ) - (pathForestComponentFirstDeficit hk P p.1 : ℚ) := by
      rw [hdata.2.1, Nat.cast_sub (by omega : pathForestComponentFirstDeficit hk P p.1 ≤ k - 1)]
    have hc : endpointCharge δ (pathForestComponentLastDeficit hk P p.1) =
        (pathForestComponentFirstDeficit hk P p.1 : ℚ) - δ := by
      rw [← hdata.1, endpointCharge, max_eq_right (by linarith)]
    have hm := min_le_right (endpointCharge δ (pathForestComponentFirstDeficit hk P p.1 - 1)) (β - 1)
    unfold rationalComponentSurplus
    rw [componentBudget_eq_z_of_mem_U hk P p hp, hz, Nat.cast_one, mul_one, hb, hc]
    linarith

theorem rationalComponentSurplus_sum (hk : 7 ≤ k) (P : HamiltonianPath k) (δ : ℚ) :
    (∑ C : WeakComponent (pathForest (by omega) P), rationalComponentSurplus hk P δ C) =
      ((k - 1).factorial : ℚ) - (((k - 1 : ℕ) : ℚ) - δ) *
        (pathForestTotalBudget (by omega) P : ℚ) := by
  classical
  have hb : (∑ C : WeakComponent (pathForest (by omega) P),
      (pathForestComponentBlockCount (by omega) P C : ℚ)) = ((k - 1).factorial : ℚ) := by
    exact_mod_cast pathForestComponentBlockCount_sum hk P
  have hyNat : (∑ C : WeakComponent (pathForest (by omega) P),
      pathForestComponentBudget (by omega) P C) = pathForestTotalBudget (by omega) P := by
    simp [pathForestTotalBudget, weakComponents]
  have hy : (∑ C : WeakComponent (pathForest (by omega) P),
      (pathForestComponentBudget (by omega) P C : ℚ)) =
      (pathForestTotalBudget (by omega) P : ℚ) := by exact_mod_cast hyNat
  simp only [rationalComponentSurplus, Finset.sum_sub_distrib, ← Finset.mul_sum, hb, hy]

end SuperpermutationLowerBound.Refinement
