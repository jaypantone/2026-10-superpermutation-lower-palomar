module

public import SuperpermutationLowerBound.Refinement.ForestAssembly
public import bridge.OneWord

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open scoped BigOperators

variable {k : ℕ}

/-- Every absorbed component costs a uniformly positive part of the affine
margin. This retains the slack discarded in `forest_edge_bound`. -/
theorem forest_edge_bound_with_slack (hk : 7 ≤ k) {δ β ε : ℚ}
    (hδ0 : 0 < δ) (hδ : δ < 1) (hβ : 1 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (hε : ε ≤ 1 - δ)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {q C : ForestVertex hk P} (he : (pathForestAbsorptionGraph hk P).Adj q C) :
    forestIntercept hk P δ β C + ε ≤
      forestOutCharge hk P δ β q + forestInCharge hk P δ β C := by
  classical
  have ht := pathForestAbsorption_target_data hk P he
  have hc : forestCheap hk P C := ⟨⟨C, ht.1⟩, rfl, ht.2⟩
  simp only [forestIntercept, ht.1, hc, ite_false, ite_true, forestInCharge]
  rcases pathForestAbsorption_edgeTypes hk P hP he with hI | hII
  · have hq : q = C := hI.1.1.1.symm
    subst q
    have hs : forestSpecial hk P C := ⟨he, hI.1⟩
    rw [forestOutCharge, if_pos hs, hI.1.2.2.2.1]
    simp only [Nat.sub_self, endpointCharge, Nat.cast_zero, zero_sub,
      max_eq_left (by linarith : -δ ≤ 0),
      min_eq_left (by linarith : (0 : ℚ) ≤ β - 1)]
    linarith
  · have hs : ¬forestSpecial hk P q := by
      intro hs
      have hqC := pathForestAbsorptionGraph_out_unique hk P hs.1 he
      subst C
      exact hII.2 hs.2
    rw [forestOutCharge, if_neg hs]
    have hf := hII.1.2.1
    have hl := hII.1.2.2.1
    have hsum := hII.1.2.2.2.1
    have hfq : 2 ≤ (pathForestComponentFirstDeficit hk P C : ℚ) := by exact_mod_cast hf
    have hlq : 2 ≤ (pathForestComponentLastDeficit hk P q : ℚ) := by exact_mod_cast hl
    have hsumq : (k : ℚ) ≤ (pathForestComponentFirstDeficit hk P C : ℚ) +
        (pathForestComponentLastDeficit hk P q : ℚ) := by exact_mod_cast hsum
    have hkq : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hA : endpointCharge δ (pathForestComponentFirstDeficit hk P C - 1) =
        (pathForestComponentFirstDeficit hk P C : ℚ) - 1 - δ := by
      rw [endpointCharge, Nat.cast_sub (by omega : 1 ≤ pathForestComponentFirstDeficit hk P C),
        Nat.cast_one, max_eq_right (by linarith)]
    have hB : endpointCharge δ (pathForestComponentLastDeficit hk P q) =
        (pathForestComponentLastDeficit hk P q : ℚ) - δ := by
      rw [endpointCharge, max_eq_right (by linarith)]
    rw [hA, hB]
    by_cases ha : (pathForestComponentFirstDeficit hk P C : ℚ) - 1 - δ ≤ β - 1
    · rw [min_eq_left ha]
      rw [hkq] at hβα
      linarith
    · rw [min_eq_right (le_of_not_ge ha)]
      linarith

/-- Marking a single nonroot component adds its charge to the left side of
the forest estimate. No count of components or graph decomposition is needed. -/
theorem pathForest_affine_marked (hk : 7 ≤ k) {δ β ε : ℚ}
    (H : HereditarySegmentBound hk δ β) (hδ0 : 0 < δ) (hδ : δ < 1)
    (hβ : 1 ≤ β) (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ 1 - δ)
    (hεβ : ε ≤ ((k - 1 : ℕ) : ℚ) - δ - β)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (C₀ : ForestVertex hk P) (hC₀ : C₀ ≠ pathForestRootComponent (by omega) P) :
    ((k - 1).factorial : ℚ) + ε ≤ (((k - 1 : ℕ) : ℚ) - δ) *
      ((pathForestTotalBudget (by omega) P : ℚ) + (pathForestV hk P : ℚ)) + β := by
  classical
  let E := ForestEdge hk P
  letI : Fintype E := Fintype.ofFinite E
  let source : E → ForestVertex hk P := fun e => e.1.1
  let target : E → ForestVertex hk P := fun e => e.1.2
  let mark : ForestVertex hk P → ℚ := fun C => if C = C₀ then ε else 0
  let c : ForestVertex hk P → ℚ := fun C => forestIntercept hk P δ β C + mark C
  let s : ForestVertex hk P → ℚ := fun C => rationalComponentSurplus hk P δ C + mark C
  have hmark (C : ForestVertex hk P) : 0 ≤ mark C ∧ mark C ≤ ε := by
    dsimp [mark]
    split <;> constructor <;> linarith
  have hs : Function.Injective source := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext hef
    exact pathForestAbsorptionGraph_out_unique hk P e.2 (by
      have h : e.1.1 = f.1.1 := hef
      rw [h]
      exact f.2)
  have ht : Function.Injective target := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext _ hef
    exact pathForestAbsorptionGraph_in_unique hk P e.2 (by
      have h : e.1.2 = f.1.2 := hef
      rw [h]
      exact f.2)
  have hlocal (C : ForestVertex hk P) : s C +
      (if ∃ e, target e = C then forestInCharge hk P δ β C else 0) +
      (if ∃ e, source e = C then forestOutCharge hk P δ β C else 0) ≤ c C := by
    have hfull := forest_full_local_bound hk H hδ0 hδ hβ hβα P C
    have ha := forestInCharge_nonneg hk P (δ := δ) hβ C
    have hb := forestOutCharge_nonneg hk P hδ hβ C
    dsimp [s, c]
    split <;> split <;> linarith
  have hedge (e : E) : c (target e) ≤
      forestOutCharge hk P δ β (source e) + forestInCharge hk P δ β (target e) := by
    have he := forest_edge_bound_with_slack hk hδ0 hδ hβ hβα hεδ P hP e.2
    have hm := (hmark (target e)).2
    dsimp [c]
    linarith
  have hsum := finite_incidence_assembly source target hs ht s c
    (forestInCharge hk P δ β) (forestOutCharge hk P δ β) hlocal hedge
  have hin (C : ForestVertex hk P) : (∃ e, target e = C) ↔
      ∃ q, (pathForestAbsorptionGraph hk P).Adj q C := by
    constructor
    · rintro ⟨e, he⟩
      exact ⟨source e, by simpa [← he, source, target] using e.2⟩
    · rintro ⟨q, hq⟩
      exact ⟨⟨(q, C), hq⟩, rfl⟩
  simp only [hin] at hsum
  let U := (pathForestUnabsorbedU hk P).image (fun p => p.1)
  let α : ℚ := ((k - 1 : ℕ) : ℚ) - δ
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hUcard : U.card = pathForestV hk P := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      pathForestUnabsorbedU_card]
  have hp (C : ForestVertex hk P) :
      (if ¬∃ q, (pathForestAbsorptionGraph hk P).Adj q C then c C else 0) ≤
        (if C = pathForestRootComponent (by omega) P then β else 0) +
        (if C ∈ U then α else 0) := by
    by_cases hi : ∃ q, (pathForestAbsorptionGraph hk P).Adj q C
    · simp only [hi, not_true_eq_false, ite_false]
      have hr : 0 ≤ (if C = pathForestRootComponent (by omega) P then β else 0) := by
        split <;> linarith
      have hu : 0 ≤ (if C ∈ U then α else 0) := by split <;> linarith
      linarith
    · simp only [hi, not_false_eq_true, ite_true]
      by_cases hr : C = pathForestRootComponent (by omega) P
      · have hm : mark C = 0 := by
          dsimp [mark]
          rw [if_neg (by intro h; exact hC₀ (h.symm.trans hr))]
        have hmroot : mark (pathForestRootComponent (by omega) P) = 0 := by
          simpa only [hr] using hm
        simp only [c, forestIntercept, hr, ite_true, hmroot, add_zero]
        split <;> linarith
      · by_cases hc : forestCheap hk P C
        · have hU : C ∈ U := by
            rcases hc with ⟨p, hpC, hp⟩
            apply Finset.mem_image.mpr
            refine ⟨p, ?_, hpC⟩
            apply (mem_pathForestUnabsorbedU hk P p).mpr
            exact ⟨hp, by simpa [hpC] using hi⟩
          have hm := (hmark C).2
          simp only [c, forestIntercept, hr, hc, hU, ite_false, ite_true, zero_add]
          dsimp [α]
          linarith
        · have hm := (hmark C).2
          simp only [c, forestIntercept, hr, hc, ite_false, zero_add]
          have hu : 0 ≤ (if C ∈ U then α else 0) := by split <;> linarith
          linarith
  have hheads := Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) => hp C)
  rw [Finset.sum_add_distrib] at hheads
  have hroot : (∑ C : ForestVertex hk P,
      if C = pathForestRootComponent (by omega) P then β else 0) = β := by simp
  have hfilter : Finset.univ.filter (fun C => C ∈ U) = U := by ext C; simp
  have hU : (∑ C : ForestVertex hk P, if C ∈ U then α else 0) =
      α * (pathForestV hk P : ℚ) := by
    rw [← Finset.sum_filter, hfilter]
    simp [hUcard, mul_comm]
  rw [hroot, hU] at hheads
  have hfinal := hsum.trans hheads
  have hmarks : (∑ C : ForestVertex hk P, mark C) = ε := by simp [mark]
  simp only [s, Finset.sum_add_distrib] at hfinal
  rw [rationalComponentSurplus_sum hk P δ, hmarks] at hfinal
  dsimp [α] at hfinal
  linarith

/-- A near-equality path has one forest component and no unused residual. -/
theorem pathForest_rigidity_of_margin (hk : 7 ≤ k) {δ β ε : ℚ}
    (H : HereditarySegmentBound hk δ β) (hδ0 : 0 < δ) (hδ : δ < 1)
    (hβ : 1 ≤ β) (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (hε0 : 0 < ε) (hεδ : ε ≤ 1 - δ)
    (hεβ : ε ≤ ((k - 1 : ℕ) : ℚ) - δ - β)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (hmargin : (((k - 1 : ℕ) : ℚ) - δ) *
      ((P.weight : ℚ) - (((k + 1) * (k - 1).factorial : ℕ) : ℚ) + 3) + β -
      ((k - 1).factorial : ℚ) < ε) :
    (∀ C : ForestVertex hk P, C = pathForestRootComponent (by omega) P) ∧
      forestResidualExcess hk P = 0 := by
  have hα : 0 < ((k - 1 : ℕ) : ℚ) - δ := by linarith
  have hbase : 3 ≤ (k + 1) * (k - 1).factorial := by
    have hfac := Nat.factorial_pos (k - 1)
    nlinarith
  have hres := pathForest_residual_exact hk P hP
  have hresQ : (P.weight : ℚ) =
      (((k + 1) * (k - 1).factorial : ℕ) : ℚ) - 3 +
      (pathForestTotalBudget (by omega) P : ℚ) + (pathForestV hk P : ℚ) +
      (forestResidualExcess hk P : ℚ) := by
    simpa only [Nat.cast_add, Nat.cast_sub hbase, Nat.cast_ofNat] using
      congrArg (fun z : ℕ => (z : ℚ)) hres
  have hbudget : (pathForestTotalBudget (by omega) P : ℚ) +
      (pathForestV hk P : ℚ) ≤
      (P.weight : ℚ) - (((k + 1) * (k - 1).factorial : ℕ) : ℚ) + 3 := by
    have := Nat.cast_nonneg (α := ℚ) (forestResidualExcess hk P)
    linarith
  constructor
  · intro C
    by_contra hC
    have hm := pathForest_affine_marked hk H hδ0 hδ hβ hβα
      hε0.le hεδ hεβ P hP C hC
    have hmul := mul_le_mul_of_nonneg_left hbudget hα.le
    linarith
  · have hf := pathForest_affine_assembly hk H hδ0 hδ hβ hβα P hP
    by_contra hr
    have hr1 : (1 : ℚ) ≤ (forestResidualExcess hk P : ℚ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hmul := mul_le_mul_of_nonneg_left hr1 hα.le
    nlinarith

/-- A one-component forest with no unused residual required no surgery:
every rotation-class visit of the original Hamiltonian path was intact. -/
theorem residualVertices_empty_of_rigidity (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (hone : ∀ C : ForestVertex hk P,
      C = pathForestRootComponent (by omega) P)
    (hR : forestResidualExcess hk P = 0) :
    residualVertices (by omega) P = ∅ := by
  classical
  have hU : pathForestUnabsorbedU hk P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p _hp
    exact p.2 (hone p.1)
  have hV : pathForestV hk P = 0 := by
    rw [← pathForestUnabsorbedU_card hk P, hU]
    rfl
  have hselected : pathForestSelectedTailEdges hk P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨p, _hp⟩ := (mem_pathForestSelectedTailEdges hk P e).mp he
    exact p.2 (hone p.1)
  have hzero : forestHeadIndicator P (residualVertices (by omega) P) +
      pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
      pathForestSigmaThree hk P = 0 := by
    simpa only [forestResidualExcess, hV, Nat.sub_zero] using hR
  have hI : forestHeadIndicator P (residualVertices (by omega) P) = 0 := by omega
  have hS : pathForestSigmaTwo hk P = 0 := by omega
  have hsum : (∑ e ∈ forestDeltaOne P (residualVertices (by omega) P),
      (e.weight - 1)) = 0 := by
    simpa only [pathForestSigmaTwo, hselected, Finset.sdiff_empty] using hS
  have hdel : forestDeltaOne P (residualVertices (by omega) P) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hw := pathForestDeltaOne_weight_ge_two hk P he
    have hle := Finset.single_le_sum
      (fun f (_hf : f ∈ forestDeltaOne P (residualVertices (by omega) P)) =>
        Nat.zero_le (f.weight - 1)) he
    rw [hsum] at hle
    omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hout : outgoingEdgesAt P.edgeSet v = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hei := mem_outgoingEdgesAt.mp he
    have hmem : e ∈ forestDeltaOne P (residualVertices (by omega) P) := by
      rw [forestDeltaOne_eq_outgoing]
      exact mem_outgoingEdges.mpr ⟨hei.1, by simpa only [hei.2] using hv⟩
    simpa only [hdel, Finset.notMem_empty] using hmem
  have hhead : v = P.head := by
    have hm := (mem_graphHeads (X := P.edgeSet) (v := v)).mpr hout
    simpa only [P.edgeSet_heads, Finset.mem_singleton] using hm
  have hheadmem : P.head ∈ residualVertices (by omega) P := by simpa only [hhead] using hv
  simp only [forestHeadIndicator, hheadmem, ite_true] at hI
  omega

/-- Empty surgery support identifies the actual forest with the original
Hamiltonian overlap path; this is an equality of literal edge sets. -/
theorem pathForest_eq_edgeSet_of_residual_empty (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hres : residualVertices (by omega) P = ∅) :
    pathForest (by omega) P = P.edgeSet := by
  classical
  have hs1 : forestStepOne (by omega : 2 ≤ k) P ∅ = P.edgeSet := by
    simp [forestStepOne, forestStepZero, forestDeltaOne, outgoingEdges, rotationEdges]
  have hdouble : doubleIncomingVertices (by omega : 2 ≤ k) P ∅ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hv' : inDegree P.edgeSet v = 2 := by
      simpa only [doubleIncomingVertices, hs1, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    have hle := P.edgeSet_inDegree_rule v
    omega
  simp only [pathForest, forestTransform, forestStepTwo, hres, hs1, hdouble]
  simp [incomingEdges, forestStepZero]
 
/-- Keep the cost of heavy seams instead of dropping it in the affine
component estimate. Both literal endpoints are charged only when there
are at least two runs. -/
theorem blockAligned_affine_capacity_with_excess (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hq : 2 ≤ blockAlignedRunCount hk p hp) :
    (pathBlockCount p : ℚ) - (((k - 1 : ℕ) : ℚ) - δ) * (blockAlignedZ p hp : ℚ) +
      endpointCharge δ (blockAlignedFirstDeficit hk p hp) +
      endpointCharge δ (blockAlignedLastDeficit hk p hp) +
      ((((k - 1 : ℕ) : ℚ) - δ) - β) *
        (blockAlignedRunBoundaryExcess hk p hp : ℚ) ≤ β := by
  have hs := blockAligned_affine_endpoint_sum hk H p hp True (fun _ => hq)
  simp only [ite_true] at hs
  have hm : 1 ≤ (blockAlignedLightSegments hk p hp).length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  have he := blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one hk p hp
  have heq : (((blockAlignedLightSegments hk p hp).length : ℚ) - 1) ≤
      (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by
    have hh : (blockAlignedLightSegments hk p hp).length ≤
        blockAlignedRunBoundaryExcess hk p hp + 1 := by omega
    have hc : ((blockAlignedLightSegments hk p hp).length : ℚ) ≤
        (blockAlignedRunBoundaryExcess hk p hp : ℚ) + 1 := by exact_mod_cast hh
    linarith
  have hmul := mul_le_mul_of_nonneg_left heq hβ
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

/-- Near equality forces a single light segment with full endpoint runs.
The hypotheses concern an actual block-aligned path, not a deficit model. -/
theorem blockAligned_endpoint_rigidity (hk : 7 ≤ k) {δ β ε : ℚ}
    (H : HereditarySegmentBound hk δ β) (hβ : 0 ≤ β)
    (hε0 : 0 < ε) (hεδ : ε ≤ 1 - δ)
    (hεβ : ε ≤ ((k - 1 : ℕ) : ℚ) - δ - β)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hq : 2 ≤ blockAlignedRunCount hk p hp)
    (hmargin : (((k - 1 : ℕ) : ℚ) - δ) * (blockAlignedZ p hp : ℚ) + β -
      (pathBlockCount p : ℚ) < ε) :
    blockAlignedRunBoundaryExcess hk p hp = 0 ∧
      blockAlignedFirstDeficit hk p hp = 0 ∧
      blockAlignedLastDeficit hk p hp = 0 := by
  have hc := blockAligned_affine_capacity_with_excess hk H hβ p hp hq
  have hf := endpointCharge_nonneg δ (blockAlignedFirstDeficit hk p hp)
  have hl := endpointCharge_nonneg δ (blockAlignedLastDeficit hk p hp)
  have hE : 0 ≤ (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by positivity
  have hcoef : 0 ≤ ((k - 1 : ℕ) : ℚ) - δ - β := by linarith
  have hmul := mul_nonneg hcoef hE
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    have hpos : (1 : ℚ) ≤ (blockAlignedRunBoundaryExcess hk p hp : ℚ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
    nlinarith
  · by_contra hne
    have hpos : (1 : ℚ) ≤ (blockAlignedFirstDeficit hk p hp : ℚ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
    have hbound : (blockAlignedFirstDeficit hk p hp : ℚ) - δ ≤
        endpointCharge δ (blockAlignedFirstDeficit hk p hp) := le_max_right _ _
    nlinarith
  · by_contra hne
    have hpos : (1 : ℚ) ≤ (blockAlignedLastDeficit hk p hp : ℚ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
    have hbound : (blockAlignedLastDeficit hk p hp : ℚ) - δ ≤
        endpointCharge δ (blockAlignedLastDeficit hk p hp) := le_max_right _ _
    nlinarith
 
/-- With one component, its literal block count and budget are the global
counts. This is only a singleton finite-sum identity. -/
theorem pathForest_root_totals_of_unique (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (hone : ∀ C : ForestVertex hk P,
      C = pathForestRootComponent (by omega) P) :
    pathForestComponentBlockCount (by omega) P
        (pathForestRootComponent (by omega) P) = (k - 1).factorial ∧
      pathForestTotalBudget (by omega) P =
        pathForestComponentZ (by omega) P (pathForestRootComponent (by omega) P) ∧
      pathForestV hk P = 0 := by
  classical
  have huniv : (Finset.univ : Finset (ForestVertex hk P)) =
      {pathForestRootComponent (show 3 ≤ k from by omega) P} := by
    ext C
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hone C
  have hblocks := pathForestComponentBlockCount_sum hk P
  rw [huniv, Finset.sum_singleton] at hblocks
  refine ⟨hblocks, ?_, ?_⟩
  · change (∑ C : ForestVertex hk P, pathForestComponentBudget (by omega) P C) = _
    rw [huniv, Finset.sum_singleton, pathForestComponentBudget_root]
  · rw [← pathForestUnabsorbedU_card hk P]
    have hempty : pathForestUnabsorbedU hk P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p _hp
      exact p.2 (hone p.1)
    rw [hempty]
    rfl
 
/-- A forest with just its root covers every permutation in that root's
literal component path. -/
theorem pathForest_root_complete_of_unique (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (hone : ∀ C : ForestVertex hk P,
      C = pathForestRootComponent (by omega) P) :
    (pathForestComponentPath (by omega) P
      (pathForestRootComponent (by omega) P)).vertexSet = Finset.univ := by
  classical
  rw [pathForestComponentPath_vertexSet]
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  let C : ForestVertex hk P :=
    (underlyingSimpleGraph (pathForest (by omega) P)).connectedComponentMk v
  have hv : v ∈ C.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rw [hone C] at hv
  exact mem_weakComponentVertices.mpr hv

/-- With no heavy seam, the entire actual run list is one of its maximal
light segments. -/
theorem exists_whole_light_segment_of_excess_zero (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hE : blockAlignedRunBoundaryExcess hk p hp = 0) :
    ∃ s : BlockAlignedLightSegment hk p hp, s.runs = blockAlignedRuns hk p hp := by
  classical
  have hn := List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  have he := blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one hk p hp
  have hlen : (blockAlignedLightSegments hk p hp).length = 1 := by omega
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hlen
  have hflat := (blockAlignedLightSegments_spec hk p hp).1
  rw [hr] at hflat
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hflat
  have hseg : blockAlignedLightSegments hk p hp = [blockAlignedRuns hk p hp] := by
    simpa only [hflat] using hr
  refine ⟨⟨blockAlignedRuns hk p hp, ?_⟩, rfl⟩
  rw [hseg]
  simp

/-- The frozen geometric theorem supplies the exact fourteen-letter
packing premise used below. -/
theorem actualPacking_fourteen_explicit :
    _root_.SuperpermutationLowerBound.ChainReturns.ActualPacking 14 (by omega)
      36 (569 / 15) := by
  have h := _root_.SuperpermutationLowerBound.ChainReturns.frozen_actualPacking_fourteen
  rw [_root_.SuperpermutationLowerBound.ChainReturns.exactParameters_fourteen] at h
  exact h

theorem hereditary_fourteen_explicit :
    HereditarySegmentBound (by omega : 7 ≤ 14) (1138 / 6229) (15816 / 6229) := by
  have ha : _root_.SuperpermutationLowerBound.ChainReturns.Admissible 13 36 (569 / 15) := by
    constructor <;> norm_num
  have h := _root_.SuperpermutationLowerBound.ChainReturns.hereditary_of_actualPacking
    (by omega : 8 ≤ 14) ha actualPacking_fourteen_explicit
  norm_num [_root_.SuperpermutationLowerBound.ChainReturns.delta,
    _root_.SuperpermutationLowerBound.ChainReturns.beta,
    _root_.SuperpermutationLowerBound.ChainReturns.lam,
    _root_.SuperpermutationLowerBound.ChainReturns.intercept] at h
  exact h

/-- All scalar data needed for the new contradiction are derived from the
actual reduced minimum path at the old fourteen-letter bound. -/
theorem exists_fourteen_rigid_segment_of_weight
    (P : HamiltonianPath 14) (hP : IsReducedMinimumPath P)
    (hweight : P.weight = 93891141135) :
    ∃ (p : OverlapPath 14) (hp : IsBlockAligned p)
        (s : BlockAlignedLightSegment (by omega : 7 ≤ 14) p hp),
      p.vertexSet = Finset.univ ∧ s.runs = blockAlignedRuns (by omega) p hp ∧
      s.deficitString.length = 485829138 ∧ s.deficitString.sum = 88757994 ∧
      s.deficitString.head? = some 0 ∧ s.deficitString.getLast? = some 0 ∧
      IsLegalDeficitSequence 13 s.deficitString ∧
      ChainPacking 11 36 (569 / 15) s.deficitString ∧
      scalarEnergy 11 36 (569 / 15) s.deficitString = 1398 / 15 := by
  classical
  let hk : 7 ≤ 14 := by omega
  have hrig := pathForest_rigidity_of_margin hk hereditary_fourteen_explicit
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ε := (1 / 2 : ℚ)) (by norm_num) (by norm_num) (by norm_num) P hP
    (by norm_num [hweight, Nat.factorial])
  have htot := pathForest_root_totals_of_unique hk P hrig.1
  let C := pathForestRootComponent (by omega : 3 ≤ 14) P
  let p := pathForestComponentPath (by omega : 3 ≤ 14) P C
  let hp : IsBlockAligned p := pathForestComponentPath_blockAligned (by omega) P C
  have hb : pathBlockCount p = 6227020800 := by
    have hh := htot.1
    norm_num [Nat.factorial] at hh
    exact hh
  have hres := pathForest_residual_exact hk P hP
  have hbudget : pathForestTotalBudget (by omega) P = 485829138 := by
    rw [hweight, htot.2.2, hrig.2] at hres
    norm_num [Nat.factorial] at hres
    omega
  have hz : blockAlignedZ p hp = 485829138 := by
    change pathForestComponentZ (by omega) P C = _
    rw [← htot.2.1]
    exact hbudget
  have hq : 2 ≤ blockAlignedRunCount hk p hp := by
    have hblocks := pathBlockCount_eq_runCount_sub_totalDeficit hk p hp
    rw [hb] at hblocks
    norm_num at hblocks
    omega
  have hend := blockAligned_endpoint_rigidity hk hereditary_fourteen_explicit
    (by norm_num) (ε := (1 / 2 : ℚ)) (by norm_num) (by norm_num)
    (by norm_num) p hp hq (by norm_num [hz, hb])
  have hqexact : blockAlignedRunCount hk p hp = 485829138 := by
    have hh := blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp
    rw [hz, hend.1] at hh
    omega
  have hD : blockAlignedTotalDeficit hk p hp = 88757994 := by
    have hh := pathBlockCount_eq_runCount_sub_totalDeficit hk p hp
    rw [hb, hqexact] at hh
    norm_num at hh
    omega
  obtain ⟨s, hs⟩ := exists_whole_light_segment_of_excess_zero hk p hp hend.1
  have hd : s.deficitString = blockAlignedDeficitString hk p hp := by
    simp only [BlockAlignedLightSegment.deficitString, blockAlignedDeficitString, hs]
  have hlen : s.deficitString.length = 485829138 := by
    rw [hd, blockAlignedDeficitString_length, hqexact]
  have hsum : s.deficitString.sum = 88757994 := by
    rw [hd]
    exact hD
  have hne : s.deficitString ≠ [] := by
    intro hh
    simp only [hh, List.length_nil] at hlen
    omega
  have hfirst : s.deficitString.head hne = 0 := by
    have hh := hend.2.1
    change (blockAlignedDeficitString hk p hp).head _ = 0 at hh
    simpa only [← hd] using hh
  have hlast : s.deficitString.getLast hne = 0 := by
    have hh := hend.2.2
    change (blockAlignedDeficitString hk p hp).getLast _ = 0 at hh
    simpa only [← hd] using hh
  refine ⟨p, hp, s, ?_, hs, hlen, hsum, ?_, ?_, ?_, ?_, ?_⟩
  · exact pathForest_root_complete_of_unique hk P hrig.1
  · simpa only [List.head?_eq_some_head hne, hfirst]
  · simpa only [List.getLast?_eq_some_getLast hne, hlast]
  · exact blockAlignedLightSegment_deficitString_legal hk p hp s
  · exact actualPacking_fourteen_explicit p hp s
  · norm_num [scalarEnergy, chainLambda, chainIntercept, hsum, hlen]

end SuperpermutationLowerBound.Refinement
