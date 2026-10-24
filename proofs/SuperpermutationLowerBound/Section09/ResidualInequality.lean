module

public import SuperpermutationLowerBound.Section08.ComponentCapacity

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 9 through the residual inequality.
All component and edge families below are the literal families attached to the reduced
minimum Hamiltonian path and its transformed forest.
-/

open PermutationVertex

variable {k : ℕ}

/-- The genuine finite type of nonroot components of `F(P)`. -/
abbrev PathForestNonrootComponent (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  {C : WeakComponent (pathForest (by omega) P) //
    C ≠ pathForestRootComponent (by omega) P}

noncomputable instance pathForestNonrootComponentFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) : Fintype (PathForestNonrootComponent hk P) :=
  Fintype.ofFinite _

/-- A component tail is a vertex of that component. -/
theorem pathForestComponentTail_mem_component_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentTail (by omega) P C ∈ weakComponentVertices C := by
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  exact List.mem_toFinset.mpr
    ((pathForestComponentPath (by omega) P C).vertex_mem
      ⟨0, (pathForestComponentPath (by omega) P C).length_pos⟩)

/-- A component head is a vertex of that component. -/
theorem pathForestComponentHead_mem_component_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentHead (by omega) P C ∈ weakComponentVertices C := by
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  exact List.mem_toFinset.mpr
    (by simp [pathForestComponentHead, List.getLast_mem])

/-- Equality of the genuine component tails determines the component. -/
theorem pathForestComponent_eq_of_tail_eq_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    {C D : WeakComponent (pathForest (by omega) P)}
    (h : pathForestComponentTail (by omega) P C =
      pathForestComponentTail (by omega) P D) : C = D := by
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (mem_weakComponentVertices.mp
      (pathForestComponentTail_mem_component_I hk P C))
  have hD := mem_weakComponentVertices.mp
    (pathForestComponentTail_mem_component_I hk P D)
  simpa [h] using hD

/-- Every named component tail is a genuine graph tail of `F(P)`. -/
theorem pathForestComponentTail_mem_graphTails_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentTail (by omega) P C ∈
      graphTails (pathForest (by omega) P) := by
  classical
  apply mem_graphTails.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have heInfo := mem_incomingEdgesAt.mp he
  have htargetC : e.target ∈ C.supp := by
    simpa [heInfo.2] using
      mem_weakComponentVertices.mp
        (pathForestComponentTail_mem_component_I hk P C)
  have hsourceC := weakComponent_edge_source_mem C htargetC heInfo.1
  have heWeak : e ∈ weakComponentEdges C :=
    mem_weakComponentEdges.mpr ⟨heInfo.1, hsourceC, htargetC⟩
  have heIn : e ∈ incomingEdgesAt (weakComponentEdges C)
      (pathForestComponentTail (by omega) P C) :=
    mem_incomingEdgesAt.mpr ⟨heWeak, heInfo.2⟩
  have hempty : incomingEdgesAt (weakComponentEdges C)
      (pathForestComponentTail (by omega) P C) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentInDegree, inDegree] using
      pathForestComponentTail_inDegree_zero (by omega) P C
  rw [hempty] at heIn
  simp at heIn

private theorem pathForestNonroot_tail_ne_pathTail (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    pathForestComponentTail (by omega) P p.1 ≠ P.tail := by
  intro htail
  apply p.2
  apply (pathForestComponent_eq_root_iff (by omega) P p.1).mpr
  simpa [htail] using pathForestComponentTail_mem_component_I hk P p.1

private theorem predecessorIndex_pos (P : HamiltonianPath k)
    (v : PermutationVertex k) (hv : v ≠ P.tail) :
    0 < P.vertexIndex v := by
  by_contra hnot
  have hzero : P.vertexIndex v = 0 := Nat.eq_zero_of_not_pos hnot
  apply hv
  apply P.vertexIndex_injective
  rw [hzero, P.vertexIndex_tail]

/-- For a nonroot component `p`, the actual edge of `P` entering its tail. -/
noncomputable def pathForestTailEdge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) : DirectedOverlapEdge k :=
  let v := pathForestComponentTail (by omega) P p.1
  let hv := pathForestNonroot_tail_ne_pathTail hk P p
  P.indexedEdge ⟨P.vertexIndex v - 1, by
    have hpos := predecessorIndex_pos P v hv
    have hlt := P.vertexIndex_lt_length v
    omega⟩

/-- The selected edge `e_p` is literally an edge of `P`. -/
theorem pathForestTailEdge_mem_path (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    pathForestTailEdge hk P p ∈ P.edgeSet := by
  apply HamiltonianPath.mem_edgeSet.mpr
  refine ⟨⟨P.vertexIndex (pathForestComponentTail (by omega) P p.1) - 1, ?_⟩, rfl⟩
  have hpos := predecessorIndex_pos P
    (pathForestComponentTail (by omega) P p.1)
    (pathForestNonroot_tail_ne_pathTail hk P p)
  have hlt := P.vertexIndex_lt_length
    (pathForestComponentTail (by omega) P p.1)
  omega

/-- The target of `e_p` is exactly the component tail `v_p`. -/
theorem pathForestTailEdge_target (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    (pathForestTailEdge hk P p).target =
      pathForestComponentTail (by omega) P p.1 := by
  let v := pathForestComponentTail (by omega) P p.1
  have hpos := predecessorIndex_pos P v
    (pathForestNonroot_tail_ne_pathTail hk P p)
  have hlt : P.vertexIndex v - 1 + 1 < P.vertices.length := by
    have := P.vertexIndex_lt_length v
    omega
  change P.vertices[P.vertexIndex v - 1 + 1]'hlt = v
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ P.vertexIndex v)] using
    P.getElem_vertexIndex v

/-- The source of `e_p` lies genuinely outside the component. -/
theorem pathForestTailEdge_source_outside (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    (pathForestTailEdge hk P p).source ∈
      pathForestComponentOutsideVertices (by omega) P p.1 := by
  apply (mem_pathForestComponentOutsideVertices_iff (by omega) P p.1 _).mpr
  intro hsource
  have hearly := pathForestComponentTail_earliest (by omega) P p.1 hsource
  have hbefore := HamiltonianPath.strictlyPrecedes_of_edge
    (pathForestTailEdge_mem_path hk P p)
  change P.vertexIndex (pathForestTailEdge hk P p).source <
    P.vertexIndex (pathForestTailEdge hk P p).target at hbefore
  rw [pathForestTailEdge_target hk P p] at hbefore
  omega

/-- The actual outside-entry minimum of a nonroot component. -/
noncomputable def pathForestNonrootMinto (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) : ℕ :=
  pathForestMinto (by omega) P p.1
    (pathForestComponent_vertexSet_ne_univ_of_nonroot (by omega) P p.1 p.2)

/-- The genuine selected edge has weight at least the actual `minto`. -/
theorem pathForestNonrootMinto_le_tailEdge_weight (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    pathForestNonrootMinto hk P p ≤ (pathForestTailEdge hk P p).weight := by
  have hle := pathForestMinto_le (by omega) P p.1
    (pathForestComponent_vertexSet_ne_univ_of_nonroot (by omega) P p.1 p.2)
    (pathForestTailEdge_source_outside hk P p)
  simpa [pathForestNonrootMinto, DirectedOverlapEdge.weight,
    pathForestTailEdge_target hk P p] using hle

/-- The actual nonroot entry cost lies in the frozen range `2,...,k`. -/
theorem pathForestNonrootMinto_bounds (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    2 ≤ pathForestNonrootMinto hk P p ∧ pathForestNonrootMinto hk P p ≤ k := by
  simpa [pathForestNonrootMinto] using
    pathForestMinto_bounds (by omega) P p.1
      (pathForestComponent_vertexSet_ne_univ_of_nonroot (by omega) P p.1 p.2)

/-- Every selected nonroot tail edge belongs to the literal Step-1 deletion set `Δ₁`. -/
theorem pathForestTailEdge_mem_deltaOne (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    pathForestTailEdge hk P p ∈
      forestDeltaOne P (residualVertices (by omega) P) := by
  have htailX : pathForestComponentTail (by omega) P p.1 ∈
      graphTails (pathForest (by omega) P) :=
    pathForestComponentTail_mem_graphTails_I hk P p.1
  have htailNotP : pathForestComponentTail (by omega) P p.1 ∉
      graphTails P.edgeSet := by
    rw [P.edgeSet_tails]
    simpa using pathForestNonroot_tail_ne_pathTail hk P p
  have hincoming : pathForestTailEdge hk P p ∈
      incomingEdges P.edgeSet
        (graphTails (pathForest (by omega) P) \ graphTails P.edgeSet) := by
    apply mem_incomingEdges.mpr
    refine ⟨pathForestTailEdge_mem_path hk P p, ?_⟩
    rw [pathForestTailEdge_target hk P p]
    exact Finset.mem_sdiff.mpr ⟨htailX, htailNotP⟩
  exact forestIncoming_newTails_subset_deltaOne (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P) hincoming

/-- The map `p ↦ e_p` is injective on genuine nonroot components. -/
theorem pathForestTailEdge_injective (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Function.Injective (pathForestTailEdge hk P) := by
  intro p q hpq
  apply Subtype.ext
  apply pathForestComponent_eq_of_tail_eq_I hk P
  calc
    pathForestComponentTail (by omega) P p.1 =
        (pathForestTailEdge hk P p).target :=
      (pathForestTailEdge_target hk P p).symm
    _ = (pathForestTailEdge hk P q).target :=
      congrArg DirectedOverlapEdge.target hpq
    _ = pathForestComponentTail (by omega) P q.1 :=
      pathForestTailEdge_target hk P q

/-- The literal finite set `{e_p : p nonroot}` of selected tail edges. -/
noncomputable def pathForestSelectedTailEdges (hk : 7 ≤ k)
    (P : HamiltonianPath k) : FiniteDirectedSubgraph k := by
  classical
  exact Finset.univ.image (pathForestTailEdge hk P)

@[simp]
theorem mem_pathForestSelectedTailEdges (hk : 7 ≤ k)
    (P : HamiltonianPath k) (e : DirectedOverlapEdge k) :
    e ∈ pathForestSelectedTailEdges hk P ↔
      ∃ p : PathForestNonrootComponent hk P, pathForestTailEdge hk P p = e := by
  classical
  simp [pathForestSelectedTailEdges]

/-- The selected family consists of exactly `c-1` distinct actual path edges. -/
theorem pathForestSelectedTailEdges_card (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestSelectedTailEdges hk P).card =
      pathForestComponentCount (by omega) P - 1 := by
  classical
  rw [pathForestSelectedTailEdges,
    Finset.card_image_of_injective _ (pathForestTailEdge_injective hk P)]
  rw [Finset.card_univ, pathForestComponentCount_eq_fintypeCard]
  simp [PathForestNonrootComponent]

/-- The full selected family is contained in the actual `Δ₁`. -/
theorem pathForestSelectedTailEdges_subset_deltaOne (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    pathForestSelectedTailEdges hk P ⊆
      forestDeltaOne P (residualVertices (by omega) P) := by
  intro e he
  obtain ⟨p, rfl⟩ := (mem_pathForestSelectedTailEdges hk P e).mp he
  exact pathForestTailEdge_mem_deltaOne hk P p

/-! ## The three literal residual sums -/

/-- `Σ₁`, summed over exactly the selected nonroot tail edges. -/
noncomputable def pathForestSigmaOne (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℕ :=
  Finset.univ.sum fun p : PathForestNonrootComponent hk P =>
    (pathForestTailEdge hk P p).weight - pathForestNonrootMinto hk P p

/-- `Σ₂`, summed over exactly the Step-1 edges not selected as any `e_p`. -/
noncomputable def pathForestSigmaTwo (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℕ :=
  ∑ e ∈ forestDeltaOne P (residualVertices (by omega) P) \
      pathForestSelectedTailEdges hk P, (e.weight - 1)

/-- `Σ₃`, summed over exactly all Step-2 deleted edges. -/
noncomputable def pathForestSigmaThree (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℕ :=
  ∑ e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P),
    (e.weight - 2)

/-- Every Step-1 deleted edge has weight at least two. -/
theorem pathForestDeltaOne_weight_ge_two (hk : 7 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k}
    (he : e ∈ forestDeltaOne P (residualVertices (by omega) P)) :
    2 ≤ e.weight := by
  have heInfo := mem_outgoingEdges.mp he
  have hres := (mem_residualVertices_iff (by omega) P e.source).mp heInfo.2
  have hpos : 1 ≤ e.weight := (overlapWeight_spec e.source e.target).1
  by_contra hnot
  have hone : overlapWeight e.source e.target = 1 := by
    change e.weight = 1
    omega
  have htarget := (unique_weight_one_successor e.source e.target (by omega) e.ne).mp hone
  apply hres.2
  have hedge : e = rotationEdge (by omega) e.source := by
    cases e with
    | mk source target hne =>
        simp_all [rotationEdge]
  rw [← hedge]
  exact heInfo.1

/-- The subtraction in every `Σ₁` summand is justified by the actual outside minimum. -/
theorem pathForestSigmaOne_subtraction_exact (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    (pathForestTailEdge hk P p).weight - pathForestNonrootMinto hk P p +
        pathForestNonrootMinto hk P p =
      (pathForestTailEdge hk P p).weight := by
  have := pathForestNonrootMinto_le_tailEdge_weight hk P p
  omega

/-- The subtraction in every `Σ₂` summand is justified. -/
theorem pathForestSigmaTwo_subtraction_exact (hk : 7 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k}
    (he : e ∈ forestDeltaOne P (residualVertices (by omega) P) \
      pathForestSelectedTailEdges hk P) :
    e.weight - 1 + 1 = e.weight := by
  have := pathForestDeltaOne_weight_ge_two hk P (Finset.mem_sdiff.mp he).1
  omega

/-- The subtraction in every `Σ₃` summand is justified for a reduced minimum path. -/
theorem pathForestSigmaThree_subtraction_exact (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {e : DirectedOverlapEdge k}
    (he : e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P)) :
    e.weight - 2 + 2 = e.weight := by
  have := (reducedMinimumPath_newHeadWeight (by omega) P hP).1 e he
  omega

/-- The four residual quantities in Lemma 9.1 are separately nonnegative. -/
theorem pathForestHeadIndicator_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    0 ≤ forestHeadIndicator P (residualVertices (by omega) P) :=
  Nat.zero_le _

theorem pathForestSigmaOne_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) : 0 ≤ pathForestSigmaOne hk P :=
  Nat.zero_le _

theorem pathForestSigmaTwo_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) : 0 ≤ pathForestSigmaTwo hk P :=
  Nat.zero_le _

theorem pathForestSigmaThree_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) : 0 ≤ pathForestSigmaThree hk P :=
  Nat.zero_le _

theorem pathForestResidualQuantities_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    0 ≤ forestHeadIndicator P (residualVertices (by omega) P) ∧
      0 ≤ pathForestSigmaOne hk P ∧
      0 ≤ pathForestSigmaTwo hk P ∧
      0 ≤ pathForestSigmaThree hk P := by
  exact ⟨pathForestHeadIndicator_nonnegative hk P,
    pathForestSigmaOne_nonnegative hk P,
    pathForestSigmaTwo_nonnegative hk P,
    pathForestSigmaThree_nonnegative hk P⟩

private theorem weakComponentEdges_biUnion_eq
    (X : FiniteDirectedSubgraph k) :
    (weakComponents X).biUnion weakComponentEdges = X := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨C, _hC, heC⟩ := Finset.mem_biUnion.mp he
    exact (mem_weakComponentEdges.mp heC).1
  · intro he
    let C : WeakComponent X :=
      (underlyingSimpleGraph X).connectedComponentMk e.source
    have hsource : e.source ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have htarget : e.target ∈ C.supp :=
      weakComponent_edge_target_mem C hsource he
    apply Finset.mem_biUnion.mpr
    exact ⟨C, by simp [weakComponents],
      mem_weakComponentEdges.mpr ⟨he, hsource, htarget⟩⟩

private theorem weakComponentEdges_pairwiseDisjoint
    (X : FiniteDirectedSubgraph k) :
    (↑(weakComponents X) : Set (WeakComponent X)).PairwiseDisjoint
      weakComponentEdges := by
  intro C _hC D _hD hCD
  change Disjoint (weakComponentEdges C) (weakComponentEdges D)
  rw [Finset.disjoint_left]
  intro e heC heD
  apply hCD
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (mem_weakComponentEdges.mp heC).2.1
  exact (mem_weakComponentEdges.mp heD).2.1

private theorem graphWeight_eq_sum_weakComponents
    (X : FiniteDirectedSubgraph k) :
    graphWeight X =
      ∑ C : WeakComponent X, graphWeight (weakComponentEdges C) := by
  classical
  calc
    graphWeight X =
        graphWeight ((weakComponents X).biUnion weakComponentEdges) := by
      rw [weakComponentEdges_biUnion_eq X]
    _ = ∑ C ∈ weakComponents X, graphWeight (weakComponentEdges C) := by
      rw [graphWeight,
        Finset.sum_biUnion (weakComponentEdges_pairwiseDisjoint X)]
      rfl
    _ = ∑ C : WeakComponent X, graphWeight (weakComponentEdges C) := by
      simp [weakComponents]

private theorem overlapPath_graphWeight_edgeSet (p : OverlapPath k) :
    graphWeight p.edgeSet = p.weight := by
  classical
  have hinjective : Function.Injective
      (fun i : Fin (p.length - 1) => p.edgeAt i.1 (by omega)) := by
    intro i j hij
    apply Fin.ext
    have hsource := congrArg DirectedOverlapEdge.source hij
    have hi : i.1 < p.vertices.length := by
      have := i.2
      have := p.length_pos
      simp [OverlapPath.length] at *
      omega
    have hj : j.1 < p.vertices.length := by
      have := j.2
      have := p.length_pos
      simp [OverlapPath.length] at *
      omega
    change p.vertices[i.1]'hi = p.vertices[j.1]'hj at hsource
    exact p.nodup.getElem_inj_iff.mp hsource
  calc
    graphWeight p.edgeSet =
        ∑ i : Fin (p.length - 1), (p.edgeAt i.1 (by omega)).weight := by
      rw [graphWeight, OverlapPath.edgeSet,
        Finset.sum_image (fun _ _ _ _ h => hinjective h)]
    _ = ∑ i : Fin (p.length - 1), pathEdgeWeight p i.1 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [pathEdgeWeight_of_lt p i.1 (by omega)]
      rfl
    _ = ∑ i ∈ Finset.range (p.length - 1), pathEdgeWeight p i :=
      Fin.sum_univ_eq_sum_range _ _
    _ = p.weight := (OverlapPath.weight_eq_sum_edges p).symm

private theorem pathForest_graphWeight_eq_sum_componentWeights
    (hk : 7 ≤ k) (P : HamiltonianPath k) :
    graphWeight (pathForest (by omega) P) =
      ∑ C : WeakComponent (pathForest (by omega) P),
        (pathForestComponentPath (by omega) P C).weight := by
  rw [graphWeight_eq_sum_weakComponents]
  apply Finset.sum_congr rfl
  intro C _hC
  rw [← pathForestComponentPath_edgeSet (by omega) P C,
    overlapPath_graphWeight_edgeSet]

private theorem weakComponentVertices_biUnion_eq_univ
    (X : FiniteDirectedSubgraph k) :
    (weakComponents X).biUnion weakComponentVertices =
      (Finset.univ : Finset (PermutationVertex k)) := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  let C : WeakComponent X :=
    (underlyingSimpleGraph X).connectedComponentMk v
  exact ⟨C, by simp [weakComponents], mem_weakComponentVertices.mpr (by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff])⟩

private theorem weakComponentVertices_pairwiseDisjoint
    (X : FiniteDirectedSubgraph k) :
    (↑(weakComponents X) : Set (WeakComponent X)).PairwiseDisjoint
      weakComponentVertices := by
  intro C _hC D _hD hCD
  change Disjoint (weakComponentVertices C) (weakComponentVertices D)
  rw [Finset.disjoint_left]
  intro v hvC hvD
  exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (mem_weakComponentVertices.mp hvC)
    (mem_weakComponentVertices.mp hvD))

private theorem sum_weakComponentVertices_card
    (X : FiniteDirectedSubgraph k) :
    (∑ C : WeakComponent X, (weakComponentVertices C).card) =
      Fintype.card (PermutationVertex k) := by
  classical
  have hcard := Finset.card_biUnion (weakComponentVertices_pairwiseDisjoint X)
  rw [weakComponentVertices_biUnion_eq_univ X] at hcard
  simpa [weakComponents] using hcard.symm

private theorem pathForestComponent_vertices_card_eq_mul_blocks
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (weakComponentVertices C).card =
      k * pathForestComponentBlockCount (by omega) P C := by
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  change (pathForestComponentPath (by omega) P C).vertices.toFinset.card = _
  rw [List.toFinset_card_of_nodup
    (pathForestComponentPath (by omega) P C).nodup]
  exact blockAligned_length_eq
    (pathForestComponentPath_blockAligned (by omega) P C)

/-- The genuine component block counts sum to the `T=(k-1)!` rotation classes. -/
theorem pathForestComponentBlockCount_sum (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (∑ C : WeakComponent (pathForest (by omega) P),
      pathForestComponentBlockCount (by omega) P C) = (k - 1).factorial := by
  have hvertices := sum_weakComponentVertices_card (pathForest (by omega) P)
  have hcard : Fintype.card (PermutationVertex k) = k.factorial :=
    permutationVertex_card k
  have hfactorial : k.factorial = k * (k - 1).factorial := by
    calc
      k.factorial = ((k - 1) + 1).factorial := by congr 1; omega
      _ = ((k - 1) + 1) * (k - 1).factorial := Nat.factorial_succ (k - 1)
      _ = k * (k - 1).factorial := by congr 1; omega
  rw [hcard, hfactorial] at hvertices
  simp_rw [pathForestComponent_vertices_card_eq_mul_blocks hk P] at hvertices
  rw [← Finset.mul_sum] at hvertices
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) hvertices

private theorem pathForest_weight_normalized (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    graphWeight (pathForest (by omega) P) +
        2 * pathForestComponentCount (by omega) P =
      (k + 1) * (k - 1).factorial +
        ∑ C : WeakComponent (pathForest (by omega) P),
          pathExcess (pathForestComponentPath (by omega) P C)
            (pathForestComponentPath_blockAligned (by omega) P C) := by
  classical
  let componentWeight := fun C : WeakComponent (pathForest (by omega) P) =>
    (pathForestComponentPath (by omega) P C).weight
  let componentExcess := fun C : WeakComponent (pathForest (by omega) P) =>
    pathExcess (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C)
  have hcomponent : ∀ C : WeakComponent (pathForest (by omega) P),
      componentWeight C + 2 =
        (k + 1) * pathForestComponentBlockCount (by omega) P C +
          componentExcess C := by
    intro C
    have hweight := blockAligned_weight_eq
      (pathForestComponentPath_blockAligned (by omega) P C) (by omega)
    have hb := pathForestComponentBlockCount_pos (by omega) P C
    change (pathForestComponentPath (by omega) P C).weight + 2 = _
    change (pathForestComponentPath (by omega) P C).weight =
      (k + 1) * pathForestComponentBlockCount (by omega) P C - 2 +
        componentExcess C at hweight
    have hbase : 2 ≤
        (k + 1) * pathForestComponentBlockCount (by omega) P C := by
      nlinarith
    omega
  calc
    graphWeight (pathForest (by omega) P) +
          2 * pathForestComponentCount (by omega) P =
        (∑ C : WeakComponent (pathForest (by omega) P), componentWeight C) +
          ∑ _C : WeakComponent (pathForest (by omega) P), 2 := by
      rw [pathForest_graphWeight_eq_sum_componentWeights hk P,
        pathForestComponentCount_eq_fintypeCard]
      simp [componentWeight, Nat.mul_comm]
    _ = ∑ C : WeakComponent (pathForest (by omega) P),
          (componentWeight C + 2) := by rw [Finset.sum_add_distrib]
    _ = ∑ C : WeakComponent (pathForest (by omega) P),
          ((k + 1) * pathForestComponentBlockCount (by omega) P C +
            componentExcess C) := by
      apply Finset.sum_congr rfl
      intro C _hC
      exact hcomponent C
    _ = (k + 1) *
          (∑ C : WeakComponent (pathForest (by omega) P),
            pathForestComponentBlockCount (by omega) P C) +
          ∑ C : WeakComponent (pathForest (by omega) P), componentExcess C := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (k + 1) * (k - 1).factorial +
          ∑ C : WeakComponent (pathForest (by omega) P),
            pathExcess (pathForestComponentPath (by omega) P C)
              (pathForestComponentPath_blockAligned (by omega) P C) := by
      rw [pathForestComponentBlockCount_sum hk P]

private theorem pathForest_nonroot_budget_normalized (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    pathForestComponentBudget (by omega) P p.1 =
      pathExcess (pathForestComponentPath (by omega) P p.1)
          (pathForestComponentPath_blockAligned (by omega) P p.1) +
        (pathForestNonrootMinto hk P p - 1) := by
  rw [pathForestComponentBudget_nonroot_split (by omega) P p.1 p.2]
  change
    pathForestComponentZ (by omega) P p.1 +
        (pathForestNonrootMinto hk P p - 2) = _
  rw [pathForestComponentZ]
  have hm := (pathForestNonrootMinto_bounds hk P p).1
  omega

/-- The total budget is the literal root excess plus all genuine nonroot entry costs. -/
theorem pathForestTotalBudget_residual_decomposition (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    pathForestTotalBudget (by omega) P =
      (∑ C : WeakComponent (pathForest (by omega) P),
        pathExcess (pathForestComponentPath (by omega) P C)
          (pathForestComponentPath_blockAligned (by omega) P C)) + 1 +
      ∑ p : PathForestNonrootComponent hk P,
        (pathForestNonrootMinto hk P p - 1) := by
  classical
  let root := pathForestRootComponent (by omega) P
  let excess := fun C : WeakComponent (pathForest (by omega) P) =>
    pathExcess (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C)
  have hbudgetSplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun C : WeakComponent (pathForest (by omega) P) =>
      pathForestComponentBudget (by omega) P C) root
  have hexcessSplit := Fintype.sum_eq_add_sum_subtype_ne excess root
  have hroot : pathForestComponentBudget (by omega) P root = excess root + 1 := by
    change pathForestComponentBudget (by omega) P
      (pathForestRootComponent (by omega) P) = _
    rw [pathForestComponentBudget_root, pathForestComponentZ]
  have hnonroot :
      (∑ p : {C : WeakComponent (pathForest (by omega) P) // C ≠ root},
        pathForestComponentBudget (by omega) P p.1) =
      (∑ p : PathForestNonrootComponent hk P,
        (excess p.1 + (pathForestNonrootMinto hk P p - 1))) := by
    apply Finset.sum_bij (fun p _hp =>
      (⟨p.1, by simpa [root] using p.2⟩ : PathForestNonrootComponent hk P))
    · simp
    · intro a _ha b _hb hab
      exact Subtype.ext (congrArg Subtype.val hab)
    · intro b _hb
      refine ⟨(⟨b.1, by simpa [root] using b.2⟩ :
        {C : WeakComponent (pathForest (by omega) P) // C ≠ root}), by simp, ?_⟩
      exact Subtype.ext rfl
    · intro p _hp
      simpa [excess] using pathForest_nonroot_budget_normalized hk P
        (⟨p.1, by simpa [root] using p.2⟩ : PathForestNonrootComponent hk P)
  have hnonroot' :
      (∑ p : {C : WeakComponent (pathForest (by omega) P) // C ≠ root},
        pathForestComponentBudget (by omega) P p.1) =
      (∑ p : PathForestNonrootComponent hk P, excess p.1) +
        ∑ p : PathForestNonrootComponent hk P,
          (pathForestNonrootMinto hk P p - 1) := by
    rw [hnonroot, Finset.sum_add_distrib]
  have hexcessNonroot :
      (∑ p : {C : WeakComponent (pathForest (by omega) P) // C ≠ root},
        excess p.1) =
      ∑ p : PathForestNonrootComponent hk P, excess p.1 := by
    apply Finset.sum_bij (fun p _hp =>
      (⟨p.1, by simpa [root] using p.2⟩ : PathForestNonrootComponent hk P))
    · simp
    · intro a _ha b _hb hab
      exact Subtype.ext (congrArg Subtype.val hab)
    · intro b _hb
      refine ⟨(⟨b.1, by simpa [root] using b.2⟩ :
        {C : WeakComponent (pathForest (by omega) P) // C ≠ root}), by simp, ?_⟩
      exact Subtype.ext rfl
    · intro p _hp
      rfl
  rw [hexcessNonroot] at hexcessSplit
  change (∑ C : WeakComponent (pathForest (by omega) P),
      pathForestComponentBudget (by omega) P C) = _
  rw [hbudgetSplit, hroot, hnonroot']
  rw [hexcessSplit]
  omega

private theorem pathForest_selected_deltaOne_sum (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (∑ e ∈ pathForestSelectedTailEdges hk P, (e.weight - 1)) =
      (∑ p : PathForestNonrootComponent hk P,
        (pathForestNonrootMinto hk P p - 1)) + pathForestSigmaOne hk P := by
  classical
  rw [pathForestSelectedTailEdges,
    Finset.sum_image (fun _ _ _ _ h => pathForestTailEdge_injective hk P h)]
  change (∑ p : PathForestNonrootComponent hk P,
      ((pathForestTailEdge hk P p).weight - 1)) = _
  rw [pathForestSigmaOne]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  have hmle := pathForestNonrootMinto_le_tailEdge_weight hk P p
  have hmge := (pathForestNonrootMinto_bounds hk P p).1
  omega

/-- The Step-1 sum splits over exactly the selected `e_p` and its literal complement. -/
theorem pathForestDeltaOne_residual_decomposition (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (∑ e ∈ forestDeltaOne P (residualVertices (by omega) P), (e.weight - 1)) =
      (∑ p : PathForestNonrootComponent hk P,
        (pathForestNonrootMinto hk P p - 1)) +
        pathForestSigmaOne hk P + pathForestSigmaTwo hk P := by
  classical
  have hsplit := Finset.sum_sdiff
    (f := fun e : DirectedOverlapEdge k => e.weight - 1)
    (pathForestSelectedTailEdges_subset_deltaOne hk P)
  rw [pathForest_selected_deltaOne_sum hk P] at hsplit
  change pathForestSigmaTwo hk P +
      ((∑ p : PathForestNonrootComponent hk P,
        (pathForestNonrootMinto hk P p - 1)) + pathForestSigmaOne hk P) = _ at hsplit
  omega

/-- The Step-2 weight sum is twice its exact cardinality plus literal `Σ₃`. -/
theorem pathForestDeltaTwo_residual_decomposition (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    (∑ e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P), e.weight) =
      2 * (pathForestComponentCount (by omega) P - 1 +
        forestHeadIndicator P (residualVertices (by omega) P)) +
        pathForestSigmaThree hk P := by
  classical
  let deltaTwo := forestDeltaTwo (by omega) P (residualVertices (by omega) P)
  have hterm : ∀ e ∈ deltaTwo, e.weight = 2 + (e.weight - 2) := by
    intro e he
    have hge := (reducedMinimumPath_newHeadWeight (by omega) P hP).1 e he
    omega
  calc
    (∑ e ∈ deltaTwo, e.weight) =
        ∑ e ∈ deltaTwo, (2 + (e.weight - 2)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ _e ∈ deltaTwo, 2) + ∑ e ∈ deltaTwo, (e.weight - 2) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * deltaTwo.card + pathForestSigmaThree hk P := by
      simp [pathForestSigmaThree, deltaTwo, Nat.mul_comm]
    _ = 2 * (pathForestComponentCount (by omega) P - 1 +
          forestHeadIndicator P (residualVertices (by omega) P)) +
          pathForestSigmaThree hk P := by
      rw [(reducedMinimumPath_newHeadWeight (by omega) P hP).2]

private theorem pathForest_headIndicator_le_weight (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    forestHeadIndicator P (residualVertices (by omega) P) ≤
      graphWeight (pathForest (by omega) P) := by
  classical
  by_cases hhead : P.head ∈ residualVertices (by omega) P
  · have hnotPred : P.head ∉ firstVisitedPredecessors (by omega) P :=
      (mem_residualVertices_iff (by omega) P P.head).mp hhead |>.1
    have hrotation : rotationEdge (by omega) P.head ∈
        pathForest (by omega) P :=
      pathForest_rotationEdge_mem_of_not_predecessor (by omega) P hnotPred
    have hle : (rotationEdge (by omega) P.head).weight ≤
        graphWeight (pathForest (by omega) P) := by
      rw [graphWeight]
      exact Finset.single_le_sum (fun _e _he => Nat.zero_le _) hrotation
    have hweight : (rotationEdge (by omega) P.head).weight = 1 :=
      rotationEdge_weight (by omega) P.head
    rw [hweight] at hle
    simpa [forestHeadIndicator, hhead] using hle
  · simp [forestHeadIndicator, hhead]

private theorem pathForestComponentCount_pos_I (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    1 ≤ pathForestComponentCount (by omega) P := by
  rw [pathForestComponentCount_eq_fintypeCard]
  exact Fintype.card_pos_iff.mpr ⟨pathForestRootComponent (by omega) P⟩

/-- Lemma `residualidentity`: the exact frozen equality for the actual reduced path. -/
theorem pathForest_residualIdentity (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    P.weight =
      (k + 1) * (k - 1).factorial - 3 +
        pathForestTotalBudget (by omega) P +
        forestHeadIndicator P (residualVertices (by omega) P) +
        pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
        pathForestSigmaThree hk P := by
  have hforest := pathForest_weight_normalized hk P
  have hbudget := pathForestTotalBudget_residual_decomposition hk P
  have hdeltaOne := pathForestDeltaOne_residual_decomposition hk P
  have hdeltaTwo := pathForestDeltaTwo_residual_decomposition hk P hP
  have htransform := forestTransform_weight_rule (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P)
  change P.weight = graphWeight (pathForest (by omega) P) +
      (∑ e ∈ forestDeltaOne P (residualVertices (by omega) P),
        (e.weight - 1)) -
      forestHeadIndicator P (residualVertices (by omega) P) +
      (∑ e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P),
        e.weight) at htransform
  have hindicator := pathForest_headIndicator_le_weight hk P
  have hc := pathForestComponentCount_pos_I hk P
  have hfactorial : 1 ≤ (k - 1).factorial := Nat.factorial_pos _
  have hbase : 3 ≤ (k + 1) * (k - 1).factorial := by
    nlinarith
  omega

/-- The exact identity together with the four separate nonnegativity clauses. -/
theorem pathForest_residualIdentity_with_nonnegative (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    P.weight =
        (k + 1) * (k - 1).factorial - 3 +
          pathForestTotalBudget (by omega) P +
          forestHeadIndicator P (residualVertices (by omega) P) +
          pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
          pathForestSigmaThree hk P ∧
      0 ≤ forestHeadIndicator P (residualVertices (by omega) P) ∧
      0 ≤ pathForestSigmaOne hk P ∧
      0 ≤ pathForestSigmaTwo hk P ∧
      0 ≤ pathForestSigmaThree hk P := by
  exact ⟨pathForest_residualIdentity hk P hP,
    pathForestResidualQuantities_nonnegative hk P⟩

/-! ## Door entry from the actual selected edge -/

/-- Lemma `doorentry`(1): the actual source of `e_p` is `ex(α_p)`. -/
theorem pathForest_doorEntry_source (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hminto : pathForestNonrootMinto hk P p = 2)
    (hweight : (pathForestTailEdge hk P p).weight = 2) :
    (pathForestTailEdge hk P p).source =
      blockExit (pathForestComponentEntranceDoor hk P p.1) := by
  have houtside : EntranceDoorClassOutside hk P p.1 :=
    ((pathForestComponent_minto_eq_two_iff hk P p.1
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P p.1 p.2)).2).mp (by
          simpa [pathForestNonrootMinto] using hminto)
  have hunique :=
    pathForestComponent_unique_external_weightTwo_predecessor hk P p.1 houtside
  have hactual : (pathForestTailEdge hk P p).source ∈
        pathForestComponentOutsideVertices (by omega) P p.1 ∧
      overlapWeight (pathForestTailEdge hk P p).source
        (pathForestComponentTail (by omega) P p.1) = 2 :=
    ⟨pathForestTailEdge_source_outside hk P p, by
      simpa [DirectedOverlapEdge.weight, pathForestTailEdge_target hk P p] using hweight⟩
  have hblockOutside : blockExit (pathForestComponentEntranceDoor hk P p.1) ∈
      pathForestComponentOutsideVertices (by omega) P p.1 := by
    simpa using
      (entranceDoorClassOutside_iff_blockExit_outside hk P p.1).mp houtside
  have hblockNe : blockExit (pathForestComponentEntranceDoor hk P p.1) ≠
      pathForestComponentTail (by omega) P p.1 := by
    intro heq
    have hnotComponent :=
      (mem_pathForestComponentOutsideVertices_iff (by omega) P p.1 _).mp hblockOutside
    apply hnotComponent
    rw [heq]
    exact pathForestComponentTail_mem_component_I hk P p.1
  have hblockWeight : overlapWeight
      (blockExit (pathForestComponentEntranceDoor hk P p.1))
      (pathForestComponentTail (by omega) P p.1) = 2 :=
    ((pathForestComponent_weightTwo_predecessors hk P p.1).1 _ hblockNe).mpr
      (Or.inr rfl)
  exact hunique.unique hactual ⟨hblockOutside, hblockWeight⟩

/-- Lemma `doorentry`(2): the actual entrance door is not first visited. -/
theorem pathForest_doorEntry_entranceDoor_not_firstVisited (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hminto : pathForestNonrootMinto hk P p = 2)
    (hweight : (pathForestTailEdge hk P p).weight = 2) :
    pathForestComponentEntranceDoor hk P p.1 ∉
      firstVisitedVertices (by omega) P := by
  intro halpha
  have hsource := pathForest_doorEntry_source hk P p hminto hweight
  have hsourcePred : (pathForestTailEdge hk P p).source ∈
      firstVisitedPredecessors (by omega) P := by
    apply (mem_firstVisitedPredecessors_iff (by omega) P _).mpr
    rw [hsource, rotation_blockExit (by omega)]
    exact halpha
  have hsourceResidual : (pathForestTailEdge hk P p).source ∈
      residualVertices (by omega) P :=
    (mem_outgoingEdges.mp (pathForestTailEdge_mem_deltaOne hk P p)).2
  exact ((mem_residualVertices_iff (by omega) P _).mp hsourceResidual).1 hsourcePred

/-- Lemma `doorentry`(3): Step 1 literally deletes `e_p` and installs
`ex(α_p) → α_p`. -/
theorem pathForest_doorEntry_stepOne (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hminto : pathForestNonrootMinto hk P p = 2)
    (hweight : (pathForestTailEdge hk P p).weight = 2) :
    let alpha := pathForestComponentEntranceDoor hk P p.1
    blockExit alpha ∈ residualVertices (by omega) P ∧
      pathForestTailEdge hk P p ∈
        forestDeltaOne P (residualVertices (by omega) P) ∧
      rotationEdge (by omega) (blockExit alpha) ∈
        forestStepOne (by omega) P (residualVertices (by omega) P) ∧
      (rotationEdge (by omega) (blockExit alpha)).source = blockExit alpha ∧
      (rotationEdge (by omega) (blockExit alpha)).target = alpha := by
  dsimp only
  have hsource := pathForest_doorEntry_source hk P p hminto hweight
  have heDelta := pathForestTailEdge_mem_deltaOne hk P p
  have hresSource : (pathForestTailEdge hk P p).source ∈
      residualVertices (by omega) P := (mem_outgoingEdges.mp heDelta).2
  have hres : blockExit (pathForestComponentEntranceDoor hk P p.1) ∈
      residualVertices (by omega) P := by simpa [hsource] using hresSource
  refine ⟨hres, heDelta, ?_, rfl, rotation_blockExit (by omega) _⟩
  rw [forestStepOne_eq]
  exact Finset.mem_union_right _
    (mem_rotationEdges.mpr
      ⟨blockExit (pathForestComponentEntranceDoor hk P p.1), hres, rfl⟩)

/-- The three clauses of Lemma `doorentry`, bundled without suppressing the actual edge. -/
theorem pathForest_doorEntry (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hminto : pathForestNonrootMinto hk P p = 2)
    (hweight : (pathForestTailEdge hk P p).weight = 2) :
    (pathForestTailEdge hk P p).source =
        blockExit (pathForestComponentEntranceDoor hk P p.1) ∧
      pathForestComponentEntranceDoor hk P p.1 ∉
        firstVisitedVertices (by omega) P ∧
      blockExit (pathForestComponentEntranceDoor hk P p.1) ∈
        residualVertices (by omega) P := by
  refine ⟨pathForest_doorEntry_source hk P p hminto hweight,
    pathForest_doorEntry_entranceDoor_not_firstVisited hk P p hminto hweight, ?_⟩
  exact (pathForest_doorEntry_stepOne hk P p hminto hweight).1

/-! ## Literal component classes -/

/-- The actual path predecessor edge of a noninitial vertex. -/
noncomputable def hamiltonianPredecessorEdge (P : HamiltonianPath k)
    (v : PermutationVertex k) (hv : v ≠ P.tail) : DirectedOverlapEdge k :=
  P.indexedEdge ⟨P.vertexIndex v - 1, by
    have hpos := predecessorIndex_pos P v hv
    have hlt := P.vertexIndex_lt_length v
    omega⟩

/-- The predecessor edge is an actual edge of `P`. -/
theorem hamiltonianPredecessorEdge_mem_path (P : HamiltonianPath k)
    (v : PermutationVertex k) (hv : v ≠ P.tail) :
    hamiltonianPredecessorEdge P v hv ∈ P.edgeSet := by
  apply HamiltonianPath.mem_edgeSet.mpr
  refine ⟨⟨P.vertexIndex v - 1, ?_⟩, rfl⟩
  have hpos := predecessorIndex_pos P v hv
  have hlt := P.vertexIndex_lt_length v
  omega

/-- The actual predecessor edge targets the specified vertex. -/
theorem hamiltonianPredecessorEdge_target (P : HamiltonianPath k)
    (v : PermutationVertex k) (hv : v ≠ P.tail) :
    (hamiltonianPredecessorEdge P v hv).target = v := by
  have hpos := predecessorIndex_pos P v hv
  have hlt : P.vertexIndex v - 1 + 1 < P.vertices.length := by
    have := P.vertexIndex_lt_length v
    omega
  change P.vertices[P.vertexIndex v - 1 + 1]'hlt = v
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ P.vertexIndex v)] using
    P.getElem_vertexIndex v

/-- The optional genuine predecessor edge `g_p` entering `α_p`. It is absent
exactly when `α_p=P[1]`. -/
noncomputable def pathForestEntrancePredecessorEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    Option (DirectedOverlapEdge k) := by
  classical
  let alpha := pathForestComponentEntranceDoor hk P p.1
  exact if h : alpha = P.tail then none else
    some (hamiltonianPredecessorEdge P alpha h)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pathForestEntrancePredecessorEdge_eq_none_iff (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    pathForestEntrancePredecessorEdge hk P p = none ↔
      pathForestComponentEntranceDoor hk P p.1 = P.tail := by
  classical
  simp [pathForestEntrancePredecessorEdge]

/-- If `α_p` is not initial, the optional accessor is the literal path edge
entering it. -/
theorem pathForestEntrancePredecessorEdge_exists (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (halpha : pathForestComponentEntranceDoor hk P p.1 ≠ P.tail) :
    ∃ g : DirectedOverlapEdge k,
      pathForestEntrancePredecessorEdge hk P p = some g ∧
      g ∈ P.edgeSet ∧
      g.target = pathForestComponentEntranceDoor hk P p.1 := by
  let alpha := pathForestComponentEntranceDoor hk P p.1
  have halpha' : runMapInverse (by omega)
      (pathForestComponentTail (by omega) P p.1) ≠ P.tail := by
    simpa only [pathForestComponentEntranceDoor_eq] using halpha
  refine ⟨hamiltonianPredecessorEdge P alpha (by simpa [alpha] using halpha), ?_, ?_, ?_⟩
  · simp [pathForestEntrancePredecessorEdge, alpha, halpha']
  · exact hamiltonianPredecessorEdge_mem_path P alpha _
  · exact hamiltonianPredecessorEdge_target P alpha _

/-- Every value returned by `g_p` is an actual `P`-edge with target `α_p`. -/
theorem pathForestEntrancePredecessorEdge_spec (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    {g : DirectedOverlapEdge k}
    (hg : pathForestEntrancePredecessorEdge hk P p = some g) :
    g ∈ P.edgeSet ∧ g.target = pathForestComponentEntranceDoor hk P p.1 := by
  classical
  by_cases halpha : pathForestComponentEntranceDoor hk P p.1 = P.tail
  · have hnone :=
      (pathForestEntrancePredecessorEdge_eq_none_iff hk P p).mpr halpha
    rw [hnone] at hg
    simp at hg
  · have hsome := pathForestEntrancePredecessorEdge_exists hk P p
      halpha
    obtain ⟨g', hg', hg'P, hg'target⟩ := hsome
    have hgg' : g = g' := Option.some.inj (hg.symm.trans hg')
    simpa [hgg'] using And.intro hg'P hg'target

/-- `U`: exactly the nonroot components with actual `minto = 2`. -/
noncomputable def pathForestU (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact Finset.univ.filter fun p => pathForestNonrootMinto hk P p = 2

@[simp]
theorem mem_pathForestU (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestU hk P ↔ pathForestNonrootMinto hk P p = 2 := by
  classical
  simp [pathForestU]

/-- `M=|U|`. -/
noncomputable def pathForestM (hk : 7 ≤ k) (P : HamiltonianPath k) : ℕ :=
  (pathForestU hk P).card

/-- `M₁`: cheap-entry components whose actual selected edge has weight at least three. -/
noncomputable def pathForestMOne (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter fun p => 3 ≤ (pathForestTailEdge hk P p).weight

/-- `M₀`: selected weight two and `α_p=P[1]`. -/
noncomputable def pathForestMZero (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter fun p =>
    (pathForestTailEdge hk P p).weight = 2 ∧
      pathForestComponentEntranceDoor hk P p.1 = P.tail

/-- `M₂`: selected weight two and the actual predecessor `g_p` lies in `Δ₁`. -/
noncomputable def pathForestMTwo (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter fun p =>
    (pathForestTailEdge hk P p).weight = 2 ∧
      ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
        g ∈ forestDeltaOne P (residualVertices (by omega) P)

/-- `M₃`: selected weight two and `g_p∈Δ₂` has weight at least three. -/
noncomputable def pathForestMThree (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter fun p =>
    (pathForestTailEdge hk P p).weight = 2 ∧
      ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
        g ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) ∧
        3 ≤ g.weight

/-- `M₄`: selected weight two and `g_p∈Δ₂` has weight exactly two. -/
noncomputable def pathForestMFour (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter fun p =>
    (pathForestTailEdge hk P p).weight = 2 ∧
      ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
        g ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) ∧
        g.weight = 2

@[simp]
theorem mem_pathForestMOne (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMOne hk P ↔
      p ∈ pathForestU hk P ∧ 3 ≤ (pathForestTailEdge hk P p).weight := by
  classical
  simp [pathForestMOne]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mem_pathForestMZero (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMZero hk P ↔
      p ∈ pathForestU hk P ∧ (pathForestTailEdge hk P p).weight = 2 ∧
        pathForestComponentEntranceDoor hk P p.1 = P.tail := by
  classical
  simp [pathForestMZero]

@[simp]
theorem mem_pathForestMTwo (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMTwo hk P ↔
      p ∈ pathForestU hk P ∧ (pathForestTailEdge hk P p).weight = 2 ∧
        ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
          g ∈ forestDeltaOne P (residualVertices (by omega) P) := by
  classical
  simp [pathForestMTwo]

@[simp]
theorem mem_pathForestMThree (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMThree hk P ↔
      p ∈ pathForestU hk P ∧ (pathForestTailEdge hk P p).weight = 2 ∧
        ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
          g ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) ∧
          3 ≤ g.weight := by
  classical
  simp [pathForestMThree]

@[simp]
theorem mem_pathForestMFour (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMFour hk P ↔
      p ∈ pathForestU hk P ∧ (pathForestTailEdge hk P p).weight = 2 ∧
        ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
          g ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) ∧
          g.weight = 2 := by
  classical
  simp [pathForestMFour]

/-- `f=|M₄|`. -/
noncomputable def pathForestF (hk : 7 ≤ k) (P : HamiltonianPath k) : ℕ :=
  (pathForestMFour hk P).card

/-- `V=M-f`, with the literal natural subtraction from Definition `classes`. -/
noncomputable def pathForestV (hk : 7 ≤ k) (P : HamiltonianPath k) : ℕ :=
  pathForestM hk P - pathForestF hk P

/-- The literal absorber relation: `q` absorbs `p` exactly when `p∈M₄`
and the source of its actual `g_p` is the head of `q`. -/
def PathForestAbsorbs (hk : 7 ≤ k) (P : HamiltonianPath k)
    (q : WeakComponent (pathForest (by omega) P))
    (p : PathForestNonrootComponent hk P) : Prop :=
  p ∈ pathForestMFour hk P ∧
    ∃ g, pathForestEntrancePredecessorEdge hk P p = some g ∧
      g.source = pathForestComponentHead (by omega) P q

/-- The actual Step-1 and Step-2 deletion families are disjoint. -/
theorem pathForest_deltaOne_disjoint_deltaTwo (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Disjoint (forestDeltaOne P (residualVertices (by omega) P))
      (forestDeltaTwo (by omega) P (residualVertices (by omega) P)) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOne heTwo
  have heOneInfo := mem_outgoingEdges.mp heOne
  have heStepOne : e ∈
      forestStepOne (by omega) P (residualVertices (by omega) P) :=
    (Finset.mem_sdiff.mp heTwo).1
  rw [forestStepOne_eq] at heStepOne
  rcases Finset.mem_union.mp heStepOne with heOriginal | heRotation
  · exact (Finset.mem_sdiff.mp heOriginal).2 heOne
  · obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp heRotation
    have hnotP := (residualVertices_rotationEdgesAdmissible (by omega) P) v hv
    have heP : e ∈ P.edgeSet := by simpa [forestStepZero] using heOneInfo.1
    exact hnotP (by simpa [hve] using heP)

private theorem pathForest_g_mem_deltaOne_or_deltaTwo (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hminto : pathForestNonrootMinto hk P p = 2)
    (heWeight : (pathForestTailEdge hk P p).weight = 2)
    {g : DirectedOverlapEdge k}
    (hg : pathForestEntrancePredecessorEdge hk P p = some g) :
    g ∈ forestDeltaOne P (residualVertices (by omega) P) ∨
      g ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) := by
  classical
  by_cases hgOne : g ∈ forestDeltaOne P (residualVertices (by omega) P)
  · exact Or.inl hgOne
  · right
    have hgSpec := pathForestEntrancePredecessorEdge_spec hk P p hg
    have hdoor := pathForest_doorEntry_stepOne hk P p hminto heWeight
    let alpha := pathForestComponentEntranceDoor hk P p.1
    let r : DirectedOverlapEdge k := rotationEdge (by omega) (blockExit alpha)
    have hrOne : r ∈ forestStepOne (by omega) P (residualVertices (by omega) P) := by
      simpa [alpha, r] using hdoor.2.2.1
    have hrSourceResidual : blockExit alpha ∈ residualVertices (by omega) P := by
      simpa [alpha] using hdoor.1
    have hrNotP : r ∉ P.edgeSet := by
      exact (mem_residualVertices_iff (by omega) P (blockExit alpha)).mp
        hrSourceResidual |>.2
    have hgOneGraph : g ∈
        forestStepOne (by omega) P (residualVertices (by omega) P) := by
      rw [forestStepOne_eq]
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hgSpec.1, hgOne⟩)
    by_contra hgNotTwo
    have hgTwoGraph : g ∈
        forestStepTwo (by omega) P (residualVertices (by omega) P) := by
      by_contra hgNotGraph
      apply hgNotTwo
      exact Finset.mem_sdiff.mpr ⟨hgOneGraph, hgNotGraph⟩
    have hrTwoGraph : r ∈
        forestStepTwo (by omega) P (residualVertices (by omega) P) := by
      rw [forestStepTwo_eq]
      apply Finset.mem_sdiff.mpr
      refine ⟨hrOne, ?_⟩
      intro hrRemoved
      exact hrNotP (mem_incomingEdges.mp hrRemoved).1
    have hgTarget : g.target = alpha := by simpa [alpha] using hgSpec.2
    have hrTarget : r.target = alpha := by
      simpa [alpha, r] using hdoor.2.2.2.2
    have hgr : g ≠ r := by
      intro hgr
      exact hrNotP (hgr ▸ hgSpec.1)
    have hgIn : g ∈ incomingEdgesAt
        (forestTransform (by omega) P (residualVertices (by omega) P)) alpha := by
      exact mem_incomingEdgesAt.mpr ⟨hgTwoGraph, hgTarget⟩
    have hrIn : r ∈ incomingEdgesAt
        (forestTransform (by omega) P (residualVertices (by omega) P)) alpha := by
      exact mem_incomingEdgesAt.mpr ⟨hrTwoGraph, hrTarget⟩
    have hle := forestTransform_inDegree_rule (by omega) P
      (residualVertices (by omega) P)
      (residualVertices_rotationEdgesAdmissible (by omega) P) alpha
    rw [inDegree, Finset.card_le_one] at hle
    exact hgr (hle g hgIn r hrIn)

/-- Every member of `U` lies in one of the five literal classes. -/
theorem pathForest_classes_exhaust (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {p : PathForestNonrootComponent hk P} (hpU : p ∈ pathForestU hk P) :
    p ∈ pathForestMZero hk P ∨ p ∈ pathForestMOne hk P ∨
      p ∈ pathForestMTwo hk P ∨ p ∈ pathForestMThree hk P ∨
        p ∈ pathForestMFour hk P := by
  have hminto := (mem_pathForestU hk P p).mp hpU
  have hle := pathForestNonrootMinto_le_tailEdge_weight hk P p
  by_cases hthree : 3 ≤ (pathForestTailEdge hk P p).weight
  · exact Or.inr (Or.inl ((mem_pathForestMOne hk P p).mpr ⟨hpU, hthree⟩))
  · have heWeight : (pathForestTailEdge hk P p).weight = 2 := by omega
    by_cases halpha : pathForestComponentEntranceDoor hk P p.1 = P.tail
    · exact Or.inl ((mem_pathForestMZero hk P p).mpr ⟨hpU, heWeight, halpha⟩)
    · obtain ⟨g, hg, hgP, hgTarget⟩ :=
        pathForestEntrancePredecessorEdge_exists hk P p halpha
      rcases pathForest_g_mem_deltaOne_or_deltaTwo hk P p hminto heWeight hg with
        hgOne | hgTwo
      · exact Or.inr (Or.inr (Or.inl
          ((mem_pathForestMTwo hk P p).mpr ⟨hpU, heWeight, g, hg, hgOne⟩)))
      · have hgGe := (reducedMinimumPath_newHeadWeight (by omega) P hP).1 g hgTwo
        by_cases hgWeight : g.weight = 2
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            ((mem_pathForestMFour hk P p).mpr
              ⟨hpU, heWeight, g, hg, hgTwo, hgWeight⟩))))
        · have hgThree : 3 ≤ g.weight := by omega
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ((mem_pathForestMThree hk P p).mpr
              ⟨hpU, heWeight, g, hg, hgTwo, hgThree⟩))))

/-- The finite union of all five literal classes. -/
noncomputable def pathForestClassUnion (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact pathForestMZero hk P ∪ pathForestMOne hk P ∪
    pathForestMTwo hk P ∪ pathForestMThree hk P ∪ pathForestMFour hk P

/-- The five literal classes have union exactly `U`. -/
theorem pathForest_classes_union (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestClassUnion hk P = pathForestU hk P := by
  classical
  ext p
  rw [pathForestClassUnion]
  constructor
  · intro hp
    simp only [Finset.mem_union] at hp
    rcases hp with (((hp | hp) | hp) | hp) | hp
    · exact (mem_pathForestMZero hk P p).mp hp |>.1
    · exact (mem_pathForestMOne hk P p).mp hp |>.1
    · exact (mem_pathForestMTwo hk P p).mp hp |>.1
    · exact (mem_pathForestMThree hk P p).mp hp |>.1
    · exact (mem_pathForestMFour hk P p).mp hp |>.1
  · intro hpU
    rcases pathForest_classes_exhaust hk P hP hpU with hp | hp | hp | hp | hp
    · simp [hp]
    · simp [hp]
    · simp [hp]
    · simp [hp]
    · simp [hp]

private theorem pathForest_MZero_disjoint_gClass (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (S : Finset (PathForestNonrootComponent hk P))
    (hS : ∀ p ∈ S, ∃ g, pathForestEntrancePredecessorEdge hk P p = some g) :
    Disjoint (pathForestMZero hk P) S := by
  rw [Finset.disjoint_left]
  intro p hpZero hpS
  obtain ⟨g, hg⟩ := hS p hpS
  have hnone := (pathForestEntrancePredecessorEdge_eq_none_iff hk P p).mpr
    ((mem_pathForestMZero hk P p).mp hpZero).2.2
  rw [hnone] at hg
  simp at hg

/-- All ten pairwise disjointness claims for the five literal classes. -/
theorem pathForest_classes_pairwiseDisjoint (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Disjoint (pathForestMZero hk P) (pathForestMOne hk P) ∧
    Disjoint (pathForestMZero hk P) (pathForestMTwo hk P) ∧
    Disjoint (pathForestMZero hk P) (pathForestMThree hk P) ∧
    Disjoint (pathForestMZero hk P) (pathForestMFour hk P) ∧
    Disjoint (pathForestMOne hk P) (pathForestMTwo hk P) ∧
    Disjoint (pathForestMOne hk P) (pathForestMThree hk P) ∧
    Disjoint (pathForestMOne hk P) (pathForestMFour hk P) ∧
    Disjoint (pathForestMTwo hk P) (pathForestMThree hk P) ∧
    Disjoint (pathForestMTwo hk P) (pathForestMFour hk P) ∧
    Disjoint (pathForestMThree hk P) (pathForestMFour hk P) := by
  classical
  have honeTwo : ∀ S : Finset (PathForestNonrootComponent hk P),
      (∀ p ∈ S, (pathForestTailEdge hk P p).weight = 2) →
      Disjoint (pathForestMOne hk P) S := by
    intro S hS
    rw [Finset.disjoint_left]
    intro p hpOne hpS
    have hthree := (mem_pathForestMOne hk P p).mp hpOne |>.2
    have htwo := hS p hpS
    omega
  have hzeroTwo := pathForest_MZero_disjoint_gClass hk P (pathForestMTwo hk P)
    (fun p hp => by
      obtain ⟨_hpU, _he, g, hg, _⟩ := (mem_pathForestMTwo hk P p).mp hp
      exact ⟨g, hg⟩)
  have hzeroThree := pathForest_MZero_disjoint_gClass hk P (pathForestMThree hk P)
    (fun p hp => by
      obtain ⟨_hpU, _he, g, hg, _⟩ := (mem_pathForestMThree hk P p).mp hp
      exact ⟨g, hg⟩)
  have hzeroFour := pathForest_MZero_disjoint_gClass hk P (pathForestMFour hk P)
    (fun p hp => by
      obtain ⟨_hpU, _he, g, hg, _⟩ := (mem_pathForestMFour hk P p).mp hp
      exact ⟨g, hg⟩)
  have htwoThree : Disjoint (pathForestMTwo hk P) (pathForestMThree hk P) := by
    rw [Finset.disjoint_left]
    intro p hpTwo hpThree
    obtain ⟨_u2, _e2, g, hg, hgOne⟩ := (mem_pathForestMTwo hk P p).mp hpTwo
    obtain ⟨_u3, _e3, g', hg', hg'Two, _⟩ :=
      (mem_pathForestMThree hk P p).mp hpThree
    have hgg : g = g' := Option.some.inj (hg.symm.trans hg')
    exact (Finset.disjoint_left.mp (pathForest_deltaOne_disjoint_deltaTwo hk P))
      hgOne (hgg ▸ hg'Two)
  have htwoFour : Disjoint (pathForestMTwo hk P) (pathForestMFour hk P) := by
    rw [Finset.disjoint_left]
    intro p hpTwo hpFour
    obtain ⟨_u2, _e2, g, hg, hgOne⟩ := (mem_pathForestMTwo hk P p).mp hpTwo
    obtain ⟨_u4, _e4, g', hg', hg'Two, _⟩ :=
      (mem_pathForestMFour hk P p).mp hpFour
    have hgg : g = g' := Option.some.inj (hg.symm.trans hg')
    exact (Finset.disjoint_left.mp (pathForest_deltaOne_disjoint_deltaTwo hk P))
      hgOne (hgg ▸ hg'Two)
  have hthreeFour : Disjoint (pathForestMThree hk P) (pathForestMFour hk P) := by
    rw [Finset.disjoint_left]
    intro p hpThree hpFour
    obtain ⟨_u3, _e3, g, hg, _hgTwo, hgThree⟩ :=
      (mem_pathForestMThree hk P p).mp hpThree
    obtain ⟨_u4, _e4, g', hg', _hg'Two, hg'TwoWeight⟩ :=
      (mem_pathForestMFour hk P p).mp hpFour
    have hgg : g = g' := Option.some.inj (hg.symm.trans hg')
    rw [← hgg] at hg'TwoWeight
    omega
  exact ⟨(honeTwo _ (fun p hp => (mem_pathForestMZero hk P p).mp hp |>.2.1)).symm,
    hzeroTwo, hzeroThree, hzeroFour,
    honeTwo _ (fun p hp => (mem_pathForestMTwo hk P p).mp hp |>.2.1),
    honeTwo _ (fun p hp => (mem_pathForestMThree hk P p).mp hp |>.2.1),
    honeTwo _ (fun p hp => (mem_pathForestMFour hk P p).mp hp |>.2.1),
    htwoThree, htwoFour, hthreeFour⟩

/-- The genuine component of `F(P)` containing a specified vertex. -/
noncomputable def pathForestComponentAtVertex (hk : 7 ≤ k)
    (P : HamiltonianPath k) (v : PermutationVertex k) :
    WeakComponent (pathForest (by omega) P) :=
  (underlyingSimpleGraph (pathForest (by omega) P)).connectedComponentMk v

/-- A vertex lies in its genuine weak component. -/
theorem pathForestComponentAtVertex_mem (hk : 7 ≤ k)
    (P : HamiltonianPath k) (v : PermutationVertex k) :
    v ∈ weakComponentVertices (pathForestComponentAtVertex hk P v) := by
  exact mem_weakComponentVertices.mpr
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- A global forest head is the named head of its genuine component. -/
theorem pathForestComponentAtVertex_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) {v : PermutationVertex k}
    (hvHead : v ∈ graphHeads (pathForest (by omega) P)) :
    pathForestComponentHead (by omega) P
      (pathForestComponentAtVertex hk P v) = v := by
  classical
  let C := pathForestComponentAtVertex hk P v
  have hvC : v ∈ weakComponentVertices C := by
    simpa [C] using pathForestComponentAtVertex_mem hk P v
  have hvZero : weakComponentOutDegree C v = 0 := by
    rw [weakComponentOutDegree, outDegree]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have heInfo := mem_outgoingEdgesAt.mp he
    have heWeak := mem_weakComponentEdges.mp heInfo.1
    have heGlobal : e ∈ outgoingEdgesAt (pathForest (by omega) P) v :=
      mem_outgoingEdgesAt.mpr ⟨heWeak.1, heInfo.2⟩
    rw [mem_graphHeads.mp hvHead] at heGlobal
    simp at heGlobal
  rcases pathForest_component_isDirectedPath (by omega) P C with
    ⟨tail, htail, head, hhead, _htailZero, _hotherIn,
      hheadZero, hotherOut⟩
  have hvEq : v = head := by
    by_contra hne
    have hvOne := hotherOut v hvC hne
    omega
  have hnamedEq : pathForestComponentHead (by omega) P C = head := by
    by_contra hne
    have hnamedOne := hotherOut (pathForestComponentHead (by omega) P C)
      (pathForestComponentHead_mem_component_I hk P C) hne
    have hnamedZero := pathForestComponentHead_outDegree_zero (by omega) P C
    omega
  exact hnamedEq.trans hvEq.symm

/-- A `g_p` lying in `Δ₂` leaves a genuine new component head. -/
theorem pathForest_g_deltaTwo_source_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    {g : DirectedOverlapEdge k}
    (_hg : pathForestEntrancePredecessorEdge hk P p = some g)
    (hgTwo : g ∈ forestDeltaTwo (by omega) P
      (residualVertices (by omega) P)) :
    g.source ∈ graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet ∧
      g.source = pathForestComponentHead (by omega) P
        (pathForestComponentAtVertex hk P g.source) := by
  have hboundary := forestDeltaTwo_eq_outgoing_heads (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P)
  change forestDeltaTwo (by omega) P (residualVertices (by omega) P) =
    outgoingEdges P.edgeSet
      (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) at hboundary
  have hsource : g.source ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet := by
    rw [hboundary] at hgTwo
    exact (mem_outgoingEdges.mp hgTwo).2
  exact ⟨hsource,
    (pathForestComponentAtVertex_head hk P (Finset.mem_sdiff.mp hsource).1).symm⟩

/-- The `M₄` door equality `α_p=β_{p'}` for the actual absorbing component. -/
theorem pathForest_MFour_door_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {p : PathForestNonrootComponent hk P} (hp : p ∈ pathForestMFour hk P) :
    pathForestComponentEntranceDoor hk P p.1 =
      pathForestComponentExitDoor hk P
        (pathForestComponentAtVertex hk P
          (match pathForestEntrancePredecessorEdge hk P p with
            | some g => g.source
            | none => P.tail)) := by
  obtain ⟨_hpU, _heWeight, g, hg, hgTwo, hgWeight⟩ :=
    (mem_pathForestMFour hk P p).mp hp
  have hgSpec := pathForestEntrancePredecessorEdge_spec hk P p hg
  have hsource := (pathForest_g_deltaTwo_source_head hk P p hg hgTwo).2
  have htarget := reducedPath_weightTwo_edge_from_componentHead hk P hP
    (pathForestComponentAtVertex hk P g.source) g hgSpec.1 hsource hgWeight
  have hoptionSource :
      (match pathForestEntrancePredecessorEdge hk P p with
        | some e => e.source
        | none => P.tail) = g.source := by rw [hg]
  rw [hoptionSource]
  exact hgSpec.2.symm.trans htarget

/-- Every budget-one nonroot component belongs to the literal set `U`. -/
theorem pathForest_budgetOne_nonroot_mem_U (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hbudget : pathForestComponentBudget (by omega) P p.1 = 1) :
    p ∈ pathForestU hk P := by
  have hnormalized := pathForest_nonroot_budget_normalized hk P p
  have hm := (pathForestNonrootMinto_bounds hk P p).1
  apply (mem_pathForestU hk P p).mpr
  omega

/-- Lemma `exhaustive`, exposing the genuine partition, source/head facts,
the `M₄` door equality, and the budget-one inclusion. -/
theorem pathForest_exhaustive (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestClassUnion hk P = pathForestU hk P ∧
      (∀ p : PathForestNonrootComponent hk P,
        p ∈ pathForestMThree hk P ∨ p ∈ pathForestMFour hk P →
          ∃ g : DirectedOverlapEdge k,
            pathForestEntrancePredecessorEdge hk P p = some g ∧
            g.source ∈ graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet ∧
            g.source = pathForestComponentHead (by omega) P
              (pathForestComponentAtVertex hk P g.source)) ∧
      (∀ p : PathForestNonrootComponent hk P, p ∈ pathForestMFour hk P →
        pathForestComponentEntranceDoor hk P p.1 =
          pathForestComponentExitDoor hk P
            (pathForestComponentAtVertex hk P
              (match pathForestEntrancePredecessorEdge hk P p with
                | some g => g.source
                | none => P.tail))) ∧
      (∀ p : PathForestNonrootComponent hk P,
        pathForestComponentBudget (by omega) P p.1 = 1 →
          p ∈ pathForestU hk P) := by
  refine ⟨pathForest_classes_union hk P hP, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with hpThree | hpFour
    · obtain ⟨_hpU, _he, g, hg, hgTwo, _hgWeight⟩ :=
        (mem_pathForestMThree hk P p).mp hpThree
      exact ⟨g, hg, pathForest_g_deltaTwo_source_head hk P p hg hgTwo⟩
    · obtain ⟨_hpU, _he, g, hg, hgTwo, _hgWeight⟩ :=
        (mem_pathForestMFour hk P p).mp hpFour
      exact ⟨g, hg, pathForest_g_deltaTwo_source_head hk P p hg hgTwo⟩
  · exact fun p hp => pathForest_MFour_door_eq hk P hP hp
  · exact fun p hp => pathForest_budgetOne_nonroot_mem_U hk P p hp

/-! ## Injectivity and absorption degrees -/

/-- Equality of genuine component heads determines the component. -/
theorem pathForestComponent_eq_of_head_eq_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    {C D : WeakComponent (pathForest (by omega) P)}
    (h : pathForestComponentHead (by omega) P C =
      pathForestComponentHead (by omega) P D) : C = D := by
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (mem_weakComponentVertices.mp
      (pathForestComponentHead_mem_component_I hk P C))
  have hD := mem_weakComponentVertices.mp
    (pathForestComponentHead_mem_component_I hk P D)
  simpa [h] using hD

/-- Lemma `injective`(1): `p↦α_p` is injective on all genuine components. -/
theorem pathForestEntranceDoor_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Function.Injective (pathForestComponentEntranceDoor hk P) := by
  intro C D hdoor
  apply pathForestComponent_eq_of_tail_eq_I hk P
  calc
    pathForestComponentTail (by omega) P C =
        runMap (by omega) (pathForestComponentEntranceDoor hk P C) := by
      rw [pathForestComponentEntranceDoor_eq,
        runMap_runMapInverse (by omega)]
    _ = runMap (by omega) (pathForestComponentEntranceDoor hk P D) :=
      congrArg (runMap (by omega)) hdoor
    _ = pathForestComponentTail (by omega) P D := by
      rw [pathForestComponentEntranceDoor_eq,
        runMap_runMapInverse (by omega)]

/-- The exact domain `M₂∪M₃∪M₄` on which the genuine `g_p` exists. -/
noncomputable def pathForestGClassUnion (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact pathForestMTwo hk P ∪ pathForestMThree hk P ∪ pathForestMFour hk P

@[simp]
theorem mem_pathForestGClassUnion (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestGClassUnion hk P ↔
      p ∈ pathForestMTwo hk P ∨ p ∈ pathForestMThree hk P ∨
        p ∈ pathForestMFour hk P := by
  classical
  simp [pathForestGClassUnion]

private theorem pathForestGClassUnion_has_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hp : p ∈ pathForestGClassUnion hk P) :
    ∃ g, pathForestEntrancePredecessorEdge hk P p = some g := by
  rcases (mem_pathForestGClassUnion hk P p).mp hp with hp | hp | hp
  · obtain ⟨_u, _e, g, hg, _⟩ := (mem_pathForestMTwo hk P p).mp hp
    exact ⟨g, hg⟩
  · obtain ⟨_u, _e, g, hg, _⟩ := (mem_pathForestMThree hk P p).mp hp
    exact ⟨g, hg⟩
  · obtain ⟨_u, _e, g, hg, _⟩ := (mem_pathForestMFour hk P p).mp hp
    exact ⟨g, hg⟩

/-- The actual edge-valued map `p↦g_p` on `M₂∪M₃∪M₄`. -/
noncomputable def pathForestGEdge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P //
      q ∈ pathForestGClassUnion hk P}) : DirectedOverlapEdge k :=
  Classical.choose (pathForestGClassUnion_has_edge hk P p.1 p.2)

/-- The edge accessor is exactly the value of the optional literal predecessor. -/
theorem pathForestGEdge_spec (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P //
      q ∈ pathForestGClassUnion hk P}) :
    pathForestEntrancePredecessorEdge hk P p.1 =
      some (pathForestGEdge hk P p) :=
  Classical.choose_spec (pathForestGClassUnion_has_edge hk P p.1 p.2)

/-- Lemma `injective`(2): the actual map `p↦g_p` is injective on its exact class domain. -/
theorem pathForestGEdge_injective (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Function.Injective (pathForestGEdge hk P) := by
  intro p q hg
  apply Subtype.ext
  apply Subtype.ext
  apply pathForestEntranceDoor_injective hk P
  have hpSpec := pathForestEntrancePredecessorEdge_spec hk P p.1
    (pathForestGEdge_spec hk P p)
  have hqSpec := pathForestEntrancePredecessorEdge_spec hk P q.1
    (pathForestGEdge_spec hk P q)
  exact hpSpec.2.symm.trans ((congrArg DirectedOverlapEdge.target hg).trans hqSpec.2)

/-- Exact domain `M₃∪M₄` for absorber heads. -/
noncomputable def pathForestAbsorberDomain (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact pathForestMThree hk P ∪ pathForestMFour hk P

@[simp]
theorem mem_pathForestAbsorberDomain (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestAbsorberDomain hk P ↔
      p ∈ pathForestMThree hk P ∨ p ∈ pathForestMFour hk P := by
  classical
  simp [pathForestAbsorberDomain]

private theorem pathForestAbsorberDomain_has_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hp : p ∈ pathForestAbsorberDomain hk P) :
    ∃ g, pathForestEntrancePredecessorEdge hk P p = some g := by
  rcases (mem_pathForestAbsorberDomain hk P p).mp hp with hp | hp
  · obtain ⟨_u, _e, g, hg, _⟩ := (mem_pathForestMThree hk P p).mp hp
    exact ⟨g, hg⟩
  · obtain ⟨_u, _e, g, hg, _⟩ := (mem_pathForestMFour hk P p).mp hp
    exact ⟨g, hg⟩

/-- The actual source/head carried by `g_p` on `M₃∪M₄`. -/
noncomputable def pathForestAbsorberHead (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P //
      q ∈ pathForestAbsorberDomain hk P}) : PermutationVertex k :=
  (Classical.choose (pathForestAbsorberDomain_has_edge hk P p.1 p.2)).source

private theorem pathForestAbsorberHead_edge_spec (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P //
      q ∈ pathForestAbsorberDomain hk P}) :
    pathForestEntrancePredecessorEdge hk P p.1 = some
        (Classical.choose (pathForestAbsorberDomain_has_edge hk P p.1 p.2)) :=
  Classical.choose_spec (pathForestAbsorberDomain_has_edge hk P p.1 p.2)

private theorem hamiltonianPath_edges_eq_of_same_source (P : HamiltonianPath k)
    {e f : DirectedOverlapEdge k} (he : e ∈ P.edgeSet) (hf : f ∈ P.edgeSet)
    (hsource : e.source = f.source) : e = f := by
  have hle := P.edgeSet_outDegree_rule e.source
  rw [outDegree, Finset.card_le_one] at hle
  exact hle e (mem_outgoingEdgesAt.mpr ⟨he, rfl⟩)
    f (mem_outgoingEdgesAt.mpr ⟨hf, hsource.symm⟩)

/-- Lemma `injective`(3): the actual absorber-head map is injective. -/
theorem pathForestAbsorberHead_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Function.Injective (pathForestAbsorberHead hk P) := by
  intro p q hhead
  let gp := Classical.choose (pathForestAbsorberDomain_has_edge hk P p.1 p.2)
  let gq := Classical.choose (pathForestAbsorberDomain_has_edge hk P q.1 q.2)
  have hgpOption : pathForestEntrancePredecessorEdge hk P p.1 = some gp :=
    pathForestAbsorberHead_edge_spec hk P p
  have hgqOption : pathForestEntrancePredecessorEdge hk P q.1 = some gq :=
    pathForestAbsorberHead_edge_spec hk P q
  have hgpP := (pathForestEntrancePredecessorEdge_spec hk P p.1 hgpOption).1
  have hgqP := (pathForestEntrancePredecessorEdge_spec hk P q.1 hgqOption).1
  have hsources : gp.source = gq.source := by simpa [pathForestAbsorberHead, gp, gq] using hhead
  have hgg := hamiltonianPath_edges_eq_of_same_source P hgpP hgqP hsources
  have halpha := (pathForestEntrancePredecessorEdge_spec hk P p.1 hgpOption).2.symm.trans
    ((congrArg DirectedOverlapEdge.target hgg).trans
      (pathForestEntrancePredecessorEdge_spec hk P q.1 hgqOption).2)
  apply Subtype.ext
  apply Subtype.ext
  exact pathForestEntranceDoor_injective hk P halpha

/-- Lemma `injective`(4): `|M₀|≤1`. -/
theorem pathForestMZero_card_le_one (hk : 7 ≤ k) (P : HamiltonianPath k) :
    (pathForestMZero hk P).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  apply Subtype.ext
  apply pathForestEntranceDoor_injective hk P
  exact ((mem_pathForestMZero hk P p).mp hp).2.2.trans
    ((mem_pathForestMZero hk P q).mp hq).2.2.symm

/-- Every `M₄` component has its genuine absorber. -/
theorem pathForestAbsorber_exists (hk : 7 ≤ k) (P : HamiltonianPath k)
    {p : PathForestNonrootComponent hk P} (hp : p ∈ pathForestMFour hk P) :
    ∃ q : WeakComponent (pathForest (by omega) P), PathForestAbsorbs hk P q p := by
  obtain ⟨_hpU, _he, g, hg, hgTwo, _hgWeight⟩ :=
    (mem_pathForestMFour hk P p).mp hp
  let q := pathForestComponentAtVertex hk P g.source
  have hhead := (pathForest_g_deltaTwo_source_head hk P p hg hgTwo).2
  exact ⟨q, hp, g, hg, by simpa [q] using hhead⟩

/-- Absorption in-degree is at most one: a target has at most one absorber. -/
theorem pathForestAbsorbs_inDegree_le_one (hk : 7 ≤ k) (P : HamiltonianPath k)
    {p : PathForestNonrootComponent hk P}
    {q r : WeakComponent (pathForest (by omega) P)}
    (hq : PathForestAbsorbs hk P q p) (hr : PathForestAbsorbs hk P r p) : q = r := by
  obtain ⟨_hp, g, hg, hgSource⟩ := hq
  obtain ⟨_hp', g', hg', hg'Source⟩ := hr
  have hgg : g = g' := Option.some.inj (hg.symm.trans hg')
  apply pathForestComponent_eq_of_head_eq_I hk P
  exact hgSource.symm.trans ((congrArg DirectedOverlapEdge.source hgg).trans hg'Source)

/-- Absorption out-degree is at most one: an absorber has at most one target. -/
theorem pathForestAbsorbs_outDegree_le_one (hk : 7 ≤ k) (P : HamiltonianPath k)
    {q : WeakComponent (pathForest (by omega) P)}
    {p r : PathForestNonrootComponent hk P}
    (hp : PathForestAbsorbs hk P q p) (hr : PathForestAbsorbs hk P q r) : p = r := by
  obtain ⟨hpFour, g, hg, hgSource⟩ := hp
  obtain ⟨hrFour, g', hg', hg'Source⟩ := hr
  have hgP := (pathForestEntrancePredecessorEdge_spec hk P p hg).1
  have hg'P := (pathForestEntrancePredecessorEdge_spec hk P r hg').1
  have hgg := hamiltonianPath_edges_eq_of_same_source P hgP hg'P
    (hgSource.trans hg'Source.symm)
  have halpha := (pathForestEntrancePredecessorEdge_spec hk P p hg).2.symm.trans
    ((congrArg DirectedOverlapEdge.target hgg).trans
      (pathForestEntrancePredecessorEdge_spec hk P r hg').2)
  apply Subtype.ext
  exact pathForestEntranceDoor_injective hk P halpha

/-- Lemma `injective`, with all five map/cardinality/degree clauses exposed. -/
theorem pathForest_injective (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Function.Injective (pathForestComponentEntranceDoor hk P) ∧
      Function.Injective (pathForestGEdge hk P) ∧
      Function.Injective (pathForestAbsorberHead hk P) ∧
      (pathForestMZero hk P).card ≤ 1 ∧
      (∀ p q r, PathForestAbsorbs hk P q p → PathForestAbsorbs hk P r p → q = r) ∧
      (∀ q p r, PathForestAbsorbs hk P q p → PathForestAbsorbs hk P q r → p = r) := by
  exact ⟨pathForestEntranceDoor_injective hk P,
    pathForestGEdge_injective hk P,
    pathForestAbsorberHead_injective hk P,
    pathForestMZero_card_le_one hk P,
    fun _p _q _r => pathForestAbsorbs_inDegree_le_one hk P,
    fun _q _p _r => pathForestAbsorbs_outDegree_le_one hk P⟩

/-! ## The two actual head sets -/

/-- Every named component head is a genuine head of `F(P)`. -/
theorem pathForestComponentHead_mem_graphHeads_I (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) := by
  classical
  apply mem_graphHeads.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have heInfo := mem_outgoingEdgesAt.mp he
  have hheadC := mem_weakComponentVertices.mp
    (pathForestComponentHead_mem_component_I hk P C)
  have hsourceC : e.source ∈ C.supp := by simpa [heInfo.2] using hheadC
  have htargetC := weakComponent_edge_target_mem C hsourceC heInfo.1
  have heWeak : e ∈ weakComponentEdges C :=
    mem_weakComponentEdges.mpr ⟨heInfo.1, hsourceC, htargetC⟩
  have heWeakOut : e ∈ outgoingEdgesAt (weakComponentEdges C)
      (pathForestComponentHead (by omega) P C) :=
    mem_outgoingEdgesAt.mpr ⟨heWeak, heInfo.2⟩
  have hempty : outgoingEdgesAt (weakComponentEdges C)
      (pathForestComponentHead (by omega) P C) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentOutDegree, outDegree] using
      pathForestComponentHead_outDegree_zero (by omega) P C
  rw [hempty] at heWeakOut
  simp at heWeakOut

/-- Terminal-full components whose heads are actual new heads. -/
noncomputable def pathForestTerminalFullNewHeadComponents (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Finset (WeakComponent (pathForest (by omega) P)) := by
  classical
  exact (pathForestTerminalFullComponents hk P).filter fun C =>
    pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet

/-- The literal set `H_full`. -/
noncomputable def pathForestHFull (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PermutationVertex k) := by
  classical
  exact (pathForestTerminalFullNewHeadComponents hk P).image
    (pathForestComponentHead (by omega) P)

/-- Total source accessor used only after a class-membership proof guarantees `g_p`. -/
noncomputable def pathForestGSource (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) : PermutationVertex k :=
  match pathForestEntrancePredecessorEdge hk P p with
  | some g => g.source
  | none => P.tail

/-- The literal set `H₂` of sources of the actual `g_p`, `p∈M₃`. -/
noncomputable def pathForestHTwo (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Finset (PermutationVertex k) := by
  classical
  exact (pathForestMThree hk P).image (pathForestGSource hk P)

/-- Membership in `H_full` retains the actual terminal-full component and new-head fact. -/
theorem mem_pathForestHFull (hk : 7 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    v ∈ pathForestHFull hk P ↔
      ∃ C : WeakComponent (pathForest (Nat.le_trans (by decide) hk) P),
        C ∈ pathForestTerminalFullComponents hk P ∧
        pathForestComponentHead (by omega) P C ∈
          graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet ∧
        pathForestComponentHead (by omega) P C = v := by
  classical
  rw [pathForestHFull]
  simp only [Finset.mem_image, pathForestTerminalFullNewHeadComponents,
    Finset.mem_filter]
  constructor
  · rintro ⟨C, ⟨hterminal, hnew⟩, hCv⟩
    exact ⟨C, hterminal, hnew, hCv⟩
  · rintro ⟨C, hterminal, hnew, hCv⟩
    exact ⟨C, ⟨hterminal, hnew⟩, hCv⟩

/-- Membership in `H₂` retains the actual `M₃` component and actual source. -/
theorem mem_pathForestHTwo (hk : 7 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    v ∈ pathForestHTwo hk P ↔
      ∃ p : PathForestNonrootComponent hk P,
        p ∈ pathForestMThree hk P ∧ pathForestGSource hk P p = v := by
  classical
  simp [pathForestHTwo]

/-- On `M₃` (and similarly every genuine-`g` class), the total source accessor
is literally the source of the returned edge. -/
theorem pathForestGSource_eq (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) {g : DirectedOverlapEdge k}
    (hg : pathForestEntrancePredecessorEdge hk P p = some g) :
    pathForestGSource hk P p = g.source := by
  simp [pathForestGSource, hg]

private theorem pathForestGSource_injective_on_MThree (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Set.InjOn (pathForestGSource hk P) ↑(pathForestMThree hk P) := by
  intro p hp q hq hsources
  obtain ⟨_up, _ep, gp, hgp, _hgpTwo, _hgpThree⟩ :=
    (mem_pathForestMThree hk P p).mp hp
  obtain ⟨_uq, _eq, gq, hgq, _hgqTwo, _hgqThree⟩ :=
    (mem_pathForestMThree hk P q).mp hq
  have hsource : gp.source = gq.source := by
    simpa [pathForestGSource_eq hk P p hgp,
      pathForestGSource_eq hk P q hgq] using hsources
  have hgpP := (pathForestEntrancePredecessorEdge_spec hk P p hgp).1
  have hgqP := (pathForestEntrancePredecessorEdge_spec hk P q hgq).1
  have hgg := hamiltonianPath_edges_eq_of_same_source P hgpP hgqP hsource
  apply Subtype.ext
  apply pathForestEntranceDoor_injective hk P
  exact (pathForestEntrancePredecessorEdge_spec hk P p hgp).2.symm.trans
    ((congrArg DirectedOverlapEdge.target hgg).trans
      (pathForestEntrancePredecessorEdge_spec hk P q hgq).2)

/-- The literal head set `H₂` has cardinality exactly `|M₃|`. -/
theorem pathForestHTwo_card (hk : 7 ≤ k) (P : HamiltonianPath k) :
    (pathForestHTwo hk P).card = (pathForestMThree hk P).card := by
  classical
  rw [pathForestHTwo]
  exact (Finset.card_image_iff.mpr (pathForestGSource_injective_on_MThree hk P))

private theorem pathForestTerminalFull_isFull (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (Nat.le_trans (by decide) hk) P))
    (hterminal : C ∈ pathForestTerminalFullComponents hk P) :
    (pathForestComponentLastRun hk P C).IsFull := by
  have hzero : pathForestComponentLastDeficit hk P C = 0 := by
    simpa [pathForestTerminalFullComponents, IsTerminalFullComponent] using hterminal
  rw [pathForestComponentLastDeficit_eq_lastRun_deficit,
    PathForestRun.deficit] at hzero
  have hle := pathForestRun_length_le hk P (pathForestComponentLastRun hk P C)
  change (pathForestComponentLastRun hk P C).length = k - 1
  omega

private noncomputable def pathForestHeavyDeltaTwoEdges (hk : 7 ≤ k)
    (P : HamiltonianPath k) : Finset (DirectedOverlapEdge k) := by
  classical
  exact (forestDeltaTwo (by omega) P (residualVertices (by omega) P)).filter
    fun e => 3 ≤ e.weight

private noncomputable def pathForestHeavyDeltaTwoSources (hk : 7 ≤ k)
    (P : HamiltonianPath k) : Finset (PermutationVertex k) := by
  classical
  exact (pathForestHeavyDeltaTwoEdges hk P).image DirectedOverlapEdge.source

private theorem pathForestDeltaTwo_edge_mem_path (hk : 7 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k}
    (he : e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P)) :
    e ∈ P.edgeSet := by
  have hboundary := forestDeltaTwo_eq_outgoing_heads (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P)
  change forestDeltaTwo (by omega) P (residualVertices (by omega) P) =
    outgoingEdges P.edgeSet
      (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) at hboundary
  rw [hboundary] at he
  exact (mem_outgoingEdges.mp he).1

private theorem pathForestHeavyDeltaTwo_source_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Set.InjOn (fun e : DirectedOverlapEdge k => e.source)
      (↑(pathForestHeavyDeltaTwoEdges hk P) : Set (DirectedOverlapEdge k)) := by
  intro e he f hf hsource
  exact hamiltonianPath_edges_eq_of_same_source P
    (pathForestDeltaTwo_edge_mem_path hk P (Finset.mem_filter.mp he).1)
    (pathForestDeltaTwo_edge_mem_path hk P (Finset.mem_filter.mp hf).1) hsource

private theorem pathForest_headUnion_subset_heavySources (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestHFull hk P ∪ pathForestHTwo hk P ⊆
      pathForestHeavyDeltaTwoSources hk P := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hvFull | hvTwo
  · obtain ⟨C, hterminal, hnew, hhead⟩ :=
      (mem_pathForestHFull hk P v).mp hvFull
    let e := pathForestDeletedHeadEdge hk P C hnew
    have heDelta : e ∈ forestDeltaTwo (by omega) P
        (residualVertices (by omega) P) :=
      pathForestDeletedHeadEdge_mem_deltaTwo hk P C hnew
    have heHeavy : 3 ≤ e.weight := fullLastRun_deletedHeadEdge_weight_ge_three
      hk P hP C hnew (pathForestTerminalFull_isFull hk P C hterminal)
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨heDelta, heHeavy⟩, ?_⟩
    exact (pathForestDeletedHeadEdge_source hk P C hnew).trans hhead
  · obtain ⟨p, hpThree, hpSource⟩ := (mem_pathForestHTwo hk P v).mp hvTwo
    obtain ⟨_hpU, _he, g, hg, hgTwo, hgThree⟩ :=
      (mem_pathForestMThree hk P p).mp hpThree
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hgTwo, hgThree⟩, ?_⟩
    exact (pathForestGSource_eq hk P p hg).symm.trans hpSource

private theorem pathForestSigmaThree_ge_heavySources (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    pathForestSigmaThree hk P ≥ (pathForestHeavyDeltaTwoSources hk P).card := by
  classical
  have hsourceCard : (pathForestHeavyDeltaTwoSources hk P).card =
      (pathForestHeavyDeltaTwoEdges hk P).card := by
    exact Finset.card_image_iff.mpr
      (pathForestHeavyDeltaTwo_source_injective hk P)
  have hterm : (∑ _e ∈ pathForestHeavyDeltaTwoEdges hk P, 1) ≤
      ∑ e ∈ pathForestHeavyDeltaTwoEdges hk P, (e.weight - 2) := by
    apply Finset.sum_le_sum
    intro e he
    have hthree := (Finset.mem_filter.mp he).2
    omega
  have hsubset : pathForestHeavyDeltaTwoEdges hk P ⊆
      forestDeltaTwo (by omega) P (residualVertices (by omega) P) := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  calc
    (pathForestHeavyDeltaTwoSources hk P).card =
        (pathForestHeavyDeltaTwoEdges hk P).card := hsourceCard
    _ = ∑ _e ∈ pathForestHeavyDeltaTwoEdges hk P, 1 := by simp
    _ ≤ ∑ e ∈ pathForestHeavyDeltaTwoEdges hk P, (e.weight - 2) := hterm
    _ ≤ ∑ e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P),
          (e.weight - 2) := Finset.sum_le_sum_of_subset hsubset
    _ = pathForestSigmaThree hk P := by rw [pathForestSigmaThree]

/-- The first inequality of Lemma `headunion`. -/
theorem pathForest_headUnion_first_inequality (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestSigmaThree hk P ≥
      (pathForestHFull hk P ∪ pathForestHTwo hk P).card := by
  exact (Finset.card_le_card (pathForest_headUnion_subset_heavySources hk P hP)).trans
    (pathForestSigmaThree_ge_heavySources hk P)

private noncomputable def pathForestTerminalFullExcludedComponents (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Finset (WeakComponent (pathForest (by omega) P)) := by
  classical
  exact pathForestTerminalFullComponents hk P \
    pathForestTerminalFullNewHeadComponents hk P

private theorem pathForestTerminalFullExcluded_card_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestTerminalFullExcludedComponents hk P).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro C hC D hD
  have hCInfo := Finset.mem_sdiff.mp hC
  have hDInfo := Finset.mem_sdiff.mp hD
  have hCNotNew : pathForestComponentHead (by omega) P C ∉
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet := by
    intro hnew
    exact hCInfo.2 (Finset.mem_filter.mpr ⟨hCInfo.1, hnew⟩)
  have hDNotNew : pathForestComponentHead (by omega) P D ∉
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet := by
    intro hnew
    exact hDInfo.2 (Finset.mem_filter.mpr ⟨hDInfo.1, hnew⟩)
  have hCHeadX := pathForestComponentHead_mem_graphHeads_I hk P C
  have hDHeadX := pathForestComponentHead_mem_graphHeads_I hk P D
  have hCHeadP : pathForestComponentHead (by omega) P C ∈ graphHeads P.edgeSet := by
    by_contra hnot
    exact hCNotNew (Finset.mem_sdiff.mpr ⟨hCHeadX, hnot⟩)
  have hDHeadP : pathForestComponentHead (by omega) P D ∈ graphHeads P.edgeSet := by
    by_contra hnot
    exact hDNotNew (Finset.mem_sdiff.mpr ⟨hDHeadX, hnot⟩)
  rw [P.edgeSet_heads, Finset.mem_singleton] at hCHeadP hDHeadP
  exact pathForestComponent_eq_of_head_eq_I hk P (hCHeadP.trans hDHeadP.symm)

/-- At most the path head is excluded, so `|H_full|≥C-1` (and hence also
the displayed `max(0,C-1)`). -/
theorem pathForestHFull_card_lower (hk : 7 ≤ k) (P : HamiltonianPath k) :
    max 0 (pathForestTerminalFullCount hk P - 1) ≤
      (pathForestHFull hk P).card := by
  classical
  have hheadInjective : Function.Injective
      (pathForestComponentHead (by omega) P) := by
    intro C D h
    exact pathForestComponent_eq_of_head_eq_I hk P h
  have hHCard : (pathForestHFull hk P).card =
      (pathForestTerminalFullNewHeadComponents hk P).card := by
    rw [pathForestHFull,
      Finset.card_image_of_injective _ hheadInjective]
  have hgoodSubset : pathForestTerminalFullNewHeadComponents hk P ⊆
      pathForestTerminalFullComponents hk P := by
    intro C hC
    exact (Finset.mem_filter.mp hC).1
  have hsplit := Finset.card_sdiff_add_card
    (pathForestTerminalFullComponents hk P)
    (pathForestTerminalFullNewHeadComponents hk P)
  rw [Finset.union_eq_left.mpr hgoodSubset] at hsplit
  have hbad := pathForestTerminalFullExcluded_card_le_one hk P
  change (pathForestTerminalFullComponents hk P \
      pathForestTerminalFullNewHeadComponents hk P).card ≤ 1 at hbad
  rw [hHCard]
  change max 0 ((pathForestTerminalFullComponents hk P).card - 1) ≤ _
  omega

/-- The second inequality of Lemma `headunion`. -/
theorem pathForest_headUnion_second_inequality (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestHFull hk P ∪ pathForestHTwo hk P).card ≥
      max (max 0 (pathForestTerminalFullCount hk P - 1))
        (pathForestMThree hk P).card := by
  classical
  have hfullSubset : pathForestHFull hk P ⊆
      pathForestHFull hk P ∪ pathForestHTwo hk P := Finset.subset_union_left
  have htwoSubset : pathForestHTwo hk P ⊆
      pathForestHFull hk P ∪ pathForestHTwo hk P := Finset.subset_union_right
  have hfull := (pathForestHFull_card_lower hk P).trans
    (Finset.card_le_card hfullSubset)
  have htwo : (pathForestMThree hk P).card ≤
      (pathForestHFull hk P ∪ pathForestHTwo hk P).card := by
    rw [← pathForestHTwo_card hk P]
    exact Finset.card_le_card htwoSubset
  exact Nat.max_le.mpr ⟨hfull, htwo⟩

/-- Lemma `headunion`, with both literal head sets and both inequalities. -/
theorem pathForest_headUnion (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestSigmaThree hk P ≥
        (pathForestHFull hk P ∪ pathForestHTwo hk P).card ∧
      (pathForestHFull hk P ∪ pathForestHTwo hk P).card ≥
        max (max 0 (pathForestTerminalFullCount hk P - 1))
          (pathForestMThree hk P).card :=
  ⟨pathForest_headUnion_first_inequality hk P hP,
    pathForest_headUnion_second_inequality hk P⟩

/-! ## The residual lower bound -/

/-- The three literal edge-indexing families are pairwise disjoint: selected
`e_p`, the Step-1 complement, and `Δ₂`. -/
theorem pathForest_residual_edgeFamilies_pairwiseDisjoint (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Disjoint (pathForestSelectedTailEdges hk P)
        (forestDeltaOne P (residualVertices (by omega) P) \
          pathForestSelectedTailEdges hk P) ∧
      Disjoint (pathForestSelectedTailEdges hk P)
        (forestDeltaTwo (by omega) P (residualVertices (by omega) P)) ∧
      Disjoint
        (forestDeltaOne P (residualVertices (by omega) P) \
          pathForestSelectedTailEdges hk P)
        (forestDeltaTwo (by omega) P (residualVertices (by omega) P)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro e hselected hcomplement
    exact (Finset.mem_sdiff.mp hcomplement).2 hselected
  · exact (pathForest_deltaOne_disjoint_deltaTwo hk P).mono
      (pathForestSelectedTailEdges_subset_deltaOne hk P) (by rfl)
  · exact (pathForest_deltaOne_disjoint_deltaTwo hk P).mono
      Finset.sdiff_subset (by rfl)

/-- Every `M₁` component contributes at least one to the literal `Σ₁`. -/
theorem pathForestSigmaOne_ge_MOne (hk : 7 ≤ k) (P : HamiltonianPath k) :
    (pathForestMOne hk P).card ≤ pathForestSigmaOne hk P := by
  classical
  have hterm : (∑ _p ∈ pathForestMOne hk P, 1) ≤
      ∑ p ∈ pathForestMOne hk P,
        ((pathForestTailEdge hk P p).weight - pathForestNonrootMinto hk P p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpInfo := (mem_pathForestMOne hk P p).mp hp
    have hminto := (mem_pathForestU hk P p).mp hpInfo.1
    omega
  calc
    (pathForestMOne hk P).card = ∑ _p ∈ pathForestMOne hk P, 1 := by simp
    _ ≤ ∑ p ∈ pathForestMOne hk P,
        ((pathForestTailEdge hk P p).weight - pathForestNonrootMinto hk P p) := hterm
    _ ≤ ∑ p : PathForestNonrootComponent hk P,
        ((pathForestTailEdge hk P p).weight - pathForestNonrootMinto hk P p) := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = pathForestSigmaOne hk P := by rw [pathForestSigmaOne]

private theorem pathForestMTwo_has_edge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) (hp : p ∈ pathForestMTwo hk P) :
    ∃ g, pathForestEntrancePredecessorEdge hk P p = some g := by
  obtain ⟨_hpU, _he, g, hg, _hgOne⟩ := (mem_pathForestMTwo hk P p).mp hp
  exact ⟨g, hg⟩

/-- The actual `g_p` on the exact finite domain `M₂`. -/
noncomputable def pathForestMTwoEdge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P // q ∈ pathForestMTwo hk P}) :
    DirectedOverlapEdge k :=
  Classical.choose (pathForestMTwo_has_edge hk P p.1 p.2)

/-- The `M₂` edge accessor is literally the optional predecessor value. -/
theorem pathForestMTwoEdge_spec (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P // q ∈ pathForestMTwo hk P}) :
    pathForestEntrancePredecessorEdge hk P p.1 =
      some (pathForestMTwoEdge hk P p) :=
  Classical.choose_spec (pathForestMTwo_has_edge hk P p.1 p.2)

/-- The actual `M₂` edge map is injective. -/
theorem pathForestMTwoEdge_injective (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Function.Injective (pathForestMTwoEdge hk P) := by
  intro p q hedge
  have hpSpec := pathForestEntrancePredecessorEdge_spec hk P p.1
    (pathForestMTwoEdge_spec hk P p)
  have hqSpec := pathForestEntrancePredecessorEdge_spec hk P q.1
    (pathForestMTwoEdge_spec hk P q)
  have halpha := hpSpec.2.symm.trans
    ((congrArg DirectedOverlapEdge.target hedge).trans hqSpec.2)
  apply Subtype.ext
  apply Subtype.ext
  exact pathForestEntranceDoor_injective hk P halpha

/-- Every `M₂` edge lies in the literal `Σ₂` family; in particular it is
excluded from every selected tail edge for the stated first-visited reason. -/
theorem pathForestMTwoEdge_mem_sigmaTwoFamily (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (p : {q : PathForestNonrootComponent hk P // q ∈ pathForestMTwo hk P}) :
    pathForestMTwoEdge hk P p ∈
      forestDeltaOne P (residualVertices (by omega) P) \
        pathForestSelectedTailEdges hk P := by
  have hpInfo := (mem_pathForestMTwo hk P p.1).mp p.2
  obtain ⟨hpU, heWeight, g, hg, hgOne⟩ := hpInfo
  have hchosen : g = pathForestMTwoEdge hk P p :=
    Option.some.inj (hg.symm.trans (pathForestMTwoEdge_spec hk P p))
  subst g
  apply Finset.mem_sdiff.mpr
  refine ⟨hgOne, ?_⟩
  intro hselected
  obtain ⟨q, hqEdge⟩ :=
    (mem_pathForestSelectedTailEdges hk P (pathForestMTwoEdge hk P p)).mp hselected
  have htarget := congrArg DirectedOverlapEdge.target hqEdge
  have hgTarget := (pathForestEntrancePredecessorEdge_spec hk P p.1
    (pathForestMTwoEdge_spec hk P p)).2
  have halphaTail : pathForestComponentEntranceDoor hk P p.1 =
      pathForestComponentTail (by omega) P q.1 := by
    calc
      pathForestComponentEntranceDoor hk P p.1 =
          (pathForestMTwoEdge hk P p).target := hgTarget.symm
      _ = (pathForestTailEdge hk P q).target := htarget.symm
      _ = pathForestComponentTail (by omega) P q.1 :=
        pathForestTailEdge_target hk P q
  have halphaNot := pathForest_doorEntry_entranceDoor_not_firstVisited hk P p.1
    ((mem_pathForestU hk P p.1).mp hpU) heWeight
  apply halphaNot
  rw [halphaTail]
  exact pathForestComponentTail_mem_firstVisited (by omega) P q.1

/-- Every `M₂` component contributes at least one to the literal `Σ₂`. -/
theorem pathForestSigmaTwo_ge_MTwo (hk : 7 ≤ k) (P : HamiltonianPath k) :
    (pathForestMTwo hk P).card ≤ pathForestSigmaTwo hk P := by
  classical
  let domain := {q : PathForestNonrootComponent hk P // q ∈ pathForestMTwo hk P}
  let edgeImage : Finset (DirectedOverlapEdge k) :=
    Finset.univ.image (pathForestMTwoEdge hk P)
  have himageCard : edgeImage.card = (pathForestMTwo hk P).card := by
    dsimp [edgeImage]
    rw [Finset.card_image_of_injective _
      (pathForestMTwoEdge_injective hk P)]
    simp
  have himageSubset : edgeImage ⊆
      forestDeltaOne P (residualVertices (by omega) P) \
        pathForestSelectedTailEdges hk P := by
    intro e he
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp he
    exact pathForestMTwoEdge_mem_sigmaTwoFamily hk P p
  have hterm : (∑ _e ∈ edgeImage, 1) ≤
      ∑ e ∈ edgeImage, (e.weight - 1) := by
    apply Finset.sum_le_sum
    intro e he
    have heFamily := himageSubset he
    have hweight := pathForestDeltaOne_weight_ge_two hk P
      (Finset.mem_sdiff.mp heFamily).1
    omega
  calc
    (pathForestMTwo hk P).card = edgeImage.card := himageCard.symm
    _ = ∑ _e ∈ edgeImage, 1 := by simp
    _ ≤ ∑ e ∈ edgeImage, (e.weight - 1) := hterm
    _ ≤ ∑ e ∈ forestDeltaOne P (residualVertices (by omega) P) \
          pathForestSelectedTailEdges hk P, (e.weight - 1) :=
      Finset.sum_le_sum_of_subset himageSubset
    _ = pathForestSigmaTwo hk P := by rw [pathForestSigmaTwo]

/-- The genuine five-way partition gives the exact cardinality identity. -/
theorem pathForest_classes_card_identity (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestM hk P =
      (pathForestMZero hk P).card + (pathForestMOne hk P).card +
        (pathForestMTwo hk P).card + (pathForestMThree hk P).card +
        pathForestF hk P := by
  classical
  rcases pathForest_classes_pairwiseDisjoint hk P with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have h012 : Disjoint
      (pathForestMZero hk P ∪ pathForestMOne hk P) (pathForestMTwo hk P) :=
    Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  have h013 : Disjoint
      (pathForestMZero hk P ∪ pathForestMOne hk P) (pathForestMThree hk P) :=
    Finset.disjoint_union_left.mpr ⟨h03, h13⟩
  have h0123 : Disjoint
      ((pathForestMZero hk P ∪ pathForestMOne hk P) ∪ pathForestMTwo hk P)
      (pathForestMThree hk P) :=
    Finset.disjoint_union_left.mpr ⟨h013, h23⟩
  have h014 : Disjoint
      (pathForestMZero hk P ∪ pathForestMOne hk P) (pathForestMFour hk P) :=
    Finset.disjoint_union_left.mpr ⟨h04, h14⟩
  have h0124 : Disjoint
      ((pathForestMZero hk P ∪ pathForestMOne hk P) ∪ pathForestMTwo hk P)
      (pathForestMFour hk P) :=
    Finset.disjoint_union_left.mpr ⟨h014, h24⟩
  have h01234 : Disjoint
      (((pathForestMZero hk P ∪ pathForestMOne hk P) ∪ pathForestMTwo hk P) ∪
        pathForestMThree hk P) (pathForestMFour hk P) :=
    Finset.disjoint_union_left.mpr ⟨h0124, h34⟩
  have hcard := congrArg Finset.card (pathForest_classes_union hk P hP)
  rw [pathForestClassUnion,
    Finset.card_union_of_disjoint h01234,
    Finset.card_union_of_disjoint h0123,
    Finset.card_union_of_disjoint h012,
    Finset.card_union_of_disjoint h01] at hcard
  simpa [pathForestM, pathForestF] using hcard.symm

/-- The subtraction `M-f` is justified by the literal inclusion `M₄⊆U`. -/
theorem pathForestF_le_M (hk : 7 ≤ k) (P : HamiltonianPath k) :
    pathForestF hk P ≤ pathForestM hk P := by
  apply Finset.card_le_card
  intro p hp
  exact ((mem_pathForestMFour hk P p).mp hp).1

/-- The partition and `|M₀|≤1` give the exact class contribution
`M-f-1 ≤ |M₁|+|M₂|+|M₃|`. -/
theorem pathForest_classContribution_lower (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestM hk P - pathForestF hk P - 1 ≤
      (pathForestMOne hk P).card + (pathForestMTwo hk P).card +
        (pathForestMThree hk P).card := by
  have hcard := pathForest_classes_card_identity hk P hP
  have hzero := pathForestMZero_card_le_one hk P
  have hf := pathForestF_le_M hk P
  omega

/-- The three literal residual sums dominate the exact maximum needed in
Theorem `residual`. -/
theorem pathForest_residualSums_lower (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    max (max 0 (pathForestTerminalFullCount hk P - 1))
        (pathForestM hk P - pathForestF hk P - 1) ≤
      pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
        pathForestSigmaThree hk P := by
  have hSigmaOne := pathForestSigmaOne_ge_MOne hk P
  have hSigmaTwo := pathForestSigmaTwo_ge_MTwo hk P
  have hHead := pathForest_headUnion hk P hP
  have hSigmaThree :
      max (max 0 (pathForestTerminalFullCount hk P - 1))
          (pathForestMThree hk P).card ≤ pathForestSigmaThree hk P :=
    hHead.2.trans hHead.1
  have hA : max 0 (pathForestTerminalFullCount hk P - 1) ≤
      pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
        pathForestSigmaThree hk P := by
    have := (Nat.le_max_left
      (max 0 (pathForestTerminalFullCount hk P - 1))
      (pathForestMThree hk P).card).trans hSigmaThree
    omega
  have hMThree := (Nat.le_max_right
    (max 0 (pathForestTerminalFullCount hk P - 1))
    (pathForestMThree hk P).card).trans hSigmaThree
  have hclasses := pathForest_classContribution_lower hk P hP
  have hB : pathForestM hk P - pathForestF hk P - 1 ≤
      pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
        pathForestSigmaThree hk P := by
    omega
  exact Nat.max_le.mpr ⟨hA, hB⟩

/-- The exact residual quantity
`W=R+max(max(0,C-1),M-f-1)`. -/
noncomputable def pathForestResidualW (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℕ :=
  pathForestTotalBudget (by omega) P +
    max (max 0 (pathForestTerminalFullCount hk P - 1))
      (pathForestM hk P - pathForestF hk P - 1)

/-- The public definitional equation for the exact `W`. -/
theorem pathForestResidualW_eq (hk : 7 ≤ k) (P : HamiltonianPath k) :
    pathForestResidualW hk P =
      pathForestTotalBudget (by omega) P +
        max (max 0 (pathForestTerminalFullCount hk P - 1))
          (pathForestM hk P - pathForestF hk P - 1) := rfl

/-- Theorem `residual`: for the actual reduced minimum path and exact `W`,
`L(k) ≥ (k+1)T-3+W`. -/
theorem pathForest_residual (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    minimumHamiltonianPathWeight k ≥
      (k + 1) * (k - 1).factorial - 3 + pathForestResidualW hk P := by
  have hsum := pathForest_residualSums_lower hk P hP
  have hidentity := pathForest_residualIdentity hk P hP
  rw [← hP.minimumWeight]
  rw [hidentity, pathForestResidualW]
  omega

/-- The same theorem with `W` expanded literally in the conclusion. -/
theorem pathForest_residual_expanded (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    minimumHamiltonianPathWeight k ≥
      (k + 1) * (k - 1).factorial - 3 +
        (pathForestTotalBudget (by omega) P +
          max (max 0 (pathForestTerminalFullCount hk P - 1))
            (pathForestM hk P - pathForestF hk P - 1)) := by
  simpa [pathForestResidualW] using pathForest_residual hk P hP

end SuperpermutationLowerBound
