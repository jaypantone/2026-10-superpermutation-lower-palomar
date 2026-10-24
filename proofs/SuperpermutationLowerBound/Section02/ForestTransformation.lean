module

public import SuperpermutationLowerBound.Section01.Blocks
public import SuperpermutationLowerBound.Foundation.FiniteDigraph

@[expose] public section

namespace SuperpermutationLowerBound

/-! Frozen Definition 2.1 and Lemmas 2.2--2.4. All edge-set updates below are simultaneous
finite-set assignments. -/

open PermutationVertex

variable {k : ℕ}

namespace HamiltonianPath

/-- The first vertex of a Hamiltonian path. -/
noncomputable def tail (P : HamiltonianPath k) : PermutationVertex k :=
  P.toOverlapPath.vertex ⟨0, P.toOverlapPath.length_pos⟩

/-- The last vertex of a Hamiltonian path. -/
noncomputable def head (P : HamiltonianPath k) : PermutationVertex k :=
  P.vertices.getLast P.toOverlapPath.nonempty

/-- Zero-based indices of the edges of a Hamiltonian path. -/
abbrev EdgeIndex (P : HamiltonianPath k) := Fin (P.vertices.length - 1)

/-- The typed overlap edge at a Hamiltonian path edge index. -/
noncomputable def indexedEdge (P : HamiltonianPath k) (i : EdgeIndex P) :
    DirectedOverlapEdge k :=
  P.toOverlapPath.edgeAt i.1 (by
    change i.1 + 1 < P.vertices.length
    omega)

private theorem indexedEdge_injective (P : HamiltonianPath k) :
    Function.Injective P.indexedEdge := by
  intro i j hij
  apply Fin.ext
  have hsource := congrArg DirectedOverlapEdge.source hij
  change P.vertices[i.1] = P.vertices[j.1] at hsource
  exact P.nodup.getElem_inj_iff.mp hsource

/-- The finite edge set `E(P)` of a Hamiltonian path. -/
noncomputable def edgeSet (P : HamiltonianPath k) : FiniteDirectedSubgraph k := by
  classical
  exact Finset.univ.image P.indexedEdge

@[simp]
theorem mem_edgeSet {P : HamiltonianPath k} {e : DirectedOverlapEdge k} :
    e ∈ P.edgeSet ↔ ∃ i : EdgeIndex P, P.indexedEdge i = e := by
  classical
  simp [edgeSet]

theorem edgeSet_card (P : HamiltonianPath k) :
    P.edgeSet.card = P.vertices.length - 1 := by
  classical
  rw [edgeSet, Finset.card_image_of_injective _ P.indexedEdge_injective]
  simp

/-- The graph weight of `E(P)` is the recursive path weight. -/
theorem edgeSet_weight (P : HamiltonianPath k) : graphWeight P.edgeSet = P.weight := by
  classical
  calc
    graphWeight P.edgeSet = ∑ i : EdgeIndex P, (P.indexedEdge i).weight := by
      rw [graphWeight, edgeSet,
        Finset.sum_image (fun _ _ _ _ h => P.indexedEdge_injective h)]
    _ = ∑ i : Fin (P.toOverlapPath.length - 1),
          pathEdgeWeight P.toOverlapPath i.1 := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hi' : i.1 + 1 < P.toOverlapPath.length := by
        change i.1 + 1 < P.vertices.length
        omega
      rw [pathEdgeWeight_of_lt P.toOverlapPath i.1 hi']
      rfl
    _ = ∑ i ∈ Finset.range (P.toOverlapPath.length - 1),
          pathEdgeWeight P.toOverlapPath i :=
      Fin.sum_univ_eq_sum_range _ _
    _ = P.weight := by
      rw [← OverlapPath.weight_eq_sum_edges]
      rfl

private theorem edgeSet_outDegree_le_one (P : HamiltonianPath k)
    (v : PermutationVertex k) : outDegree P.edgeSet v ≤ 1 := by
  classical
  rw [outDegree, Finset.card_le_one]
  intro e he f hf
  have he' := mem_outgoingEdgesAt.mp he
  have hf' := mem_outgoingEdgesAt.mp hf
  obtain ⟨i, hi⟩ := mem_edgeSet.mp he'.1
  obtain ⟨j, hj⟩ := mem_edgeSet.mp hf'.1
  have hsource : (P.indexedEdge i).source = (P.indexedEdge j).source := by
    rw [hi, hj, he'.2, hf'.2]
  have hij : i = j := by
    apply Fin.ext
    change P.vertices[i.1] = P.vertices[j.1] at hsource
    exact P.nodup.getElem_inj_iff.mp hsource
  rw [← hi, ← hj, hij]

private theorem edgeSet_inDegree_le_one (P : HamiltonianPath k)
    (v : PermutationVertex k) : inDegree P.edgeSet v ≤ 1 := by
  classical
  rw [inDegree, Finset.card_le_one]
  intro e he f hf
  have he' := mem_incomingEdgesAt.mp he
  have hf' := mem_incomingEdgesAt.mp hf
  obtain ⟨i, hi⟩ := mem_edgeSet.mp he'.1
  obtain ⟨j, hj⟩ := mem_edgeSet.mp hf'.1
  have htarget : (P.indexedEdge i).target = (P.indexedEdge j).target := by
    rw [hi, hj, he'.2, hf'.2]
  have hij : i = j := by
    apply Fin.ext
    have hget : P.vertices[i.1 + 1] = P.vertices[j.1 + 1] := htarget
    have := P.nodup.getElem_inj_iff.mp hget
    omega
  rw [← hi, ← hj, hij]

private theorem head_eq_getElem_last (P : HamiltonianPath k) :
    P.head = P.vertices[P.vertices.length - 1]'(by
      have := P.toOverlapPath.length_pos
      simpa [OverlapPath.length] using this) := by
  simpa [head, OverlapPath.length] using List.getLast_eq_getElem P.toOverlapPath.nonempty

private theorem outgoing_nonempty_iff_ne_head (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    (outgoingEdgesAt P.edgeSet v).Nonempty ↔ v ≠ P.head := by
  classical
  constructor
  · rintro ⟨e, he⟩ hhead
    have he' := mem_outgoingEdgesAt.mp he
    obtain ⟨i, hi⟩ := mem_edgeSet.mp he'.1
    have hsource : P.vertices[i.1] = v := by
      change (P.indexedEdge i).source = v
      rw [hi, he'.2]
    have hlenpos : 0 < P.vertices.length := by
      simpa [OverlapPath.length] using P.toOverlapPath.length_pos
    have hlast : P.vertices[P.vertices.length - 1]'(by omega) = v := by
      calc
        P.vertices[P.vertices.length - 1]'(by omega) = P.head :=
          (head_eq_getElem_last P).symm
        _ = v := hhead.symm
    have hindex := P.nodup.getElem_inj_iff.mp (hsource.trans hlast.symm)
    have hiLt : i.1 + 1 < P.vertices.length := by
      have := i.2
      omega
    omega
  · intro hv
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp (P.complete v)
    have hilast : i ≠ P.vertices.length - 1 := by
      intro hilast
      apply hv
      have hlenpos : 0 < P.vertices.length := by
        simpa [OverlapPath.length] using P.toOverlapPath.length_pos
      calc
        v = P.vertices[i] := hget.symm
        _ = P.vertices[P.vertices.length - 1]'(by omega) := by subst i; rfl
        _ = P.head := (head_eq_getElem_last P).symm
    have hiEdge : i < P.vertices.length - 1 := by omega
    let j : EdgeIndex P := ⟨i, hiEdge⟩
    refine ⟨P.indexedEdge j, mem_outgoingEdgesAt.mpr ⟨?_, ?_⟩⟩
    · exact mem_edgeSet.mpr ⟨j, rfl⟩
    · change P.vertices[i] = v
      exact hget

private theorem incoming_nonempty_iff_ne_tail (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    (incomingEdgesAt P.edgeSet v).Nonempty ↔ v ≠ P.tail := by
  classical
  constructor
  · rintro ⟨e, he⟩ htail
    have he' := mem_incomingEdgesAt.mp he
    obtain ⟨i, hi⟩ := mem_edgeSet.mp he'.1
    have htarget : P.vertices[i.1 + 1] = v := by
      change (P.indexedEdge i).target = v
      rw [hi, he'.2]
    have hlenpos : 0 < P.vertices.length := by
      simpa [OverlapPath.length] using P.toOverlapPath.length_pos
    have hfirst : P.vertices[0]'hlenpos = v := by
      calc
        P.vertices[0]'hlenpos = P.tail := by rfl
        _ = v := htail.symm
    have hindex := P.nodup.getElem_inj_iff.mp (htarget.trans hfirst.symm)
    omega
  · intro hv
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp (P.complete v)
    have hizero : i ≠ 0 := by
      intro hizero
      apply hv
      calc
        v = P.vertices[i] := hget.symm
        _ = P.vertices[0]'(by omega) := by subst i; rfl
        _ = P.tail := by rfl
    have hipos : 0 < i := Nat.pos_of_ne_zero hizero
    let j : EdgeIndex P := ⟨i - 1, by omega⟩
    refine ⟨P.indexedEdge j, mem_incomingEdgesAt.mpr ⟨?_, ?_⟩⟩
    · exact mem_edgeSet.mpr ⟨j, rfl⟩
    · change P.vertices[(i - 1) + 1] = v
      simpa [show i - 1 + 1 = i by omega] using hget

/-- Every path vertex has out-degree at most one in `E(P)`. -/
theorem edgeSet_outDegree_rule (P : HamiltonianPath k) (v : PermutationVertex k) :
    outDegree P.edgeSet v ≤ 1 := P.edgeSet_outDegree_le_one v

/-- Every path vertex has in-degree at most one in `E(P)`. -/
theorem edgeSet_inDegree_rule (P : HamiltonianPath k) (v : PermutationVertex k) :
    inDegree P.edgeSet v ≤ 1 := P.edgeSet_inDegree_le_one v

/-- A Hamiltonian path's only graph head is its last vertex. -/
theorem edgeSet_heads (P : HamiltonianPath k) : graphHeads P.edgeSet = {P.head} := by
  classical
  ext v
  rw [mem_graphHeads, Finset.mem_singleton]
  constructor
  · intro hempty
    by_contra hne
    have hnonempty := (outgoing_nonempty_iff_ne_head P v).2 hne
    rw [hempty] at hnonempty
    simp at hnonempty
  · rintro rfl
    apply Finset.not_nonempty_iff_eq_empty.mp
    exact fun h => (outgoing_nonempty_iff_ne_head P P.head).1 h rfl

/-- A Hamiltonian path's only graph tail is its first vertex. -/
theorem edgeSet_tails (P : HamiltonianPath k) : graphTails P.edgeSet = {P.tail} := by
  classical
  ext v
  rw [mem_graphTails, Finset.mem_singleton]
  constructor
  · intro hempty
    by_contra hne
    have hnonempty := (incoming_nonempty_iff_ne_tail P v).2 hne
    rw [hempty] at hnonempty
    simp at hnonempty
  · rintro rfl
    apply Finset.not_nonempty_iff_eq_empty.mp
    exact fun h => (incoming_nonempty_iff_ne_tail P P.tail).1 h rfl

end HamiltonianPath

/-- The loopless weight-one rotation edge out of `v`. -/
def rotationEdge (hk : 2 ≤ k) (v : PermutationVertex k) : DirectedOverlapEdge k where
  source := v
  target := rotation v
  ne := (rotation_ne_self hk v).symm

@[simp]
theorem rotationEdge_weight (hk : 3 ≤ k) (v : PermutationVertex k) :
    (rotationEdge (by omega) v).weight = 1 := rotation_has_weight_one v hk

/-- The simultaneous set of rotation edges installed at `V`. -/
noncomputable def rotationEdges (hk : 2 ≤ k) (V : Finset (PermutationVertex k)) :
    FiniteDirectedSubgraph k := by
  classical
  exact V.image (rotationEdge hk)

private theorem rotationEdge_injective (hk : 2 ≤ k) :
    Function.Injective (rotationEdge hk : PermutationVertex k → DirectedOverlapEdge k) := by
  intro u v h
  exact congrArg DirectedOverlapEdge.source h

@[simp]
theorem mem_rotationEdges {hk : 2 ≤ k} {V : Finset (PermutationVertex k)}
    {e : DirectedOverlapEdge k} :
    e ∈ rotationEdges hk V ↔ ∃ v ∈ V, rotationEdge hk v = e := by
  classical
  simp [rotationEdges]

theorem rotationEdges_card (hk : 2 ≤ k) (V : Finset (PermutationVertex k)) :
    (rotationEdges hk V).card = V.card := by
  classical
  rw [rotationEdges, Finset.card_image_of_injective _ (rotationEdge_injective hk)]

theorem rotationEdges_weight (hk : 3 ≤ k) (V : Finset (PermutationVertex k)) :
    graphWeight (rotationEdges (by omega) V) = V.card := by
  classical
  calc
    graphWeight (rotationEdges (by omega) V) =
        ∑ v ∈ V, (rotationEdge (by omega) v).weight := by
      rw [graphWeight, rotationEdges, Finset.sum_image]
      exact fun _ _ _ _ h => rotationEdge_injective (by omega) h
    _ = V.card := by simp [rotationEdge_weight hk]

/-- The precondition of frozen Definition 2.1: no installed rotation edge is already an
edge of the original Hamiltonian path. -/
def RotationEdgesAdmissible (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : Prop :=
  ∀ v ∈ V, rotationEdge hk v ∉ P.edgeSet

/-- `E₀`, the original Hamiltonian path edge set. -/
noncomputable def forestStepZero (P : HamiltonianPath k) : FiniteDirectedSubgraph k :=
  P.edgeSet

/-- `Δ₁`, defined from the actual simultaneous Step 1 removal set. -/
noncomputable def forestDeltaOne (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k :=
  outgoingEdges (forestStepZero P) V

/-- `E₁`: simultaneously remove the original `P`-out-edges at `V` and install all
rotation edges at `V`. -/
noncomputable def forestStepOne (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k :=
  (forestStepZero P \ forestDeltaOne P V) ∪ rotationEdges hk V

/-- Vertices having exactly two incoming edges after simultaneous Step 1. -/
noncomputable def doubleIncomingVertices (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun u => inDegree (forestStepOne hk P V) u = 2

/-- `E₂`: simultaneously remove the original `P`-in-edge at every double-incoming Step 1
target. -/
noncomputable def forestStepTwo (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k :=
  forestStepOne hk P V \
    incomingEdges (forestStepZero P) (doubleIncomingVertices hk P V)

/-- Frozen Definition 2.1, the simultaneous transformation `f(P,V)`. -/
noncomputable def forestTransform (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k :=
  forestStepTwo hk P V

/-- `Δ₂`, defined as the edges actually present after Step 1 and absent after Step 2. -/
noncomputable def forestDeltaTwo (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k :=
  forestStepOne hk P V \ forestStepTwo hk P V

/-- `I = 1[H(P) ∈ V]`, including the endpoint case in which Step 1 adds without removing. -/
noncomputable def forestHeadIndicator (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) : ℕ := by
  classical
  exact if P.head ∈ V then 1 else 0

/-- The exact frozen identity `Δ₁ = out(P,V)`. -/
theorem forestDeltaOne_eq_outgoing (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    forestDeltaOne P V = outgoingEdges P.edgeSet V := rfl

/-- The exact frozen simultaneous assignment for `E₁`. -/
theorem forestStepOne_eq (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    forestStepOne hk P V =
      (P.edgeSet \ outgoingEdges P.edgeSet V) ∪ rotationEdges hk V := rfl

/-- The exact frozen simultaneous assignment for `E₂`. -/
theorem forestStepTwo_eq (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    forestStepTwo hk P V = forestStepOne hk P V \
      incomingEdges P.edgeSet (doubleIncomingVertices hk P V) := rfl

/-- The exact actual-set definition `Δ₂ = E₁ \ E₂`. -/
theorem forestDeltaTwo_eq_stepDifference (hk : 2 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    forestDeltaTwo hk P V = forestStepOne hk P V \ forestStepTwo hk P V := rfl

private theorem mem_forestStepOne_iff {hk : 2 ≤ k} {P : HamiltonianPath k}
    {V : Finset (PermutationVertex k)} {e : DirectedOverlapEdge k} :
    e ∈ forestStepOne hk P V ↔
      (e ∈ P.edgeSet ∧ e.source ∉ V) ∨ e ∈ rotationEdges hk V := by
  classical
  simp only [forestStepOne, forestStepZero, forestDeltaOne, Finset.mem_union,
    Finset.mem_sdiff, mem_outgoingEdges]
  tauto

private theorem original_mem_stepOne_iff {hk : 2 ≤ k} {P : HamiltonianPath k}
    {V : Finset (PermutationVertex k)}
    (hadm : RotationEdgesAdmissible hk P V) {e : DirectedOverlapEdge k}
    (heP : e ∈ P.edgeSet) :
    e ∈ forestStepOne hk P V ↔ e.source ∉ V := by
  constructor
  · intro he
    rcases mem_forestStepOne_iff.mp he with horiginal | hrotation
    · exact horiginal.2
    · obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp hrotation
      exfalso
      apply hadm v hv
      rw [hve]
      exact heP
  · intro hsource
    exact mem_forestStepOne_iff.mpr (Or.inl ⟨heP, hsource⟩)

private theorem rotationEdge_mem_stepOne (hk : 2 ≤ k) (P : HamiltonianPath k)
    {V : Finset (PermutationVertex k)} {v : PermutationVertex k} (hv : v ∈ V) :
    rotationEdge hk v ∈ forestStepOne hk P V := by
  exact mem_forestStepOne_iff.mpr (Or.inr (mem_rotationEdges.mpr ⟨v, hv, rfl⟩))

private theorem rotationEdge_not_original {hk : 2 ≤ k} {P : HamiltonianPath k}
    {V : Finset (PermutationVertex k)}
    (hadm : RotationEdgesAdmissible hk P V) {v : PermutationVertex k} (hv : v ∈ V) :
    rotationEdge hk v ∉ P.edgeSet := hadm v hv

private theorem rotationEdge_mem_stepTwo {hk : 2 ≤ k} {P : HamiltonianPath k}
    {V : Finset (PermutationVertex k)}
    (hadm : RotationEdgesAdmissible hk P V) {v : PermutationVertex k} (hv : v ∈ V) :
    rotationEdge hk v ∈ forestStepTwo hk P V := by
  classical
  apply Finset.mem_sdiff.mpr
  refine ⟨rotationEdge_mem_stepOne hk P hv, ?_⟩
  intro hremoved
  exact hadm v hv (mem_incomingEdges.mp hremoved).1

private theorem rotationEdges_outDegree_le_one (hk : 2 ≤ k)
    (V : Finset (PermutationVertex k)) (x : PermutationVertex k) :
    outDegree (rotationEdges hk V) x ≤ 1 := by
  classical
  rw [outDegree, Finset.card_le_one]
  intro e he f hf
  obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp (mem_outgoingEdgesAt.mp he).1
  obtain ⟨w, hw, hwf⟩ := mem_rotationEdges.mp (mem_outgoingEdgesAt.mp hf).1
  have hvx : v = x := by
    calc
      v = (rotationEdge hk v).source := rfl
      _ = e.source := congrArg DirectedOverlapEdge.source hve
      _ = x := (mem_outgoingEdgesAt.mp he).2
  have hwx : w = x := by
    calc
      w = (rotationEdge hk w).source := rfl
      _ = f.source := congrArg DirectedOverlapEdge.source hwf
      _ = x := (mem_outgoingEdgesAt.mp hf).2
  subst w
  subst v
  exact hve.symm.trans hwf

private theorem rotationEdges_inDegree_le_one (hk : 3 ≤ k)
    (V : Finset (PermutationVertex k)) (x : PermutationVertex k) :
    inDegree (rotationEdges (by omega) V) x ≤ 1 := by
  classical
  rw [inDegree, Finset.card_le_one]
  intro e he f hf
  obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp (mem_incomingEdgesAt.mp he).1
  obtain ⟨w, hw, hwf⟩ := mem_rotationEdges.mp (mem_incomingEdgesAt.mp hf).1
  have htargets : rotation v = rotation w := by
    calc
      rotation v = e.target := by rw [← hve]; rfl
      _ = x := (mem_incomingEdgesAt.mp he).2
      _ = f.target := (mem_incomingEdgesAt.mp hf).2.symm
      _ = rotation w := by rw [← hwf]; rfl
  have hvw := rotation_injective (by omega : 1 ≤ k) htargets
  subst w
  exact hve.symm.trans hwf

private theorem forestStepOne_outDegree_le_one (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (x : PermutationVertex k) : outDegree (forestStepOne (by omega) P V) x ≤ 1 := by
  classical
  rw [outDegree, Finset.card_le_one]
  intro e he f hf
  have heSource := (mem_outgoingEdgesAt.mp he).2
  have hfSource := (mem_outgoingEdgesAt.mp hf).2
  rcases mem_forestStepOne_iff.mp (mem_outgoingEdgesAt.mp he).1 with heP | heR
  · rcases mem_forestStepOne_iff.mp (mem_outgoingEdgesAt.mp hf).1 with hfP | hfR
    · have hle := P.edgeSet_outDegree_rule x
      rw [outDegree, Finset.card_le_one] at hle
      exact hle e (mem_outgoingEdgesAt.mpr ⟨heP.1, heSource⟩)
        f (mem_outgoingEdgesAt.mpr ⟨hfP.1, hfSource⟩)
    · obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp hfR
      exfalso
      apply heP.2
      have hvx : v = x := by
        calc
          v = (rotationEdge (by omega) v).source := rfl
          _ = f.source := congrArg DirectedOverlapEdge.source hve
          _ = x := hfSource
      have hxV : x ∈ V := by simpa [hvx] using hv
      simpa [heSource] using hxV
  · rcases mem_forestStepOne_iff.mp (mem_outgoingEdgesAt.mp hf).1 with hfP | hfR
    · obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp heR
      exfalso
      apply hfP.2
      have hvx : v = x := by
        calc
          v = (rotationEdge (by omega) v).source := rfl
          _ = e.source := congrArg DirectedOverlapEdge.source hve
          _ = x := heSource
      have hxV : x ∈ V := by simpa [hvx] using hv
      simpa [hfSource] using hxV
    · have hle := rotationEdges_outDegree_le_one (by omega : 2 ≤ k) V x
      rw [outDegree, Finset.card_le_one] at hle
      exact hle e (mem_outgoingEdgesAt.mpr ⟨heR, heSource⟩)
        f (mem_outgoingEdgesAt.mpr ⟨hfR, hfSource⟩)

private theorem forestStepOne_inDegree_le_two (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (x : PermutationVertex k) : inDegree (forestStepOne (by omega) P V) x ≤ 2 := by
  classical
  let A := incomingEdgesAt P.edgeSet x
  let B := incomingEdgesAt (rotationEdges (by omega) V) x
  have hsubset : incomingEdgesAt (forestStepOne (by omega) P V) x ⊆ A ∪ B := by
    intro e he
    have heTarget := (mem_incomingEdgesAt.mp he).2
    rcases mem_forestStepOne_iff.mp (mem_incomingEdgesAt.mp he).1 with heP | heR
    · exact Finset.mem_union_left _ (mem_incomingEdgesAt.mpr ⟨heP.1, heTarget⟩)
    · exact Finset.mem_union_right _ (mem_incomingEdgesAt.mpr ⟨heR, heTarget⟩)
  calc
    inDegree (forestStepOne (by omega) P V) x =
        (incomingEdgesAt (forestStepOne (by omega) P V) x).card := rfl
    _ ≤ (A ∪ B).card := Finset.card_le_card hsubset
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ 1 + 1 := Nat.add_le_add (P.edgeSet_inDegree_rule x)
      (rotationEdges_inDegree_le_one hk V x)
    _ = 2 := rfl

private theorem forestStepTwo_outDegree_le_one (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (x : PermutationVertex k) : outDegree (forestStepTwo (by omega) P V) x ≤ 1 := by
  classical
  apply (Finset.card_le_card ?_).trans (forestStepOne_outDegree_le_one hk P V x)
  intro e he
  exact mem_outgoingEdgesAt.mpr
    ⟨(Finset.mem_sdiff.mp (mem_outgoingEdgesAt.mp he).1).1,
      (mem_outgoingEdgesAt.mp he).2⟩

private theorem forestStepTwo_inDegree_le_one (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (_hadm : RotationEdgesAdmissible (by omega) P V)
    (x : PermutationVertex k) : inDegree (forestStepTwo (by omega) P V) x ≤ 1 := by
  classical
  rw [inDegree, Finset.card_le_one]
  intro e he f hf
  by_contra hef
  have he2 := mem_incomingEdgesAt.mp he
  have hf2 := mem_incomingEdgesAt.mp hf
  have he1 : e ∈ incomingEdgesAt (forestStepOne (by omega) P V) x :=
    mem_incomingEdgesAt.mpr ⟨(Finset.mem_sdiff.mp he2.1).1, he2.2⟩
  have hf1 : f ∈ incomingEdgesAt (forestStepOne (by omega) P V) x :=
    mem_incomingEdgesAt.mpr ⟨(Finset.mem_sdiff.mp hf2.1).1, hf2.2⟩
  have honeLt : 1 < (incomingEdgesAt (forestStepOne (by omega) P V) x).card :=
    Finset.one_lt_card.mpr ⟨e, he1, f, hf1, hef⟩
  have hleTwo := forestStepOne_inDegree_le_two hk P V x
  have hcard : inDegree (forestStepOne (by omega) P V) x = 2 := by
    rw [inDegree] at hleTwo ⊢
    omega
  have hxDouble : x ∈ doubleIncomingVertices (by omega) P V := by
    simp [doubleIncomingVertices, hcard]
  have heNotP : e ∉ P.edgeSet := by
    intro heP
    apply (Finset.mem_sdiff.mp he2.1).2
    exact mem_incomingEdges.mpr ⟨heP, by simpa [he2.2] using hxDouble⟩
  have hfNotP : f ∉ P.edgeSet := by
    intro hfP
    apply (Finset.mem_sdiff.mp hf2.1).2
    exact mem_incomingEdges.mpr ⟨hfP, by simpa [hf2.2] using hxDouble⟩
  have heR : e ∈ rotationEdges (by omega) V := by
    rcases mem_forestStepOne_iff.mp (Finset.mem_sdiff.mp he2.1).1 with heP | heR
    · exact (heNotP heP.1).elim
    · exact heR
  have hfR : f ∈ rotationEdges (by omega) V := by
    rcases mem_forestStepOne_iff.mp (Finset.mem_sdiff.mp hf2.1).1 with hfP | hfR
    · exact (hfNotP hfP.1).elim
    · exact hfR
  have hle := rotationEdges_inDegree_le_one hk V x
  rw [inDegree, Finset.card_le_one] at hle
  exact hef (hle e (mem_incomingEdgesAt.mpr ⟨heR, he2.2⟩)
    f (mem_incomingEdgesAt.mpr ⟨hfR, hf2.2⟩))

/-- Frozen Lemma 2.2, in-degree half. -/
theorem forestTransform_inDegree_rule (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V)
    (x : PermutationVertex k) : inDegree (forestTransform (by omega) P V) x ≤ 1 :=
  forestStepTwo_inDegree_le_one hk P V hadm x

/-- Frozen Lemma 2.2, out-degree half. -/
theorem forestTransform_outDegree_rule (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) (_hadm : RotationEdgesAdmissible (by omega) P V)
    (x : PermutationVertex k) : outDegree (forestTransform (by omega) P V) x ≤ 1 :=
  forestStepTwo_outDegree_le_one hk P V x

/-- Frozen Lemma 2.2, exact weak-component conclusion. -/
theorem forestTransform_component_rule (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V)
    (C : WeakComponent (forestTransform (by omega) P V)) :
    IsDirectedPathComponent C ∨ IsDirectedCycleComponent C :=
  weakComponent_directedPath_or_directedCycle _
    (forestTransform_inDegree_rule hk P V hadm)
    (forestTransform_outDegree_rule hk P V hadm) C

/-- Frozen Lemma 2.2 as one exported degree-and-component statement. -/
theorem forestTransform_degree_rule (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    (∀ x : PermutationVertex k,
      inDegree (forestTransform (by omega) P V) x ≤ 1 ∧
      outDegree (forestTransform (by omega) P V) x ≤ 1) ∧
    (∀ C : WeakComponent (forestTransform (by omega) P V),
      IsDirectedPathComponent C ∨ IsDirectedCycleComponent C) := by
  exact ⟨fun x => ⟨forestTransform_inDegree_rule hk P V hadm x,
      forestTransform_outDegree_rule hk P V hadm x⟩,
    forestTransform_component_rule hk P V hadm⟩

private theorem mem_forestDeltaTwo_iff {hk : 2 ≤ k} {P : HamiltonianPath k}
    {V : Finset (PermutationVertex k)} {e : DirectedOverlapEdge k} :
    e ∈ forestDeltaTwo hk P V ↔
      e ∈ forestStepOne hk P V ∧
      e ∈ incomingEdges P.edgeSet (doubleIncomingVertices hk P V) := by
  classical
  simp only [forestDeltaTwo, forestStepTwo, forestStepZero, Finset.mem_sdiff,
    mem_incomingEdges]
  tauto

/-- Frozen Lemma 2.3, exact head-boundary equality
`Δ₂ = out(P, H(X) \ H(P))`. -/
theorem forestDeltaTwo_eq_outgoing_heads (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    forestDeltaTwo (by omega) P V =
      outgoingEdges P.edgeSet
        (graphHeads (forestTransform (by omega) P V) \ graphHeads P.edgeSet) := by
  classical
  ext e
  constructor
  · intro heDelta
    have heInfo := mem_forestDeltaTwo_iff.mp heDelta
    have heP : e ∈ P.edgeSet := (mem_incomingEdges.mp heInfo.2).1
    have heSourceNot : e.source ∉ V :=
      (original_mem_stepOne_iff hadm heP).1 heInfo.1
    have heNotTwo : e ∉ forestStepTwo (by omega) P V :=
      (Finset.mem_sdiff.mp heDelta).2
    have hheadX : e.source ∈ graphHeads (forestTransform (by omega) P V) := by
      apply mem_graphHeads.mpr
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨f, hf⟩
      have hfTwo := mem_outgoingEdgesAt.mp hf
      have hfOne : f ∈ forestStepOne (by omega) P V :=
        (Finset.mem_sdiff.mp hfTwo.1).1
      have hle := forestStepOne_outDegree_le_one hk P V e.source
      rw [outDegree, Finset.card_le_one] at hle
      have hfe := hle f (mem_outgoingEdgesAt.mpr ⟨hfOne, hfTwo.2⟩)
        e (mem_outgoingEdgesAt.mpr ⟨heInfo.1, rfl⟩)
      have hfInTwo := hfTwo.1
      rw [hfe] at hfInTwo
      exact heNotTwo hfInTwo
    have hnotHeadP : e.source ∉ graphHeads P.edgeSet := by
      intro hhead
      have hempty := mem_graphHeads.mp hhead
      have : e ∈ outgoingEdgesAt P.edgeSet e.source :=
        mem_outgoingEdgesAt.mpr ⟨heP, rfl⟩
      rw [hempty] at this
      simp at this
    exact mem_outgoingEdges.mpr
      ⟨heP, Finset.mem_sdiff.mpr ⟨hheadX, hnotHeadP⟩⟩
  · intro heOut
    have heOut' := mem_outgoingEdges.mp heOut
    have heP := heOut'.1
    have hsourceBoundary := Finset.mem_sdiff.mp heOut'.2
    have hsourceNotV : e.source ∉ V := by
      intro hsourceV
      have hrotTwo := rotationEdge_mem_stepTwo hadm hsourceV
      have hrotOut : rotationEdge (by omega) e.source ∈
          outgoingEdgesAt (forestTransform (by omega) P V) e.source :=
        mem_outgoingEdgesAt.mpr ⟨hrotTwo, rfl⟩
      have hempty := mem_graphHeads.mp hsourceBoundary.1
      rw [hempty] at hrotOut
      simp at hrotOut
    have heOne : e ∈ forestStepOne (by omega) P V :=
      (original_mem_stepOne_iff hadm heP).2 hsourceNotV
    have heNotTwo : e ∉ forestStepTwo (by omega) P V := by
      intro heTwo
      have heOutX : e ∈ outgoingEdgesAt (forestTransform (by omega) P V) e.source :=
        mem_outgoingEdgesAt.mpr ⟨heTwo, rfl⟩
      have hempty := mem_graphHeads.mp hsourceBoundary.1
      rw [hempty] at heOutX
      simp at heOutX
    exact Finset.mem_sdiff.mpr ⟨heOne, heNotTwo⟩

/-- Frozen Lemma 2.3, exact tail-boundary inclusion. -/
theorem forestIncoming_newTails_subset_deltaOne (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    incomingEdges P.edgeSet
        (graphTails (forestTransform (by omega) P V) \ graphTails P.edgeSet) ⊆
      forestDeltaOne P V := by
  classical
  intro e heIncoming
  have heIncoming' := mem_incomingEdges.mp heIncoming
  have heP := heIncoming'.1
  have htargetBoundary := Finset.mem_sdiff.mp heIncoming'.2
  by_contra heNotDelta
  have hsourceNotV : e.source ∉ V := by
    intro hsourceV
    exact heNotDelta (by
      exact mem_outgoingEdges.mpr ⟨heP, hsourceV⟩)
  have heOne : e ∈ forestStepOne (by omega) P V :=
    (original_mem_stepOne_iff hadm heP).2 hsourceNotV
  have heNotTwo : e ∉ forestStepTwo (by omega) P V := by
    intro heTwo
    have heInX : e ∈ incomingEdgesAt (forestTransform (by omega) P V) e.target :=
      mem_incomingEdgesAt.mpr ⟨heTwo, rfl⟩
    have hempty := mem_graphTails.mp htargetBoundary.1
    rw [hempty] at heInX
    simp at heInX
  have heDelta : e ∈ forestDeltaTwo (by omega) P V :=
    Finset.mem_sdiff.mpr ⟨heOne, heNotTwo⟩
  have heDeltaInfo := mem_forestDeltaTwo_iff.mp heDelta
  have htargetDouble : e.target ∈ doubleIncomingVertices (by omega) P V :=
    (mem_incomingEdges.mp heDeltaInfo.2).2
  have hcard : inDegree (forestStepOne (by omega) P V) e.target = 2 := by
    simpa [doubleIncomingVertices] using htargetDouble
  have heInOne : e ∈ incomingEdgesAt (forestStepOne (by omega) P V) e.target :=
    mem_incomingEdgesAt.mpr ⟨heOne, rfl⟩
  have hcardErase :
      ((incomingEdgesAt (forestStepOne (by omega) P V) e.target).erase e).card = 1 := by
    have hcard' : (incomingEdgesAt (forestStepOne (by omega) P V) e.target).card = 2 := hcard
    rw [Finset.card_erase_of_mem heInOne, hcard']
  obtain ⟨f, hfErase⟩ :
      (incomingEdgesAt (forestStepOne (by omega) P V) e.target).erase e |>.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hfInOne : f ∈ incomingEdgesAt (forestStepOne (by omega) P V) e.target :=
    Finset.mem_of_mem_erase hfErase
  have hfe : f ≠ e := Finset.ne_of_mem_erase hfErase
  have hfNotP : f ∉ P.edgeSet := by
    intro hfP
    have hle := P.edgeSet_inDegree_rule e.target
    rw [inDegree, Finset.card_le_one] at hle
    exact hfe (hle f (mem_incomingEdgesAt.mpr ⟨hfP,
      (mem_incomingEdgesAt.mp hfInOne).2⟩)
      e (mem_incomingEdgesAt.mpr ⟨heP, rfl⟩))
  have hfRotation : f ∈ rotationEdges (by omega) V := by
    rcases mem_forestStepOne_iff.mp (mem_incomingEdgesAt.mp hfInOne).1 with hfP | hfR
    · exact (hfNotP hfP.1).elim
    · exact hfR
  have hfTwo : f ∈ forestStepTwo (by omega) P V := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_incomingEdgesAt.mp hfInOne).1, ?_⟩
    intro hfRemoved
    exact hfNotP (mem_incomingEdges.mp hfRemoved).1
  have hfInX : f ∈ incomingEdgesAt (forestTransform (by omega) P V) e.target :=
    mem_incomingEdgesAt.mpr ⟨hfTwo, (mem_incomingEdgesAt.mp hfInOne).2⟩
  have hempty := mem_graphTails.mp htargetBoundary.1
  rw [hempty] at hfInX
  simp at hfInX

/-- Frozen Lemma 2.3 with both boundary-set statements bundled. -/
theorem forestTransform_boundary_sets (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    forestDeltaTwo (by omega) P V =
        outgoingEdges P.edgeSet
          (graphHeads (forestTransform (by omega) P V) \ graphHeads P.edgeSet) ∧
      incomingEdges P.edgeSet
          (graphTails (forestTransform (by omega) P V) \ graphTails P.edgeSet) ⊆
        forestDeltaOne P V :=
  ⟨forestDeltaTwo_eq_outgoing_heads hk P V hadm,
    forestIncoming_newTails_subset_deltaOne hk P V hadm⟩

private theorem graphWeight_sdiff_add {A B : FiniteDirectedSubgraph k} (hAB : A ⊆ B) :
    graphWeight (B \ A) + graphWeight A = graphWeight B := by
  simpa [graphWeight] using
    (Finset.sum_sdiff (f := fun e : DirectedOverlapEdge k => e.weight) hAB)

private theorem graphWeight_eq_card_add_excess (X : FiniteDirectedSubgraph k) :
    graphWeight X = X.card + ∑ e ∈ X, (e.weight - 1) := by
  classical
  rw [graphWeight]
  calc
    (∑ e ∈ X, e.weight) = ∑ e ∈ X, (1 + (e.weight - 1)) := by
      apply Finset.sum_congr rfl
      intro e _he
      have hweight : 1 ≤ e.weight := (overlapWeight_spec e.source e.target).1
      omega
    _ = (∑ _e ∈ X, 1) + ∑ e ∈ X, (e.weight - 1) := by
      rw [Finset.sum_add_distrib]
    _ = X.card + ∑ e ∈ X, (e.weight - 1) := by simp

private theorem outgoingEdges_card_eq_sum_outDegree (X : FiniteDirectedSubgraph k)
    (V : Finset (PermutationVertex k)) :
    (outgoingEdges X V).card = ∑ v ∈ V, outDegree X v := by
  classical
  have hunion : outgoingEdges X V = V.biUnion (outgoingEdgesAt X) := by
    ext e
    simp only [mem_outgoingEdges, Finset.mem_biUnion, mem_outgoingEdgesAt]
    constructor
    · rintro ⟨heX, hsource⟩
      exact ⟨e.source, hsource, heX, rfl⟩
    · rintro ⟨v, hv, heX, hsource⟩
      exact ⟨heX, hsource ▸ hv⟩
  have hpair :
      (↑V : Set (PermutationVertex k)).PairwiseDisjoint (outgoingEdgesAt X) := by
    intro u hu v hv huv
    change Disjoint (outgoingEdgesAt X u) (outgoingEdgesAt X v)
    rw [Finset.disjoint_left]
    intro e heu hev
    apply huv
    exact (mem_outgoingEdgesAt.mp heu).2.symm.trans
      (mem_outgoingEdgesAt.mp hev).2
  rw [hunion, Finset.card_biUnion hpair]
  rfl

private theorem HamiltonianPath.edgeSet_outDegree_eq (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    outDegree P.edgeSet v = if v = P.head then 0 else 1 := by
  classical
  by_cases hv : v = P.head
  · rw [if_pos hv]
    subst v
    rw [outDegree]
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    exact fun h => (P.outgoing_nonempty_iff_ne_head P.head).1 h rfl
  · rw [if_neg hv]
    have hnonempty := (P.outgoing_nonempty_iff_ne_head v).2 hv
    have hpos : 0 < outDegree P.edgeSet v := by
      rw [outDegree]
      exact Finset.card_pos.mpr hnonempty
    have hle := P.edgeSet_outDegree_rule v
    omega

private theorem forestDeltaOne_card_add_indicator (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    (forestDeltaOne P V).card + forestHeadIndicator P V = V.card := by
  classical
  rw [forestDeltaOne, forestStepZero,
    outgoingEdges_card_eq_sum_outDegree]
  simp only [P.edgeSet_outDegree_eq]
  by_cases hhead : P.head ∈ V
  · have herase := Finset.sum_erase_add V
      (fun v => if v = P.head then 0 else 1) hhead
    have herase' :
        (∑ v ∈ V.erase P.head, if v = P.head then 0 else 1) =
          ∑ v ∈ V, if v = P.head then 0 else 1 := by
      simpa using herase
    have hsum :
        (∑ v ∈ V, if v = P.head then 0 else 1) =
          (V.erase P.head).card := by
      rw [← herase']
      calc
        (∑ v ∈ V.erase P.head, if v = P.head then 0 else 1) =
            ∑ _v ∈ V.erase P.head, 1 := by
          apply Finset.sum_congr rfl
          intro v hv
          simp [(Finset.mem_erase.mp hv).1]
        _ = (V.erase P.head).card := by simp
    rw [forestHeadIndicator, if_pos hhead, hsum]
    exact Finset.card_erase_add_one hhead
  · have hsum :
        (∑ v ∈ V, if v = P.head then 0 else 1) = V.card := by
      calc
        (∑ v ∈ V, if v = P.head then 0 else 1) = ∑ _v ∈ V, 1 := by
          apply Finset.sum_congr rfl
          intro v hv
          have hvne : v ≠ P.head := fun h => hhead (by simpa [h] using hv)
          simp [hvne]
        _ = V.card := by simp
    rw [forestHeadIndicator, if_neg hhead, hsum, Nat.add_zero]

private theorem forestStepOne_weight (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    graphWeight (forestStepOne (by omega) P V) =
      graphWeight (P.edgeSet \ forestDeltaOne P V) + V.card := by
  classical
  have hdisjoint : Disjoint (P.edgeSet \ forestDeltaOne P V)
      (rotationEdges (by omega) V) := by
    rw [Finset.disjoint_left]
    intro e heP heRotation
    obtain ⟨v, hv, hve⟩ := mem_rotationEdges.mp heRotation
    exact hadm v hv (by simpa [hve] using (Finset.mem_sdiff.mp heP).1)
  calc
    graphWeight (forestStepOne (by omega) P V) =
        graphWeight (P.edgeSet \ forestDeltaOne P V) +
          graphWeight (rotationEdges (by omega) V) := by
      simpa [forestStepOne, forestStepZero, graphWeight] using
        (Finset.sum_union (f := fun e : DirectedOverlapEdge k => e.weight) hdisjoint)
    _ = graphWeight (P.edgeSet \ forestDeltaOne P V) + V.card := by
      rw [rotationEdges_weight hk V]

private theorem forestStepTwo_weight (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k)) :
    graphWeight (forestDeltaTwo (by omega) P V) +
        graphWeight (forestTransform (by omega) P V) =
      graphWeight (forestStepOne (by omega) P V) := by
  classical
  have hsubset : forestStepTwo (by omega) P V ⊆ forestStepOne (by omega) P V := by
    intro e he
    exact (Finset.mem_sdiff.mp he).1
  simpa [forestDeltaTwo, forestTransform] using graphWeight_sdiff_add hsubset

private theorem forestHeadIndicator_le_weight (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    forestHeadIndicator P V ≤ graphWeight (forestTransform (by omega) P V) := by
  classical
  by_cases hhead : P.head ∈ V
  · have hrotation : rotationEdge (by omega) P.head ∈
        forestTransform (by omega) P V := rotationEdge_mem_stepTwo hadm hhead
    have hle : (rotationEdge (by omega) P.head).weight ≤
        graphWeight (forestTransform (by omega) P V) := by
      rw [graphWeight]
      exact Finset.single_le_sum (fun _e _he => Nat.zero_le _) hrotation
    simpa [forestHeadIndicator, hhead, rotationEdge_weight hk] using hle
  · simp [forestHeadIndicator, hhead]

private theorem forestTransform_weight_rule_add_indicator (hk : 3 ≤ k)
    (P : HamiltonianPath k) (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    P.weight + forestHeadIndicator P V =
      graphWeight (forestTransform (by omega) P V) +
        (∑ e ∈ forestDeltaOne P V, (e.weight - 1)) +
        graphWeight (forestDeltaTwo (by omega) P V) := by
  classical
  have hDeltaSubset : forestDeltaOne P V ⊆ P.edgeSet := by
    intro e he
    exact (mem_outgoingEdges.mp he).1
  have hPathSplit := graphWeight_sdiff_add hDeltaSubset
  have hStepOne := forestStepOne_weight hk P V hadm
  have hStepTwo := forestStepTwo_weight hk P V
  have hDeltaWeight := graphWeight_eq_card_add_excess (forestDeltaOne P V)
  have hDeltaCard := forestDeltaOne_card_add_indicator P V
  have hPathWeight := P.edgeSet_weight
  omega

/-- Frozen Lemma 2.4. The sums and subtraction are in `ℕ`; the proof first establishes
the addition-normalized identity and then uses the surviving head rotation edge to justify
the displayed subtraction exactly. -/
theorem forestTransform_weight_rule (hk : 3 ≤ k) (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hadm : RotationEdgesAdmissible (by omega) P V) :
    P.weight =
      graphWeight (forestTransform (by omega) P V) +
          (∑ e ∈ forestDeltaOne P V, (e.weight - 1)) -
        forestHeadIndicator P V +
        ∑ e ∈ forestDeltaTwo (by omega) P V, e.weight := by
  classical
  have hnormalized := forestTransform_weight_rule_add_indicator hk P V hadm
  have hindicator := forestHeadIndicator_le_weight hk P V hadm
  change P.weight =
    graphWeight (forestTransform (by omega) P V) +
        (∑ e ∈ forestDeltaOne P V, (e.weight - 1)) -
      forestHeadIndicator P V +
      graphWeight (forestDeltaTwo (by omega) P V)
  omega

end SuperpermutationLowerBound
