module

public import SuperpermutationLowerBound.Section02.ForestTransformation

@[expose] public section

-- Export private witnesses used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! The specialization of the frozen forest transformation to a Hamiltonian path, including
the remainder of frozen Section 2.
-/

open PermutationVertex

variable {k : ℕ}

namespace HamiltonianPath

/-- The zero-based position at which a vertex is visited by a Hamiltonian path. -/
noncomputable def vertexIndex (P : HamiltonianPath k) (v : PermutationVertex k) : ℕ :=
  P.vertices.idxOf v

theorem vertexIndex_lt_length (P : HamiltonianPath k) (v : PermutationVertex k) :
    P.vertexIndex v < P.vertices.length := by
  classical
  exact List.idxOf_lt_length_iff.mpr (P.complete v)

theorem getElem_vertexIndex (P : HamiltonianPath k) (v : PermutationVertex k) :
    P.vertices[P.vertexIndex v]'(P.vertexIndex_lt_length v) = v := by
  classical
  exact List.getElem_idxOf (P.vertexIndex_lt_length v)

theorem vertexIndex_injective (P : HamiltonianPath k) :
    Function.Injective P.vertexIndex := by
  classical
  intro u v huv
  exact (List.idxOf_inj (P.complete u)).mp huv

theorem vertexIndex_tail (P : HamiltonianPath k) : P.vertexIndex P.tail = 0 := by
  classical
  have hlen : 0 < P.vertices.length := by
    simpa [OverlapPath.length] using P.toOverlapPath.length_pos
  have hget : P.vertices[0] = P.tail := rfl
  simpa [vertexIndex, hget] using
    (List.get_idxOf P.nodup (⟨0, hlen⟩ : Fin P.vertices.length))

/-- Strict precedence in the original Hamiltonian path. -/
def StrictlyPrecedes (P : HamiltonianPath k) (u v : PermutationVertex k) : Prop :=
  P.vertexIndex u < P.vertexIndex v

theorem strictlyPrecedes_of_edge {P : HamiltonianPath k} {e : DirectedOverlapEdge k}
    (he : e ∈ P.edgeSet) : P.StrictlyPrecedes e.source e.target := by
  classical
  obtain ⟨i, rfl⟩ := HamiltonianPath.mem_edgeSet.mp he
  have hi : i.1 < P.vertices.length := by omega
  have his : i.1 + 1 < P.vertices.length := by omega
  have hidx := List.get_idxOf P.nodup (⟨i.1, hi⟩ : Fin P.vertices.length)
  have hidxs := List.get_idxOf P.nodup (⟨i.1 + 1, his⟩ : Fin P.vertices.length)
  change P.vertices.idxOf (P.vertices.get ⟨i.1, hi⟩) <
    P.vertices.idxOf (P.vertices.get ⟨i.1 + 1, his⟩)
  calc
    P.vertices.idxOf (P.vertices.get ⟨i.1, hi⟩) = i.1 := hidx
    _ < i.1 + 1 := by omega
    _ = P.vertices.idxOf (P.vertices.get ⟨i.1 + 1, his⟩) := hidxs.symm

end HamiltonianPath

/-- A rotation block, bundled with the proof that it is one of the blocks of `S_k`. -/
abbrev RotationBlock (k : ℕ) := {B : Finset (PermutationVertex k) // B ∈ rotationBlocks k}

private theorem rotationBlock_nonempty (hk : 1 ≤ k) (B : RotationBlock k) :
    B.1.Nonempty := by
  classical
  obtain ⟨v, _hv, hB⟩ := Finset.mem_image.mp B.2
  refine ⟨v, ?_⟩
  rw [← hB]
  exact self_mem_rotationClass hk v

/-- The earliest vertex of a rotation block in the Hamiltonian path. -/
noncomputable def firstVisitedInBlock (hk : 1 ≤ k) (P : HamiltonianPath k)
    (B : RotationBlock k) : PermutationVertex k :=
  Classical.choose
    (Finset.exists_min_image B.1 P.vertexIndex (rotationBlock_nonempty hk B))

theorem firstVisitedInBlock_mem (hk : 1 ≤ k) (P : HamiltonianPath k)
    (B : RotationBlock k) : firstVisitedInBlock hk P B ∈ B.1 :=
  (Classical.choose_spec
    (Finset.exists_min_image B.1 P.vertexIndex (rotationBlock_nonempty hk B))).1

theorem firstVisitedInBlock_earliest (hk : 1 ≤ k) (P : HamiltonianPath k)
    (B : RotationBlock k) {v : PermutationVertex k} (hv : v ∈ B.1) :
    P.vertexIndex (firstVisitedInBlock hk P B) ≤ P.vertexIndex v :=
  (Classical.choose_spec
    (Finset.exists_min_image B.1 P.vertexIndex (rotationBlock_nonempty hk B))).2 v hv

theorem firstVisitedInBlock_unique (hk : 1 ≤ k) (P : HamiltonianPath k)
    (B : RotationBlock k) {v : PermutationVertex k} (hv : v ∈ B.1)
    (hmin : ∀ u ∈ B.1, P.vertexIndex v ≤ P.vertexIndex u) :
    v = firstVisitedInBlock hk P B := by
  apply P.vertexIndex_injective
  apply Nat.le_antisymm
  · exact hmin _ (firstVisitedInBlock_mem hk P B)
  · exact firstVisitedInBlock_earliest hk P B hv

/-- A vertex is first in its class precisely when it is reached no later than every vertex
in that rotation class. -/
def IsFirstVisitedInClass (P : HamiltonianPath k) (v : PermutationVertex k) : Prop :=
  ∀ u ∈ rotationClass v, P.vertexIndex v ≤ P.vertexIndex u

/-- `F`, the set containing the genuinely earliest vertex of every rotation class. -/
noncomputable def firstVisitedVertices (hk : 1 ≤ k) (P : HamiltonianPath k) :
    Finset (PermutationVertex k) := by
  classical
  exact (Finset.univ : Finset (RotationBlock k)).image (firstVisitedInBlock hk P)

private theorem firstVisitedInBlock_injective (hk : 1 ≤ k) (P : HamiltonianPath k) :
    Function.Injective (firstVisitedInBlock hk P : RotationBlock k → PermutationVertex k) := by
  classical
  intro A B hAB
  apply Subtype.ext
  obtain ⟨a, _ha, hA⟩ := Finset.mem_image.mp A.2
  obtain ⟨b, _hb, hB⟩ := Finset.mem_image.mp B.2
  have hfirstA := firstVisitedInBlock_mem hk P A
  have hfirstB := firstVisitedInBlock_mem hk P B
  rw [← hA] at hfirstA
  rw [← hB] at hfirstB
  have hinter : (rotationClass a ∩ rotationClass b).Nonempty := by
    refine ⟨firstVisitedInBlock hk P A, Finset.mem_inter.mpr ⟨hfirstA, ?_⟩⟩
    simpa only [hAB] using hfirstB
  calc
    A.1 = rotationClass a := hA.symm
    _ = rotationClass b := rotationClasses_eq_of_intersect hk hinter
    _ = B.1 := hB

theorem mem_firstVisitedVertices_iff (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    v ∈ firstVisitedVertices hk P ↔ IsFirstVisitedInClass P v := by
  classical
  constructor
  · intro hv
    obtain ⟨B, _hB, hBv⟩ := Finset.mem_image.mp hv
    subst v
    intro u hu
    have hclass : rotationClass (firstVisitedInBlock hk P B) = B.1 := by
      obtain ⟨b, _hb, hB⟩ := Finset.mem_image.mp B.2
      have hmem := firstVisitedInBlock_mem hk P B
      rw [← hB] at hmem
      exact (rotationClass_eq_of_mem hk hmem).trans hB
    apply firstVisitedInBlock_earliest hk P B
    rwa [← hclass]
  · intro hv
    let B : RotationBlock k :=
      ⟨rotationClass v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
    have hrep : firstVisitedInBlock hk P B = v := by
      symm
      apply firstVisitedInBlock_unique hk P B
      · exact self_mem_rotationClass hk v
      · exact hv
    exact Finset.mem_image.mpr ⟨B, Finset.mem_univ B, hrep⟩

theorem firstVisitedVertices_card (hk : 1 ≤ k) (P : HamiltonianPath k) :
    (firstVisitedVertices hk P).card = (k - 1).factorial := by
  classical
  rw [firstVisitedVertices,
    Finset.card_image_of_injective _ (firstVisitedInBlock_injective hk P),
    Finset.card_univ, Fintype.card_coe]
  exact rotationBlocks_card hk

theorem existsUnique_firstVisited_in_rotationClass (hk : 1 ≤ k)
    (P : HamiltonianPath k) (v : PermutationVertex k) :
    ∃! f, f ∈ rotationClass v ∧ f ∈ firstVisitedVertices hk P := by
  classical
  let B : RotationBlock k :=
    ⟨rotationClass v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩
  refine ⟨firstVisitedInBlock hk P B, ?_, ?_⟩
  · exact ⟨firstVisitedInBlock_mem hk P B,
      Finset.mem_image.mpr ⟨B, Finset.mem_univ B, rfl⟩⟩
  · intro f hf
    apply P.vertexIndex_injective
    apply Nat.le_antisymm
    · exact (mem_firstVisitedVertices_iff hk P f).mp hf.2 _
        (by
          have hclass := rotationClass_eq_of_mem hk hf.1
          rw [hclass]
          exact firstVisitedInBlock_mem hk P B)
    · exact firstVisitedInBlock_earliest hk P B hf.1

/-- The first vertex of the rotation class containing `v`. -/
noncomputable def classFirstVertex (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) : PermutationVertex k :=
  firstVisitedInBlock hk P
    ⟨rotationClass v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩

theorem classFirstVertex_mem_class (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) : classFirstVertex hk P v ∈ rotationClass v :=
  by
    simpa [classFirstVertex] using firstVisitedInBlock_mem hk P
      (⟨rotationClass v,
        Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩ : RotationBlock k)

theorem classFirstVertex_mem_firstVisitedVertices (hk : 1 ≤ k)
    (P : HamiltonianPath k) (v : PermutationVertex k) :
    classFirstVertex hk P v ∈ firstVisitedVertices hk P := by
  classical
  exact Finset.mem_image.mpr
    ⟨⟨rotationClass v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩⟩,
      Finset.mem_univ _, rfl⟩

theorem classFirstVertex_earliest (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    P.vertexIndex (classFirstVertex hk P v) ≤ P.vertexIndex v :=
  firstVisitedInBlock_earliest hk P _ (self_mem_rotationClass hk v)

theorem classFirstVertex_class (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    rotationClass (classFirstVertex hk P v) = rotationClass v :=
  rotationClass_eq_of_mem hk (classFirstVertex_mem_class hk P v)

theorem classFirstVertex_eq_of_mem_firstVisitedVertices (hk : 1 ≤ k)
    (P : HamiltonianPath k) {v : PermutationVertex k}
    (hv : v ∈ firstVisitedVertices hk P) : classFirstVertex hk P v = v := by
  apply P.vertexIndex_injective
  apply Nat.le_antisymm
  · exact classFirstVertex_earliest hk P v
  · exact (mem_firstVisitedVertices_iff hk P v).mp hv _
      (classFirstVertex_mem_class hk P v)

/-- `F⁻ = {v : rotation v ∈ F}` exactly as in frozen Section 2. -/
noncomputable def firstVisitedPredecessors (hk : 1 ≤ k) (P : HamiltonianPath k) :
    Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun v => rotation v ∈ firstVisitedVertices hk P

@[simp]
theorem mem_firstVisitedPredecessors_iff (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    v ∈ firstVisitedPredecessors hk P ↔ rotation v ∈ firstVisitedVertices hk P := by
  classical
  simp [firstVisitedPredecessors]

theorem firstVisitedPredecessors_card (hk : 1 ≤ k) (P : HamiltonianPath k) :
    (firstVisitedPredecessors hk P).card = (k - 1).factorial := by
  classical
  let f : {v // v ∈ firstVisitedPredecessors hk P} ≃
      {v // v ∈ firstVisitedVertices hk P} :=
    { toFun := fun v => ⟨rotation v.1, (mem_firstVisitedPredecessors_iff hk P v.1).mp v.2⟩
      invFun := fun v => ⟨inverseRotation v.1, by
        apply (mem_firstVisitedPredecessors_iff hk P _).mpr
        simp [rotation_inverseRotation hk, v.2]⟩
      left_inv := fun v => by
        apply Subtype.ext
        exact inverseRotation_rotation hk v.1
      right_inv := fun v => by
        apply Subtype.ext
        exact rotation_inverseRotation hk v.1 }
  calc
    (firstVisitedPredecessors hk P).card =
        Fintype.card {v // v ∈ firstVisitedPredecessors hk P} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {v // v ∈ firstVisitedVertices hk P} := Fintype.card_congr f
    _ = (firstVisitedVertices hk P).card := Fintype.card_coe _
    _ = (k - 1).factorial := firstVisitedVertices_card hk P

theorem firstVisited_disjoint_predecessors (hk : 2 ≤ k) (P : HamiltonianPath k) :
    Disjoint (firstVisitedVertices (by omega) P)
      (firstVisitedPredecessors (by omega) P) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvF hvFm
  have hrotF := (mem_firstVisitedPredecessors_iff (by omega) P v).mp hvFm
  have hunique := existsUnique_firstVisited_in_rotationClass (by omega) P v
  have hvclass : v ∈ rotationClass v := self_mem_rotationClass (by omega) v
  have hrotclass : rotation v ∈ rotationClass v := by
    simpa [rotationPower, Function.iterate_one] using
      (rotationPower_mem_rotationClass (by omega) 1 v)
  have heq : v = rotation v := hunique.unique ⟨hvclass, hvF⟩ ⟨hrotclass, hrotF⟩
  exact rotation_ne_self hk v heq.symm

/-- The last vertex of the complete block containing `v`, measured from that block's first
visited entry. -/
noncomputable def classLastVertex (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) : PermutationVertex k :=
  blockExit (classFirstVertex hk P v)

theorem classLastVertex_mem_predecessors (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    classLastVertex hk P v ∈ firstVisitedPredecessors hk P := by
  apply (mem_firstVisitedPredecessors_iff hk P _).mpr
  rw [classLastVertex, rotation_blockExit hk]
  exact classFirstVertex_mem_firstVisitedVertices hk P v

theorem classLastVertex_class (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    rotationClass (classLastVertex hk P v) = rotationClass v := by
  rw [classLastVertex]
  calc
    rotationClass (blockExit (classFirstVertex hk P v)) =
        rotationClass (classFirstVertex hk P v) := by
      apply rotationClass_eq_of_mem hk
      rw [← rotationPower_pred_eq_blockExit hk]
      exact rotationPower_mem_rotationClass hk _ _
    _ = rotationClass v := classFirstVertex_class hk P v

theorem mem_predecessors_in_class_iff_eq_last (hk : 2 ≤ k) (P : HamiltonianPath k)
    {u v : PermutationVertex k} (hu : u ∈ rotationClass v) :
    u ∈ firstVisitedPredecessors (by omega) P ↔
      u = classLastVertex (by omega) P v := by
  classical
  constructor
  · intro huMinus
    have hrotF := (mem_firstVisitedPredecessors_iff (by omega) P u).mp huMinus
    have hrotClass : rotation u ∈ rotationClass v := by
      have huClass : rotationClass u = rotationClass v :=
        rotationClass_eq_of_mem (by omega) hu
      rw [← huClass]
      simpa [rotationPower, Function.iterate_one] using
        (rotationPower_mem_rotationClass (by omega) 1 u)
    have hfirst : rotation u = classFirstVertex (by omega) P v := by
      have hrepF := classFirstVertex_mem_firstVisitedVertices (by omega) P v
      exact (existsUnique_firstVisited_in_rotationClass (by omega) P v).unique
        ⟨hrotClass, hrotF⟩
        ⟨classFirstVertex_mem_class (by omega) P v, hrepF⟩
    calc
      u = inverseRotation (rotation u) := (inverseRotation_rotation (by omega) u).symm
      _ = inverseRotation (classFirstVertex (by omega) P v) := congrArg inverseRotation hfirst
      _ = classLastVertex (by omega) P v := rfl
  · rintro rfl
    exact classLastVertex_mem_predecessors (by omega) P v

theorem classFirst_strictlyPrecedes_classLast (hk : 2 ≤ k)
    (P : HamiltonianPath k) (v : PermutationVertex k) :
    P.StrictlyPrecedes (classFirstVertex (by omega) P v)
      (classLastVertex (by omega) P v) := by
  have hle : P.vertexIndex (classFirstVertex (by omega) P v) ≤
      P.vertexIndex (classLastVertex (by omega) P v) :=
    (mem_firstVisitedVertices_iff (by omega) P
      (classFirstVertex (by omega) P v)).mp
      (classFirstVertex_mem_firstVisitedVertices (by omega) P v) _
      (by
        rw [classFirstVertex_class (by omega) P v,
          ← classLastVertex_class (by omega) P v]
        exact self_mem_rotationClass (by omega) (classLastVertex (by omega) P v))
  have hne : classFirstVertex (by omega) P v ≠ classLastVertex (by omega) P v := by
    intro h
    apply rotation_ne_self hk (classFirstVertex (by omega) P v)
    calc
      rotation (classFirstVertex (by omega) P v) =
          rotation (classLastVertex (by omega) P v) := congrArg rotation h
      _ = classFirstVertex (by omega) P v := by
        rw [classLastVertex, rotation_blockExit (by omega)]
  have hindexNe := fun hidx => hne (P.vertexIndex_injective hidx)
  exact lt_of_le_of_ne hle hindexNe

/-- `Res(P)` with exactly the two conditions in frozen Section 2. -/
noncomputable def residualVertices (hk : 2 ≤ k) (P : HamiltonianPath k) :
    Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∉ firstVisitedPredecessors (by omega) P ∧ rotationEdge hk v ∉ P.edgeSet

@[simp]
theorem mem_residualVertices_iff (hk : 2 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    v ∈ residualVertices hk P ↔
      v ∉ firstVisitedPredecessors (by omega) P ∧ rotationEdge hk v ∉ P.edgeSet := by
  classical
  simp [residualVertices]

/-- Every rotation edge selected by `Res(P)` satisfies Definition 2.1's precondition. -/
theorem residualVertices_rotationEdgesAdmissible (hk : 3 ≤ k) (P : HamiltonianPath k) :
    RotationEdgesAdmissible (by omega) P (residualVertices (by omega) P) := by
  intro v hv
  exact (mem_residualVertices_iff (by omega) P v).mp hv |>.2

/-- `F(P)`, the specialization of the accepted simultaneous transformation. -/
noncomputable def pathForest (hk : 3 ≤ k) (P : HamiltonianPath k) :
    FiniteDirectedSubgraph k :=
  forestTransform (by omega) P (residualVertices (by omega) P)

theorem pathForest_eq_forestTransform (hk : 3 ≤ k) (P : HamiltonianPath k) :
    pathForest hk P =
      forestTransform (by omega) P (residualVertices (by omega) P) := rfl

private theorem mem_forestStepOne_specialized_iff (hk : 3 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k} :
    e ∈ forestStepOne (by omega) P (residualVertices (by omega) P) ↔
      (e ∈ P.edgeSet ∧ e.source ∉ residualVertices (by omega) P) ∨
        e ∈ rotationEdges (by omega) (residualVertices (by omega) P) := by
  classical
  simp only [forestStepOne, forestStepZero, forestDeltaOne, Finset.mem_union,
    Finset.mem_sdiff, mem_outgoingEdges]
  tauto

private theorem pathForest_subset_stepOne (hk : 3 ≤ k) (P : HamiltonianPath k) :
    pathForest hk P ⊆ forestStepOne (by omega) P (residualVertices (by omega) P) := by
  intro e he
  exact (Finset.mem_sdiff.mp he).1

/-- Structure theorem (i), membership core: every vertex outside `F⁻` carries its rotation
edge in `F(P)`, whether that edge was already in `P` or was installed by Step 1. -/
theorem pathForest_rotationEdge_mem_of_not_predecessor (hk : 3 ≤ k)
    (P : HamiltonianPath k) {v : PermutationVertex k}
    (hv : v ∉ firstVisitedPredecessors (by omega) P) :
    rotationEdge (by omega) v ∈ pathForest hk P := by
  classical
  by_cases hP : rotationEdge (by omega) v ∈ P.edgeSet
  · have hvNotRes : v ∉ residualVertices (by omega) P := by
      intro hvRes
      exact (mem_residualVertices_iff (by omega) P v).mp hvRes |>.2 hP
    have hstepOne : rotationEdge (by omega) v ∈
        forestStepOne (by omega) P (residualVertices (by omega) P) :=
      mem_forestStepOne_specialized_iff hk P |>.mpr (Or.inl ⟨hP, hvNotRes⟩)
    apply Finset.mem_sdiff.mpr
    refine ⟨hstepOne, ?_⟩
    intro hremoved
    have hdouble := (mem_incomingEdges.mp hremoved).2
    change rotation v ∈
      doubleIncomingVertices (by omega) P (residualVertices (by omega) P) at hdouble
    have hdegree : inDegree
        (forestStepOne (by omega) P (residualVertices (by omega) P)) (rotation v) = 2 := by
      simpa [doubleIncomingVertices] using hdouble
    have hcardLe : inDegree
        (forestStepOne (by omega) P (residualVertices (by omega) P)) (rotation v) ≤ 1 := by
      rw [inDegree, Finset.card_le_one]
      intro e he f hf
      have heTarget := (mem_incomingEdgesAt.mp he).2
      have hfTarget := (mem_incomingEdgesAt.mp hf).2
      rcases (mem_forestStepOne_specialized_iff hk P).mp
          (mem_incomingEdgesAt.mp he).1 with heOrig | heRot
      · rcases (mem_forestStepOne_specialized_iff hk P).mp
            (mem_incomingEdgesAt.mp hf).1 with hfOrig | hfRot
        · have hle := P.edgeSet_inDegree_rule (rotation v)
          rw [inDegree, Finset.card_le_one] at hle
          exact hle e (mem_incomingEdgesAt.mpr ⟨heOrig.1, heTarget⟩)
            f (mem_incomingEdgesAt.mpr ⟨hfOrig.1, hfTarget⟩)
        · obtain ⟨z, hzRes, hzf⟩ := mem_rotationEdges.mp hfRot
          have hzv : z = v := rotation_injective (by omega) (by
            calc
              rotation z = f.target := by rw [← hzf]; rfl
              _ = rotation v := hfTarget)
          exact (hvNotRes (hzv ▸ hzRes)).elim
      · obtain ⟨z, hzRes, hze⟩ := mem_rotationEdges.mp heRot
        have hzv : z = v := rotation_injective (by omega) (by
          calc
            rotation z = e.target := by rw [← hze]; rfl
            _ = rotation v := heTarget)
        exact (hvNotRes (hzv ▸ hzRes)).elim
    omega
  · have hvRes : v ∈ residualVertices (by omega) P :=
      (mem_residualVertices_iff (by omega) P v).mpr ⟨hv, hP⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · exact (mem_forestStepOne_specialized_iff hk P).mpr
        (Or.inr (mem_rotationEdges.mpr ⟨v, hvRes, rfl⟩))
    · intro hremoved
      exact hP (mem_incomingEdges.mp hremoved).1

/-- Structure theorem (i), exact outgoing singleton. -/
theorem pathForest_outgoing_of_not_predecessor (hk : 3 ≤ k)
    (P : HamiltonianPath k) {v : PermutationVertex k}
    (hv : v ∉ firstVisitedPredecessors (by omega) P) :
    outgoingEdgesAt (pathForest hk P) v = {rotationEdge (by omega) v} := by
  classical
  have hrot : rotationEdge (by omega) v ∈ outgoingEdgesAt (pathForest hk P) v :=
    mem_outgoingEdgesAt.mpr
      ⟨pathForest_rotationEdge_mem_of_not_predecessor hk P hv, rfl⟩
  have hle := forestTransform_outDegree_rule hk P (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible hk P) v
  rw [outDegree, Finset.card_le_one] at hle
  ext e
  constructor
  · intro he
    have heq := hle e he (rotationEdge (by omega) v) hrot
    simp [heq]
  · intro he
    have heq : e = rotationEdge (by omega) v := Finset.mem_singleton.mp he
    subst e
    exact hrot

/-- Structure theorem (i), exact incoming singleton. -/
theorem pathForest_incoming_of_not_first (hk : 3 ≤ k)
    (P : HamiltonianPath k) {v : PermutationVertex k}
    (hv : v ∉ firstVisitedVertices (by omega) P) :
    incomingEdgesAt (pathForest hk P) v =
      {rotationEdge (by omega) (inverseRotation v)} := by
  classical
  have hpredNot : inverseRotation v ∉ firstVisitedPredecessors (by omega) P := by
    intro hpred
    have := (mem_firstVisitedPredecessors_iff (by omega) P (inverseRotation v)).mp hpred
    rw [rotation_inverseRotation (by omega)] at this
    exact hv this
  have hedge : rotationEdge (by omega) (inverseRotation v) ∈ pathForest hk P :=
    pathForest_rotationEdge_mem_of_not_predecessor hk P hpredNot
  have htarget : (rotationEdge (by omega) (inverseRotation v)).target = v := by
    exact rotation_inverseRotation (by omega) v
  have hin : rotationEdge (by omega) (inverseRotation v) ∈
      incomingEdgesAt (pathForest hk P) v :=
    mem_incomingEdgesAt.mpr ⟨hedge, htarget⟩
  have hle := forestTransform_inDegree_rule hk P (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible hk P) v
  rw [inDegree, Finset.card_le_one] at hle
  ext e
  constructor
  · intro he
    have heq := hle e he (rotationEdge (by omega) (inverseRotation v)) hin
    simp [heq]
  · intro he
    have heq : e = rotationEdge (by omega) (inverseRotation v) :=
      Finset.mem_singleton.mp he
    subst e
    exact hin

/-- Structure theorem (i), the complete internal weight-one path from a block's first vertex
to its `F⁻` vertex. -/
theorem pathForest_complete_internal_rotation_path (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f : PermutationVertex k}
    (hf : f ∈ firstVisitedVertices (by omega) P)
    (i : ℕ) (hi : i < k - 1) :
    rotationEdge (by omega) (rotationPower i f) ∈ pathForest hk P := by
  have hsourceClass : rotationPower i f ∈ rotationClass f :=
    rotationPower_mem_rotationClass (by omega) i f
  have hnotMinus : rotationPower i f ∉ firstVisitedPredecessors (by omega) P := by
    intro hminus
    have heq := (mem_predecessors_in_class_iff_eq_last (by omega) P hsourceClass).mp hminus
    have hfirst : classFirstVertex (by omega) P f = f :=
      classFirstVertex_eq_of_mem_firstVisitedVertices (by omega) P hf
    rw [classLastVertex, hfirst, ← rotationPower_pred_eq_blockExit (by omega)] at heq
    have hinj := rotationPower_injective_on_range (by omega) f
      (by omega : i < k) (by omega : k - 1 < k) heq
    omega
  exact pathForest_rotationEdge_mem_of_not_predecessor hk P hnotMinus

/-- Structure theorem (ii), edgewise form: every surviving edge from an `F⁻` vertex is an
original path edge whose target lies in `F`. -/
theorem pathForest_edge_from_predecessor (hk : 3 ≤ k) (P : HamiltonianPath k)
    {e : DirectedOverlapEdge k} (he : e ∈ pathForest hk P)
    (hsource : e.source ∈ firstVisitedPredecessors (by omega) P) :
    e ∈ P.edgeSet ∧ e.target ∈ firstVisitedVertices (by omega) P := by
  classical
  have heStepOne := pathForest_subset_stepOne hk P he
  have hsourceNotRes : e.source ∉ residualVertices (by omega) P := by
    intro hres
    exact (mem_residualVertices_iff (by omega) P e.source).mp hres |>.1 hsource
  have heP : e ∈ P.edgeSet := by
    rcases (mem_forestStepOne_specialized_iff hk P).mp heStepOne with hOrig | hRot
    · exact hOrig.1
    · obtain ⟨z, hzRes, hze⟩ := mem_rotationEdges.mp hRot
      have hzSource : z = e.source := by
        calc
          z = (rotationEdge (by omega) z).source := rfl
          _ = e.source := congrArg DirectedOverlapEdge.source hze
      exact (hsourceNotRes (hzSource ▸ hzRes)).elim
  refine ⟨heP, ?_⟩
  by_contra htarget
  have hinEq := pathForest_incoming_of_not_first hk P htarget
  have heIncoming : e ∈ incomingEdgesAt (pathForest hk P) e.target :=
    mem_incomingEdgesAt.mpr ⟨he, rfl⟩
  rw [hinEq] at heIncoming
  have heq : e = rotationEdge (by omega) (inverseRotation e.target) :=
    Finset.mem_singleton.mp heIncoming
  have htargetEq : e.target = rotation e.source := by
    calc
      e.target = rotation (inverseRotation e.target) :=
        (rotation_inverseRotation (by omega) e.target).symm
      _ = rotation e.source := by
        have hs := congrArg DirectedOverlapEdge.source heq
        have hs' : e.source = inverseRotation e.target := by
          calc
            e.source = (rotationEdge (by omega) (inverseRotation e.target)).source := hs
            _ = inverseRotation e.target := rfl
        exact congrArg rotation hs'.symm
  have hrotFirst := (mem_firstVisitedPredecessors_iff (by omega) P e.source).mp hsource
  exact htarget (htargetEq ▸ hrotFirst)

/-- Structure theorem (ii), exact outgoing-set form. -/
theorem pathForest_outgoing_of_predecessor (hk : 3 ≤ k)
    (P : HamiltonianPath k) {u : PermutationVertex k}
    (hu : u ∈ firstVisitedPredecessors (by omega) P)
    (hnonempty : (outgoingEdgesAt (pathForest hk P) u).Nonempty) :
    ∃ e : DirectedOverlapEdge k,
      e ∈ P.edgeSet ∧ e.source = u ∧
      e.target ∈ firstVisitedVertices (by omega) P ∧
      outgoingEdgesAt (pathForest hk P) u = {e} := by
  classical
  obtain ⟨e, heOut⟩ := hnonempty
  have he := (mem_outgoingEdgesAt.mp heOut).1
  have hsource := (mem_outgoingEdgesAt.mp heOut).2
  have hinfo := pathForest_edge_from_predecessor hk P he (hsource ▸ hu)
  refine ⟨e, hinfo.1, hsource, hinfo.2, ?_⟩
  have hle := forestTransform_outDegree_rule hk P (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible hk P) u
  rw [outDegree, Finset.card_le_one] at hle
  ext f
  constructor
  · intro hf
    exact Finset.mem_singleton.mpr (hle f hf e heOut)
  · intro hf
    rw [Finset.mem_singleton] at hf
    simpa [hf] using heOut

/-- A genuine directed adjacency in a finite directed subgraph. -/
def HasDirectedEdge (X : FiniteDirectedSubgraph k)
    (u v : PermutationVertex k) : Prop :=
  ∃ e ∈ X, e.source = u ∧ e.target = v

/-- A genuine directed walk: a nonempty vertex list whose consecutive pairs are edges of
the graph. Vertices may repeat, as they may in an ordinary walk. -/
def IsDirectedWalk (X : FiniteDirectedSubgraph k)
    (walk : List (PermutationVertex k)) : Prop :=
  walk ≠ [] ∧ walk.IsChain (HasDirectedEdge X)

/-- Genuine strict precedence of two occurrences in a list. -/
def StrictlyPrecedesInList (walk : List (PermutationVertex k))
    (u v : PermutationVertex k) : Prop :=
  ∃ i j, ∃ hi : i < walk.length, ∃ hj : j < walk.length,
    i < j ∧ walk[i] = u ∧ walk[j] = v

private theorem isChain_rel_getElem {α : Type*} {R : α → α → Prop}
    {l : List α} (hchain : l.IsChain R) (i : ℕ) (hi : i + 1 < l.length) :
    R l[i] l[i + 1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
      rcases l with _ | ⟨b, rest⟩
      · simp at hi
      · cases i with
        | zero =>
          simpa using hchain.rel
        | succ j =>
          have hj : j + 1 < (b :: rest).length := by simp at hi ⊢; omega
          have htail : (b :: rest).IsChain R := hchain.tail
          have hrec := ih htail j hj
          simpa only [List.getElem_cons_succ] using hrec

private theorem isChain_trans_rel_getElem_le {α : Type*} {E R : α → α → Prop}
    (hrefl : ∀ x, R x x) (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hedge : ∀ {x y}, E x y → R x y)
    {l : List α} (hchain : l.IsChain E)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    R l[i] l[j] := by
  induction j using Nat.strong_induction_on generalizing i with
  | h j ih =>
      by_cases heq : i = j
      · subst i
        exact hrefl _
      · have hij' : i < j := lt_of_le_of_ne hij heq
        have hjpos : 0 < j := by omega
        let q := j - 1
        have hqj : q + 1 = j := by dsimp [q]; omega
        have hq : q < l.length := by omega
        have hiq : i ≤ q := by omega
        have hleft : R l[i] l[q] := ih q (by omega) hi hq hiq
        have hright : R l[q] l[j] := by
          have hadj := isChain_rel_getElem hchain q (by simpa [hqj] using hj)
          simpa [hqj] using hedge hadj
        exact htrans hleft hright

private theorem classFirstVertex_eq_of_same_class (hk : 1 ≤ k)
    (P : HamiltonianPath k) {u v : PermutationVertex k}
    (hclass : rotationClass u = rotationClass v) :
    classFirstVertex hk P u = classFirstVertex hk P v := by
  have hmemU : classFirstVertex hk P u ∈ rotationClass v := by
    rw [← hclass]
    exact classFirstVertex_mem_class hk P u
  exact (existsUnique_firstVisited_in_rotationClass hk P v).unique
    ⟨hmemU, classFirstVertex_mem_firstVisitedVertices hk P u⟩
    ⟨classFirstVertex_mem_class hk P v,
      classFirstVertex_mem_firstVisitedVertices hk P v⟩

private theorem classFirstVertex_idem (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    classFirstVertex hk P (classFirstVertex hk P v) = classFirstVertex hk P v :=
  classFirstVertex_eq_of_same_class hk P (classFirstVertex_class hk P v)

private theorem classLastVertex_eq_of_same_class (hk : 1 ≤ k)
    (P : HamiltonianPath k) {u v : PermutationVertex k}
    (hclass : rotationClass u = rotationClass v) :
    classLastVertex hk P u = classLastVertex hk P v := by
  simp only [classLastVertex]
  rw [classFirstVertex_eq_of_same_class hk P hclass]

private theorem classLastVertex_idem (hk : 1 ≤ k) (P : HamiltonianPath k)
    (v : PermutationVertex k) :
    classLastVertex hk P (classLastVertex hk P v) = classLastVertex hk P v :=
  classLastVertex_eq_of_same_class hk P (classLastVertex_class hk P v)

/-- Every forest edge either stays inside one rotation class or is an original path edge
from the last vertex of one class to the first vertex of a different class. -/
theorem pathForest_edge_classification (hk : 3 ≤ k) (P : HamiltonianPath k)
    {e : DirectedOverlapEdge k} (he : e ∈ pathForest hk P) :
    rotationClass e.source = rotationClass e.target ∨
      (e.source = classLastVertex (by omega) P e.source ∧
       e.target = classFirstVertex (by omega) P e.target ∧
       rotationClass e.source ≠ rotationClass e.target ∧
       e ∈ P.edgeSet ∧ P.StrictlyPrecedes e.source e.target) := by
  classical
  by_cases hsource : e.source ∈ firstVisitedPredecessors (by omega) P
  · right
    have hinfo := pathForest_edge_from_predecessor hk P he hsource
    have hlast := (mem_predecessors_in_class_iff_eq_last (by omega) P
      (self_mem_rotationClass (by omega) e.source)).mp hsource
    have hfirst := classFirstVertex_eq_of_mem_firstVisitedVertices (by omega) P hinfo.2
    have hclasses : rotationClass e.source ≠ rotationClass e.target := by
      intro hsame
      have hfirstSame := classFirstVertex_eq_of_same_class (by omega) P hsame
      have hsourceFirst : P.vertexIndex (classFirstVertex (by omega) P e.source) ≤
          P.vertexIndex e.source := classFirstVertex_earliest (by omega) P e.source
      have htargetFirst : classFirstVertex (by omega) P e.target = e.target := hfirst
      have hedgeOrder := HamiltonianPath.strictlyPrecedes_of_edge hinfo.1
      rw [hfirstSame, htargetFirst] at hsourceFirst
      exact (Nat.not_lt_of_ge hsourceFirst) hedgeOrder
    exact ⟨hlast, hfirst.symm, hclasses, hinfo.1,
      HamiltonianPath.strictlyPrecedes_of_edge hinfo.1⟩
  · left
    have hout := pathForest_outgoing_of_not_predecessor hk P hsource
    have heOut : e ∈ outgoingEdgesAt (pathForest hk P) e.source :=
      mem_outgoingEdgesAt.mpr ⟨he, rfl⟩
    rw [hout] at heOut
    have heq : e = rotationEdge (by omega) e.source := Finset.mem_singleton.mp heOut
    have htarget : e.target = rotation e.source := by
      have ht := congrArg DirectedOverlapEdge.target heq
      calc
        e.target = (rotationEdge (by omega) e.source).target := ht
        _ = rotation e.source := rfl
    rw [htarget]
    have hmem : rotation e.source ∈ rotationClass e.source := by
      simpa [rotationPower, Function.iterate_one] using
        (rotationPower_mem_rotationClass (by omega) 1 e.source)
    exact (rotationClass_eq_of_mem (by omega) hmem).symm

private def ClassesOrdered (hk : 1 ≤ k) (P : HamiltonianPath k)
    (u v : PermutationVertex k) : Prop :=
  classFirstVertex hk P u = classFirstVertex hk P v ∨
    P.StrictlyPrecedes (classLastVertex hk P u) (classFirstVertex hk P v)

private theorem classesOrdered_refl (hk : 1 ≤ k) (P : HamiltonianPath k)
    (u : PermutationVertex k) : ClassesOrdered hk P u u := Or.inl rfl

private theorem classesOrdered_trans (hk : 2 ≤ k) (P : HamiltonianPath k)
    {u v x : PermutationVertex k} :
    ClassesOrdered (by omega) P u v → ClassesOrdered (by omega) P v x →
      ClassesOrdered (by omega) P u x := by
  rintro (huv | huv) (hvx | hvx)
  · exact Or.inl (huv.trans hvx)
  · right
    have hlast : classLastVertex (by omega) P u = classLastVertex (by omega) P v := by
      simp only [classLastVertex]
      rw [huv]
    rwa [hlast]
  · right
    rwa [← hvx]
  · right
    have hmiddle := classFirst_strictlyPrecedes_classLast hk P v
    exact lt_trans huv (lt_trans hmiddle hvx)

private theorem pathForest_edge_classesOrdered (hk : 3 ≤ k) (P : HamiltonianPath k)
    {u v : PermutationVertex k} (hedge : HasDirectedEdge (pathForest hk P) u v) :
    ClassesOrdered (by omega) P u v := by
  obtain ⟨e, he, hsource, htarget⟩ := hedge
  have hclass := pathForest_edge_classification hk P he
  rcases hclass with hsame | hbridge
  · left
    exact classFirstVertex_eq_of_same_class (by omega) P (by simpa [hsource, htarget] using hsame)
  · right
    have hlast : classLastVertex (by omega) P u = e.source := by
      calc
        classLastVertex (by omega) P u = classLastVertex (by omega) P e.source :=
          congrArg (classLastVertex (by omega) P) hsource.symm
        _ = e.source := hbridge.1.symm
    have hfirst : classFirstVertex (by omega) P v = e.target := by
      calc
        classFirstVertex (by omega) P v = classFirstVertex (by omega) P e.target :=
          congrArg (classFirstVertex (by omega) P) htarget.symm
        _ = e.target := hbridge.2.1.symm
    change P.vertexIndex (classLastVertex (by omega) P u) <
      P.vertexIndex (classFirstVertex (by omega) P v)
    rw [hlast, hfirst]
    exact hbridge.2.2.2.2

private theorem classesOrdered_strict_of_strict_left (hk : 2 ≤ k)
    (P : HamiltonianPath k) {u v x : PermutationVertex k}
    (huv : P.StrictlyPrecedes (classLastVertex (by omega) P u)
      (classFirstVertex (by omega) P v))
    (hvx : ClassesOrdered (by omega) P v x) :
    P.StrictlyPrecedes (classLastVertex (by omega) P u)
      (classFirstVertex (by omega) P x) := by
  rcases hvx with hvx | hvx
  · rwa [← hvx]
  · exact lt_trans huv (lt_trans (classFirst_strictlyPrecedes_classLast hk P v) hvx)

private theorem classesOrdered_strict_of_strict_right (hk : 2 ≤ k)
    (P : HamiltonianPath k) {u v x : PermutationVertex k}
    (huv : ClassesOrdered (by omega) P u v)
    (hvx : P.StrictlyPrecedes (classLastVertex (by omega) P v)
      (classFirstVertex (by omega) P x)) :
    P.StrictlyPrecedes (classLastVertex (by omega) P u)
      (classFirstVertex (by omega) P x) := by
  rcases huv with huv | huv
  · have hlast : classLastVertex (by omega) P u = classLastVertex (by omega) P v := by
      simp only [classLastVertex]
      rw [huv]
    rwa [hlast]
  · exact lt_trans huv (lt_trans (classFirst_strictlyPrecedes_classLast hk P v) hvx)

private theorem no_strict_class_order_of_same_first (hk : 2 ≤ k)
    (P : HamiltonianPath k) {u v : PermutationVertex k}
    (hsame : classFirstVertex (by omega) P u = classFirstVertex (by omega) P v) :
    ¬P.StrictlyPrecedes (classLastVertex (by omega) P u)
      (classFirstVertex (by omega) P v) := by
  intro hstrict
  have hinside := classFirst_strictlyPrecedes_classLast hk P u
  rw [hsame] at hinside
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hinside)) hstrict

private theorem pathForest_edge_to_first_is_strict (hk : 3 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k}
    (he : e ∈ pathForest hk P)
    (htarget : e.target ∈ firstVisitedVertices (by omega) P) :
    P.StrictlyPrecedes (classLastVertex (by omega) P e.source)
      (classFirstVertex (by omega) P e.target) := by
  have hclass := pathForest_edge_classification hk P he
  rcases hclass with hsame | hbridge
  · have hsourceNot : e.source ∉ firstVisitedPredecessors (by omega) P := by
      intro hsource
      have hinfo := pathForest_edge_from_predecessor hk P he hsource
      have hfirstSource := classFirstVertex_eq_of_same_class (by omega) P hsame
      have htargetFirst := classFirstVertex_eq_of_mem_firstVisitedVertices
        (by omega) P htarget
      have hedgeOrder := HamiltonianPath.strictlyPrecedes_of_edge hinfo.1
      have hfirstLe := classFirstVertex_earliest (by omega) P e.source
      rw [hfirstSource, htargetFirst] at hfirstLe
      exact (Nat.not_lt_of_ge hfirstLe) hedgeOrder
    have hout := pathForest_outgoing_of_not_predecessor hk P hsourceNot
    have heOut : e ∈ outgoingEdgesAt (pathForest hk P) e.source :=
      mem_outgoingEdgesAt.mpr ⟨he, rfl⟩
    rw [hout] at heOut
    have heq : e = rotationEdge (by omega) e.source := Finset.mem_singleton.mp heOut
    have hrot : rotation e.source = e.target := by
      calc
        rotation e.source = (rotationEdge (by omega) e.source).target := rfl
        _ = e.target := congrArg DirectedOverlapEdge.target heq.symm
    have hsourceMinus : e.source ∈ firstVisitedPredecessors (by omega) P :=
      (mem_firstVisitedPredecessors_iff (by omega) P e.source).mpr (hrot ▸ htarget)
    exact (hsourceNot hsourceMinus).elim
  · change P.vertexIndex (classLastVertex (by omega) P e.source) <
      P.vertexIndex (classFirstVertex (by omega) P e.target)
    calc
      P.vertexIndex (classLastVertex (by omega) P e.source) =
          P.vertexIndex e.source := congrArg P.vertexIndex hbridge.1.symm
      _ < P.vertexIndex e.target := hbridge.2.2.2.2
      _ = P.vertexIndex (classFirstVertex (by omega) P e.target) :=
        congrArg P.vertexIndex hbridge.2.1

/-- Structure theorem (iii): along a genuine directed walk, genuine precedence between two
`F ∪ F⁻` occurrences implies strict precedence in the original Hamiltonian path. -/
theorem pathForest_walk_special_precedes_in_path (hk : 3 ≤ k)
    (P : HamiltonianPath k) {walk : List (PermutationVertex k)}
    (hwalk : IsDirectedWalk (pathForest hk P) walk)
    {u v : PermutationVertex k}
    (hu : u ∈ firstVisitedVertices (by omega) P ∪
      firstVisitedPredecessors (by omega) P)
    (hv : v ∈ firstVisitedVertices (by omega) P ∪
      firstVisitedPredecessors (by omega) P)
    (hprecede : StrictlyPrecedesInList walk u v) :
    P.StrictlyPrecedes u v := by
  classical
  obtain ⟨i, j, hi, hj, hij, hiu, hjv⟩ := hprecede
  have hordered : ClassesOrdered (by omega) P walk[i] walk[j] :=
    isChain_trans_rel_getElem_le
      (classesOrdered_refl (by omega) P)
      (classesOrdered_trans (by omega) P)
      (pathForest_edge_classesOrdered hk P) hwalk.2 hi hj (Nat.le_of_lt hij)
  rw [hiu, hjv] at hordered
  rcases hordered with hsame | hstrict
  · have hnextRel : HasDirectedEdge (pathForest hk P) walk[i] walk[i + 1] :=
      isChain_rel_getElem hwalk.2 i (by omega)
    have htailOrdered : ClassesOrdered (by omega) P walk[i + 1] walk[j] :=
      isChain_trans_rel_getElem_le
        (classesOrdered_refl (by omega) P)
        (classesOrdered_trans (by omega) P)
        (pathForest_edge_classesOrdered hk P) hwalk.2 (by omega) hj (by omega)
    have huNotMinus : u ∉ firstVisitedPredecessors (by omega) P := by
      intro huMinus
      obtain ⟨e, he, hes, het⟩ := hnextRel
      have hbridge := pathForest_edge_classification hk P he
      have hstrictFirst : P.StrictlyPrecedes
          (classLastVertex (by omega) P u)
          (classFirstVertex (by omega) P walk[i + 1]) := by
        have hinfo := pathForest_edge_from_predecessor hk P he (by simpa [hes, hiu] using huMinus)
        have hlast := (mem_predecessors_in_class_iff_eq_last (by omega) P
          (self_mem_rotationClass (by omega) u)).mp huMinus
        have hfirst := classFirstVertex_eq_of_mem_firstVisitedVertices (by omega) P hinfo.2
        have horder := HamiltonianPath.strictlyPrecedes_of_edge hinfo.1
        have hesu : e.source = u := hes.trans hiu
        calc
          P.vertexIndex (classLastVertex (by omega) P u) = P.vertexIndex u :=
            congrArg P.vertexIndex hlast.symm
          _ = P.vertexIndex e.source := congrArg P.vertexIndex hesu.symm
          _ < P.vertexIndex e.target := horder
          _ = P.vertexIndex (classFirstVertex (by omega) P e.target) :=
            congrArg P.vertexIndex hfirst.symm
          _ = P.vertexIndex (classFirstVertex (by omega) P walk[i + 1]) :=
            congrArg (fun x => P.vertexIndex (classFirstVertex (by omega) P x)) het
      have hstrictUV := classesOrdered_strict_of_strict_left (by omega) P
        hstrictFirst (by simpa [hiu, hjv] using htailOrdered)
      exact (no_strict_class_order_of_same_first (by omega) P hsame) hstrictUV
    have huFirst : u ∈ firstVisitedVertices (by omega) P := by
      rcases Finset.mem_union.mp hu with huF | huM
      · exact huF
      · exact (huNotMinus huM).elim
    have hprevRel : HasDirectedEdge (pathForest hk P) walk[j - 1] walk[j] := by
      have := isChain_rel_getElem hwalk.2 (j - 1) (by omega)
      simpa [show j - 1 + 1 = j by omega] using this
    have hprefixOrdered : ClassesOrdered (by omega) P walk[i] walk[j - 1] :=
      isChain_trans_rel_getElem_le
        (classesOrdered_refl (by omega) P)
        (classesOrdered_trans (by omega) P)
        (pathForest_edge_classesOrdered hk P) hwalk.2 hi (by omega) (by omega)
    have hvNotFirst : v ∉ firstVisitedVertices (by omega) P := by
      intro hvFirst
      obtain ⟨e, he, hes, het⟩ := hprevRel
      have hstrictLast := pathForest_edge_to_first_is_strict hk P he (by simpa [het, hjv] using hvFirst)
      have hstrictUV := classesOrdered_strict_of_strict_right (by omega) P
        (by simpa [hiu, hes] using hprefixOrdered)
        (by simpa [hes, het, hjv] using hstrictLast)
      exact (no_strict_class_order_of_same_first (by omega) P hsame) hstrictUV
    have hvMinus : v ∈ firstVisitedPredecessors (by omega) P := by
      rcases Finset.mem_union.mp hv with hvF | hvM
      · exact (hvNotFirst hvF).elim
      · exact hvM
    have huEq : classFirstVertex (by omega) P u = u :=
      classFirstVertex_eq_of_mem_firstVisitedVertices (by omega) P huFirst
    have hvEq : v = classLastVertex (by omega) P v :=
      (mem_predecessors_in_class_iff_eq_last (by omega) P
        (self_mem_rotationClass (by omega) v)).mp hvMinus
    have hbase := classFirst_strictlyPrecedes_classLast (by omega) P u
    have hlastSame : classLastVertex (by omega) P u = classLastVertex (by omega) P v := by
      simp only [classLastVertex]
      rw [hsame]
    change P.vertexIndex u < P.vertexIndex v
    calc
      P.vertexIndex u = P.vertexIndex (classFirstVertex (by omega) P u) :=
        congrArg P.vertexIndex huEq.symm
      _ < P.vertexIndex (classLastVertex (by omega) P u) := hbase
      _ = P.vertexIndex (classLastVertex (by omega) P v) :=
        congrArg P.vertexIndex hlastSame
      _ = P.vertexIndex v := congrArg P.vertexIndex hvEq.symm
  · have huLeLast : P.vertexIndex u ≤
        P.vertexIndex (classLastVertex (by omega) P u) := by
      rcases Finset.mem_union.mp hu with huF | huM
      · have huEq := classFirstVertex_eq_of_mem_firstVisitedVertices (by omega) P huF
        exact Nat.le_of_lt (by
          calc
            P.vertexIndex u = P.vertexIndex (classFirstVertex (by omega) P u) :=
              congrArg P.vertexIndex huEq.symm
            _ < P.vertexIndex (classLastVertex (by omega) P u) :=
              classFirst_strictlyPrecedes_classLast (by omega) P u)
      · have huEq := (mem_predecessors_in_class_iff_eq_last (by omega) P
          (self_mem_rotationClass (by omega) u)).mp huM
        exact Nat.le_of_eq (congrArg P.vertexIndex huEq)
    have hfirstLeV : P.vertexIndex (classFirstVertex (by omega) P v) ≤
        P.vertexIndex v := classFirstVertex_earliest (by omega) P v
    exact lt_of_le_of_lt huLeLast (lt_of_lt_of_le hstrict hfirstLeV)

private theorem component_rotationPower_mem_iff_first_mem (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (v : PermutationVertex k) (i : ℕ) (hi : i < k) :
    rotationPower i (classFirstVertex (by omega) P v) ∈ C.supp ↔
      classFirstVertex (by omega) P v ∈ C.supp := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hiPred : i < k - 1 := by omega
      have hfirstF := classFirstVertex_mem_firstVisitedVertices (by omega) P v
      have hedge := pathForest_complete_internal_rotation_path hk P hfirstF i hiPred
      have htarget : (rotationEdge (by omega)
          (rotationPower i (classFirstVertex (by omega) P v))).target =
          rotationPower (i + 1) (classFirstVertex (by omega) P v) := by
        exact rotation_rotationPower (by omega) i _
      constructor
      · intro hnext
        have hsource := weakComponent_edge_source_mem C (by simpa [htarget] using hnext) hedge
        exact (ih (by omega)).mp hsource
      · intro hfirst
        have hsource := (ih (by omega)).mpr hfirst
        have hnext := weakComponent_edge_target_mem C hsource hedge
        simpa [htarget] using hnext

/-- Every weak component of `F(P)` contains whole rotation classes. -/
theorem pathForest_component_contains_rotationClass (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    {v : PermutationVertex k} (hv : v ∈ C.supp) :
    rotationClass v ⊆ weakComponentVertices C := by
  classical
  let f := classFirstVertex (by omega) P v
  have hvInFirstClass : v ∈ rotationClass f := by
    rw [classFirstVertex_class (by omega) P v]
    exact self_mem_rotationClass (by omega) v
  obtain ⟨i, hi, hif⟩ := (mem_rotationClass_iff f v).mp hvInFirstClass
  have hfC : f ∈ C.supp := by
    apply (component_rotationPower_mem_iff_first_mem hk P C v i hi).mp
    simpa [f, hif] using hv
  intro u hu
  have huInFirstClass : u ∈ rotationClass f := by
    rw [classFirstVertex_class (by omega) P v]
    exact hu
  obtain ⟨j, hj, hjf⟩ := (mem_rotationClass_iff f u).mp huInFirstClass
  apply mem_weakComponentVertices.mpr
  have := (component_rotationPower_mem_iff_first_mem hk P C v j hj).mpr hfC
  simpa [f, hjf] using this

private noncomputable def cycleOutgoingEdge (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hcycle : IsDirectedCycleComponent C) (v : C) :
    DirectedOverlapEdge k := by
  classical
  have hcard : (outgoingEdgesAt (weakComponentEdges C) v.1).card = 1 := by
    exact (hcycle v.1 (mem_weakComponentVertices.mpr v.2)).2
  exact Classical.choose (Finset.card_pos.mp (by omega :
    0 < (outgoingEdgesAt (weakComponentEdges C) v.1).card))

private theorem cycleOutgoingEdge_mem (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hcycle : IsDirectedCycleComponent C) (v : C) :
    cycleOutgoingEdge X C hcycle v ∈ outgoingEdgesAt (weakComponentEdges C) v.1 := by
  classical
  have hcard : (outgoingEdgesAt (weakComponentEdges C) v.1).card = 1 := by
    exact (hcycle v.1 (mem_weakComponentVertices.mpr v.2)).2
  exact Classical.choose_spec (Finset.card_pos.mp (by omega :
    0 < (outgoingEdgesAt (weakComponentEdges C) v.1).card))

private noncomputable def cycleNext (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hcycle : IsDirectedCycleComponent C) (v : C) : C :=
  ⟨(cycleOutgoingEdge X C hcycle v).target,
    (mem_weakComponentEdges.mp
      (mem_outgoingEdgesAt.mp (cycleOutgoingEdge_mem X C hcycle v)).1).2.2⟩

private theorem cycleNext_edge (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hcycle : IsDirectedCycleComponent C) (v : C) :
    HasDirectedEdge X v.1 (cycleNext X C hcycle v).1 := by
  let e := cycleOutgoingEdge X C hcycle v
  have heOut := cycleOutgoingEdge_mem X C hcycle v
  refine ⟨e, (mem_weakComponentEdges.mp (mem_outgoingEdgesAt.mp heOut).1).1,
    (mem_outgoingEdgesAt.mp heOut).2, rfl⟩

private theorem cycleNext_injective (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hcycle : IsDirectedCycleComponent C) :
    Function.Injective (cycleNext X C hcycle) := by
  classical
  intro u v huv
  let eu := cycleOutgoingEdge X C hcycle u
  let ev := cycleOutgoingEdge X C hcycle v
  have heu := cycleOutgoingEdge_mem X C hcycle u
  have hev := cycleOutgoingEdge_mem X C hcycle v
  have htarget : eu.target = ev.target := congrArg Subtype.val huv
  have hle : (incomingEdgesAt (weakComponentEdges C) eu.target).card ≤ 1 := by
    have hone := (hcycle eu.target
      (mem_weakComponentVertices.mpr
        (mem_weakComponentEdges.mp (mem_outgoingEdgesAt.mp heu).1).2.2)).1
    exact hone.le
  rw [Finset.card_le_one] at hle
  have heq : eu = ev := hle eu
    (mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp heu).1, rfl⟩) ev
    (mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp hev).1, htarget.symm⟩)
  apply Subtype.ext
  calc
    u.1 = eu.source := (mem_outgoingEdgesAt.mp heu).2.symm
    _ = ev.source := congrArg DirectedOverlapEdge.source heq
    _ = v.1 := (mem_outgoingEdgesAt.mp hev).2

private theorem listIterate_chain {α : Type*} {R : α → α → Prop}
    (f : α → α) (hstep : ∀ x, R x (f x)) (a : α) (n : ℕ) :
    (List.iterate f a (n + 1)).IsChain R := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        List.IsChain.cons_cons (hstep a) (ih (f a))

private theorem isChain_map {α β : Type*} {R : α → α → Prop} {S : β → β → Prop}
    (g : α → β) {l : List α} (hchain : l.IsChain R)
    (hmap : ∀ {u v}, R u v → S (g u) (g v)) :
    (l.map g).IsChain S := by
  induction hchain with
  | nil => exact .nil
  | singleton a => exact .singleton _
  | cons_cons huv _ ih => exact .cons_cons (hmap huv) ih

private theorem finiteInjective_returns {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    ∃ d, 0 < d ∧ (f^[d]) a = a := by
  classical
  let s : Finset (Fin (Fintype.card α + 1)) := Finset.univ
  let t : Finset α := Finset.univ
  let g : Fin (Fintype.card α + 1) → α := fun i => (f^[i.1]) a
  have hcard : t.card < s.card := by simp [s, t]
  have hmaps : Set.MapsTo g (↑s) (↑t) := by simp [s, t]
  obtain ⟨i, _hi, j, _hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hneVal : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have derive : ∀ {p q : ℕ}, p < q →
      (f^[p]) a = (f^[q]) a → ∃ d, 0 < d ∧ (f^[d]) a = a := by
    intro p q hpq hpqEq
    let d := q - p
    have hd : 0 < d := by dsimp [d]; omega
    have hq : q = p + d := by dsimp [d]; omega
    have heq' : (f^[p]) a = (f^[p]) ((f^[d]) a) := by
      calc
        (f^[p]) a = (f^[q]) a := hpqEq
        _ = (f^[p + d]) a := by rw [hq]
        _ = (f^[p]) ((f^[d]) a) := Function.iterate_add_apply f p d a
    have hreturn : a = (f^[d]) a := (hf.iterate p) heq'
    exact ⟨d, hd, hreturn.symm⟩
  rcases Nat.lt_or_gt_of_ne hneVal with hijlt | hjilt
  · exact derive hijlt heq
  · exact derive hjilt heq.symm

/-- Structure theorem (iv), cycle exclusion. The contradiction is obtained by applying
structure theorem (iii) to the repeated first-in-class vertex of a genuine directed cycle
walk. -/
theorem pathForest_component_not_directedCycle (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    ¬IsDirectedCycleComponent C := by
  classical
  intro hcycle
  obtain ⟨x, hx⟩ := C.nonempty_supp
  let f := classFirstVertex (by omega) P x
  have hfC : f ∈ C.supp := by
    have hall := pathForest_component_contains_rotationClass hk P C hx
    exact mem_weakComponentVertices.mp
      (hall (classFirstVertex_mem_class (by omega) P x))
  let start : C := ⟨f, hfC⟩
  let next := cycleNext (pathForest hk P) C hcycle
  obtain ⟨d, hd, hreturn⟩ := finiteInjective_returns next
    (cycleNext_injective (pathForest hk P) C hcycle) start
  let subtypeWalk := List.iterate next start (d + 1)
  let walk := subtypeWalk.map Subtype.val
  have hstep : ∀ v : C,
      HasDirectedEdge (pathForest hk P) v.1 (next v).1 := by
    intro v
    exact cycleNext_edge (pathForest hk P) C hcycle v
  have hwalk : IsDirectedWalk (pathForest hk P) walk := by
    constructor
    · dsimp [walk]
      simp [subtypeWalk]
    · dsimp [walk, subtypeWalk]
      apply isChain_map Subtype.val
        (listIterate_chain
          (R := fun u v : C => HasDirectedEdge (pathForest hk P) u.1 v.1)
          next hstep start d)
      intro u v huv
      exact huv
  have hprecede : StrictlyPrecedesInList walk f f := by
    refine ⟨0, d, ?_, ?_, hd, ?_, ?_⟩
    · simp [walk, subtypeWalk]
    · simp [walk, subtypeWalk]
    · simp [walk, subtypeWalk, start]
    · have hsub : subtypeWalk[d]'(by simp [subtypeWalk]) = start := by
        change (List.iterate next start (d + 1))[d] = start
        rw [List.getElem_iterate]
        exact hreturn
      simpa [walk, start] using congrArg Subtype.val hsub
  have hspecial : f ∈ firstVisitedVertices (by omega) P ∪
      firstVisitedPredecessors (by omega) P :=
    Finset.mem_union_left _ (classFirstVertex_mem_firstVisitedVertices (by omega) P x)
  have horder := pathForest_walk_special_precedes_in_path hk P hwalk hspecial hspecial hprecede
  exact (Nat.lt_irrefl (P.vertexIndex f)) horder

/-- Structure theorem (iv), every weak component is a directed path component. -/
theorem pathForest_component_isDirectedPath (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsDirectedPathComponent C := by
  rcases forestTransform_component_rule hk P (residualVertices (by omega) P)
      (residualVertices_rotationEdgesAdmissible hk P) C with hpath | hcycle
  · exact hpath
  · exact (pathForest_component_not_directedCycle hk P C hcycle).elim

private structure DirectedPathEndpoints (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) where
  tail : C
  head : C
  tail_inDegree_zero : weakComponentInDegree C tail.1 = 0
  other_inDegree_one :
    ∀ v : C, v ≠ tail → weakComponentInDegree C v.1 = 1
  head_outDegree_zero : weakComponentOutDegree C head.1 = 0
  other_outDegree_one :
    ∀ v : C, v ≠ head → weakComponentOutDegree C v.1 = 1

private noncomputable def directedPathEndpoints (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hpath : IsDirectedPathComponent C) :
    DirectedPathEndpoints X C := by
  classical
  let tail := Classical.choose hpath
  have htailSpec := Classical.choose_spec hpath
  let hheadExists := htailSpec.2
  let head := Classical.choose hheadExists
  have hheadSpec := Classical.choose_spec hheadExists
  exact
    { tail := ⟨tail, mem_weakComponentVertices.mp htailSpec.1⟩
      head := ⟨head, mem_weakComponentVertices.mp hheadSpec.1⟩
      tail_inDegree_zero := hheadSpec.2.1
      other_inDegree_one := by
        intro v hv
        exact hheadSpec.2.2.1 v.1 (mem_weakComponentVertices.mpr v.2)
          (fun h => hv (Subtype.ext h))
      head_outDegree_zero := hheadSpec.2.2.2.1
      other_outDegree_one := by
        intro v hv
        exact hheadSpec.2.2.2.2 v.1 (mem_weakComponentVertices.mpr v.2)
          (fun h => hv (Subtype.ext h)) }

private noncomputable def pathOutgoingEdge (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) (hv : v ≠ D.head) : DirectedOverlapEdge k := by
  classical
  have hcard : (outgoingEdgesAt (weakComponentEdges C) v.1).card = 1 := by
    simpa [weakComponentOutDegree, outDegree] using D.other_outDegree_one v hv
  exact Classical.choose (Finset.card_pos.mp (by omega :
    0 < (outgoingEdgesAt (weakComponentEdges C) v.1).card))

private theorem pathOutgoingEdge_mem (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) (hv : v ≠ D.head) :
    pathOutgoingEdge X C D v hv ∈ outgoingEdgesAt (weakComponentEdges C) v.1 := by
  classical
  have hcard : (outgoingEdgesAt (weakComponentEdges C) v.1).card = 1 := by
    simpa [weakComponentOutDegree, outDegree] using D.other_outDegree_one v hv
  exact Classical.choose_spec (Finset.card_pos.mp (by omega :
    0 < (outgoingEdgesAt (weakComponentEdges C) v.1).card))

private noncomputable def pathNext (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) (v : C) : C := by
  classical
  by_cases hv : v = D.head
  · exact D.tail
  · exact
      ⟨(pathOutgoingEdge X C D v hv).target,
        (mem_weakComponentEdges.mp
          (mem_outgoingEdgesAt.mp (pathOutgoingEdge_mem X C D v hv)).1).2.2⟩

@[simp] private theorem pathNext_head (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    pathNext X C D D.head = D.tail := by
  simp [pathNext]

private theorem pathNext_of_ne_head (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) (hv : v ≠ D.head) :
    (pathNext X C D v).1 = (pathOutgoingEdge X C D v hv).target := by
  simp [pathNext, hv]

private theorem pathNext_hasEdge (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) (hv : v ≠ D.head) :
    HasDirectedEdge X v.1 (pathNext X C D v).1 := by
  let e := pathOutgoingEdge X C D v hv
  have heOut := pathOutgoingEdge_mem X C D v hv
  refine ⟨e, (mem_weakComponentEdges.mp (mem_outgoingEdgesAt.mp heOut).1).1,
    (mem_outgoingEdgesAt.mp heOut).2, ?_⟩
  exact (pathNext_of_ne_head X C D v hv).symm

private theorem directedPath_inDegree_le_one (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) (v : C) :
    (incomingEdgesAt (weakComponentEdges C) v.1).card ≤ 1 := by
  by_cases hv : v = D.tail
  · subst v
    have hzero : (incomingEdgesAt (weakComponentEdges C) D.tail.1).card = 0 := by
      simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
    omega
  · simpa [weakComponentInDegree, inDegree] using (D.other_inDegree_one v hv).le

private theorem pathNext_injective (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    Function.Injective (pathNext X C D) := by
  classical
  intro u v huv
  by_cases hu : u = D.head
  · subst u
    by_cases hv : v = D.head
    · exact hv.symm
    · let ev := pathOutgoingEdge X C D v hv
      have hev := pathOutgoingEdge_mem X C D v hv
      have htarget : ev.target = D.tail.1 := by
        have hval := congrArg Subtype.val huv
        rw [pathNext_head, pathNext_of_ne_head X C D v hv] at hval
        exact hval.symm
      have hein : ev ∈ incomingEdgesAt (weakComponentEdges C) D.tail.1 :=
        mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp hev).1, htarget⟩
      have hempty : incomingEdgesAt (weakComponentEdges C) D.tail.1 = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
      rw [hempty] at hein
      simp at hein
  · by_cases hv : v = D.head
    · subst v
      let eu := pathOutgoingEdge X C D u hu
      have heu := pathOutgoingEdge_mem X C D u hu
      have htarget : eu.target = D.tail.1 := by
        have hval := congrArg Subtype.val huv
        rw [pathNext_of_ne_head X C D u hu, pathNext_head] at hval
        exact hval
      have hein : eu ∈ incomingEdgesAt (weakComponentEdges C) D.tail.1 :=
        mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp heu).1, htarget⟩
      have hempty : incomingEdgesAt (weakComponentEdges C) D.tail.1 = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
      rw [hempty] at hein
      simp at hein
    · let eu := pathOutgoingEdge X C D u hu
      let ev := pathOutgoingEdge X C D v hv
      have heu := pathOutgoingEdge_mem X C D u hu
      have hev := pathOutgoingEdge_mem X C D v hv
      have htarget : eu.target = ev.target := by
        have hval := congrArg Subtype.val huv
        rw [pathNext_of_ne_head X C D u hu,
          pathNext_of_ne_head X C D v hv] at hval
        exact hval
      let target : C :=
        ⟨eu.target, (mem_weakComponentEdges.mp (mem_outgoingEdgesAt.mp heu).1).2.2⟩
      have hle : (incomingEdgesAt (weakComponentEdges C) eu.target).card ≤ 1 := by
        simpa [target] using directedPath_inDegree_le_one X C D target
      rw [Finset.card_le_one] at hle
      have heq : eu = ev := hle eu
        (mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp heu).1, rfl⟩) ev
        (mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp hev).1, htarget.symm⟩)
      apply Subtype.ext
      calc
        u.1 = eu.source := (mem_outgoingEdgesAt.mp heu).2.symm
        _ = ev.source := congrArg DirectedOverlapEdge.source heq
        _ = v.1 := (mem_outgoingEdgesAt.mp hev).2

private noncomputable def pathPeriod (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) : ℕ :=
  Nat.find (finiteInjective_returns (pathNext X C D)
    (pathNext_injective X C D) D.tail)

private theorem pathPeriod_pos (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    0 < pathPeriod X C D := by
  exact (Nat.find_spec (finiteInjective_returns (pathNext X C D)
    (pathNext_injective X C D) D.tail)).1

private theorem pathPeriod_returns (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    ((pathNext X C D)^[pathPeriod X C D]) D.tail = D.tail := by
  exact (Nat.find_spec (finiteInjective_returns (pathNext X C D)
    (pathNext_injective X C D) D.tail)).2

private theorem pathPeriod_minimal (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    {d : ℕ} (hd : 0 < d) (hreturn : ((pathNext X C D)^[d]) D.tail = D.tail) :
    pathPeriod X C D ≤ d := by
  exact Nat.find_min' (finiteInjective_returns (pathNext X C D)
    (pathNext_injective X C D) D.tail) ⟨hd, hreturn⟩

private noncomputable def directedComponentSubtypeList (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) : List C :=
  List.iterate (pathNext X C D) D.tail (pathPeriod X C D)

private theorem directedComponentSubtypeList_nodup (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    (directedComponentSubtypeList X C D).Nodup := by
  classical
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [directedComponentSubtypeList, List.length_iterate] at hi hj
  simp only [directedComponentSubtypeList, List.getElem_iterate]
  intro heq
  let f := pathNext X C D
  let d := pathPeriod X C D
  let q := j - i
  have hqpos : 0 < q := by dsimp [q]; omega
  have hjEq : j = i + q := by dsimp [q]; omega
  have heq' : (f^[i]) D.tail = (f^[i]) ((f^[q]) D.tail) := by
    calc
      (f^[i]) D.tail = (f^[j]) D.tail := heq
      _ = (f^[i + q]) D.tail := by rw [hjEq]
      _ = (f^[i]) ((f^[q]) D.tail) := Function.iterate_add_apply f i q D.tail
  have hreturn : (f^[q]) D.tail = D.tail :=
    ((pathNext_injective X C D).iterate i heq').symm
  have hminimal : d ≤ q := pathPeriod_minimal X C D hqpos hreturn
  dsimp [d, q] at hminimal
  omega

private theorem pathIterate_ne_head_before_period (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (i : ℕ) (hi : i + 1 < pathPeriod X C D) :
    ((pathNext X C D)^[i]) D.tail ≠ D.head := by
  intro heq
  have hreturn : ((pathNext X C D)^[i + 1]) D.tail = D.tail := by
    rw [Function.iterate_succ_apply', heq, pathNext_head]
  have hminimal := pathPeriod_minimal X C D (by omega) hreturn
  omega

private def InPathOrbit (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) (v : C) : Prop :=
  ∃ i < pathPeriod X C D, ((pathNext X C D)^[i]) D.tail = v

private theorem tail_in_pathOrbit (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    InPathOrbit X C D D.tail := by
  exact ⟨0, pathPeriod_pos X C D, rfl⟩

private theorem pathOrbit_closed_next (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    {v : C} (hv : InPathOrbit X C D v) :
    InPathOrbit X C D (pathNext X C D v) := by
  obtain ⟨i, hi, hiv⟩ := hv
  by_cases hisucc : i + 1 < pathPeriod X C D
  · refine ⟨i + 1, hisucc, ?_⟩
    rw [Function.iterate_succ_apply', hiv]
  · have hieq : i + 1 = pathPeriod X C D := by omega
    have hnextTail : pathNext X C D v = D.tail := by
      calc
        pathNext X C D v =
            pathNext X C D (((pathNext X C D)^[i]) D.tail) :=
          congrArg (pathNext X C D) hiv.symm
        _ = ((pathNext X C D)^[i + 1]) D.tail :=
          (Function.iterate_succ_apply' (pathNext X C D) i D.tail).symm
        _ = ((pathNext X C D)^[pathPeriod X C D]) D.tail := by rw [hieq]
        _ = D.tail := pathPeriod_returns X C D
    rw [hnextTail]
    exact tail_in_pathOrbit X C D

private theorem pathOutgoingEdge_unique (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) (hv : v ≠ D.head) {e : DirectedOverlapEdge k}
    (he : e ∈ weakComponentEdges C) (hsource : e.source = v.1) :
    e = pathOutgoingEdge X C D v hv := by
  classical
  have hcard : (outgoingEdgesAt (weakComponentEdges C) v.1).card = 1 := by
    simpa [weakComponentOutDegree, outDegree] using D.other_outDegree_one v hv
  have hle : (outgoingEdgesAt (weakComponentEdges C) v.1).card ≤ 1 := hcard.le
  rw [Finset.card_le_one] at hle
  exact hle e (mem_outgoingEdgesAt.mpr ⟨he, hsource⟩)
    (pathOutgoingEdge X C D v hv) (pathOutgoingEdge_mem X C D v hv)

private theorem directedPath_incoming_unique (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    (v : C) {e e' : DirectedOverlapEdge k}
    (he : e ∈ weakComponentEdges C) (het : e.target = v.1)
    (he' : e' ∈ weakComponentEdges C) (he't : e'.target = v.1) :
    e = e' := by
  classical
  have hle := directedPath_inDegree_le_one X C D v
  rw [Finset.card_le_one] at hle
  exact hle e (mem_incomingEdgesAt.mpr ⟨he, het⟩) e'
    (mem_incomingEdgesAt.mpr ⟨he', he't⟩)

private theorem pathOrbit_closed_adj (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C)
    {a b : C} (hab : C.toSimpleGraph.Adj a b)
    (ha : InPathOrbit X C D a) : InPathOrbit X C D b := by
  classical
  have habBase : (underlyingSimpleGraph X).Adj a.1 b.1 :=
    (C.toSimpleGraph_adj a.2 b.2).1 hab
  obtain ⟨e, heX, hdir⟩ := habBase
  rcases hdir with hforward | hbackward
  · obtain ⟨hes, het⟩ := hforward
    have heC : e ∈ weakComponentEdges C :=
      mem_weakComponentEdges.mpr ⟨heX, hes.symm ▸ a.2, het.symm ▸ b.2⟩
    have haNotHead : a ≠ D.head := by
      intro haHead
      have heOut : e ∈ outgoingEdgesAt (weakComponentEdges C) D.head.1 := by
        subst a
        exact mem_outgoingEdgesAt.mpr ⟨heC, hes⟩
      have hempty : outgoingEdgesAt (weakComponentEdges C) D.head.1 = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [weakComponentOutDegree, outDegree] using D.head_outDegree_zero
      rw [hempty] at heOut
      simp at heOut
    have heq := pathOutgoingEdge_unique X C D a haNotHead heC hes
    have hbNext : b = pathNext X C D a := by
      apply Subtype.ext
      calc
        b.1 = e.target := het.symm
        _ = (pathOutgoingEdge X C D a haNotHead).target :=
          congrArg DirectedOverlapEdge.target heq
        _ = (pathNext X C D a).1 :=
          (pathNext_of_ne_head X C D a haNotHead).symm
    rw [hbNext]
    exact pathOrbit_closed_next X C D ha
  · obtain ⟨hes, het⟩ := hbackward
    have heC : e ∈ weakComponentEdges C :=
      mem_weakComponentEdges.mpr ⟨heX, hes.symm ▸ b.2, het.symm ▸ a.2⟩
    obtain ⟨i, hi, hia⟩ := ha
    by_cases hiZero : i = 0
    · subst i
      have haTail : a = D.tail := by simpa using hia.symm
      have heIn : e ∈ incomingEdgesAt (weakComponentEdges C) D.tail.1 := by
        subst a
        exact mem_incomingEdgesAt.mpr ⟨heC, het⟩
      have hempty : incomingEdgesAt (weakComponentEdges C) D.tail.1 = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
      rw [hempty] at heIn
      simp at heIn
    · let q := i - 1
      have hqi : q + 1 = i := by dsimp [q]; omega
      have hqSucc : q + 1 < pathPeriod X C D := by omega
      let prev : C := ((pathNext X C D)^[q]) D.tail
      have hprevNotHead : prev ≠ D.head := by
        exact pathIterate_ne_head_before_period X C D q hqSucc
      let ep := pathOutgoingEdge X C D prev hprevNotHead
      have hepOut := pathOutgoingEdge_mem X C D prev hprevNotHead
      have hepC : ep ∈ weakComponentEdges C := (mem_outgoingEdgesAt.mp hepOut).1
      have hepTarget : ep.target = a.1 := by
        calc
          ep.target = (pathNext X C D prev).1 :=
            (pathNext_of_ne_head X C D prev hprevNotHead).symm
          _ = (((pathNext X C D)^[q + 1]) D.tail).1 := by
            exact congrArg Subtype.val
              (Function.iterate_succ_apply' (pathNext X C D) q D.tail).symm
          _ = (((pathNext X C D)^[i]) D.tail).1 := by rw [hqi]
          _ = a.1 := congrArg Subtype.val hia
      have heq : e = ep := directedPath_incoming_unique X C D a heC het hepC hepTarget
      refine ⟨q, by omega, ?_⟩
      apply Subtype.ext
      calc
        prev.1 = ep.source := (mem_outgoingEdgesAt.mp hepOut).2.symm
        _ = e.source := congrArg DirectedOverlapEdge.source heq.symm
        _ = b.1 := hes

private theorem every_component_vertex_in_subtypeList (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) (v : C) :
    v ∈ directedComponentSubtypeList X C D := by
  have hwalkClosed : ∀ {a b : C}, C.toSimpleGraph.Walk a b →
      InPathOrbit X C D a → InPathOrbit X C D b := by
    intro a b w
    induction w with
    | nil => exact fun h => h
    | @cons u v z hadj rest ih =>
        intro hu
        exact ih (pathOrbit_closed_adj X C D hadj hu)
  obtain ⟨w⟩ := C.connected_toSimpleGraph D.tail v
  have horbit := hwalkClosed w (tail_in_pathOrbit X C D)
  obtain ⟨i, hi, hiv⟩ := horbit
  apply List.mem_iterate.mpr
  exact ⟨i, hi, hiv.symm⟩

private theorem pathFinalIterate_eq_head (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (D : DirectedPathEndpoints X C) :
    ((pathNext X C D)^[pathPeriod X C D - 1]) D.tail = D.head := by
  classical
  let d := pathPeriod X C D
  let i := d - 1
  have hd : 0 < d := pathPeriod_pos X C D
  have hiSucc : i + 1 = d := by dsimp [i]; omega
  let last : C := ((pathNext X C D)^[i]) D.tail
  have hnextTail : pathNext X C D last = D.tail := by
    calc
      pathNext X C D last = ((pathNext X C D)^[i + 1]) D.tail :=
        (Function.iterate_succ_apply' (pathNext X C D) i D.tail).symm
      _ = ((pathNext X C D)^[d]) D.tail := by rw [hiSucc]
      _ = D.tail := pathPeriod_returns X C D
  by_contra hlast
  have hlastNe : last ≠ D.head := by
    simpa [last, i, d] using hlast
  let e := pathOutgoingEdge X C D last hlastNe
  have heOut := pathOutgoingEdge_mem X C D last hlastNe
  have htarget : e.target = D.tail.1 := by
    calc
      e.target = (pathNext X C D last).1 :=
        (pathNext_of_ne_head X C D last hlastNe).symm
      _ = D.tail.1 := congrArg Subtype.val hnextTail
  have heIn : e ∈ incomingEdgesAt (weakComponentEdges C) D.tail.1 :=
    mem_incomingEdgesAt.mpr ⟨(mem_outgoingEdgesAt.mp heOut).1, htarget⟩
  have hempty : incomingEdgesAt (weakComponentEdges C) D.tail.1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
  rw [hempty] at heIn
  simp at heIn

private noncomputable def directedComponentPathOfEndpoints
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) : OverlapPath k where
  vertices := (directedComponentSubtypeList X C D).map Subtype.val
  nodup := (directedComponentSubtypeList_nodup X C D).map Subtype.val_injective
  nonempty := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_map, directedComponentSubtypeList, List.length_iterate,
      List.length_nil] at hlen
    exact (Nat.ne_of_gt (pathPeriod_pos X C D)) hlen

/-- The honest ordered path carried by a finite weak component satisfying the directed-path
degree pattern. Its construction starts at the unique in-degree-zero vertex and follows the
actual outgoing edges, closing only after all component vertices have been listed. -/
noncomputable def directedPathComponentPath (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hpath : IsDirectedPathComponent C) : OverlapPath k :=
  directedComponentPathOfEndpoints X C (directedPathEndpoints X C hpath)

@[simp] private theorem directedComponentPathOfEndpoints_length
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) :
    (directedComponentPathOfEndpoints X C D).length = pathPeriod X C D := by
  simp [directedComponentPathOfEndpoints, OverlapPath.length,
    directedComponentSubtypeList]

private theorem directedComponentPathOfEndpoints_vertex
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) (i : ℕ)
    (hi : i < (directedComponentPathOfEndpoints X C D).length) :
    (directedComponentPathOfEndpoints X C D).vertex ⟨i, hi⟩ =
      ((pathNext X C D)^[i]) D.tail := by
  have hi' : i < (List.iterate (pathNext X C D) D.tail (pathPeriod X C D)).length := by
    simpa only [directedComponentPathOfEndpoints_length, List.length_iterate] using hi
  exact (List.getElem_map (Subtype.val : C → PermutationVertex k)
    (l := List.iterate (pathNext X C D) D.tail (pathPeriod X C D))
    (i := i) (h := by simpa only [List.length_map] using hi')).trans
      (congrArg (Subtype.val : C → PermutationVertex k)
        (List.getElem_iterate (pathNext X C D) D.tail (pathPeriod X C D) i hi'))

private theorem directedComponentPathOfEndpoints_first
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) :
    (directedComponentPathOfEndpoints X C D).vertex
      ⟨0, (directedComponentPathOfEndpoints X C D).length_pos⟩ = D.tail := by
  rw [directedComponentPathOfEndpoints_vertex]
  rfl

/-- `F(P)` spans every permutation vertex: every vertex belongs to one of its weak
components, including isolated vertices. -/
theorem pathForest_spans_vertices (hk : 3 ≤ k) (P : HamiltonianPath k) :
    (weakComponents (pathForest hk P)).biUnion weakComponentVertices =
      (Finset.univ : Finset (PermutationVertex k)) := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  apply Finset.mem_biUnion.mpr
  let C : WeakComponent (pathForest hk P) :=
    (underlyingSimpleGraph (pathForest hk P)).connectedComponentMk v
  exact ⟨C, Finset.mem_univ C, mem_weakComponentVertices.mpr
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

private theorem directedComponentPathOfEndpoints_last
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) :
    (directedComponentPathOfEndpoints X C D).vertices.getLast
      (directedComponentPathOfEndpoints X C D).nonempty = D.head := by
  let p := directedComponentPathOfEndpoints X C D
  have hpos := p.length_pos
  have hget : p.vertices.getLast p.nonempty =
      p.vertex ⟨p.length - 1, by omega⟩ := by
    simpa [p, OverlapPath.vertex, OverlapPath.length] using
      List.getLast_eq_getElem p.nonempty
  rw [hget, directedComponentPathOfEndpoints_vertex]
  have hlen : p.length = pathPeriod X C D := by
    exact directedComponentPathOfEndpoints_length X C D
  rw [hlen]
  exact congrArg Subtype.val (pathFinalIterate_eq_head X C D)

/-- The component path lists exactly the vertices of its weak component, including when the
component is a singleton. -/
theorem directedPathComponentPath_vertexSet (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hpath : IsDirectedPathComponent C) :
    (directedPathComponentPath X C hpath).vertexSet = weakComponentVertices C := by
  classical
  let D := directedPathEndpoints X C hpath
  change (directedComponentPathOfEndpoints X C D).vertexSet = weakComponentVertices C
  ext v
  constructor
  · intro hv
    have hvList : v ∈ (directedComponentPathOfEndpoints X C D).vertices := by
      exact List.mem_toFinset.mp hv
    rcases List.mem_map.mp hvList with ⟨u, _hu, huv⟩
    exact mem_weakComponentVertices.mpr (huv ▸ u.2)
  · intro hv
    let u : C := ⟨v, mem_weakComponentVertices.mp hv⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨u, every_component_vertex_in_subtypeList X C D u, rfl⟩

namespace OverlapPath

/-- The finite set of consecutive directed edges represented by an overlap path. -/
noncomputable def edgeSet (p : OverlapPath k) : FiniteDirectedSubgraph k := by
  classical
  exact Finset.univ.image fun i : Fin (p.length - 1) =>
    p.edgeAt i.1 (by omega)

@[simp]
theorem mem_edgeSet_iff {p : OverlapPath k} {e : DirectedOverlapEdge k} :
    e ∈ p.edgeSet ↔ ∃ i, ∃ hi : i + 1 < p.length, p.edgeAt i hi = e := by
  classical
  constructor
  · intro he
    obtain ⟨i, _hi, hie⟩ := Finset.mem_image.mp he
    exact ⟨i.1, by omega, hie⟩
  · rintro ⟨i, hi, rfl⟩
    apply Finset.mem_image.mpr
    let j : Fin (p.length - 1) := ⟨i, by omega⟩
    exact ⟨j, Finset.mem_univ j, rfl⟩

end OverlapPath

private theorem directedOverlapEdge_eq_of_source_target
    {e e' : DirectedOverlapEdge k}
    (hsource : e.source = e'.source) (htarget : e.target = e'.target) : e = e' := by
  cases e with
  | mk source target ne =>
      cases e' with
      | mk source' target' ne' =>
          simp only at hsource htarget
          subst source'
          subst target'
          rfl

private theorem directedComponentPath_edgeAt_eq_outgoing
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) (i : ℕ)
    (hi : i + 1 < (directedComponentPathOfEndpoints X C D).length) :
    let current : C := ((pathNext X C D)^[i]) D.tail
    (directedComponentPathOfEndpoints X C D).edgeAt i hi =
      pathOutgoingEdge X C D current
        (pathIterate_ne_head_before_period X C D i (by
          simpa [directedComponentPathOfEndpoints_length] using hi)) := by
  let p := directedComponentPathOfEndpoints X C D
  let current : C := ((pathNext X C D)^[i]) D.tail
  have hiPeriod : i + 1 < pathPeriod X C D := by
    simpa [p, directedComponentPathOfEndpoints_length] using hi
  have hcurrent : current ≠ D.head :=
    pathIterate_ne_head_before_period X C D i hiPeriod
  have hiP : i < p.length := by
    exact (Nat.lt_succ_self i).trans hi
  apply directedOverlapEdge_eq_of_source_target
  · change p.vertex ⟨i, hiP⟩ =
      (pathOutgoingEdge X C D current hcurrent).source
    calc
      p.vertex ⟨i, hiP⟩ = current.1 :=
        directedComponentPathOfEndpoints_vertex X C D i hiP
      _ = (pathOutgoingEdge X C D current hcurrent).source :=
        (mem_outgoingEdgesAt.mp
          (pathOutgoingEdge_mem X C D current hcurrent)).2.symm
  · change p.vertex ⟨i + 1, hi⟩ =
      (pathOutgoingEdge X C D current hcurrent).target
    calc
      p.vertex ⟨i + 1, hi⟩ =
          (((pathNext X C D)^[i + 1]) D.tail).1 :=
        directedComponentPathOfEndpoints_vertex X C D (i + 1) hi
      _ = (pathNext X C D current).1 := by
        exact congrArg Subtype.val
          (Function.iterate_succ_apply' (pathNext X C D) i D.tail)
      _ = (pathOutgoingEdge X C D current hcurrent).target :=
        pathNext_of_ne_head X C D current hcurrent

private theorem directedComponentPath_edgeAt_mem
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) (i : ℕ)
    (hi : i + 1 < (directedComponentPathOfEndpoints X C D).length) :
    (directedComponentPathOfEndpoints X C D).edgeAt i hi ∈
      weakComponentEdges C := by
  rw [directedComponentPath_edgeAt_eq_outgoing X C D i hi]
  exact (mem_outgoingEdgesAt.mp
    (pathOutgoingEdge_mem X C D _ _)).1

private theorem directedComponentPath_covers_edge
    (X : FiniteDirectedSubgraph k) (C : WeakComponent X)
    (D : DirectedPathEndpoints X C) {e : DirectedOverlapEdge k}
    (he : e ∈ weakComponentEdges C) :
    ∃ i, ∃ hi : i + 1 < (directedComponentPathOfEndpoints X C D).length,
      (directedComponentPathOfEndpoints X C D).edgeAt i hi = e := by
  classical
  let a : C := ⟨e.source, (mem_weakComponentEdges.mp he).2.1⟩
  have haNotHead : a ≠ D.head := by
    intro haHead
    have heOut : e ∈ outgoingEdgesAt (weakComponentEdges C) D.head.1 := by
      exact mem_outgoingEdgesAt.mpr ⟨he, by
        exact congrArg Subtype.val haHead⟩
    have hempty : outgoingEdgesAt (weakComponentEdges C) D.head.1 = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [weakComponentOutDegree, outDegree] using D.head_outDegree_zero
    rw [hempty] at heOut
    simp at heOut
  have haMem := every_component_vertex_in_subtypeList X C D a
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp haMem
  let i := idx.1
  have hiPeriod : i < pathPeriod X C D := by
    have := idx.2
    simpa [i, directedComponentSubtypeList] using this
  have hiterateA : ((pathNext X C D)^[i]) D.tail = a := by
    exact (List.getElem_iterate (pathNext X C D) D.tail (pathPeriod X C D)
      idx.1 idx.2).symm.trans hidx
  have hiSucc : i + 1 < pathPeriod X C D := by
    by_contra hnot
    have hiLast : i = pathPeriod X C D - 1 := by omega
    have haHead : a = D.head := by
      calc
        a = ((pathNext X C D)^[i]) D.tail := hiterateA.symm
        _ = ((pathNext X C D)^[pathPeriod X C D - 1]) D.tail := by rw [hiLast]
        _ = D.head := pathFinalIterate_eq_head X C D
    exact haNotHead haHead
  have hiPath : i + 1 < (directedComponentPathOfEndpoints X C D).length := by
    simpa [directedComponentPathOfEndpoints_length] using hiSucc
  refine ⟨i, hiPath, ?_⟩
  rw [directedComponentPath_edgeAt_eq_outgoing X C D i hiPath]
  let current : C := ((pathNext X C D)^[i]) D.tail
  have hcurrent : current = a := hiterateA
  have heq : e = pathOutgoingEdge X C D a haNotHead :=
    pathOutgoingEdge_unique X C D a haNotHead he
      (by rfl)
  simpa [current, hiterateA] using heq.symm

/-- Consecutive edges of the honest component path are exactly the directed edges induced by
the weak component. -/
theorem directedPathComponentPath_edgeSet (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hpath : IsDirectedPathComponent C) :
    (directedPathComponentPath X C hpath).edgeSet = weakComponentEdges C := by
  classical
  let D := directedPathEndpoints X C hpath
  change (directedComponentPathOfEndpoints X C D).edgeSet = weakComponentEdges C
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, hie⟩ := OverlapPath.mem_edgeSet_iff.mp he
    rw [← hie]
    exact directedComponentPath_edgeAt_mem X C D i hi
  · intro he
    obtain ⟨i, hi, hie⟩ := directedComponentPath_covers_edge X C D he
    exact OverlapPath.mem_edgeSet_iff.mpr ⟨i, hi, hie⟩

/-- A one-vertex directed component is represented by the required one-term path and has no
path edge. -/
theorem directedPathComponentPath_singleton (X : FiniteDirectedSubgraph k)
    (C : WeakComponent X) (hpath : IsDirectedPathComponent C)
    (hcard : (weakComponentVertices C).card = 1) :
    (directedPathComponentPath X C hpath).length = 1 ∧
      (directedPathComponentPath X C hpath).edgeSet = ∅ := by
  classical
  let p := directedPathComponentPath X C hpath
  have hvertexCard : p.vertexSet.card = 1 := by
    rw [directedPathComponentPath_vertexSet X C hpath, hcard]
  have hlength : p.length = 1 := by
    calc
      p.length = p.vertices.toFinset.card := by
        exact (List.toFinset_card_of_nodup p.nodup).symm
      _ = p.vertexSet.card := rfl
      _ = 1 := hvertexCard
  refine ⟨hlength, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨i, hi, _hie⟩ := OverlapPath.mem_edgeSet_iff.mp he
  rw [hlength] at hi
  omega

/-- The honest directed path sequence attached to a weak component of `F(P)`. -/
noncomputable def pathForestComponentPath (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) : OverlapPath k :=
  directedPathComponentPath (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)

/-- The specialized component path contains exactly the component vertices. -/
theorem pathForestComponentPath_vertexSet (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) :
    (pathForestComponentPath hk P C).vertexSet = weakComponentVertices C := by
  exact directedPathComponentPath_vertexSet (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)

/-- The specialized component path contains exactly the component edges. -/
theorem pathForestComponentPath_edgeSet (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) :
    (pathForestComponentPath hk P C).edgeSet = weakComponentEdges C := by
  exact directedPathComponentPath_edgeSet (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)

/-- Singleton components are represented by one-term sequences with no edges. -/
theorem pathForestComponentPath_singleton (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hcard : (weakComponentVertices C).card = 1) :
    (pathForestComponentPath hk P C).length = 1 ∧
      (pathForestComponentPath hk P C).edgeSet = ∅ := by
  exact directedPathComponentPath_singleton (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C) hcard

/-- The component sequence is a genuine directed walk in `F(P)`. -/
theorem pathForestComponentPath_isDirectedWalk (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsDirectedWalk (pathForest hk P) (pathForestComponentPath hk P C).vertices := by
  let p := pathForestComponentPath hk P C
  constructor
  · exact p.nonempty
  · rw [List.isChain_iff_getElem]
    intro i hi
    let e := p.edgeAt i (by simpa [p, OverlapPath.length] using hi)
    have hePath : e ∈ p.edgeSet := by
      apply OverlapPath.mem_edgeSet_iff.mpr
      exact ⟨i, by simpa [p, OverlapPath.length] using hi, rfl⟩
    have heWeak : e ∈ weakComponentEdges C := by
      rw [← pathForestComponentPath_edgeSet hk P C]
      exact hePath
    refine ⟨e, (mem_weakComponentEdges.mp heWeak).1, ?_, ?_⟩
    · rfl
    · rfl

/-- The tail (first vertex) of a component's honest directed path. -/
noncomputable def pathForestComponentTail (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) : PermutationVertex k :=
  (pathForestComponentPath hk P C).vertex
    ⟨0, (pathForestComponentPath hk P C).length_pos⟩

/-- The head (last vertex) of a component's honest directed path. -/
noncomputable def pathForestComponentHead (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) : PermutationVertex k :=
  (pathForestComponentPath hk P C).vertices.getLast
    (pathForestComponentPath hk P C).nonempty

private theorem pathForestComponentTail_eq_endpoint (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentTail hk P C =
      (directedPathEndpoints (pathForest hk P) C
        (pathForest_component_isDirectedPath hk P C)).tail.1 := by
  exact directedComponentPathOfEndpoints_first (pathForest hk P) C
    (directedPathEndpoints (pathForest hk P) C
      (pathForest_component_isDirectedPath hk P C))

private theorem pathForestComponentHead_eq_endpoint (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentHead hk P C =
      (directedPathEndpoints (pathForest hk P) C
        (pathForest_component_isDirectedPath hk P C)).head.1 := by
  exact directedComponentPathOfEndpoints_last (pathForest hk P) C
    (directedPathEndpoints (pathForest hk P) C
      (pathForest_component_isDirectedPath hk P C))

/-- Every component tail is its block's first-visited vertex. -/
theorem pathForestComponentTail_mem_firstVisited (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentTail hk P C ∈ firstVisitedVertices (by omega) P := by
  classical
  let D := directedPathEndpoints (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)
  have htailEq : pathForestComponentTail hk P C = D.tail.1 :=
    pathForestComponentTail_eq_endpoint hk P C
  by_contra hnot
  have hIncoming := pathForest_incoming_of_not_first hk P (by simpa [htailEq] using hnot)
  let e := rotationEdge (by omega) (inverseRotation D.tail.1)
  have heGraph : e ∈ pathForest hk P := by
    have : e ∈ incomingEdgesAt (pathForest hk P) D.tail.1 := by
      rw [hIncoming]
      simp [e]
    exact (mem_incomingEdgesAt.mp this).1
  have heTarget : e.target = D.tail.1 := by
    change rotation (inverseRotation D.tail.1) = D.tail.1
    exact rotation_inverseRotation (by omega) D.tail.1
  have heTargetC : e.target ∈ C.supp := by
    rw [heTarget]
    exact D.tail.2
  have heSourceC : e.source ∈ C.supp :=
    weakComponent_edge_source_mem C heTargetC heGraph
  have heWeak : e ∈ weakComponentEdges C :=
    mem_weakComponentEdges.mpr ⟨heGraph, heSourceC, heTargetC⟩
  have heIn : e ∈ incomingEdgesAt (weakComponentEdges C) D.tail.1 :=
    mem_incomingEdgesAt.mpr ⟨heWeak, heTarget⟩
  have hempty : incomingEdgesAt (weakComponentEdges C) D.tail.1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentInDegree, inDegree] using D.tail_inDegree_zero
  rw [hempty] at heIn
  simp at heIn

/-- Every component head is the predecessor of a first-visited vertex. -/
theorem pathForestComponentHead_mem_firstVisitedPredecessors (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentHead hk P C ∈ firstVisitedPredecessors (by omega) P := by
  classical
  let D := directedPathEndpoints (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)
  have hheadEq : pathForestComponentHead hk P C = D.head.1 :=
    pathForestComponentHead_eq_endpoint hk P C
  by_contra hnot
  have hOutgoing := pathForest_outgoing_of_not_predecessor hk P
    (by simpa [hheadEq] using hnot)
  let e := rotationEdge (by omega) D.head.1
  have heGraph : e ∈ pathForest hk P := by
    have : e ∈ outgoingEdgesAt (pathForest hk P) D.head.1 := by
      rw [hOutgoing]
      simp [e]
    exact (mem_outgoingEdgesAt.mp this).1
  have heSource : e.source = D.head.1 := rfl
  have heTargetC : e.target ∈ C.supp :=
    weakComponent_edge_target_mem C D.head.2 heGraph
  have heWeak : e ∈ weakComponentEdges C :=
    mem_weakComponentEdges.mpr ⟨heGraph, D.head.2, heTargetC⟩
  have heOut : e ∈ outgoingEdgesAt (weakComponentEdges C) D.head.1 :=
    mem_outgoingEdgesAt.mpr ⟨heWeak, heSource⟩
  have hempty : outgoingEdgesAt (weakComponentEdges C) D.head.1 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentOutDegree, outDegree] using D.head_outDegree_zero
  rw [hempty] at heOut
  simp at heOut

/-- The named component tail is the genuine in-degree-zero endpoint. -/
theorem pathForestComponentTail_inDegree_zero (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    weakComponentInDegree C (pathForestComponentTail hk P C) = 0 := by
  let D := directedPathEndpoints (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)
  rw [pathForestComponentTail_eq_endpoint hk P C]
  exact D.tail_inDegree_zero

/-- The named component head is the genuine out-degree-zero endpoint. -/
theorem pathForestComponentHead_outDegree_zero (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    weakComponentOutDegree C (pathForestComponentHead hk P C) = 0 := by
  let D := directedPathEndpoints (pathForest hk P) C
    (pathForest_component_isDirectedPath hk P C)
  rw [pathForestComponentHead_eq_endpoint hk P C]
  exact D.head_outDegree_zero

private theorem pathForestComponentPath_stronglyExitless_direct (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsStronglyExitless (pathForestComponentPath hk P C) := by
  classical
  let p := pathForestComponentPath hk P C
  have hwalk : IsDirectedWalk (pathForest hk P) p.vertices :=
    pathForestComponentPath_isDirectedWalk hk P C
  constructor
  · rintro ⟨i, hi, hheavy, hnotvisited⟩
    have hiP : i + 1 < p.length := by simpa [p] using hi
    let u := p.vertex ⟨i, by omega⟩
    let v := p.vertex ⟨i + 1, hiP⟩
    let e := p.edgeAt i hiP
    have hheavyUV : 1 < overlapWeight u v := by
      simpa [p, u, v] using hheavy
    have hnotvisitedUV : rotation u ∉ p.vertices.take (i + 1) := by
      simpa [p, u] using hnotvisited
    have hePath : e ∈ p.edgeSet :=
      OverlapPath.mem_edgeSet_iff.mpr ⟨i, hiP, rfl⟩
    have heGraph : e ∈ pathForest hk P := by
      have heWeak : e ∈ weakComponentEdges C := by
        rw [← pathForestComponentPath_edgeSet hk P C]
        exact hePath
      exact (mem_weakComponentEdges.mp heWeak).1
    have huMinus : u ∈ firstVisitedPredecessors (by omega) P := by
      by_contra huNot
      have hOut := pathForest_outgoing_of_not_predecessor hk P huNot
      have heOut : e ∈ outgoingEdgesAt (pathForest hk P) u :=
        mem_outgoingEdgesAt.mpr ⟨heGraph, rfl⟩
      rw [hOut] at heOut
      have heq : e = rotationEdge (by omega) u := by simpa using heOut
      have hone : overlapWeight u v = 1 := by
        change e.weight = 1
        rw [heq]
        exact rotationEdge_weight hk u
      omega
    let r := rotation u
    have hrFirst : r ∈ firstVisitedVertices (by omega) P := by
      exact (mem_firstVisitedPredecessors_iff (by omega) P u).mp huMinus
    have huC : u ∈ C.supp := by
      apply mem_weakComponentVertices.mp
      have hset : p.vertexSet = weakComponentVertices C := by
        simpa [p] using pathForestComponentPath_vertexSet hk P C
      rw [← hset]
      exact List.mem_toFinset.mpr (p.vertex_mem ⟨i, by omega⟩)
    have hrClass : r ∈ rotationClass u := by
      apply (mem_rotationClass_iff u r).mpr
      refine ⟨1, by omega, ?_⟩
      simp [r, rotationPower]
    have hrC : r ∈ C.supp := by
      exact mem_weakComponentVertices.mp
        (pathForest_component_contains_rotationClass hk P C huC hrClass)
    have hrList : r ∈ p.vertices := by
      have hset : p.vertexSet = weakComponentVertices C := by
        simpa [p] using pathForestComponentPath_vertexSet hk P C
      have hrSet : r ∈ p.vertexSet := by
        rw [hset]
        exact mem_weakComponentVertices.mpr hrC
      exact List.mem_toFinset.mp hrSet
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hrList
    have hij : i < j.1 := by
      by_contra hnotlt
      have hjle : j.1 < i + 1 := by omega
      apply hnotvisitedUV
      apply List.mem_take_iff_getElem.mpr
      refine ⟨j.1, ?_, ?_⟩
      · exact lt_min hjle j.2
      · exact hj
    have hprecede : StrictlyPrecedesInList p.vertices u r := by
      refine ⟨i, j.1, by omega, j.2, hij, ?_, ?_⟩
      · rfl
      · exact hj
    have hspecialU : u ∈ firstVisitedVertices (by omega) P ∪
        firstVisitedPredecessors (by omega) P := Finset.mem_union_right _ huMinus
    have hspecialR : r ∈ firstVisitedVertices (by omega) P ∪
        firstVisitedPredecessors (by omega) P := Finset.mem_union_left _ hrFirst
    have horder := pathForest_walk_special_precedes_in_path hk P hwalk
      hspecialU hspecialR hprecede
    have hclass : rotationClass u = rotationClass r :=
      (rotationClass_eq_of_mem (by omega) hrClass).symm
    have hfirstEq : classFirstVertex (by omega) P u = r := by
      calc
        classFirstVertex (by omega) P u = classFirstVertex (by omega) P r :=
          classFirstVertex_eq_of_same_class (by omega) P hclass
        _ = r := classFirstVertex_eq_of_mem_firstVisitedVertices
          (by omega) P hrFirst
    have hle := classFirstVertex_earliest (by omega) P u
    rw [hfirstEq] at hle
    exact (Nat.not_lt_of_ge hle) horder
  · let h := pathForestComponentHead hk P C
    have hhMinus := pathForestComponentHead_mem_firstVisitedPredecessors hk P C
    have hrotFirst : rotation h ∈ firstVisitedVertices (by omega) P :=
      (mem_firstVisitedPredecessors_iff (by omega) P h).mp hhMinus
    have hhC : h ∈ C.supp := by
      let D := directedPathEndpoints (pathForest hk P) C
        (pathForest_component_isDirectedPath hk P C)
      rw [show h = D.head.1 by
        simpa [h, D] using pathForestComponentHead_eq_endpoint hk P C]
      exact D.head.2
    have hrotClass : rotation h ∈ rotationClass h := by
      apply (mem_rotationClass_iff h (rotation h)).mpr
      refine ⟨1, by omega, ?_⟩
      simp [rotationPower]
    have hrotC : rotation h ∈ C.supp := by
      exact mem_weakComponentVertices.mp
        (pathForest_component_contains_rotationClass hk P C hhC hrotClass)
    have hrotList : rotation h ∈ p.vertices := by
      have hset : p.vertexSet = weakComponentVertices C := by
        simpa [p] using pathForestComponentPath_vertexSet hk P C
      have hrotSet : rotation h ∈ p.vertexSet := by
        rw [hset]
        exact mem_weakComponentVertices.mpr hrotC
      exact List.mem_toFinset.mp hrotSet
    simpa [p, h, pathForestComponentHead] using hrotList

/-- Every specialized component path is block-aligned. -/
theorem pathForestComponentPath_blockAligned (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsBlockAligned (pathForestComponentPath hk P C) := by
  have hstrong := pathForestComponentPath_stronglyExitless_direct hk P C
  exact ⟨hstrong.1, stronglyExitless_length_dvd hstrong hk⟩

/-- The ordered list of complete-block entries in a component path. -/
noncomputable def pathForestComponentBlockEntries (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    List (PermutationVertex k) := by
  let p := pathForestComponentPath hk P C
  let hp := pathForestComponentPath_blockAligned hk P C
  exact List.ofFn fun j : Fin (pathBlockCount p) =>
    p.vertex ⟨k * j.1, by
      rw [blockAligned_length_eq hp]
      exact Nat.mul_lt_mul_of_pos_left j.2 (by omega)⟩

@[simp]
theorem pathForestComponentBlockEntries_length (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    (pathForestComponentBlockEntries hk P C).length =
      pathBlockCount (pathForestComponentPath hk P C) := by
  simp [pathForestComponentBlockEntries]

/-- The component has at least one complete block. -/
theorem pathForestComponentBlockEntries_nonempty (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentBlockEntries hk P C ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [pathForestComponentBlockEntries_length] at hlen
  simp at hlen
  exact (Nat.ne_of_gt (blockAligned_blockCount_pos
    (pathForestComponentPath_blockAligned hk P C))) hlen

/-- The complete blocks of one component occur in pairwise distinct rotation classes. -/
theorem pathForestComponentBlockEntries_pairwiseDistinct (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    PairwiseDistinctRotationClasses (pathForestComponentBlockEntries hk P C) := by
  let p := pathForestComponentPath hk P C
  let hp := pathForestComponentPath_blockAligned hk P C
  rw [PairwiseDistinctRotationClasses, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hiB : i < pathBlockCount p := by
    simpa [p] using hi
  have hjB : j < pathBlockCount p := by
    simpa [p] using hj
  have hjPos : k * j < p.length := by
    rw [blockAligned_length_eq hp]
    exact Nat.mul_lt_mul_of_pos_left hjB (by omega)
  simpa [pathForestComponentBlockEntries, p, hp] using
    exitless_block_entries_distinct hp.1 hk hij hjPos

/-- Each component path is exactly a nonempty concatenation of complete rotation blocks. -/
theorem pathForestComponentPath_isCompleteBlockSequence (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsCompleteBlockSequence (pathForestComponentPath hk P C) (by omega) := by
  let p := pathForestComponentPath hk P C
  let hp := pathForestComponentPath_blockAligned hk P C
  let entries := pathForestComponentBlockEntries hk P C
  refine ⟨entries, pathForestComponentBlockEntries_nonempty hk P C, ?_⟩
  have hlen : p.length = k * entries.length := by
    calc
      p.length = k * pathBlockCount p := blockAligned_length_eq hp
      _ = k * entries.length := by
        rw [pathForestComponentBlockEntries_length]
  apply List.ext_getElem
  · simpa [OverlapPath.length, blockSequenceVertices_length] using hlen
  · intro i hiLeft hiRight
    have hiP : i < p.length := by simpa [OverlapPath.length] using hiLeft
    have hiExpanded : i < k * entries.length := by
      simpa [blockSequenceVertices_length] using hiRight
    rw [blockSequenceVertices_getElem (by omega) entries i hiExpanded]
    change p.vertex ⟨i, hiP⟩ = _
    have hentry : entries.get ⟨i / k, by
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        simpa [Nat.mul_comm] using hiExpanded⟩ =
        p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hiP⟩ := by
      simp [entries, pathForestComponentBlockEntries, p]
    rw [hentry]
    exact exitless_vertex_formula hp.1 hk i hiP

/-- Structure theorem (iv): every component path is strongly exitless. After the honest
component sequence has been proved to be a concatenation of complete blocks, this is exactly
the accepted Section 1 block-locality theorem. -/
theorem pathForestComponentPath_stronglyExitless (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    IsStronglyExitless (pathForestComponentPath hk P C) :=
  completeBlockSequence_stronglyExitless hk
    (pathForestComponentPath_isCompleteBlockSequence hk P C)

/-- Structure theorem (v): the tail is the first vertex of its component reached by `P`. -/
theorem pathForestComponentTail_earliest (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    {u : PermutationVertex k} (hu : u ∈ weakComponentVertices C) :
    P.vertexIndex (pathForestComponentTail hk P C) ≤ P.vertexIndex u := by
  classical
  let p := pathForestComponentPath hk P C
  let tail := pathForestComponentTail hk P C
  let f := classFirstVertex (by omega) P u
  have huC : u ∈ C.supp := mem_weakComponentVertices.mp hu
  have hfC : f ∈ C.supp := by
    exact mem_weakComponentVertices.mp
      (pathForest_component_contains_rotationClass hk P C huC
        (classFirstVertex_mem_class (by omega) P u))
  have hfList : f ∈ p.vertices := by
    have hset : p.vertexSet = weakComponentVertices C := by
      simpa [p] using pathForestComponentPath_vertexSet hk P C
    have hfSet : f ∈ p.vertexSet := by
      rw [hset]
      exact mem_weakComponentVertices.mpr hfC
    exact List.mem_toFinset.mp hfSet
  have hfirstLeU : P.vertexIndex f ≤ P.vertexIndex u :=
    classFirstVertex_earliest (by omega) P u
  by_cases htailf : tail = f
  · have hresult : P.vertexIndex tail ≤ P.vertexIndex u := by
      rw [htailf]
      exact hfirstLeU
    simpa [tail] using hresult
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hfList
    have hjpos : 0 < j.1 := by
      by_contra hjzero
      have hzero : j.1 = 0 := Nat.eq_zero_of_not_pos hjzero
      let z : Fin p.vertices.length := ⟨0, by
        simpa [OverlapPath.length] using p.length_pos⟩
      have hfirstVertex : p.vertices.get z = tail := by
        rfl
      have hjz : j = z := Fin.ext hzero
      have : tail = f := by
        calc
          tail = p.vertices.get z := hfirstVertex.symm
          _ = p.vertices.get j := congrArg p.vertices.get hjz.symm
          _ = f := hj
      exact htailf this
    have hprecede : StrictlyPrecedesInList p.vertices tail f := by
      refine ⟨0, j.1, by simpa [OverlapPath.length] using p.length_pos,
        j.2, hjpos, ?_, hj⟩
      rfl
    have htailSpecial : tail ∈ firstVisitedVertices (by omega) P ∪
        firstVisitedPredecessors (by omega) P :=
      Finset.mem_union_left _ (pathForestComponentTail_mem_firstVisited hk P C)
    have hfSpecial : f ∈ firstVisitedVertices (by omega) P ∪
        firstVisitedPredecessors (by omega) P :=
      Finset.mem_union_left _ (classFirstVertex_mem_firstVisitedVertices (by omega) P u)
    have htailBefore := pathForest_walk_special_precedes_in_path hk P
      (pathForestComponentPath_isDirectedWalk hk P C)
      htailSpecial hfSpecial hprecede
    exact (Nat.le_of_lt htailBefore).trans hfirstLeU

/-- The frozen component count `c = |Comp(F(P))|`. -/
noncomputable def pathForestComponentCount (hk : 3 ≤ k)
    (P : HamiltonianPath k) : ℕ := (weakComponents (pathForest hk P)).card

theorem pathForestComponentCount_eq_fintypeCard (hk : 3 ≤ k)
    (P : HamiltonianPath k) :
    pathForestComponentCount hk P =
      Fintype.card (WeakComponent (pathForest hk P)) := by
  simp [pathForestComponentCount, weakComponents]

/-- The frozen block count `b_p`. -/
noncomputable def pathForestComponentBlockCount (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) : ℕ :=
  pathBlockCount (pathForestComponentPath hk P C)

theorem pathForestComponentBlockCount_pos (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    0 < pathForestComponentBlockCount hk P C :=
  blockAligned_blockCount_pos (pathForestComponentPath_blockAligned hk P C)

/-- The frozen excess-derived parameter `z_p = ε(p) + 1`. -/
noncomputable def pathForestComponentZ (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) : ℕ :=
  pathExcess (pathForestComponentPath hk P C)
    (pathForestComponentPath_blockAligned hk P C) + 1

theorem pathForestComponentZ_pos (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    1 ≤ pathForestComponentZ hk P C := by
  simp [pathForestComponentZ]

/-- The entry `ω_p` of the last complete block of a component. -/
noncomputable def pathForestComponentLastBlockEntry (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    PermutationVertex k :=
  (pathForestComponentBlockEntries hk P C).getLast
    (pathForestComponentBlockEntries_nonempty hk P C)

private theorem pathForestComponentLastBlockEntry_eq_vertex (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentLastBlockEntry hk P C =
      (pathForestComponentPath hk P C).vertex
        ⟨k * (pathForestComponentBlockCount hk P C - 1), by
          rw [blockAligned_length_eq
            (pathForestComponentPath_blockAligned hk P C)]
          exact Nat.mul_lt_mul_of_pos_left
            (by exact Nat.sub_lt (pathForestComponentBlockCount_pos hk P C) (by omega))
            (by omega)⟩ := by
  let entries := pathForestComponentBlockEntries hk P C
  have hentries : entries ≠ [] := pathForestComponentBlockEntries_nonempty hk P C
  have hlast := List.getLast_eq_getElem hentries
  rw [pathForestComponentLastBlockEntry, hlast]
  simp [entries, pathForestComponentBlockEntries,
    pathForestComponentBlockCount]

/-- The component head is the exit of its last complete block, `h_p = ex(ω_p)`. -/
theorem pathForestComponentHead_eq_blockExit_lastBlockEntry (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentHead hk P C =
      blockExit (pathForestComponentLastBlockEntry hk P C) := by
  let p := pathForestComponentPath hk P C
  let hp := pathForestComponentPath_blockAligned hk P C
  let b := pathForestComponentBlockCount hk P C
  let omega := pathForestComponentLastBlockEntry hk P C
  have hb : 0 < b := pathForestComponentBlockCount_pos hk P C
  have hlen : p.length = k * b := by
    simpa [b, p, pathForestComponentBlockCount] using blockAligned_length_eq hp
  have hmul : k * b = k * (b - 1) + k := by
    conv_lhs => rw [show b = (b - 1) + 1 by omega]
    rw [Nat.mul_add]
    simp
  have hlastIndex : p.length - 1 = k * (b - 1) + (k - 1) := by
    rw [hlen, hmul]
    omega
  have hposition : k * (b - 1) + (k - 1) < p.length := by
    rw [← hlastIndex]
    have := p.length_pos
    omega
  have homega : omega = p.vertex ⟨k * (b - 1), by omega⟩ := by
    simpa [omega, p, b] using pathForestComponentLastBlockEntry_eq_vertex hk P C
  have hheadLast : pathForestComponentHead hk P C =
      p.vertex ⟨p.length - 1, by have := p.length_pos; omega⟩ := by
    simpa [pathForestComponentHead, p, OverlapPath.vertex, OverlapPath.length] using
      List.getLast_eq_getElem p.nonempty
  calc
    pathForestComponentHead hk P C =
        p.vertex ⟨p.length - 1, by have := p.length_pos; omega⟩ := hheadLast
    _ = p.vertex ⟨k * (b - 1) + (k - 1), hposition⟩ := by
      apply congrArg p.vertex
      apply Fin.ext
      exact hlastIndex
    _ = rotationPower (k - 1) (p.vertex ⟨k * (b - 1), by omega⟩) :=
      exitless_block_vertex hp.1 hk (b - 1) (k - 1) (by omega) hposition
    _ = rotationPower (k - 1) omega := congrArg (rotationPower (k - 1)) homega.symm
    _ = blockExit omega := rotationPower_pred_eq_blockExit (by omega) omega
    _ = blockExit (pathForestComponentLastBlockEntry hk P C) := rfl

/-- The root is the unique weak component containing the first Hamiltonian-path vertex. -/
noncomputable def pathForestRootComponent (hk : 3 ≤ k) (P : HamiltonianPath k) :
    WeakComponent (pathForest hk P) :=
  (underlyingSimpleGraph (pathForest hk P)).connectedComponentMk P.tail

theorem pathForest_mem_rootComponent (hk : 3 ≤ k) (P : HamiltonianPath k) :
    P.tail ∈ weakComponentVertices (pathForestRootComponent hk P) := by
  exact mem_weakComponentVertices.mpr
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- Exact uniqueness characterization of the root component. -/
theorem pathForestComponent_eq_root_iff (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) :
    C = pathForestRootComponent hk P ↔ P.tail ∈ weakComponentVertices C := by
  constructor
  · intro hC
    subst C
    exact pathForest_mem_rootComponent hk P
  · intro hmem
    have hrootC : pathForestRootComponent hk P = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C P.tail).mp
        (mem_weakComponentVertices.mp hmem)
    exact hrootC.symm

/-- The tail of the root component is exactly `P[1]`. -/
theorem pathForestRootComponent_tail (hk : 3 ≤ k) (P : HamiltonianPath k) :
    pathForestComponentTail hk P (pathForestRootComponent hk P) = P.tail := by
  have hle := pathForestComponentTail_earliest hk P
    (pathForestRootComponent hk P) (pathForest_mem_rootComponent hk P)
  have htailZero := P.vertexIndex_tail
  apply P.vertexIndex_injective
  omega

/-- Vertices outside a component. -/
noncomputable def pathForestComponentOutsideVertices (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    Finset (PermutationVertex k) :=
  Finset.univ \ weakComponentVertices C

@[simp]
theorem mem_pathForestComponentOutsideVertices_iff (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (u : PermutationVertex k) :
    u ∈ pathForestComponentOutsideVertices hk P C ↔
      u ∉ weakComponentVertices C := by
  simp [pathForestComponentOutsideVertices]

/-- Every nonspanning component has a nonempty outside set. This includes a nonspanning
root component. -/
theorem pathForestComponentOutsideVertices_nonempty_of_nonspanning (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠ (Finset.univ : Finset (PermutationVertex k))) :
    (pathForestComponentOutsideVertices hk P C).Nonempty := by
  by_contra hEmpty
  apply hC
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra hu
  exact hEmpty ⟨u, (mem_pathForestComponentOutsideVertices_iff hk P C u).mpr hu⟩

/-- A nonroot component has a nonempty outside set, witnessed by `P[1]` in the distinct
root component. -/
theorem pathForestComponentOutsideVertices_nonempty_of_nonroot (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : C ≠ pathForestRootComponent hk P) :
    (pathForestComponentOutsideVertices hk P C).Nonempty := by
  refine ⟨P.tail, (mem_pathForestComponentOutsideVertices_iff hk P C P.tail).mpr ?_⟩
  intro htailC
  exact hC ((pathForestComponent_eq_root_iff hk P C).mpr htailC)

theorem pathForestComponent_vertexSet_ne_univ_of_nonroot (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : C ≠ pathForestRootComponent hk P) :
    weakComponentVertices C ≠ (Finset.univ : Finset (PermutationVertex k)) := by
  obtain ⟨u, hu⟩ := pathForestComponentOutsideVertices_nonempty_of_nonroot hk P C hC
  have huNot := (mem_pathForestComponentOutsideVertices_iff hk P C u).mp hu
  intro hUniv
  apply huNot
  rw [hUniv]
  exact Finset.mem_univ u

/-- The finite set of costs of entering a component tail from outside. -/
noncomputable def pathForestOutsideEntryWeights (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) : Finset ℕ :=
  (pathForestComponentOutsideVertices hk P C).image fun u =>
    overlapWeight u (pathForestComponentTail hk P C)

/-- The finite outside-entry cost set is nonempty for every nonspanning component. -/
theorem pathForestOutsideEntryWeights_nonempty_of_nonspanning (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠ (Finset.univ : Finset (PermutationVertex k))) :
    (pathForestOutsideEntryWeights hk P C).Nonempty := by
  obtain ⟨u, hu⟩ :=
    pathForestComponentOutsideVertices_nonempty_of_nonspanning hk P C hC
  exact ⟨overlapWeight u (pathForestComponentTail hk P C),
    Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem pathForestOutsideEntryWeights_nonempty_of_nonroot (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : C ≠ pathForestRootComponent hk P) :
    (pathForestOutsideEntryWeights hk P C).Nonempty := by
  exact pathForestOutsideEntryWeights_nonempty_of_nonspanning hk P C
    (pathForestComponent_vertexSet_ne_univ_of_nonroot hk P C hC)

theorem pathForestOutsideEntryWeights_bounds (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    {w : ℕ} (hw : w ∈ pathForestOutsideEntryWeights hk P C) :
    1 ≤ w ∧ w ≤ k := by
  obtain ⟨u, _hu, huw⟩ := Finset.mem_image.mp hw
  rw [← huw]
  exact ⟨(overlapWeight_spec u (pathForestComponentTail hk P C)).1,
    overlapWeight_le_length (by omega) u (pathForestComponentTail hk P C)⟩

/-- The attained outside-entry minimum `minto(p)` for every nonspanning component,
including a nonspanning root. -/
noncomputable def pathForestMinto (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) : ℕ :=
  (pathForestOutsideEntryWeights hk P C).min'
    (pathForestOutsideEntryWeights_nonempty_of_nonspanning hk P C hC)

/-- `minto(p)` is independent of the proof that the component is nonspanning. -/
theorem pathForestMinto_proof_irrel (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC hC' : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) :
    pathForestMinto hk P C hC = pathForestMinto hk P C hC' := by
  rfl

/-- For every nonspanning component, the finite minimum defining `minto` is attained by an
actual outside vertex. -/
theorem pathForestMinto_attained (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) :
    ∃ u ∈ pathForestComponentOutsideVertices hk P C,
      overlapWeight u (pathForestComponentTail hk P C) =
        pathForestMinto hk P C hC := by
  have hmin := Finset.min'_mem (pathForestOutsideEntryWeights hk P C)
    (pathForestOutsideEntryWeights_nonempty_of_nonspanning hk P C hC)
  obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hmin
  exact ⟨u, hu, huw⟩

/-- For every nonspanning component, the attained value is no larger than every
outside-entry candidate. -/
theorem pathForestMinto_le (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k)))
    {u : PermutationVertex k}
    (hu : u ∈ pathForestComponentOutsideVertices hk P C) :
    pathForestMinto hk P C hC ≤
      overlapWeight u (pathForestComponentTail hk P C) := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

/-- The entry cost of every nonspanning component lies in `{2,...,k}`. In particular this
is frozen Lemma 2.6 for nonroot components. The lower bound uses the unique weight-one
predecessor, which lies inside the component's complete first block. -/
theorem pathForestMinto_bounds (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) :
    2 ≤ pathForestMinto hk P C hC ∧ pathForestMinto hk P C hC ≤ k := by
  classical
  obtain ⟨u, huOutside, huWeight⟩ := pathForestMinto_attained hk P C hC
  have huNotC : u ∉ weakComponentVertices C :=
    (mem_pathForestComponentOutsideVertices_iff hk P C u).mp huOutside
  let tail := pathForestComponentTail hk P C
  have htailC : tail ∈ C.supp := by
    apply mem_weakComponentVertices.mp
    have hset := pathForestComponentPath_vertexSet hk P C
    rw [← hset]
    exact List.mem_toFinset.mpr
      ((pathForestComponentPath hk P C).vertex_mem
        ⟨0, (pathForestComponentPath hk P C).length_pos⟩)
  have hupper : pathForestMinto hk P C hC ≤ k := by
    rw [← huWeight]
    exact overlapWeight_le_length (by omega) u tail
  have hlower : 2 ≤ pathForestMinto hk P C hC := by
    have hpos : 1 ≤ pathForestMinto hk P C hC := by
      rw [← huWeight]
      exact (overlapWeight_spec u tail).1
    by_contra hnot
    have hone : overlapWeight u tail = 1 := by rw [huWeight]; omega
    have htailMem : tail ∈ weakComponentVertices C :=
      mem_weakComponentVertices.mpr htailC
    have hne : u ≠ tail := by
      intro hut
      apply huNotC
      rwa [hut]
    have huInv : u = inverseRotation tail :=
      (unique_weight_one_predecessor tail u hk hne).mp hone
    have hinvClass : inverseRotation tail ∈ rotationClass tail := by
      change blockExit tail ∈ rotationClass tail
      rw [← rotationPower_pred_eq_blockExit (by omega) tail]
      exact rotationPower_mem_rotationClass (by omega) (k - 1) tail
    have hinvC : inverseRotation tail ∈ weakComponentVertices C :=
      pathForest_component_contains_rotationClass hk P C htailC hinvClass
    exact huNotC (by rwa [huInv])
  exact ⟨hlower, hupper⟩

/-- For every nonspanning component, the subtraction in `minto(p) - 2` is exact, not
truncated. -/
theorem pathForestMinto_sub_two_add_two (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) :
    pathForestMinto hk P C hC - 2 + 2 = pathForestMinto hk P C hC := by
  have := (pathForestMinto_bounds hk P C hC).1
  omega

/-- The frozen root/nonroot budget `y_p`. The nonroot branch separates the justified
subtraction `minto(p)-2` before adding it to `z_p`. -/
noncomputable def pathForestComponentBudget (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) : ℕ := by
  classical
  exact if hroot : C = pathForestRootComponent hk P then
      pathForestComponentZ hk P C
    else
      pathForestComponentZ hk P C +
        (pathForestMinto hk P C
          (pathForestComponent_vertexSet_ne_univ_of_nonroot hk P C hroot) - 2)

theorem pathForestComponentBudget_root (hk : 3 ≤ k) (P : HamiltonianPath k) :
    pathForestComponentBudget hk P (pathForestRootComponent hk P) =
      pathForestComponentZ hk P (pathForestRootComponent hk P) := by
  simp [pathForestComponentBudget]

theorem pathForestComponentBudget_nonroot_split (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : C ≠ pathForestRootComponent hk P) :
    pathForestComponentBudget hk P C =
      pathForestComponentZ hk P C +
        (pathForestMinto hk P C
          (pathForestComponent_vertexSet_ne_univ_of_nonroot hk P C hC) - 2) := by
  simp [pathForestComponentBudget, hC]

/-- The nonroot branch in the literal frozen form `z_p + minto(p) - 2`; the equality
records that neither natural subtraction truncates. -/
theorem pathForestComponentBudget_nonroot (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    (hC : C ≠ pathForestRootComponent hk P) :
    pathForestComponentBudget hk P C =
      pathForestComponentZ hk P C +
        pathForestMinto hk P C
          (pathForestComponent_vertexSet_ne_univ_of_nonroot hk P C hC) - 2 := by
  rw [pathForestComponentBudget_nonroot_split hk P C hC]
  have hm := (pathForestMinto_bounds hk P C
    (pathForestComponent_vertexSet_ne_univ_of_nonroot hk P C hC)).1
  omega

/-- Every root or nonroot component budget is positive. -/
theorem pathForestComponentBudget_pos (hk : 3 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest hk P)) :
    1 ≤ pathForestComponentBudget hk P C := by
  by_cases hroot : C = pathForestRootComponent hk P
  · subst C
    rw [pathForestComponentBudget_root]
    exact pathForestComponentZ_pos hk P _
  · rw [pathForestComponentBudget_nonroot_split hk P C hroot]
    have hz := pathForestComponentZ_pos hk P C
    omega

/-- The total frozen budget `R`. -/
noncomputable def pathForestTotalBudget (hk : 3 ≤ k) (P : HamiltonianPath k) : ℕ :=
  ∑ C ∈ weakComponents (pathForest hk P), pathForestComponentBudget hk P C

/-- Frozen equation (2.1), including both the conditional component formula and the
finite component sum defining `R`. -/
theorem pathForest_budget_equation_2_1 (hk : 3 ≤ k) (P : HamiltonianPath k) :
    pathForestTotalBudget hk P =
      ∑ C ∈ weakComponents (pathForest hk P),
        pathForestComponentBudget hk P C := rfl

end SuperpermutationLowerBound
