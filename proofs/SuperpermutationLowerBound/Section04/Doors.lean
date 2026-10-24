module

public import SuperpermutationLowerBound.Section04.Runs

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 4 from Lemma `doors` through Lemma `fullheadthree`.

The standing mathematical range is `k ≥ 7`.  The sole exception is the
literal `k = 5` witness required by Example `selfabsorber`.
-/

open PermutationVertex

variable {k : ℕ}

/-! ## Cyclic support for the door arguments -/

/-- Starting an iterate after one application of `τ₂` advances the exponent
by one. -/
private theorem runMapPower_runMap (hk : 3 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    runMapPower (by omega) i (runMap (by omega) u) =
      runMapPower (by omega) (i + 1) u := by
  have hk1 : 1 ≤ k := by omega
  change ((runMap hk1)^[i]) (runMap hk1 u) =
    ((runMap hk1)^[i + 1]) u
  exact (Function.iterate_succ_apply (runMap hk1) i u).symm

/-- The predecessor in a `τ₂`-cycle is its `(k-2)`nd forward iterate. -/
private theorem runMapPower_pred_eq_runMapInverse (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    runMapPower (by omega) (k - 2) u = runMapInverse (by omega) u := by
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), runMapInverse_word]

private theorem doubleRotation_doubleInverse (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    doubleRotation (inverseRotation (inverseRotation u)) = u := by
  calc
    doubleRotation (inverseRotation (inverseRotation u)) =
        rotation (rotation (inverseRotation (inverseRotation u))) :=
      (rotation_rotation_eq_doubleRotation (by omega) _).symm
    _ = rotation (inverseRotation u) :=
      congrArg rotation (rotation_inverseRotation (by omega) (inverseRotation u))
    _ = u := rotation_inverseRotation (by omega) u

private theorem doubleInverse_of_doubleRotation_eq (hk : 3 ≤ k)
    {u v : PermutationVertex k} (h : v = doubleRotation u) :
    u = inverseRotation (inverseRotation v) := by
  symm
  calc
    inverseRotation (inverseRotation v) =
        inverseRotation (inverseRotation (doubleRotation u)) :=
      congrArg (fun x => inverseRotation (inverseRotation x)) h
    _ = inverseRotation (inverseRotation (rotation (rotation u))) := by
      rw [rotation_rotation_eq_doubleRotation (by omega)]
    _ = inverseRotation (rotation u) :=
      congrArg inverseRotation (inverseRotation_rotation (by omega) (rotation u))
    _ = u := inverseRotation_rotation (by omega) u

private theorem blockExit_entranceDoor_is_door_preimage (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    door (blockExit (pathForestComponentEntranceDoor hk P C)) =
      pathForestComponentTail (by omega) P C := by
  rw [door_blockExit (by omega), pathForestComponentEntranceDoor_eq,
    runMap_runMapInverse (by omega)]

private theorem blockExit_entranceDoor_of_door_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u : PermutationVertex k}
    (h : pathForestComponentTail (by omega) P C = door u) :
    u = blockExit (pathForestComponentEntranceDoor hk P C) := by
  have huBlock : blockExit (rotation u) = u := by
    exact inverseRotation_rotation (by omega) u
  have hdoorRun : door u = runMap (by omega) (rotation u) := by
    calc
      door u = door (blockExit (rotation u)) := congrArg door huBlock.symm
      _ = runMap (by omega) (rotation u) := door_blockExit (by omega) _
  have hrotation :
      rotation u = pathForestComponentEntranceDoor hk P C := by
    calc
      rotation u = runMapInverse (by omega) (runMap (by omega) (rotation u)) :=
        (runMapInverse_runMap (by omega) (rotation u)).symm
      _ = runMapInverse (by omega) (pathForestComponentTail (by omega) P C) :=
        congrArg (runMapInverse (by omega)) (h.trans hdoorRun).symm
      _ = pathForestComponentEntranceDoor hk P C := rfl
  calc
    u = blockExit (rotation u) := huBlock.symm
    _ = blockExit (pathForestComponentEntranceDoor hk P C) :=
      congrArg blockExit hrotation

private theorem inverseRotation_mem_rotationClass (hk : 1 ≤ k)
    (u : PermutationVertex k) :
    inverseRotation u ∈ rotationClass u := by
  change blockExit u ∈ rotationClass u
  rw [← rotationPower_pred_eq_blockExit hk u]
  exact rotationPower_mem_rotationClass hk (k - 1) u

private theorem doubleInverse_mem_rotationClass (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    inverseRotation (inverseRotation u) ∈ rotationClass u := by
  have hfirst := inverseRotation_mem_rotationClass (by omega) u
  have hsecond := inverseRotation_mem_rotationClass (by omega) (inverseRotation u)
  have hclass : rotationClass (inverseRotation u) = rotationClass u :=
    rotationClass_eq_of_mem (by omega) hfirst
  rwa [hclass] at hsecond

/-- Frozen Lemma `doors`(1): the two weight-two predecessors of a component
tail, with both asserted class memberships and the fact that the two listed
vertices are distinct. -/
theorem pathForestComponent_weightTwo_predecessors (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (∀ u : PermutationVertex k,
      u ≠ pathForestComponentTail (by omega) P C →
        (overlapWeight u (pathForestComponentTail (by omega) P C) = 2 ↔
          u = inverseRotation
              (inverseRotation (pathForestComponentTail (by omega) P C)) ∨
          u = blockExit (pathForestComponentEntranceDoor hk P C))) ∧
      inverseRotation
          (inverseRotation (pathForestComponentTail (by omega) P C)) ∈
        rotationClass (pathForestComponentTail (by omega) P C) ∧
      blockExit (pathForestComponentEntranceDoor hk P C) ∈
        rotationClass (pathForestComponentEntranceDoor hk P C) ∧
      inverseRotation
          (inverseRotation (pathForestComponentTail (by omega) P C)) ≠
        blockExit (pathForestComponentEntranceDoor hk P C) := by
  let tail := pathForestComponentTail (by omega) P C
  let alpha := pathForestComponentEntranceDoor hk P C
  have hdouble : doubleRotation (inverseRotation (inverseRotation tail)) = tail :=
    doubleRotation_doubleInverse (by omega) tail
  have hdoor : door (blockExit alpha) = tail := by
    simpa [tail, alpha] using blockExit_entranceDoor_is_door_preimage hk P C
  refine ⟨?_, doubleInverse_mem_rotationClass (by omega) tail,
    inverseRotation_mem_rotationClass (by omega) alpha, ?_⟩
  · intro u hune
    constructor
    · intro hweight
      rcases (weight_two_successors u tail (by omega) (by simpa [tail] using hune)).mp
          hweight with hdoubleU | hdoorU
      · exact Or.inl (doubleInverse_of_doubleRotation_eq (by omega) hdoubleU)
      · exact Or.inr (blockExit_entranceDoor_of_door_eq hk P C hdoorU)
    · rintro (rfl | rfl)
      · change overlapWeight (inverseRotation (inverseRotation tail)) tail = 2
        calc
          overlapWeight (inverseRotation (inverseRotation tail)) tail =
              overlapWeight (inverseRotation (inverseRotation tail))
                (doubleRotation (inverseRotation (inverseRotation tail))) := by rw [hdouble]
          _ = 2 := doubleRotation_has_weight_two (k := k) _ (by omega)
      · change overlapWeight (blockExit alpha) tail = 2
        calc
          overlapWeight (blockExit alpha) tail =
              overlapWeight (blockExit alpha) (door (blockExit alpha)) := by rw [hdoor]
          _ = 2 := door_has_weight_two (k := k) _ (by omega)
  · intro heq
    change inverseRotation (inverseRotation tail) = blockExit alpha at heq
    have hdoor' : door (inverseRotation (inverseRotation tail)) = tail := by
      rw [heq]
      exact hdoor
    exact doubleRotation_ne_door (by omega) _ (hdouble.trans hdoor'.symm)

/-- Frozen Lemma `doors`(2): the two weight-two successors of a component
head, their exact displayed forms, both class memberships, and their
distinctness. -/
theorem pathForestComponent_weightTwo_successors (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    let omegaEntry := pathForestComponentLastBlockEntry (by omega) P C
    let head := pathForestComponentHead (by omega) P C
    let beta := pathForestComponentExitDoor hk P C
    (∀ v : PermutationVertex k, head ≠ v →
      (overlapWeight head v = 2 ↔
        v = rotation omegaEntry ∨ v = beta)) ∧
      doubleRotation head = rotation omegaEntry ∧
      door head = beta ∧
      rotation omegaEntry ∈ rotationClass omegaEntry ∧
      beta ∈ rotationClass beta ∧
      rotation omegaEntry ≠ beta := by
  dsimp only
  let omegaEntry := pathForestComponentLastBlockEntry (by omega) P C
  let head := pathForestComponentHead (by omega) P C
  let beta := pathForestComponentExitDoor hk P C
  have hhead : head = blockExit omegaEntry := by
    simpa [head, omegaEntry] using
      pathForestComponentHead_eq_blockExit_lastBlockEntry (by omega) P C
  have hdouble : doubleRotation head = rotation omegaEntry := by
    rw [hhead, doubleRotation_blockExit (by omega)]
  have hdoor : door head = beta := by
    rw [hhead, door_blockExit (by omega)]
    rfl
  refine ⟨?_, hdouble, hdoor, rotation_mem_entryClass (by omega) omegaEntry,
    self_mem_rotationClass (by omega) beta, ?_⟩
  · intro v hne
    rw [weight_two_successors head v (by omega) hne, hdouble, hdoor]
  · simpa [beta] using blockExit_weight_two_successors_distinct (by omega) omegaEntry

/-! ## Component membership and endpoint bridges -/

set_option backward.isDefEq.respectTransparency false in
/-- Every block belonging to a forest run is a vertex of that run's
component. -/
theorem pathForestRun_block_mem_component (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P)
    {u : PermutationVertex k} (hu : u ∈ r.blocks) :
    u ∈ weakComponentVertices r.component := by
  let entries := pathForestComponentBlockEntries (by omega) P r.component
  let p := pathForestComponentPath (by omega) P r.component
  have huEntries : u ∈ entries := by
    change u ∈ pathForestComponentBlockEntries (by omega) P r.component
    rw [← pathForestComponentRuns_spec hk P r.component |>.1]
    exact List.mem_flatten.mpr ⟨r.blocks, r.isRun, hu⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp huEntries
  have hentry : entries.get i =
      p.vertex ⟨k * i.1, by
        rw [blockAligned_length_eq
          (pathForestComponentPath_blockAligned (by omega) P r.component)]
        exact Nat.mul_lt_mul_of_pos_left (by
          simpa [entries] using i.2) (by omega)⟩ := by
    simp [entries, p, pathForestComponentBlockEntries]
  rw [← pathForestComponentPath_vertexSet (by omega) P r.component]
  apply List.mem_toFinset.mpr
  rw [← hi, hentry]
  exact p.vertex_mem _

/-- Every rotation class recorded as occupied by a run lies wholly in its
component. -/
theorem pathForestRun_occupiedClass_subset_component (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P)
    {B : Finset (PermutationVertex k)} (hB : B ∈ r.occupiedClasses) :
    B ⊆ weakComponentVertices r.component := by
  classical
  change B ∈ r.blocks.toFinset.image rotationClass at hB
  obtain ⟨u, huSet, huB⟩ := Finset.mem_image.mp hB
  have huBlocks : u ∈ r.blocks := List.mem_toFinset.mp huSet
  have huComponent := pathForestRun_block_mem_component hk P r huBlocks
  intro v hv
  have hvClass : v ∈ rotationClass u := by simpa [huB] using hv
  exact pathForest_component_contains_rotationClass (by omega) P r.component
    (mem_weakComponentVertices.mp huComponent) hvClass

/-- A run occupies exactly as many rotation classes as it has blocks. -/
theorem pathForestRun_occupiedClasses_card (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    r.occupiedClasses.card = r.length := by
  classical
  rw [pathForestRun_occupiedClasses_eq_slots hk P r]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    exact runMap_rotationClasses_injective (by omega) r.entry
      ((Finset.mem_range.mp hi).trans_le (pathForestRun_length_le hk P r))
      ((Finset.mem_range.mp hj).trans_le (pathForestRun_length_le hk P r)) hij

/-- Applying `τ₂` once after the final block of a run is its `length`th
iterate from the run entry. -/
theorem pathForestRun_nextAfterLastEntry (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    runMapPower (by omega) r.length r.entry =
      runMap (by omega) r.lastEntry := by
  have hpos := pathForestRun_length_pos hk P r
  rw [pathForestRun_lastEntry_eq_runMapPower hk P r]
  calc
    runMapPower (by omega) r.length r.entry =
        runMapPower (by omega) ((r.length - 1) + 1) r.entry := by
      congr 2
      omega
    _ = runMap (by omega)
        (runMapPower (by omega) (r.length - 1) r.entry) := by
      simpa [runMapPower, Nat.succ_eq_add_one] using
        Function.iterate_succ_apply' (runMap (by omega)) (r.length - 1) r.entry

/-- The first run begins one `τ₂` step after the entrance door. -/
theorem pathForestComponentFirstRun_entry_eq_runMap_entranceDoor
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentFirstRun hk P C).entry =
      runMap (by omega) (pathForestComponentEntranceDoor hk P C) := by
  rw [pathForestComponentFirstRun_entry_eq_tail,
    pathForestComponentEntranceDoor_eq, runMap_runMapInverse (by omega)]

/-- The next `τ₂` entry after the last run is exactly the exit door. -/
theorem pathForestComponentLastRun_next_eq_exitDoor
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    runMapPower (by omega) (pathForestComponentLastRun hk P C).length
        (pathForestComponentLastRun hk P C).entry =
      pathForestComponentExitDoor hk P C := by
  rw [pathForestRun_nextAfterLastEntry hk P,
    pathForestComponentLastRun_lastEntry_eq_lastBlockEntry]
  rfl

/-- The exact meaning of the frozen phrase that `[α_p]` is not a class of
the component.  Components contain whole rotation classes, so non-containment
is the appropriate class-level predicate. -/
def EntranceDoorClassOutside (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : Prop :=
  ¬rotationClass (pathForestComponentEntranceDoor hk P C) ⊆
    weakComponentVertices C

private theorem componentTail_mem_vertices (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentTail (by omega) P C ∈ weakComponentVertices C := by
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  exact List.mem_toFinset.mpr
    ((pathForestComponentPath (by omega) P C).vertex_mem
      ⟨0, (pathForestComponentPath (by omega) P C).length_pos⟩)

private theorem doubleInverseTail_mem_component (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    inverseRotation
        (inverseRotation (pathForestComponentTail (by omega) P C)) ∈
      weakComponentVertices C := by
  have htail := componentTail_mem_vertices hk P C
  exact pathForest_component_contains_rotationClass (by omega) P C
    (mem_weakComponentVertices.mp htail)
    (doubleInverse_mem_rotationClass (by omega) _)

/-- The entrance-door class is outside exactly when its block exit is an
outside vertex. -/
theorem entranceDoorClassOutside_iff_blockExit_outside (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    EntranceDoorClassOutside hk P C ↔
      blockExit (pathForestComponentEntranceDoor hk P C) ∈
        pathForestComponentOutsideVertices (by omega) P C := by
  let alpha := pathForestComponentEntranceDoor hk P C
  constructor
  · intro houtsideClass
    apply (mem_pathForestComponentOutsideVertices_iff (by omega) P C _).mpr
    intro hblock
    apply houtsideClass
    have hsubset := pathForest_component_contains_rotationClass (by omega) P C
      (mem_weakComponentVertices.mp hblock)
    have hclass : rotationClass (blockExit alpha) = rotationClass alpha :=
      rotationClass_eq_of_mem (by omega)
        (inverseRotation_mem_rotationClass (by omega) alpha)
    change rotationClass (blockExit alpha) ⊆ weakComponentVertices C at hsubset
    rw [hclass] at hsubset
    exact hsubset
  · intro hblockOutside hclass
    have hnot :=
      (mem_pathForestComponentOutsideVertices_iff (by omega) P C _).mp
        hblockOutside
    apply hnot
    exact hclass (inverseRotation_mem_rotationClass (by omega) alpha)

/-! ## Frozen Lemma `doors`(3) -/

/-- For every nonspanning component, `minto = 2` exactly when the entrance
door class is outside.  The lower bound is included explicitly, including for
a nonspanning root. -/
theorem pathForestComponent_minto_eq_two_iff (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hC : weakComponentVertices C ≠
      (Finset.univ : Finset (PermutationVertex k))) :
    2 ≤ pathForestMinto (by omega) P C hC ∧
      (pathForestMinto (by omega) P C hC = 2 ↔
        EntranceDoorClassOutside hk P C) := by
  let tail := pathForestComponentTail (by omega) P C
  let alpha := pathForestComponentEntranceDoor hk P C
  have hlower := (pathForestMinto_bounds (by omega) P C hC).1
  refine ⟨hlower, ?_⟩
  constructor
  · intro hminto
    obtain ⟨u, huOutside, huWeight⟩ :=
      pathForestMinto_attained (by omega) P C hC
    have huNotComponent : u ∉ weakComponentVertices C :=
      (mem_pathForestComponentOutsideVertices_iff (by omega) P C u).mp huOutside
    have htailComponent := componentTail_mem_vertices hk P C
    have hune : u ≠ tail := by
      intro h
      apply huNotComponent
      simpa [tail, h] using htailComponent
    have hweight : overlapWeight u tail = 2 := by
      simpa [tail, hminto] using huWeight
    rcases ((pathForestComponent_weightTwo_predecessors hk P C).1 u
      (by simpa [tail] using hune)).mp hweight with hdouble | hblock
    · exfalso
      apply huNotComponent
      rw [hdouble]
      exact doubleInverseTail_mem_component hk P C
    · apply (entranceDoorClassOutside_iff_blockExit_outside hk P C).mpr
      simpa [alpha, hblock] using huOutside
  · intro houtsideClass
    have hblockOutside : blockExit alpha ∈
        pathForestComponentOutsideVertices (by omega) P C := by
      simpa [alpha] using
        (entranceDoorClassOutside_iff_blockExit_outside hk P C).mp houtsideClass
    have hmintoLe := pathForestMinto_le (by omega) P C hC hblockOutside
    have hweight : overlapWeight (blockExit alpha) tail = 2 := by
      have hdoor := blockExit_entranceDoor_is_door_preimage hk P C
      change overlapWeight (blockExit alpha) tail = 2
      rw [← show door (blockExit alpha) = tail by simpa [alpha, tail] using hdoor]
      exact door_has_weight_two (k := k) _ (by omega)
    rw [hweight] at hmintoLe
    omega

/-- In the `minto = 2` case, the external weight-two predecessor is genuinely
unique and is exactly `ex(α_p)`. -/
theorem pathForestComponent_unique_external_weightTwo_predecessor
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    ∃! u : PermutationVertex k,
      u ∈ pathForestComponentOutsideVertices (by omega) P C ∧
        overlapWeight u (pathForestComponentTail (by omega) P C) = 2 := by
  let tail := pathForestComponentTail (by omega) P C
  let alpha := pathForestComponentEntranceDoor hk P C
  have hblockOutside : blockExit alpha ∈
      pathForestComponentOutsideVertices (by omega) P C := by
    simpa [alpha] using
      (entranceDoorClassOutside_iff_blockExit_outside hk P C).mp houtside
  have hweight : overlapWeight (blockExit alpha) tail = 2 := by
    have hdoor := blockExit_entranceDoor_is_door_preimage hk P C
    change overlapWeight (blockExit alpha) tail = 2
    rw [← show door (blockExit alpha) = tail by simpa [alpha, tail] using hdoor]
    exact door_has_weight_two (k := k) _ (by omega)
  refine ⟨blockExit alpha, ⟨hblockOutside, hweight⟩, ?_⟩
  intro u hu
  have huNotComponent : u ∉ weakComponentVertices C :=
    (mem_pathForestComponentOutsideVertices_iff (by omega) P C u).mp hu.1
  have hune : u ≠ tail := by
    intro h
    apply huNotComponent
    simpa [tail, h] using componentTail_mem_vertices hk P C
  rcases ((pathForestComponent_weightTwo_predecessors hk P C).1 u
    (by simpa [tail] using hune)).mp (by simpa [tail] using hu.2) with
    hdouble | hblock
  · exfalso
    apply huNotComponent
    rw [hdouble]
    exact doubleInverseTail_mem_component hk P C
  · simpa [alpha] using hblock

/-! ## Frozen Lemma `doors`(4) -/

/-- On a reduced minimum Hamiltonian path, every weight-two path edge leaving
a component head goes through the exit door. -/
theorem reducedPath_weightTwo_edge_from_componentHead (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (C : WeakComponent (pathForest (by omega) P))
    (e : DirectedOverlapEdge k) (heP : e ∈ P.edgeSet)
    (hsource : e.source = pathForestComponentHead (by omega) P C)
    (hweight : e.weight = 2) :
    e.target = pathForestComponentExitDoor hk P C := by
  let omegaEntry := pathForestComponentLastBlockEntry (by omega) P C
  let head := pathForestComponentHead (by omega) P C
  let beta := pathForestComponentExitDoor hk P C
  have hne : head ≠ e.target := by
    intro h
    apply e.ne
    exact hsource.trans h
  have hweight' : overlapWeight head e.target = 2 := by
    simpa [DirectedOverlapEdge.weight, head, hsource] using hweight
  have hdoors := pathForestComponent_weightTwo_successors hk P C
  rcases (hdoors.1 e.target hne).mp hweight' with hrotation | hbeta
  · exfalso
    apply hP.noDoubleRotationEdge
    refine ⟨e, heP, ?_⟩
    calc
      e.target = rotation omegaEntry := by simpa [omegaEntry] using hrotation
      _ = doubleRotation head := hdoors.2.1.symm
      _ = doubleRotation e.source := congrArg doubleRotation hsource.symm
  · simpa [beta] using hbeta

/-! ## Frozen door lemma -/

/-- Case (i) of the door lemma: a genuine one-run self-absorber. -/
def DoorSelfAbsorberCase (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P)) : Prop :=
  C = D ∧ pathForestComponentRunCount hk P C = 1 ∧
    (pathForestComponentFirstRun hk P C).length = k - 2 ∧
    (pathForestComponentLastRun hk P D).length = k - 2

/-- Case (ii) of the door lemma: two different runs whose lengths fit in the
`n-1 = k-2` slots away from the matched door. -/
def DoorSeparatedCase (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P)) : Prop :=
  pathForestComponentFirstRun hk P C ≠
      pathForestComponentLastRun hk P D ∧
    (pathForestComponentFirstRun hk P C).length +
      (pathForestComponentLastRun hk P D).length ≤ k - 2

private theorem componentBlockEntries_nodup (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (pathForestComponentBlockEntries_pairwiseDistinct (by omega) P C).imp
    (by
      intro u v hclasses huv
      exact hclasses (congrArg rotationClass huv))

private theorem list_length_eq_one_of_head_eq_getLast_of_flatten_nodup
    {α : Type*} {runs : List (List α)}
    (hruns : runs ≠ []) (hnil : [] ∉ runs)
    (hflat : runs.flatten.Nodup)
    (hends : runs.head hruns = runs.getLast hruns) :
    runs.length = 1 := by
  cases runs with
  | nil => exact (hruns rfl).elim
  | cons a tail =>
      cases tail with
      | nil => simp
      | cons b rest =>
          have ha : a ≠ [] := by
            intro ha
            apply hnil
            simp [ha]
          obtain ⟨x, xs, haeq⟩ := List.exists_cons_of_ne_nil ha
          have hx : x ∈ a := by simp [haeq]
          have hpairwise := (List.nodup_flatten.mp hflat).2
          have hdisjoint : List.Disjoint a ((b :: rest).getLast (by simp)) :=
            (List.pairwise_cons.mp hpairwise).1 _ (List.getLast_mem (by simp))
          have hsame : a = (b :: rest).getLast (by simp) := by
            simpa using hends
          rw [← hsame] at hdisjoint
          exact ((List.disjoint_left.mp hdisjoint) hx hx).elim

private theorem componentRunCount_eq_one_of_first_eq_last (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hends : pathForestComponentFirstRun hk P C =
      pathForestComponentLastRun hk P C) :
    pathForestComponentRunCount hk P C = 1 := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  have hnil : [] ∉ runs := (pathForestComponentRuns_spec hk P C).2.1
  have hflat : runs.flatten.Nodup := by
    rw [(pathForestComponentRuns_spec hk P C).1]
    exact componentBlockEntries_nodup hk P C
  have hblocks := congrArg PathForestRun.blocks hends
  have hheadLast : runs.head hruns = runs.getLast hruns := by
    simpa [pathForestComponentFirstRun, pathForestComponentLastRun, runs] using hblocks
  exact list_length_eq_one_of_head_eq_getLast_of_flatten_nodup
    hruns hnil hflat hheadLast

private theorem componentFirstRun_eq_lastRun_of_runCount_eq_one (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hcount : pathForestComponentRunCount hk P C = 1) :
    pathForestComponentFirstRun hk P C =
      pathForestComponentLastRun hk P C := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  have hcount' : runs.length = 1 := by
    simpa [runs, pathForestComponentRunCount] using hcount
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hcount'
  have ha' : pathForestComponentRuns hk P C = [a] := by
    simpa [runs] using ha
  unfold pathForestComponentFirstRun pathForestComponentLastRun
  simp [ha']

private theorem runMapPower_rotationClass_mem_occupied (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P)
    (i : ℕ) (hi : i < r.length) :
    rotationClass (runMapPower (by omega) i r.entry) ∈ r.occupiedClasses := by
  rw [pathForestRun_occupiedClasses_eq_slots hk P r]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private theorem firstRun_length_le_doorComplement (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    (pathForestComponentFirstRun hk P C).length ≤ k - 2 := by
  let r := pathForestComponentFirstRun hk P C
  let alpha := pathForestComponentEntranceDoor hk P C
  have hle := pathForestRun_length_le hk P r
  by_contra hnot
  have hnot' : ¬r.length ≤ k - 2 := by simpa [r] using hnot
  have hlength : r.length = k - 1 := by omega
  have hindex : k - 2 < r.length := by omega
  have hentry : r.entry = runMap (by omega) alpha := by
    simpa [r, alpha] using
      pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
  have hpower : runMapPower (by omega) (k - 2) r.entry = alpha := by
    calc
      runMapPower (by omega) (k - 2) r.entry =
          runMapPower (by omega) (k - 2) (runMap (by omega) alpha) :=
        congrArg (runMapPower (by omega) (k - 2)) hentry
      _ = runMapPower (by omega) ((k - 2) + 1) alpha :=
        runMapPower_runMap (by omega) (k - 2) alpha
      _ = runMapPower (by omega) (k - 1) alpha := by
        congr 2
        omega
      _ = alpha := (runMap_order_exact (by omega) alpha).1
  have hoccupied : rotationClass alpha ∈ r.occupiedClasses := by
    simpa [hpower] using runMapPower_rotationClass_mem_occupied hk P r (k - 2) hindex
  exact houtside
    (pathForestRun_occupiedClass_subset_component hk P r hoccupied)

private theorem lastRun_length_le_doorComplement (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hdoors : pathForestComponentExitDoor hk P D =
      pathForestComponentEntranceDoor hk P C) :
    (pathForestComponentLastRun hk P D).length ≤ k - 2 := by
  let r := pathForestComponentFirstRun hk P C
  let s := pathForestComponentLastRun hk P D
  let alpha := pathForestComponentEntranceDoor hk P C
  have hle := pathForestRun_length_le hk P s
  by_contra hnot
  have hnot' : ¬s.length ≤ k - 2 := by simpa [s] using hnot
  have hlength : s.length = k - 1 := by omega
  have hsNext : runMapPower (by omega) s.length s.entry = alpha := by
    calc
      runMapPower (by omega) s.length s.entry =
          pathForestComponentExitDoor hk P D := by
        simpa [s] using pathForestComponentLastRun_next_eq_exitDoor hk P D
      _ = alpha := by simpa [alpha] using hdoors
  have hsEntry : s.entry = alpha := by
    calc
      s.entry = runMapPower (by omega) (k - 1) s.entry :=
        (runMap_order_exact (by omega) s.entry).1.symm
      _ = runMapPower (by omega) s.length s.entry := by rw [hlength]
      _ = alpha := hsNext
  have hrEntry : r.entry = runMap (by omega) alpha := by
    simpa [r, alpha] using
      pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
  have hrTail : rotationClass (runMap (by omega) alpha) ∈ r.occupiedClasses := by
    have hrPos := pathForestRun_length_pos hk P r
    simpa [hrEntry, runMapPower] using
      runMapPower_rotationClass_mem_occupied hk P r 0 hrPos
  have hsTail : rotationClass (runMap (by omega) alpha) ∈ s.occupiedClasses := by
    have hsOne : 1 < s.length := by omega
    have hpowOne : runMapPower (by omega) 1 s.entry = runMap (by omega) alpha := by
      simp [runMapPower, hsEntry]
    simpa [hpowOne] using
      runMapPower_rotationClass_mem_occupied hk P s 1 hsOne
  have hrs : r = s :=
    pathForestRun_eq_of_shared_rotationClass hk P r s hrTail hsTail
  have hCD : C = D := congrArg PathForestRun.component hrs
  have hsAlpha : rotationClass alpha ∈ s.occupiedClasses := by
    have hsPos := pathForestRun_length_pos hk P s
    simpa [hsEntry, runMapPower] using
      runMapPower_rotationClass_mem_occupied hk P s 0 hsPos
  have hsubset := pathForestRun_occupiedClass_subset_component hk P s hsAlpha
  apply houtside
  change rotationClass alpha ⊆ weakComponentVertices D at hsubset
  rw [← hCD] at hsubset
  exact hsubset

private theorem doorSeparated_length_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hdoors : pathForestComponentExitDoor hk P D =
      pathForestComponentEntranceDoor hk P C)
    (hdisjoint : Disjoint
      (pathForestComponentFirstRun hk P C).occupiedClasses
      (pathForestComponentLastRun hk P D).occupiedClasses) :
    (pathForestComponentFirstRun hk P C).length +
      (pathForestComponentLastRun hk P D).length ≤ k - 2 := by
  classical
  let r := pathForestComponentFirstRun hk P C
  let s := pathForestComponentLastRun hk P D
  let alpha := pathForestComponentEntranceDoor hk P C
  let loop := twoLoop (by omega) (entrySatellite (by omega) alpha) (entryCore alpha)
  have hrLe := firstRun_length_le_doorComplement hk P C houtside
  have hsLe := lastRun_length_le_doorComplement hk P C D houtside hdoors
  have hrLe' : r.length ≤ k - 2 := by simpa [r] using hrLe
  have hsLe' : s.length ≤ k - 2 := by simpa [s] using hsLe
  have hdisjoint' : Disjoint r.occupiedClasses s.occupiedClasses := by
    simpa [r, s] using hdisjoint
  have hrEntry : r.entry = runMap (by omega) alpha := by
    simpa [r, alpha] using
      pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
  have hsNext : runMapPower (by omega) s.length s.entry = alpha := by
    calc
      runMapPower (by omega) s.length s.entry =
          pathForestComponentExitDoor hk P D := by
        simpa [s] using pathForestComponentLastRun_next_eq_exitDoor hk P D
      _ = alpha := by simpa [alpha] using hdoors
  have halphaNotR : rotationClass alpha ∉ r.occupiedClasses := by
    intro hmem
    exact houtside
      (pathForestRun_occupiedClass_subset_component hk P r hmem)
  have halphaNotS : rotationClass alpha ∉ s.occupiedClasses := by
    intro hmem
    rw [pathForestRun_occupiedClasses_eq_slots hk P s] at hmem
    obtain ⟨i, hiRange, hiClass⟩ := Finset.mem_image.mp hmem
    have hi : i < s.length := Finset.mem_range.mp hiRange
    have hinj := runMap_rotationClasses_injective (by omega) s.entry
    have heq : i = s.length := hinj
      (hi.trans_le (pathForestRun_length_le hk P s))
      ((show s.length < k - 1 by omega)) (by
        calc
          rotationClass (runMapPower (by omega) i s.entry) =
              rotationClass alpha := hiClass
          _ = rotationClass (runMapPower (by omega) s.length s.entry) :=
            congrArg rotationClass hsNext.symm)
    omega
  have hrSubset : r.occupiedClasses ⊆ loop := by
    have hbase := pathForestRun_occupiedClasses_subset_twoLoop hk P r
    have hsat : entrySatellite (by omega) r.entry =
        entrySatellite (by omega) alpha := by
      rw [hrEntry, runMap_satellite (by omega)]
    have hcore : entryCore r.entry = entryCore alpha := by
      rw [hrEntry]
      simpa [runMapPower, Function.iterate_one] using
        runMapPower_core (by omega) 1 alpha
    simpa [loop, hsat, hcore] using hbase
  have hsSubset : s.occupiedClasses ⊆ loop := by
    have hbase := pathForestRun_occupiedClasses_subset_twoLoop hk P s
    have hsatPower := runMapPower_satellite (by omega) s.length s.entry
    have hsat : entrySatellite (by omega) s.entry =
        entrySatellite (by omega) alpha := by
      rw [hsNext] at hsatPower
      exact hsatPower.symm
    have hcorePower := runMapPower_core (by omega) s.length s.entry
    have hcore : entryCore s.entry = entryCore alpha := by
      rw [hsNext] at hcorePower
      exact hcorePower.symm
    simpa [loop, hsat, hcore] using hbase
  have halphaLoop : rotationClass alpha ∈ loop := by
    change rotationClass alpha ∈
      twoLoop (by omega) (entrySatellite (by omega) alpha) (entryCore alpha)
    rw [twoLoop_eq_runMapOrbitClasses (by omega)]
    exact (mem_runMapOrbitClasses (by omega) alpha (rotationClass alpha)).mpr
      ⟨0, by omega, by simp [runMapPower]⟩
  have hunionSubset :
      insert (rotationClass alpha) (r.occupiedClasses ∪ s.occupiedClasses) ⊆ loop := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hUnion
    · exact halphaLoop
    · rcases Finset.mem_union.mp hUnion with hR | hS
      · exact hrSubset hR
      · exact hsSubset hS
  have halphaNotUnion :
      rotationClass alpha ∉ r.occupiedClasses ∪ s.occupiedClasses := by
    simp [halphaNotR, halphaNotS]
  have hcardLe := Finset.card_le_card hunionSubset
  have hcardInsert := Finset.card_insert_of_notMem halphaNotUnion
  have hcardUnion := Finset.card_union_of_disjoint hdisjoint'
  have hrCard := pathForestRun_occupiedClasses_card hk P r
  have hsCard := pathForestRun_occupiedClasses_card hk P s
  have hloopCard : loop.card = k - 1 := by
    simpa [loop] using twoLoop_card (by omega) alpha
  have hunionCard :
      (r.occupiedClasses ∪ s.occupiedClasses).card = r.length + s.length := by
    rw [hcardUnion, hrCard, hsCard]
  have hinsertCard :
      (insert (rotationClass alpha)
        (r.occupiedClasses ∪ s.occupiedClasses)).card =
        r.length + s.length + 1 := by
    rw [hcardInsert, hunionCard]
  rw [hinsertCard, hloopCard] at hcardLe
  simpa [r, s] using (show r.length + s.length ≤ k - 2 by omega)

/-- Frozen Lemma `door`.  The components are deliberately not assumed
distinct.  The conclusion is a genuinely exclusive dichotomy, not a bare
disjunction. -/
theorem pathForestComponent_door_exactlyOne (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hdoors : pathForestComponentExitDoor hk P D =
      pathForestComponentEntranceDoor hk P C) :
    (DoorSelfAbsorberCase hk P C D ∧ ¬DoorSeparatedCase hk P C D) ∨
      (DoorSeparatedCase hk P C D ∧ ¬DoorSelfAbsorberCase hk P C D) := by
  let r := pathForestComponentFirstRun hk P C
  let s := pathForestComponentLastRun hk P D
  have hrLe := firstRun_length_le_doorComplement hk P C houtside
  have hrLe' : r.length ≤ k - 2 := by simpa [r] using hrLe
  have hsNext : runMapPower (by omega) s.length s.entry =
      pathForestComponentEntranceDoor hk P C := by
    calc
      runMapPower (by omega) s.length s.entry =
          pathForestComponentExitDoor hk P D := by
        simpa [s] using pathForestComponentLastRun_next_eq_exitDoor hk P D
      _ = pathForestComponentEntranceDoor hk P C := hdoors
  by_cases hrs : r = s
  · left
    have hCD : C = D := congrArg PathForestRun.component hrs
    have hlengthR : r.length = k - 2 := by
      by_contra hne
      have hlt : r.length + 1 < k - 1 := by omega
      have hrEntry : r.entry =
          runMap (by omega) (pathForestComponentEntranceDoor hk P C) := by
        simpa [r] using
          pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
      have hpower : runMapPower (by omega) (r.length + 1)
          (pathForestComponentEntranceDoor hk P C) =
          pathForestComponentEntranceDoor hk P C := by
        calc
          runMapPower (by omega) (r.length + 1)
              (pathForestComponentEntranceDoor hk P C) =
              runMapPower (by omega) r.length r.entry := by
            rw [hrEntry, runMapPower_runMap (by omega)]
          _ = runMapPower (by omega) s.length s.entry := by rw [hrs]
          _ = pathForestComponentEntranceDoor hk P C := hsNext
      have hinj := runMap_rotationClasses_injective (by omega)
        (pathForestComponentEntranceDoor hk P C)
      have hzero : (0 : ℕ) < k - 1 := by omega
      have hclasses :
          rotationClass (runMapPower (by omega) (r.length + 1)
            (pathForestComponentEntranceDoor hk P C)) =
          rotationClass (runMapPower (by omega) 0
            (pathForestComponentEntranceDoor hk P C)) := by
        calc
          rotationClass (runMapPower (by omega) (r.length + 1)
              (pathForestComponentEntranceDoor hk P C)) =
              rotationClass (pathForestComponentEntranceDoor hk P C) :=
            congrArg rotationClass hpower
          _ = rotationClass (runMapPower (by omega) 0
              (pathForestComponentEntranceDoor hk P C)) := by
            simp [runMapPower]
      have hbad : r.length + 1 = 0 := hinj hlt hzero hclasses
      omega
    have hlengthS : s.length = k - 2 := by rw [← hrs, hlengthR]
    have hcount : pathForestComponentRunCount hk P C = 1 := by
      have hends : pathForestComponentFirstRun hk P C =
          pathForestComponentLastRun hk P C := by
        simpa [r, s, hCD] using hrs
      exact componentRunCount_eq_one_of_first_eq_last hk P C hends
    refine ⟨?_, ?_⟩
    · exact ⟨hCD, hcount, by simpa [r] using hlengthR,
        by simpa [s] using hlengthS⟩
    · intro hsep
      exact hsep.1 hrs
  · right
    have hdisjoint : Disjoint r.occupiedClasses s.occupiedClasses := by
      rcases pathForestRun_eq_or_disjoint_occupiedClasses hk P r s with heq | hdisj
      · exact (hrs heq).elim
      · exact hdisj
    have hbound := doorSeparated_length_bound hk P C D houtside hdoors hdisjoint
    refine ⟨⟨hrs, by simpa [r, s] using hbound⟩, ?_⟩
    intro hself
    have hCD := hself.1
    subst D
    have hfirstLast := componentFirstRun_eq_lastRun_of_runCount_eq_one
      hk P C hself.2.1
    exact hrs (by simpa [r, s] using hfirstLast)

/-! ## No-absorption corollaries and case-(ii) numbers -/

/-- Frozen Corollary `fullnoabsorb`: a full last run cannot feed any
component whose entrance-door class is outside. -/
theorem fullLastRun_noAbsorption (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hfull : (pathForestComponentLastRun hk P D).IsFull) :
    pathForestComponentExitDoor hk P D ≠
      pathForestComponentEntranceDoor hk P C := by
  intro hdoors
  rcases pathForestComponent_door_exactlyOne hk P C D houtside hdoors with
    ⟨hself, _⟩ | ⟨hsep, _⟩
  · have hlast : (pathForestComponentLastRun hk P D).length = k - 2 :=
      hself.2.2.2
    change (pathForestComponentLastRun hk P D).length = k - 1 at hfull
    omega
  · have hfirstPos := pathForestRun_length_pos hk P
      (pathForestComponentFirstRun hk P C)
    have hbound :
        (pathForestComponentFirstRun hk P C).length +
          (pathForestComponentLastRun hk P D).length ≤ k - 2 := by
      exact hsep.2
    change (pathForestComponentLastRun hk P D).length = k - 1 at hfull
    omega

private theorem rotationClass_lastEntry_mem_occupied (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    rotationClass r.lastEntry ∈ r.occupiedClasses := by
  have hpos := pathForestRun_length_pos hk P r
  have hlast : r.length - 1 < r.length := Nat.sub_lt hpos (by omega)
  have hmem := runMapPower_rotationClass_mem_occupied hk P r
    (r.length - 1) hlast
  rw [pathForestRun_lastEntry_eq_runMapPower hk P r]
  exact hmem

/-- Frozen Corollary `deficitone`: if the first deficit is one and the
component has at least two runs, no exit door can equal its entrance door.

This theorem does not assume the entrance-door class is outside; its proof is
the direct shared-slot argument required by the statement. -/
theorem deficitOne_multiRun_noAbsorption (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hdeficit : pathForestComponentFirstDeficit hk P C = 1)
    (hruns : 2 ≤ pathForestComponentRunCount hk P C)
    (D : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentExitDoor hk P D ≠
      pathForestComponentEntranceDoor hk P C := by
  intro hdoors
  let r := pathForestComponentFirstRun hk P C
  let s := pathForestComponentLastRun hk P D
  let alpha := pathForestComponentEntranceDoor hk P C
  have hrLe := pathForestRun_length_le hk P r
  have hrDeficit : (k - 1) - r.length = 1 := by
    rw [← PathForestRun.deficit]
    rw [← pathForestComponentFirstDeficit_eq_firstRun_deficit hk P C]
    exact hdeficit
  have hrLength : r.length = k - 2 := by omega
  have hrEntry : r.entry = runMap (by omega) alpha := by
    simpa [r, alpha] using
      pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
  have hrIndex : k - 3 < r.length := by omega
  have hrPower : runMapPower (by omega) (k - 3) r.entry =
      runMapInverse (by omega) alpha := by
    calc
      runMapPower (by omega) (k - 3) r.entry =
          runMapPower (by omega) (k - 3) (runMap (by omega) alpha) :=
        congrArg (runMapPower (by omega) (k - 3)) hrEntry
      _ = runMapPower (by omega) ((k - 3) + 1) alpha :=
        runMapPower_runMap (by omega) (k - 3) alpha
      _ = runMapPower (by omega) (k - 2) alpha := by
        congr 2
        omega
      _ = runMapInverse (by omega) alpha :=
        runMapPower_pred_eq_runMapInverse (by omega) alpha
  have hrShared : rotationClass (runMapInverse (by omega) alpha) ∈
      r.occupiedClasses := by
    simpa [hrPower] using
      runMapPower_rotationClass_mem_occupied hk P r (k - 3) hrIndex
  have hsLast : s.lastEntry = runMapInverse (by omega) alpha := by
    calc
      s.lastEntry = pathForestComponentLastBlockEntry (by omega) P D := by
        simpa [s] using
          pathForestComponentLastRun_lastEntry_eq_lastBlockEntry hk P D
      _ = runMapInverse (by omega)
          (runMap (by omega)
            (pathForestComponentLastBlockEntry (by omega) P D)) :=
        (runMapInverse_runMap (by omega) _).symm
      _ = runMapInverse (by omega)
          (pathForestComponentExitDoor hk P D) := by rfl
      _ = runMapInverse (by omega) alpha :=
        congrArg (runMapInverse (by omega)) (by simpa [alpha] using hdoors)
  have hsShared : rotationClass (runMapInverse (by omega) alpha) ∈
      s.occupiedClasses := by
    simpa [hsLast] using rotationClass_lastEntry_mem_occupied hk P s
  have hrsEq : r = s :=
    pathForestRun_eq_of_shared_rotationClass hk P r s hrShared hsShared
  have hCD : C = D := congrArg PathForestRun.component hrsEq
  have hfirstLast : pathForestComponentFirstRun hk P C =
      pathForestComponentLastRun hk P C := by
    simpa [r, s, hCD] using hrsEq
  have hcount := componentRunCount_eq_one_of_first_eq_last hk P C hfirstLast
  omega

/-- Frozen Corollary `caseiinumbers`: all three numerical consequences of
the separated door case. -/
theorem doorSeparated_deficit_bounds (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C D : WeakComponent (pathForest (by omega) P))
    (hcase : DoorSeparatedCase hk P C D) :
    2 ≤ pathForestComponentFirstDeficit hk P C ∧
      2 ≤ pathForestComponentLastDeficit hk P D ∧
      k ≤ pathForestComponentFirstDeficit hk P C +
        pathForestComponentLastDeficit hk P D := by
  let r := pathForestComponentFirstRun hk P C
  let s := pathForestComponentLastRun hk P D
  have hrPos := pathForestRun_length_pos hk P r
  have hsPos := pathForestRun_length_pos hk P s
  have hbound : r.length + s.length ≤ k - 2 := by
    simpa [DoorSeparatedCase, r, s] using hcase.2
  have hrLe := pathForestRun_length_le hk P r
  have hsLe := pathForestRun_length_le hk P s
  rw [pathForestComponentFirstDeficit_eq_firstRun_deficit hk P C,
    pathForestComponentLastDeficit_eq_lastRun_deficit hk P D]
  change 2 ≤ (k - 1) - r.length ∧
    2 ≤ (k - 1) - s.length ∧
    k ≤ ((k - 1) - r.length) + ((k - 1) - s.length)
  omega

/-! ## The literal `k = 5` self-absorber -/

private def k5Symbol1 : Alphabet 5 := ⟨1, by simp⟩
private def k5Symbol2 : Alphabet 5 := ⟨2, by simp⟩
private def k5Symbol3 : Alphabet 5 := ⟨3, by simp⟩
private def k5Symbol4 : Alphabet 5 := ⟨4, by simp⟩
private def k5Symbol5 : Alphabet 5 := ⟨5, by simp⟩

private def k5BaseWord : Word 5 :=
  [k5Symbol1, k5Symbol2, k5Symbol3, k5Symbol4, k5Symbol5]

private theorem k5BaseWord_perm_alphabet :
    k5BaseWord.Perm (alphabetWord 5) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · decide
  · exact Finset.nodup_toList _
  · calc
      k5BaseWord.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro x
        have hx := x.property
        simp only [Finset.mem_Icc] at hx
        have hcases :
            x.1 = 1 ∨ x.1 = 2 ∨ x.1 = 3 ∨ x.1 = 4 ∨ x.1 = 5 := by
          omega
        simp only [List.mem_toFinset, k5BaseWord, List.mem_cons,
          List.not_mem_nil, or_false]
        rcases hcases with h | h | h | h | h
        · exact Or.inl (by apply Subtype.ext; exact h)
        · exact Or.inr (Or.inl (by apply Subtype.ext; exact h))
        · exact Or.inr (Or.inr (Or.inl (by apply Subtype.ext; exact h)))
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl (by apply Subtype.ext; exact h))))
        · exact Or.inr (Or.inr (Or.inr
            (Or.inr (by apply Subtype.ext; exact h))))
      _ = (alphabetWord 5).toFinset := by simp [alphabetWord]

/-- The first displayed block entry `12345`. -/
def selfAbsorberEntry12345 : PermutationVertex 5 :=
  ⟨k5BaseWord, k5BaseWord_perm_alphabet⟩

/-- The second displayed block entry `23415`. -/
def selfAbsorberEntry23415 : PermutationVertex 5 :=
  runMap (by omega) selfAbsorberEntry12345

/-- The third displayed block entry `34125`. -/
def selfAbsorberEntry34125 : PermutationVertex 5 :=
  runMap (by omega) selfAbsorberEntry23415

/-- The common entrance and exit door `41235`. -/
def selfAbsorberDoor41235 : PermutationVertex 5 :=
  runMapInverse (by omega) selfAbsorberEntry12345

/-- The three block entries of the displayed witness, in order. -/
def selfAbsorberBlockEntries : List (PermutationVertex 5) :=
  [selfAbsorberEntry12345, selfAbsorberEntry23415,
    selfAbsorberEntry34125]

/-- Literal word check for all three stated block entries and the common door. -/
theorem selfAbsorber_literal_words :
    selfAbsorberEntry12345.1.map (fun x => x.1) = [1, 2, 3, 4, 5] ∧
      selfAbsorberEntry23415.1.map (fun x => x.1) = [2, 3, 4, 1, 5] ∧
      selfAbsorberEntry34125.1.map (fun x => x.1) = [3, 4, 1, 2, 5] ∧
      selfAbsorberDoor41235.1.map (fun x => x.1) = [4, 1, 2, 3, 5] := by
  simp [selfAbsorberEntry12345, selfAbsorberEntry23415,
    selfAbsorberEntry34125, selfAbsorberDoor41235, k5BaseWord,
    k5Symbol1, k5Symbol2, k5Symbol3, k5Symbol4, k5Symbol5,
    runMap, runMapInverse, entrySatellite]

/-- The three displayed entries form one `τ₂`-run of length `n-1=3`. -/
theorem selfAbsorber_three_block_run :
    selfAbsorberBlockEntries.IsChain
        (fun u v => v = runMap (by omega) u) ∧
      selfAbsorberBlockEntries.length = 3 ∧ 3 = 5 - 2 := by
  simp [selfAbsorberBlockEntries, selfAbsorberEntry23415,
    selfAbsorberEntry34125]

/-- Frozen Example `selfabsorber`: `α = β = 41235`, and its rotation class
is none of the three occupied classes. -/
theorem selfAbsorber_alpha_eq_beta :
    runMapInverse (by omega) selfAbsorberEntry12345 =
        selfAbsorberDoor41235 ∧
      runMap (by omega) selfAbsorberEntry34125 =
        selfAbsorberDoor41235 ∧
      rotationClass selfAbsorberDoor41235 ∉
        selfAbsorberBlockEntries.map rotationClass := by
  refine ⟨rfl, ?_, ?_⟩
  · calc
      runMap (by omega) selfAbsorberEntry34125 =
          runMapPower (by omega) 3 selfAbsorberEntry12345 := by
        simp [selfAbsorberEntry34125, selfAbsorberEntry23415,
          runMapPower, Function.iterate_succ_apply']
      _ = runMapInverse (by omega) selfAbsorberEntry12345 :=
        runMapPower_pred_eq_runMapInverse (k := 5) (by omega) _
      _ = selfAbsorberDoor41235 := rfl
  · simp only [selfAbsorberBlockEntries, List.mem_map, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro ⟨u, (rfl | rfl | rfl), hclass⟩
    · have hinj := runMap_rotationClasses_injective (k := 5) (by omega)
        selfAbsorberEntry12345
      have hdoorPower : selfAbsorberDoor41235 =
          runMapPower (by omega) 3 selfAbsorberEntry12345 := by
        symm
        exact runMapPower_pred_eq_runMapInverse (k := 5) (by omega) _
      have hbad : (0 : ℕ) = 3 := hinj
        (show (0 : ℕ) ∈ Set.Iio (5 - 1) by norm_num)
        (show (3 : ℕ) ∈ Set.Iio (5 - 1) by norm_num) (by
        simpa [hdoorPower, runMapPower] using hclass)
      omega
    · have hinj := runMap_rotationClasses_injective (k := 5) (by omega)
        selfAbsorberEntry12345
      have hdoorPower : selfAbsorberDoor41235 =
          runMapPower (by omega) 3 selfAbsorberEntry12345 := by
        symm
        exact runMapPower_pred_eq_runMapInverse (k := 5) (by omega) _
      have hentryPower : selfAbsorberEntry23415 =
          runMapPower (by omega) 1 selfAbsorberEntry12345 := by
        rfl
      have hbad : (1 : ℕ) = 3 := hinj
        (show (1 : ℕ) ∈ Set.Iio (5 - 1) by norm_num)
        (show (3 : ℕ) ∈ Set.Iio (5 - 1) by norm_num) (by
        simpa [hdoorPower, hentryPower] using hclass)
      omega
    · have hinj := runMap_rotationClasses_injective (k := 5) (by omega)
        selfAbsorberEntry12345
      have hdoorPower : selfAbsorberDoor41235 =
          runMapPower (by omega) 3 selfAbsorberEntry12345 := by
        symm
        exact runMapPower_pred_eq_runMapInverse (k := 5) (by omega) _
      have hentryPower : selfAbsorberEntry34125 =
          runMapPower (by omega) 2 selfAbsorberEntry12345 := by
        simp [selfAbsorberEntry34125, selfAbsorberEntry23415,
          runMapPower, Function.iterate_succ_apply']
      have hbad : (2 : ℕ) = 3 := hinj
        (show (2 : ℕ) ∈ Set.Iio (5 - 1) by norm_num)
        (show (3 : ℕ) ∈ Set.Iio (5 - 1) by norm_num) (by
        simpa [hdoorPower, hentryPower] using hclass)
      omega

/-! ## The deleted edge at a new full-run head -/

private theorem d2Component_length_eq_entries_length (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentPath (by omega) P C).length =
      k * (pathForestComponentBlockEntries (by omega) P C).length := by
  rw [blockAligned_length_eq
    (pathForestComponentPath_blockAligned (by omega) P C)]
  congr 1
  exact (pathForestComponentBlockEntries_length (by omega) P C).symm

private theorem d2Component_boundary_index_lt (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    k * j + (k - 1) + 1 <
      (pathForestComponentPath (by omega) P C).length := by
  rw [d2Component_length_eq_entries_length hk P C]
  have hmul := Nat.mul_lt_mul_of_pos_left hj (show 0 < k by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

private noncomputable def d2ComponentBoundaryEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    DirectedOverlapEdge k :=
  (pathForestComponentPath (by omega) P C).edgeAt
    (k * j + (k - 1)) (d2Component_boundary_index_lt hk P C j hj)

private theorem d2Component_entry_eq_vertex (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (pathForestComponentBlockEntries (by omega) P C).get ⟨j, hj⟩ =
      (pathForestComponentPath (by omega) P C).vertex
        ⟨k * j, by
          rw [d2Component_length_eq_entries_length hk P C]
          exact Nat.mul_lt_mul_of_pos_left hj (by omega)⟩ := by
  simp [pathForestComponentBlockEntries]

private theorem d2ComponentBoundaryEdge_source (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (d2ComponentBoundaryEdge hk P C j hj).source =
      blockExit ((pathForestComponentBlockEntries (by omega) P C).get
        ⟨j, by omega⟩) := by
  let p := pathForestComponentPath (by omega) P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hposPlus : k * j + (k - 1) + 1 < p.length := by
    simpa [p] using d2Component_boundary_index_lt hk P C j hj
  have hpos : k * j + (k - 1) < p.length := by omega
  have hbase : k * j < p.length := by omega
  have hj0 : j < entries.length := by
    change j < (pathForestComponentBlockEntries (by omega) P C).length
    omega
  have hblock := exitless_block_vertex
    (pathForestComponentPath_blockAligned (by omega) P C).1
    (by omega : 3 ≤ k) j (k - 1) (by omega) hpos
  have hentry : entries.get ⟨j, hj0⟩ =
      p.vertex ⟨k * j, hbase⟩ := by
    simpa [p, entries] using d2Component_entry_eq_vertex hk P C j (by omega)
  change p.vertex ⟨k * j + (k - 1), hpos⟩ =
    blockExit (entries.get ⟨j, hj0⟩)
  calc
    p.vertex ⟨k * j + (k - 1), hpos⟩ =
        rotationPower (k - 1) (p.vertex ⟨k * j, hbase⟩) := hblock
    _ = rotationPower (k - 1) (entries.get ⟨j, hj0⟩) :=
      congrArg (rotationPower (k - 1)) hentry.symm
    _ = blockExit (entries.get ⟨j, hj0⟩) :=
      rotationPower_pred_eq_blockExit (by omega) _

private theorem d2ComponentBoundaryEdge_target (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (d2ComponentBoundaryEdge hk P C j hj).target =
      (pathForestComponentBlockEntries (by omega) P C).get
        ⟨j + 1, hj⟩ := by
  let p := pathForestComponentPath (by omega) P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  have htarget : k * j + (k - 1) + 1 < p.length :=
    d2Component_boundary_index_lt hk P C j hj
  have hindex : k * j + (k - 1) + 1 = k * (j + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hentry := d2Component_entry_eq_vertex hk P C (j + 1) hj
  change p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ =
    entries.get ⟨j + 1, hj⟩
  calc
    p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ =
        p.vertex ⟨k * (j + 1), by rw [← hindex]; exact htarget⟩ := by
      apply congrArg p.vertex
      exact Fin.ext hindex
    _ = entries.get ⟨j + 1, hj⟩ := hentry.symm

private theorem d2ComponentBoundaryEdge_mem_forest (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    d2ComponentBoundaryEdge hk P C j hj ∈ pathForest (by omega) P := by
  have hePath : d2ComponentBoundaryEdge hk P C j hj ∈
      (pathForestComponentPath (by omega) P C).edgeSet := by
    apply OverlapPath.mem_edgeSet_iff.mpr
    exact ⟨k * j + (k - 1),
      d2Component_boundary_index_lt hk P C j hj, rfl⟩
  have heWeak : d2ComponentBoundaryEdge hk P C j hj ∈
      weakComponentEdges C := by
    rw [← pathForestComponentPath_edgeSet (by omega) P C]
    exact hePath
  exact (mem_weakComponentEdges.mp heWeak).1

private theorem d2Component_entry_zero_eq_tail (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).get
        ⟨0, by
          exact (pathForestComponentBlockEntries_nonempty (by omega) P C |>
            List.length_pos_of_ne_nil)⟩ =
      pathForestComponentTail (by omega) P C := by
  have hentry := d2Component_entry_eq_vertex hk P C 0
    (pathForestComponentBlockEntries_nonempty (by omega) P C |>
      List.length_pos_of_ne_nil)
  simpa [pathForestComponentTail] using hentry

private theorem d2Component_entry_index_mem_firstVisited (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (pathForestComponentBlockEntries (by omega) P C).get ⟨j, hj⟩ ∈
      firstVisitedVertices (by omega) P := by
  induction j with
  | zero =>
      rw [d2Component_entry_zero_eq_tail hk P C]
      exact pathForestComponentTail_mem_firstVisited (by omega) P C
  | succ j ih =>
      have hj0 : j <
          (pathForestComponentBlockEntries (by omega) P C).length := by omega
      let e := d2ComponentBoundaryEdge hk P C j hj
      have heForest : e ∈ pathForest (by omega) P := by
        simpa [e] using d2ComponentBoundaryEdge_mem_forest hk P C j hj
      have heSource : e.source =
          blockExit ((pathForestComponentBlockEntries (by omega) P C).get
            ⟨j, hj0⟩) := by
        simpa [e] using d2ComponentBoundaryEdge_source hk P C j hj
      have heTarget : e.target =
          (pathForestComponentBlockEntries (by omega) P C).get
            ⟨j + 1, hj⟩ := by
        simpa [e] using d2ComponentBoundaryEdge_target hk P C j hj
      have hprevFirst := ih hj0
      have heSourcePred : e.source ∈
          firstVisitedPredecessors (by omega) P := by
        rw [heSource]
        apply (mem_firstVisitedPredecessors_iff (by omega) P _).mpr
        rw [rotation_blockExit (by omega)]
        exact hprevFirst
      have htargetFirst :=
        (pathForest_edge_from_predecessor (by omega) P heForest heSourcePred).2
      simpa [heTarget, Nat.succ_eq_add_one] using htargetFirst

/-- Every complete-block entry in a forest component is the first-visited
vertex of its rotation class.  This is the D2-facing accessor needed by
structure theorem (iii). -/
theorem pathForestComponentBlockEntry_mem_firstVisited (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u : PermutationVertex k}
    (hu : u ∈ pathForestComponentBlockEntries (by omega) P C) :
    u ∈ firstVisitedVertices (by omega) P := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hu
  rw [← hj]
  exact d2Component_entry_index_mem_firstVisited hk P C j.1 j.2

/-- Every complete-block entry genuinely precedes the component head in the
original Hamiltonian path. -/
theorem pathForestComponentBlockEntry_strictlyPrecedes_head (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u : PermutationVertex k}
    (hu : u ∈ pathForestComponentBlockEntries (by omega) P C) :
    P.StrictlyPrecedes u (pathForestComponentHead (by omega) P C) := by
  let p := pathForestComponentPath (by omega) P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hu
  have hlen : p.length = k * entries.length := by
    simpa [p, entries] using d2Component_length_eq_entries_length hk P C
  have hmul : k * (j.1 + 1) ≤ k * entries.length :=
    Nat.mul_le_mul_left k (Nat.succ_le_iff.mpr j.2)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  have hindex : k * j.1 < p.length - 1 := by omega
  have hentry : entries.get j = p.vertex ⟨k * j.1, by omega⟩ := by
    simpa [entries, p] using d2Component_entry_eq_vertex hk P C j.1 j.2
  have hhead : p.vertex ⟨p.length - 1, by have := p.length_pos; omega⟩ =
      pathForestComponentHead (by omega) P C := by
    simpa [p, pathForestComponentHead, OverlapPath.vertex, OverlapPath.length]
      using (List.getLast_eq_getElem p.nonempty).symm
  have hprecede : StrictlyPrecedesInList p.vertices u
      (pathForestComponentHead (by omega) P C) := by
    refine ⟨k * j.1, p.length - 1,
      by simpa [OverlapPath.length] using (show k * j.1 < p.length by omega),
      by simpa [OverlapPath.length] using
        (show p.length - 1 < p.length by have := p.length_pos; omega),
      hindex, ?_, ?_⟩
    · exact hentry.symm.trans hj
    · exact hhead
  have huSpecial : u ∈ firstVisitedVertices (by omega) P ∪
      firstVisitedPredecessors (by omega) P :=
    Finset.mem_union_left _
      (pathForestComponentBlockEntry_mem_firstVisited hk P C hu)
  have hheadSpecial : pathForestComponentHead (by omega) P C ∈
      firstVisitedVertices (by omega) P ∪
        firstVisitedPredecessors (by omega) P :=
    Finset.mem_union_right _
      (pathForestComponentHead_mem_firstVisitedPredecessors (by omega) P C)
  exact pathForest_walk_special_precedes_in_path (by omega) P
    (pathForestComponentPath_isDirectedWalk (by omega) P C)
    huSpecial hheadSpecial hprecede

/-- A new head of `F(P)` has exactly one Step-2 deleted edge leaving it.
This nonvacuous existence-and-uniqueness statement precedes the accessor used
in Lemma `fullheadthree`. -/
theorem existsUnique_pathForestDeletedHeadEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) :
    ∃! e : DirectedOverlapEdge k,
      e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P) ∧
        e.source = pathForestComponentHead (by omega) P C := by
  classical
  let head := pathForestComponentHead (by omega) P C
  have hboundary := forestDeltaTwo_eq_outgoing_heads (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P)
  change forestDeltaTwo (by omega) P (residualVertices (by omega) P) =
    outgoingEdges P.edgeSet
      (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) at hboundary
  have hhead' : head ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet := by
    simpa [head] using hhead
  have houtNe : outgoingEdgesAt P.edgeSet head ≠ ∅ := by
    intro hempty
    exact (Finset.mem_sdiff.mp hhead').2 (mem_graphHeads.mpr hempty)
  obtain ⟨e, heOut⟩ := Finset.nonempty_iff_ne_empty.mpr houtNe
  have heP : e ∈ P.edgeSet := (mem_outgoingEdgesAt.mp heOut).1
  have heSource : e.source = head := (mem_outgoingEdgesAt.mp heOut).2
  refine ⟨e, ⟨?_, by simpa [head] using heSource⟩, ?_⟩
  · rw [hboundary]
    exact mem_outgoingEdges.mpr ⟨heP, by simpa [heSource] using hhead'⟩
  · intro f hf
    have hfOut : f ∈ outgoingEdges P.edgeSet
        (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) := by
      rw [← hboundary]
      exact hf.1
    have hfP : f ∈ P.edgeSet := (mem_outgoingEdges.mp hfOut).1
    have hfSource : f.source = head := by simpa [head] using hf.2
    have hle := P.edgeSet_outDegree_rule head
    rw [outDegree, Finset.card_le_one] at hle
    exact hle f (mem_outgoingEdgesAt.mpr ⟨hfP, hfSource⟩)
      e (mem_outgoingEdgesAt.mpr ⟨heP, heSource⟩)

/-- The exact Step-2 deleted edge leaving a specified new component head. -/
noncomputable def pathForestDeletedHeadEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) :
    DirectedOverlapEdge k :=
  Classical.choose (existsUnique_pathForestDeletedHeadEdge hk P C hhead)

/-- The deleted-head accessor belongs to `Δ₂`. -/
theorem pathForestDeletedHeadEdge_mem_deltaTwo (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) :
    pathForestDeletedHeadEdge hk P C hhead ∈
      forestDeltaTwo (by omega) P (residualVertices (by omega) P) :=
  (Classical.choose_spec
    (existsUnique_pathForestDeletedHeadEdge hk P C hhead)).1.1

/-- The deleted-head accessor leaves the specified component head. -/
theorem pathForestDeletedHeadEdge_source (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) :
    (pathForestDeletedHeadEdge hk P C hhead).source =
      pathForestComponentHead (by omega) P C :=
  (Classical.choose_spec
    (existsUnique_pathForestDeletedHeadEdge hk P C hhead)).1.2

/-- The deleted-head accessor is an original edge of the Hamiltonian path. -/
theorem pathForestDeletedHeadEdge_mem_path (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) :
    pathForestDeletedHeadEdge hk P C hhead ∈ P.edgeSet := by
  have hboundary := forestDeltaTwo_eq_outgoing_heads (by omega) P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible (by omega) P)
  change forestDeltaTwo (by omega) P (residualVertices (by omega) P) =
    outgoingEdges P.edgeSet
      (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) at hboundary
  have hout : pathForestDeletedHeadEdge hk P C hhead ∈
      outgoingEdges P.edgeSet
        (graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet) := by
    rw [← hboundary]
    exact pathForestDeletedHeadEdge_mem_deltaTwo hk P C hhead
  exact (mem_outgoingEdges.mp hout).1

/-- Any Step-2 deleted edge leaving the specified new head is the accessor. -/
theorem pathForestDeletedHeadEdge_unique (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet)
    {e : DirectedOverlapEdge k}
    (heDelta : e ∈
      forestDeltaTwo (by omega) P (residualVertices (by omega) P))
    (heSource : e.source = pathForestComponentHead (by omega) P C) :
    e = pathForestDeletedHeadEdge hk P C hhead :=
  (Classical.choose_spec
    (existsUnique_pathForestDeletedHeadEdge hk P C hhead)).2 e
      ⟨heDelta, heSource⟩

/-- Frozen Lemma `fullheadthree`: for a reduced minimum path, the exact
Step-2 deleted edge leaving a new component head has weight at least three
when that component's last run is full. -/
theorem fullLastRun_deletedHeadEdge_weight_ge_three (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (C : WeakComponent (pathForest (by omega) P))
    (hhead : pathForestComponentHead (by omega) P C ∈
      graphHeads (pathForest (by omega) P) \ graphHeads P.edgeSet)
    (hfull : (pathForestComponentLastRun hk P C).IsFull) :
    3 ≤ (pathForestDeletedHeadEdge hk P C hhead).weight := by
  let r := pathForestComponentLastRun hk P C
  let beta := pathForestComponentExitDoor hk P C
  let head := pathForestComponentHead (by omega) P C
  let e := pathForestDeletedHeadEdge hk P C hhead
  have hrLength : r.length = k - 1 := by
    simpa [r, PathForestRun.IsFull] using hfull
  have hbetaEntry : beta = r.entry := by
    calc
      beta = runMapPower (by omega) r.length r.entry := by
        simpa [beta, r] using
          (pathForestComponentLastRun_next_eq_exitDoor hk P C).symm
      _ = runMapPower (by omega) (k - 1) r.entry := by rw [hrLength]
      _ = r.entry := (runMap_order_exact (by omega) r.entry).1
  have hrNonempty : r.blocks ≠ [] := List.ne_nil_of_mem_splitBy r.isRun
  have hrEntryBlocks : r.entry ∈ r.blocks := by
    change r.blocks.head _ ∈ r.blocks
    exact List.head_mem hrNonempty
  have hrEntryComponent : r.entry ∈
      pathForestComponentBlockEntries (by omega) P C := by
    have hrIsRun : r.blocks ∈ pathForestComponentRuns hk P C := by
      simp only [r, pathForestComponentLastRun]
      exact r.isRun
    rw [← (pathForestComponentRuns_spec hk P C).1]
    exact List.mem_flatten.mpr ⟨r.blocks, hrIsRun, hrEntryBlocks⟩
  have hbetaComponent : beta ∈
      pathForestComponentBlockEntries (by omega) P C := by
    simpa [hbetaEntry] using hrEntryComponent
  have hbetaBefore : P.StrictlyPrecedes beta head := by
    simpa [head] using
      pathForestComponentBlockEntry_strictlyPrecedes_head hk P C hbetaComponent
  have heDelta : e ∈
      forestDeltaTwo (by omega) P (residualVertices (by omega) P) := by
    simpa [e] using pathForestDeletedHeadEdge_mem_deltaTwo hk P C hhead
  have heSource : e.source = head := by
    simpa [e, head] using pathForestDeletedHeadEdge_source hk P C hhead
  have heP : e ∈ P.edgeSet := by
    simpa [e] using pathForestDeletedHeadEdge_mem_path hk P C hhead
  have hgeTwo : 2 ≤ e.weight :=
    (reducedMinimumPath_newHeadWeight (by omega) P hP).1 e heDelta
  change 3 ≤ e.weight
  by_contra hnot
  have hweight : e.weight = 2 := by omega
  have heTarget : e.target = beta := by
    simpa [e, beta] using reducedPath_weightTwo_edge_from_componentHead
      hk P hP C e heP (by simpa [head] using heSource) hweight
  have hheadBefore : P.StrictlyPrecedes head beta := by
    simpa [head, heSource, heTarget] using
      HamiltonianPath.strictlyPrecedes_of_edge heP
  exact (Nat.lt_asymm hbetaBefore hheadBefore)

end SuperpermutationLowerBound
