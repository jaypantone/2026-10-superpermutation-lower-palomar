module

public import SuperpermutationLowerBound.Section10.SurplusRows
public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 10 from Definition `def:absorptiongraph` through Lemma
`lem:pieces`.  The graph below has the genuine weak components of `F(P)` as
its vertices.  Its directed adjacency is literally the Gate I absorber
relation, and its pieces are genuine connected components after orientations
are forgotten.  Ordered path and cycle data are derived from those pieces;
they are not the definition of a piece. -/

variable {k : ℕ}

private abbrev AbsorptionVertex (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  WeakComponent (pathForest (by omega) P)

/-! ## The literal absorption digraph and its genuine pieces -/

/-- The literal absorption digraph.  An edge `q → C` exists exactly when
`C` is the underlying genuine component of some `p ∈ M₄` and `q` absorbs
that actual nonroot component.  `Digraph` deliberately permits self-loops. -/
def pathForestAbsorptionGraph (hk : 7 ≤ k) (P : HamiltonianPath k) :
    Digraph (AbsorptionVertex hk P) where
  Adj q C := ∃ p : PathForestNonrootComponent hk P,
    p.1 = C ∧ PathForestAbsorbs hk P q p

/-- Literal adjacency, with the actual `M₄` target exposed. -/
theorem pathForestAbsorptionGraph_adj_iff (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q C : AbsorptionVertex hk P) :
    (pathForestAbsorptionGraph hk P).Adj q C ↔
      ∃ p : PathForestNonrootComponent hk P,
        p.1 = C ∧ PathForestAbsorbs hk P q p := Iff.rfl

/-- Incoming neighbours in the literal absorption digraph. -/
noncomputable def pathForestAbsorptionInNeighbors (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : AbsorptionVertex hk P) :
    Finset (AbsorptionVertex hk P) := by
  classical
  exact Finset.univ.filter fun q => (pathForestAbsorptionGraph hk P).Adj q C

/-- Outgoing neighbours in the literal absorption digraph. -/
noncomputable def pathForestAbsorptionOutNeighbors (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q : AbsorptionVertex hk P) :
    Finset (AbsorptionVertex hk P) := by
  classical
  exact Finset.univ.filter fun C => (pathForestAbsorptionGraph hk P).Adj q C

/-- Genuine absorption in-degree. -/
noncomputable def pathForestAbsorptionInDegree (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : AbsorptionVertex hk P) : ℕ :=
  (pathForestAbsorptionInNeighbors hk P C).card

/-- Genuine absorption out-degree. -/
noncomputable def pathForestAbsorptionOutDegree (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q : AbsorptionVertex hk P) : ℕ :=
  (pathForestAbsorptionOutNeighbors hk P q).card

@[simp] theorem mem_pathForestAbsorptionInNeighbors (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q C : AbsorptionVertex hk P) :
    q ∈ pathForestAbsorptionInNeighbors hk P C ↔
      (pathForestAbsorptionGraph hk P).Adj q C := by
  classical
  simp [pathForestAbsorptionInNeighbors]

@[simp] theorem mem_pathForestAbsorptionOutNeighbors (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q C : AbsorptionVertex hk P) :
    C ∈ pathForestAbsorptionOutNeighbors hk P q ↔
      (pathForestAbsorptionGraph hk P).Adj q C := by
  classical
  simp [pathForestAbsorptionOutNeighbors]

/-- Gate I's target uniqueness, transported to the literal graph. -/
theorem pathForestAbsorptionGraph_in_unique (hk : 7 ≤ k)
    (P : HamiltonianPath k) {C q r : AbsorptionVertex hk P}
    (hq : (pathForestAbsorptionGraph hk P).Adj q C)
    (hr : (pathForestAbsorptionGraph hk P).Adj r C) : q = r := by
  obtain ⟨p, hpC, hp⟩ := hq
  obtain ⟨p', hp'C, hp'⟩ := hr
  have hpp' : p = p' := by
    apply Subtype.ext
    exact hpC.trans hp'C.symm
  subst p'
  exact pathForestAbsorbs_inDegree_le_one hk P hp hp'

/-- Gate I's absorber uniqueness, transported to the literal graph. -/
theorem pathForestAbsorptionGraph_out_unique (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C D : AbsorptionVertex hk P}
    (hC : (pathForestAbsorptionGraph hk P).Adj q C)
    (hD : (pathForestAbsorptionGraph hk P).Adj q D) : C = D := by
  obtain ⟨p, hpC, hp⟩ := hC
  obtain ⟨r, hrD, hr⟩ := hD
  have hpr : p = r := pathForestAbsorbs_outDegree_le_one hk P hp hr
  exact hpC.symm.trans ((congrArg Subtype.val hpr).trans hrD)

/-- The literal graph has genuine in-degree at most one. -/
theorem pathForestAbsorptionInDegree_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : AbsorptionVertex hk P) :
    pathForestAbsorptionInDegree hk P C ≤ 1 := by
  classical
  rw [pathForestAbsorptionInDegree, Finset.card_le_one]
  intro q hq r hr
  exact pathForestAbsorptionGraph_in_unique hk P
    ((mem_pathForestAbsorptionInNeighbors hk P q C).mp hq)
    ((mem_pathForestAbsorptionInNeighbors hk P r C).mp hr)

/-- The literal graph has genuine out-degree at most one. -/
theorem pathForestAbsorptionOutDegree_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q : AbsorptionVertex hk P) :
    pathForestAbsorptionOutDegree hk P q ≤ 1 := by
  classical
  rw [pathForestAbsorptionOutDegree, Finset.card_le_one]
  intro C hC D hD
  exact pathForestAbsorptionGraph_out_unique hk P
    ((mem_pathForestAbsorptionOutNeighbors hk P q C).mp hC)
    ((mem_pathForestAbsorptionOutNeighbors hk P q D).mp hD)

/-- Forget orientations and nontrivial loops.  A self-loop still belongs to
the singleton connected component of its vertex. -/
def pathForestAbsorptionUnderlyingGraph (hk : 7 ≤ k)
    (P : HamiltonianPath k) : SimpleGraph (AbsorptionVertex hk P) where
  Adj q C := q ≠ C ∧
    ((pathForestAbsorptionGraph hk P).Adj q C ∨
      (pathForestAbsorptionGraph hk P).Adj C q)
  symm := ⟨by
    intro q C h
    exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by simp⟩

/-- A piece is an actual weak/connected component of the literal absorption
digraph, not an ordered list. -/
abbrev PathForestAbsorptionPiece (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  (pathForestAbsorptionUnderlyingGraph hk P).ConnectedComponent

noncomputable instance pathForestAbsorptionPieceFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) : Fintype (PathForestAbsorptionPiece hk P) :=
  Fintype.ofFinite _

noncomputable instance pathForestAbsorptionPieceVertexFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) : Fintype Z :=
  Fintype.ofFinite _

/-- The actual finite set of pieces. -/
noncomputable def pathForestAbsorptionPieces (hk : 7 ≤ k)
    (P : HamiltonianPath k) : Finset (PathForestAbsorptionPiece hk P) :=
  Finset.univ

/-- The actual component vertices carried by a piece. -/
noncomputable def pathForestAbsorptionPieceVertices (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Finset (AbsorptionVertex hk P) := by
  classical
  exact Finset.univ.filter fun C => C ∈ Z.supp

@[simp] theorem mem_pathForestAbsorptionPieceVertices (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (C : AbsorptionVertex hk P) :
    C ∈ pathForestAbsorptionPieceVertices hk P Z ↔ C ∈ Z.supp := by
  classical
  simp [pathForestAbsorptionPieceVertices]

/-- The actual directed edges carried by a piece, including self-loops. -/
noncomputable def pathForestAbsorptionPieceEdges (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Finset (AbsorptionVertex hk P × AbsorptionVertex hk P) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
      (pathForestAbsorptionGraph hk P).Adj e.1 e.2

@[simp] theorem mem_pathForestAbsorptionPieceEdges (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (e : AbsorptionVertex hk P × AbsorptionVertex hk P) :
    e ∈ pathForestAbsorptionPieceEdges hk P Z ↔
      e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
        (pathForestAbsorptionGraph hk P).Adj e.1 e.2 := by
  classical
  simp [pathForestAbsorptionPieceEdges]

private theorem pathForestAbsorption_adj_same_piece (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (h : (pathForestAbsorptionGraph hk P).Adj q C) :
    (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk q =
      (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk C := by
  by_cases hqC : q = C
  · subst C
    rfl
  · exact SimpleGraph.ConnectedComponent.sound
      (show (pathForestAbsorptionUnderlyingGraph hk P).Adj q C from
        ⟨hqC, Or.inl h⟩).reachable

/-- Every literal edge has both endpoints in one genuine piece. -/
theorem pathForestAbsorption_edge_piece (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (h : (pathForestAbsorptionGraph hk P).Adj q C) :
    ∃ Z : PathForestAbsorptionPiece hk P,
      q ∈ pathForestAbsorptionPieceVertices hk P Z ∧
      C ∈ pathForestAbsorptionPieceVertices hk P Z ∧
      (q, C) ∈ pathForestAbsorptionPieceEdges hk P Z := by
  let Z := (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk q
  have hq : q ∈ Z.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hC : C ∈ Z.supp := by
    have heq := pathForestAbsorption_adj_same_piece hk P h
    change (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk C = Z
    exact heq.symm
  exact ⟨Z, (mem_pathForestAbsorptionPieceVertices hk P Z q).mpr hq,
    (mem_pathForestAbsorptionPieceVertices hk P Z C).mpr hC,
    (mem_pathForestAbsorptionPieceEdges hk P Z (q, C)).mpr ⟨hq, hC, h⟩⟩

/-! ## Exact edge types -/

/-- Type (i), retaining the genuine one-run self-absorber and all of its
literal numerical data. -/
def PathForestAbsorptionEdgeTypeI (hk : 7 ≤ k) (P : HamiltonianPath k)
    (q C : AbsorptionVertex hk P) : Prop :=
  DoorSelfAbsorberCase hk P C q ∧
    pathForestComponentBlockCount (by omega) P C = k - 2 ∧
    pathForestComponentBudget (by omega) P C = 1 ∧
    pathForestComponentFirstDeficit hk P C = 1 ∧
    pathForestComponentLastDeficit hk P C = 1

/-- Type (ii).  No inequality here says `q ≠ C`: a separated-run edge may
itself be a self-loop, exactly as in the corrected TeX. -/
def PathForestAbsorptionEdgeTypeII (hk : 7 ≤ k) (P : HamiltonianPath k)
    (q C : AbsorptionVertex hk P) : Prop :=
  DoorSeparatedCase hk P C q ∧
    2 ≤ pathForestComponentFirstDeficit hk P C ∧
    2 ≤ pathForestComponentLastDeficit hk P q ∧
    k ≤ pathForestComponentFirstDeficit hk P C +
      pathForestComponentLastDeficit hk P q ∧
    endpointChargeA (pathForestComponentFirstDeficit hk P C) +
        endpointChargeB (pathForestComponentLastDeficit hk P q) =
      pathForestComponentFirstDeficit hk P C +
        pathForestComponentLastDeficit hk P q - 3 ∧
    k - 3 ≤ endpointChargeA (pathForestComponentFirstDeficit hk P C) +
      endpointChargeB (pathForestComponentLastDeficit hk P q)

/-- Every target is the actual underlying component of a member of `M₄`,
hence is nonroot and belongs to the literal set `U`. -/
theorem pathForestAbsorption_target_data (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (h : (pathForestAbsorptionGraph hk P).Adj q C) :
    C ≠ pathForestRootComponent (by omega) P ∧
      (⟨C, by
        obtain ⟨p, hpC, _hp⟩ := h
        simpa [← hpC] using p.2⟩ : PathForestNonrootComponent hk P) ∈
        pathForestU hk P := by
  obtain ⟨p, hpC, hpAbs⟩ := h
  have hpFour := hpAbs.1
  have hpU := (mem_pathForestMFour hk P p).mp hpFour |>.1
  have hnonroot : C ≠ pathForestRootComponent (by omega) P := by
    simpa [← hpC] using p.2
  refine ⟨hnonroot, ?_⟩
  have hsub :
      (⟨C, hnonroot⟩ : PathForestNonrootComponent hk P) = p := by
    apply Subtype.ext
    exact hpC.symm
  simpa [hsub] using hpU

/-- The root is never an absorption target. -/
theorem pathForestAbsorption_root_not_target (hk : 7 ≤ k)
    (P : HamiltonianPath k) (q : AbsorptionVertex hk P) :
    ¬(pathForestAbsorptionGraph hk P).Adj q
      (pathForestRootComponent (by omega) P) := by
  intro h
  exact (pathForestAbsorption_target_data hk P h).1 rfl

private theorem pathForestAbsorption_typeI_consequences (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hpU : (⟨C, hnonroot⟩ : PathForestNonrootComponent hk P) ∈ pathForestU hk P)
    (hself : DoorSelfAbsorberCase hk P C q) :
    PathForestAbsorptionEdgeTypeI hk P q C := by
  have hqC : q = C := hself.1.symm
  have hrunCount : pathForestComponentRunCount hk P C = 1 := hself.2.1
  have hfirst : pathForestComponentFirstDeficit hk P C = 1 := by
    rw [pathForestComponentFirstDeficit_eq_firstRun_deficit hk P C]
    change (k - 1) - (pathForestComponentFirstRun hk P C).length = 1
    rw [hself.2.2.1]
    omega
  have hlast : pathForestComponentLastDeficit hk P C = 1 := by
    rw [pathForestComponentLastDeficit_eq_lastRun_deficit hk P C]
    change (k - 1) - (pathForestComponentLastRun hk P C).length = 1
    have := hself.2.2.2
    rw [hqC] at this
    rw [this]
    omega
  have hz : pathForestComponentZ (by omega) P C = 1 := by
    have hnotTwo : ¬2 ≤ pathForestComponentZ (by omega) P C := by
      intro hzTwo
      have hqTwo := (pathForestComponentZ_ge_two_iff_runCount_ge_two hk P C).mp hzTwo
      omega
    have hzPos := pathForestComponentZ_pos (by omega) P C
    omega
  have hblocks := (pathForestComponentZOneData hk P C hz).2.1
  have hbudget : pathForestComponentBudget (by omega) P C = 1 := by
    let p : PathForestNonrootComponent hk P := ⟨C, hnonroot⟩
    have hminto := (mem_pathForestU hk P p).mp (by simpa [p] using hpU)
    rw [pathForestComponentBudget_nonroot_split (by omega) P C p.2]
    change pathForestComponentZ (by omega) P C +
      (pathForestNonrootMinto hk P p - 2) = 1
    rw [hz, hminto]
  refine ⟨hself, ?_, hbudget, hfirst, hlast⟩
  rw [hblocks, hfirst]
  omega

private theorem pathForestAbsorption_typeII_consequences (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (hsep : DoorSeparatedCase hk P C q) :
    PathForestAbsorptionEdgeTypeII hk P q C := by
  have hnums := doorSeparated_deficit_bounds hk P C q hsep
  let a := pathForestComponentFirstDeficit hk P C
  let b := pathForestComponentLastDeficit hk P q
  have hA : endpointChargeA a = a - 2 := by simp [endpointChargeA]
  have hB : endpointChargeB b = b - 1 :=
    endpointChargeB_eq_sub_one hnums.2.1
  have hsum : endpointChargeA a + endpointChargeB b = a + b - 3 := by
    rw [hA, hB]
    omega
  have hlower : k - 3 ≤ endpointChargeA a + endpointChargeB b := by
    rw [hsum]
    omega
  exact ⟨hsep, hnums.1, hnums.2.1, hnums.2.2, hsum, hlower⟩

/-- **The exclusive two-edge dichotomy (`lem:edgetypes`).**  Type (ii)
does not assert distinct endpoints, so a separated-run self-loop remains
possible and is exclusive from the one-run type-(i) self-loop. -/
theorem pathForestAbsorption_edgeTypes (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {q C : AbsorptionVertex hk P}
    (h : (pathForestAbsorptionGraph hk P).Adj q C) :
    (PathForestAbsorptionEdgeTypeI hk P q C ∧
        ¬PathForestAbsorptionEdgeTypeII hk P q C) ∨
      (PathForestAbsorptionEdgeTypeII hk P q C ∧
        ¬PathForestAbsorptionEdgeTypeI hk P q C) := by
  have htarget := pathForestAbsorption_target_data hk P h
  obtain ⟨p, hpC, hpAbs⟩ := h
  have hpFour := hpAbs.1
  let pC : PathForestNonrootComponent hk P := ⟨C, htarget.1⟩
  have hpU : pC ∈ pathForestU hk P := by simpa [pC] using htarget.2
  obtain ⟨g, hg, hgSource⟩ := hpAbs.2
  have hgHead : g.source ∈ graphHeads (pathForest (by omega) P) := by
    rw [hgSource]
    exact pathForestComponentHead_mem_graphHeads_I hk P q
  have hAt : pathForestComponentAtVertex hk P g.source = q := by
    apply pathForestComponent_eq_of_head_eq_I hk P
    rw [pathForestComponentAtVertex_head hk P hgHead]
    exact hgSource
  have hdoorRaw := pathForest_MFour_door_eq hk P hP hpFour
  rw [hg] at hdoorRaw
  simp only at hdoorRaw
  rw [hAt] at hdoorRaw
  have hdoor : pathForestComponentExitDoor hk P q =
      pathForestComponentEntranceDoor hk P C := by
    simpa [hpC] using hdoorRaw.symm
  have hmintoNonroot := (mem_pathForestU hk P pC).mp hpU
  have hminto : pathForestMinto (by omega) P C
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P C htarget.1) = 2 := by
    simpa [pathForestNonrootMinto, pC] using hmintoNonroot
  have houtside := (pathForestComponentCheapDeficit hk P C htarget.1 hminto).1
  rcases pathForestComponent_door_exactlyOne hk P C q houtside hdoor with
    ⟨hself, hnsep⟩ | ⟨hsep, hnself⟩
  · have hI := pathForestAbsorption_typeI_consequences hk P htarget.1 hpU hself
    left
    refine ⟨hI, ?_⟩
    intro hII
    exact hnsep hII.1
  · have hII := pathForestAbsorption_typeII_consequences hk P hsep
    right
    refine ⟨hII, ?_⟩
    intro hI
    exact hnself hI.1

/-! ## Honest directed path/cycle orders derived from genuine pieces -/

private abbrev AbsorptionPieceEdge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) :=
  {e : Z × Z // (pathForestAbsorptionGraph hk P).Adj e.1.1 e.2.1}

private abbrev AbsorptionPieceOut (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) (u : Z) :=
  {v : Z // (pathForestAbsorptionGraph hk P).Adj u.1 v.1}

private abbrev AbsorptionPieceIn (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) (v : Z) :=
  {u : Z // (pathForestAbsorptionGraph hk P).Adj u.1 v.1}

private noncomputable instance absorptionPieceEdgeFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Fintype (AbsorptionPieceEdge hk P Z) := Fintype.ofFinite _

private noncomputable instance absorptionPieceOutFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) (u : Z) :
    Fintype (AbsorptionPieceOut hk P Z u) := Fintype.ofFinite _

private noncomputable instance absorptionPieceInFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) (v : Z) :
    Fintype (AbsorptionPieceIn hk P Z v) := Fintype.ofFinite _

private def absorptionPieceEdgeEquivSigmaOut (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    AbsorptionPieceEdge hk P Z ≃
      Σ u : Z, AbsorptionPieceOut hk P Z u where
  toFun e := ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
  invFun e := ⟨(e.1, e.2.1), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def absorptionPieceEdgeEquivSigmaIn (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    AbsorptionPieceEdge hk P Z ≃
      Σ v : Z, AbsorptionPieceIn hk P Z v where
  toFun e := ⟨e.1.2, ⟨e.1.1, e.2⟩⟩
  invFun e := ⟨(e.2.1, e.1), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem absorptionPiece_edge_card_eq_sum_out (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Fintype.card (AbsorptionPieceEdge hk P Z) =
      ∑ u : Z, Fintype.card (AbsorptionPieceOut hk P Z u) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (absorptionPieceEdgeEquivSigmaOut hk P Z)

private theorem absorptionPiece_edge_card_eq_sum_in (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Fintype.card (AbsorptionPieceEdge hk P Z) =
      ∑ v : Z, Fintype.card (AbsorptionPieceIn hk P Z v) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (absorptionPieceEdgeEquivSigmaIn hk P Z)

private theorem absorptionPiece_out_card_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) (u : Z) :
    Fintype.card (AbsorptionPieceOut hk P Z u) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro v w
  apply Subtype.ext
  apply Subtype.ext
  exact pathForestAbsorptionGraph_out_unique hk P v.2 w.2

private theorem absorptionPiece_in_card_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) (v : Z) :
    Fintype.card (AbsorptionPieceIn hk P Z v) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro u w
  apply Subtype.ext
  apply Subtype.ext
  exact pathForestAbsorptionGraph_in_unique hk P u.2 w.2

private abbrev AbsorptionPieceNonloopEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :=
  {e : AbsorptionPieceEdge hk P Z // e.1.1.1 ≠ e.1.2.1}

private noncomputable instance absorptionPieceNonloopEdgeFintype (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Fintype (AbsorptionPieceNonloopEdge hk P Z) := Fintype.ofFinite _

private def absorptionPieceNonloopEdgeToUnderlying (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (e : AbsorptionPieceNonloopEdge hk P Z) : Z.toSimpleGraph.edgeSet := by
  refine ⟨s(e.1.1.1, e.1.1.2), ?_⟩
  rw [SimpleGraph.mem_edgeSet]
  apply (Z.toSimpleGraph_adj e.1.1.1.2 e.1.1.2.2).2
  exact ⟨e.2, Or.inl e.1.2⟩

private theorem absorptionPieceNonloopEdgeToUnderlying_surjective
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) :
    Function.Surjective (absorptionPieceNonloopEdgeToUnderlying hk P Z) := by
  rintro ⟨q, hq⟩
  induction q using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hq
      have hab : (pathForestAbsorptionUnderlyingGraph hk P).Adj a.1 b.1 :=
        (Z.toSimpleGraph_adj a.2 b.2).1 hq
      rcases hab.2 with hforward | hbackward
      · let e : AbsorptionPieceEdge hk P Z := ⟨(a, b), hforward⟩
        let en : AbsorptionPieceNonloopEdge hk P Z := ⟨e, hab.1⟩
        refine ⟨en, Subtype.ext ?_⟩
        rfl
      · let e : AbsorptionPieceEdge hk P Z := ⟨(b, a), hbackward⟩
        have hne : b.1 ≠ a.1 := hab.1.symm
        let en : AbsorptionPieceNonloopEdge hk P Z := ⟨e, hne⟩
        refine ⟨en, Subtype.ext ?_⟩
        exact Sym2.eq_swap

private theorem absorptionPiece_card_le_edges_add_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Fintype.card Z ≤ Fintype.card (AbsorptionPieceEdge hk P Z) + 1 := by
  classical
  have hconnected := Z.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hconnected
  have hsurj : Fintype.card Z.toSimpleGraph.edgeSet ≤
      Fintype.card (AbsorptionPieceNonloopEdge hk P Z) :=
    Fintype.card_le_of_surjective _
      (absorptionPieceNonloopEdgeToUnderlying_surjective hk P Z)
  have hinj : Fintype.card (AbsorptionPieceNonloopEdge hk P Z) ≤
      Fintype.card (AbsorptionPieceEdge hk P Z) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  omega

private theorem absorption_sum_add_zeroFilter_card
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α → ℕ)
    (hle : ∀ x ∈ s, d x ≤ 1) :
    (∑ x ∈ s, d x) + (s.filter fun x => d x = 0).card = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haLe : d a ≤ 1 := hle a (by simp)
      have hsLe : ∀ x ∈ s, d x ≤ 1 := by
        intro x hx
        exact hle x (by simp [hx])
      have hrec := ih hsLe
      by_cases hzero : d a = 0
      · have hanot : a ∉ s.filter fun x => d x = 0 := by simp [ha]
        have hfilter : (insert a s).filter (fun x => d x = 0) =
            insert a (s.filter fun x => d x = 0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hx, hdx⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hx, hdx⟩
          · rintro (rfl | ⟨hx, hdx⟩)
            · exact ⟨Or.inl rfl, hzero⟩
            · exact ⟨Or.inr hx, hdx⟩
        rw [Finset.sum_insert ha, hfilter, Finset.card_insert_of_notMem hanot,
          Finset.card_insert_of_notMem ha, hzero]
        omega
      · have hone : d a = 1 := by omega
        have hfilter : (insert a s).filter (fun x => d x = 0) =
            s.filter fun x => d x = 0 := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hx, hdx⟩
            · exact (hzero hdx).elim
            · exact ⟨hx, hdx⟩
          · rintro ⟨hx, hdx⟩
            exact ⟨Or.inr hx, hdx⟩
        rw [Finset.sum_insert ha, hfilter, Finset.card_insert_of_notMem ha, hone]
        omega

private theorem absorption_all_one_of_sum_eq_card
    {α : Type*} [DecidableEq α] {s : Finset α} {d : α → ℕ}
    (hle : ∀ x ∈ s, d x ≤ 1) (hsum : ∑ x ∈ s, d x = s.card) :
    ∀ x ∈ s, d x = 1 := by
  classical
  have hzero := absorption_sum_add_zeroFilter_card s d hle
  rw [hsum] at hzero
  have hfilter : s.filter (fun x => d x = 0) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  intro x hx
  have hxnot : d x ≠ 0 := by
    intro hdx
    have : x ∈ s.filter fun y => d y = 0 := by simp [hx, hdx]
    rw [hfilter] at this
    simp at this
  have hxle := hle x hx
  omega

private theorem absorption_degree_pattern_of_sum_add_one_eq_card
    {α : Type*} [DecidableEq α] {s : Finset α} {d : α → ℕ}
    (hle : ∀ x ∈ s, d x ≤ 1) (hsum : (∑ x ∈ s, d x) + 1 = s.card) :
    ∃ z ∈ s, d z = 0 ∧ ∀ x ∈ s, x ≠ z → d x = 1 := by
  classical
  have hzero := absorption_sum_add_zeroFilter_card s d hle
  have hcard : (s.filter fun x => d x = 0).card = 1 := by omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ s := by
    have : z ∈ s.filter fun x => d x = 0 := by simp [hz]
    exact (Finset.mem_filter.mp this).1
  have hzd : d z = 0 := by
    have : z ∈ s.filter fun x => d x = 0 := by simp [hz]
    exact (Finset.mem_filter.mp this).2
  refine ⟨z, hzmem, hzd, ?_⟩
  intro x hx hxz
  have hxnot : d x ≠ 0 := by
    intro hdx
    have hxfilter : x ∈ s.filter fun y => d y = 0 := by simp [hx, hdx]
    rw [hz] at hxfilter
    exact hxz (by simpa using hxfilter)
  have hxle := hle x hx
  omega

private structure AbsorptionPathEndpoints (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) where
  tail : Z
  head : Z
  tail_in_zero : Fintype.card (AbsorptionPieceIn hk P Z tail) = 0
  other_in_one : ∀ v : Z, v ≠ tail →
    Fintype.card (AbsorptionPieceIn hk P Z v) = 1
  head_out_zero : Fintype.card (AbsorptionPieceOut hk P Z head) = 0
  other_out_one : ∀ v : Z, v ≠ head →
    Fintype.card (AbsorptionPieceOut hk P Z v) = 1

private theorem absorptionPiece_degreePattern (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    (Nonempty (AbsorptionPathEndpoints hk P Z)) ∨
      (∀ v : Z,
        Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
        Fintype.card (AbsorptionPieceOut hk P Z v) = 1) := by
  classical
  let E := Fintype.card (AbsorptionPieceEdge hk P Z)
  let V := Fintype.card Z
  have hin : ∀ v ∈ (Finset.univ : Finset Z),
      Fintype.card (AbsorptionPieceIn hk P Z v) ≤ 1 := by
    intro v _
    exact absorptionPiece_in_card_le_one hk P Z v
  have hout : ∀ v ∈ (Finset.univ : Finset Z),
      Fintype.card (AbsorptionPieceOut hk P Z v) ≤ 1 := by
    intro v _
    exact absorptionPiece_out_card_le_one hk P Z v
  have hsumIn : E = ∑ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) :=
    absorptionPiece_edge_card_eq_sum_in hk P Z
  have hsumOut : E = ∑ v : Z,
      Fintype.card (AbsorptionPieceOut hk P Z v) :=
    absorptionPiece_edge_card_eq_sum_out hk P Z
  have hupper : E ≤ V := by
    rw [hsumOut]
    calc
      (∑ v : Z, Fintype.card (AbsorptionPieceOut hk P Z v)) ≤
          ∑ _v : Z, 1 := Finset.sum_le_sum fun v _ => hout v (by simp)
      _ = V := by simp [V]
  have hlower : V ≤ E + 1 := absorptionPiece_card_le_edges_add_one hk P Z
  by_cases hcycle : E = V
  · right
    intro v
    constructor
    · exact absorption_all_one_of_sum_eq_card hin
        (by simpa [← hsumIn, E, V]) v (by simp)
    · exact absorption_all_one_of_sum_eq_card hout
        (by simpa [← hsumOut, E, V]) v (by simp)
  · left
    have hedge : E + 1 = V := by omega
    obtain ⟨tail, _htail, htailZero, htailOther⟩ :=
      absorption_degree_pattern_of_sum_add_one_eq_card hin (by
        rw [← hsumIn]
        simpa [E, V] using hedge)
    obtain ⟨head, _hhead, hheadZero, hheadOther⟩ :=
      absorption_degree_pattern_of_sum_add_one_eq_card hout (by
        rw [← hsumOut]
        simpa [E, V] using hedge)
    exact ⟨
      { tail := tail
        head := head
        tail_in_zero := htailZero
        other_in_one := fun v hv => htailOther v (by simp) hv
        head_out_zero := hheadZero
        other_out_one := fun v hv => hheadOther v (by simp) hv }⟩

/-- An honest duplicate-free directed path ordering of a genuine piece.
Every piece vertex occurs, and the consecutive pairs are exactly its literal
directed absorption edges. -/
structure PathForestAbsorptionPathOrder (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) where
  vertices : List Z
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  covers : ∀ v : Z, v ∈ vertices
  edge_iff : ∀ u v : Z,
    (pathForestAbsorptionGraph hk P).Adj u.1 v.1 ↔
      ∃ i, ∃ hi : i + 1 < vertices.length,
        vertices[i] = u ∧ vertices[i + 1] = v

/-- An honest duplicate-free directed cycle ordering of a genuine piece.
Every piece vertex occurs, and its literal edges are exactly the consecutive
pairs together with the closing last-to-first pair.  Thus a one-term order
represents precisely a genuine self-loop. -/
structure PathForestAbsorptionCycleOrder (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) where
  vertices : List Z
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  covers : ∀ v : Z, v ∈ vertices
  edge_iff : ∀ u v : Z,
    (pathForestAbsorptionGraph hk P).Adj u.1 v.1 ↔
      (∃ i, ∃ hi : i + 1 < vertices.length,
        vertices[i] = u ∧ vertices[i + 1] = v) ∨
      (u = vertices.getLast nonempty ∧ v = vertices.head nonempty)

private theorem absorption_finiteInjective_returns {α : Type*} [Fintype α]
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

private noncomputable def absorptionPeriod {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) : ℕ :=
  by
    classical
    exact Nat.find (absorption_finiteInjective_returns f hf a)

private theorem absorptionPeriod_pos {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    0 < absorptionPeriod f hf a := by
  classical
  exact (Nat.find_spec (absorption_finiteInjective_returns f hf a)).1

private theorem absorptionPeriod_returns {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (f^[absorptionPeriod f hf a]) a = a := by
  classical
  exact (Nat.find_spec (absorption_finiteInjective_returns f hf a)).2

private theorem absorptionPeriod_minimal {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α)
    {d : ℕ} (hd : 0 < d) (hreturn : (f^[d]) a = a) :
    absorptionPeriod f hf a ≤ d := by
  classical
  exact Nat.find_min' (absorption_finiteInjective_returns f hf a) ⟨hd, hreturn⟩

private noncomputable def absorptionOrbitList {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) : List α :=
  List.iterate f a (absorptionPeriod f hf a)

private theorem absorptionOrbitList_length {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (absorptionOrbitList f hf a).length = absorptionPeriod f hf a := by
  simp [absorptionOrbitList]

private theorem absorptionOrbitList_getElem {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α)
    (i : ℕ) (hi : i < (absorptionOrbitList f hf a).length) :
    (absorptionOrbitList f hf a)[i] = (f^[i]) a := by
  simp [absorptionOrbitList]

private theorem absorptionOrbitList_nodup {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (absorptionOrbitList f hf a).Nodup := by
  classical
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [absorptionOrbitList, List.length_iterate] at hi hj
  simp only [absorptionOrbitList, List.getElem_iterate]
  intro heq
  let d := absorptionPeriod f hf a
  let q := j - i
  have hqpos : 0 < q := by dsimp [q]; omega
  have hjEq : j = i + q := by dsimp [q]; omega
  have heq' : (f^[i]) a = (f^[i]) ((f^[q]) a) := by
    calc
      (f^[i]) a = (f^[j]) a := heq
      _ = (f^[i + q]) a := by rw [hjEq]
      _ = (f^[i]) ((f^[q]) a) := Function.iterate_add_apply f i q a
  have hreturn : (f^[q]) a = a := ((hf.iterate i) heq').symm
  have hminimal : d ≤ q := absorptionPeriod_minimal f hf a hqpos hreturn
  dsimp [d, q] at hminimal
  omega

private def InAbsorptionOrbit {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a v : α) : Prop :=
  ∃ i < absorptionPeriod f hf a, (f^[i]) a = v

private theorem absorption_start_in_orbit {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    InAbsorptionOrbit f hf a a :=
  ⟨0, absorptionPeriod_pos f hf a, rfl⟩

private theorem absorption_orbit_closed_next {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) {v : α}
    (hv : InAbsorptionOrbit f hf a v) :
    InAbsorptionOrbit f hf a (f v) := by
  obtain ⟨i, hi, hiv⟩ := hv
  by_cases hisucc : i + 1 < absorptionPeriod f hf a
  · refine ⟨i + 1, hisucc, ?_⟩
    rw [Function.iterate_succ_apply', hiv]
  · have hieq : i + 1 = absorptionPeriod f hf a := by omega
    have hnext : f v = a := by
      calc
        f v = f ((f^[i]) a) := congrArg f hiv.symm
        _ = (f^[i + 1]) a :=
          (Function.iterate_succ_apply' f i a).symm
        _ = (f^[absorptionPeriod f hf a]) a := by rw [hieq]
        _ = a := absorptionPeriod_returns f hf a
    rw [hnext]
    exact absorption_start_in_orbit f hf a

private theorem absorption_orbit_closed_predecessor {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) {u v : α}
    (hfv : f v = u) (hu : InAbsorptionOrbit f hf a u) :
    InAbsorptionOrbit f hf a v := by
  obtain ⟨i, hi, hiu⟩ := hu
  by_cases hiZero : i = 0
  · subst i
    have huStart : u = a := by simpa using hiu.symm
    let d := absorptionPeriod f hf a
    have hd : 0 < d := absorptionPeriod_pos f hf a
    let j := d - 1
    have hj : j < d := by dsimp [j]; omega
    have hjSucc : j + 1 = d := by dsimp [j]; omega
    refine ⟨j, by simpa [d] using hj, ?_⟩
    apply hf
    calc
      f ((f^[j]) a) = (f^[j + 1]) a :=
        (Function.iterate_succ_apply' f j a).symm
      _ = (f^[d]) a := by rw [hjSucc]
      _ = a := by simpa [d] using absorptionPeriod_returns f hf a
      _ = u := huStart.symm
      _ = f v := hfv.symm
  · let j := i - 1
    have hj : j < absorptionPeriod f hf a := by dsimp [j]; omega
    have hjSucc : j + 1 = i := by dsimp [j]; omega
    refine ⟨j, hj, ?_⟩
    apply hf
    calc
      f ((f^[j]) a) = (f^[j + 1]) a :=
        (Function.iterate_succ_apply' f j a).symm
      _ = (f^[i]) a := by rw [hjSucc]
      _ = u := hiu
      _ = f v := hfv.symm

private theorem absorptionOrbitList_mem_iff {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a v : α) :
    v ∈ absorptionOrbitList f hf a ↔ InAbsorptionOrbit f hf a v := by
  simp [absorptionOrbitList, InAbsorptionOrbit, eq_comm]

private theorem absorptionOrbitList_head {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (absorptionOrbitList f hf a).head
      (by
        rw [List.ne_nil_iff_length_pos, absorptionOrbitList_length]
        exact absorptionPeriod_pos f hf a) = a := by
  rw [List.head_eq_getElem_zero]
  rw [absorptionOrbitList_getElem]
  rfl

private theorem absorptionOrbitList_getLast {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    (absorptionOrbitList f hf a).getLast
      (by
        rw [List.ne_nil_iff_length_pos, absorptionOrbitList_length]
        exact absorptionPeriod_pos f hf a) =
      (f^[absorptionPeriod f hf a - 1]) a := by
  have hpos := absorptionPeriod_pos f hf a
  have hget := List.getLast_eq_getElem
    (l := absorptionOrbitList f hf a)
    (by
      rw [List.ne_nil_iff_length_pos, absorptionOrbitList_length]
      exact hpos)
  rw [hget, absorptionOrbitList_getElem]
  rw [absorptionOrbitList_length]

private theorem absorptionOrbit_final_next {α : Type*} [Fintype α]
    (f : α → α) (hf : Function.Injective f) (a : α) :
    f ((f^[absorptionPeriod f hf a - 1]) a) = a := by
  have hpos := absorptionPeriod_pos f hf a
  have hsucc : absorptionPeriod f hf a - 1 + 1 =
      absorptionPeriod f hf a := by omega
  calc
    f ((f^[absorptionPeriod f hf a - 1]) a) =
        (f^[absorptionPeriod f hf a - 1 + 1]) a :=
      (Function.iterate_succ_apply' f _ a).symm
    _ = (f^[absorptionPeriod f hf a]) a := by rw [hsucc]
    _ = a := absorptionPeriod_returns f hf a

private noncomputable def absorptionPieceStart (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) : Z :=
  ⟨Classical.choose Z.nonempty_supp, Classical.choose_spec Z.nonempty_supp⟩

private noncomputable def absorptionCycleOutgoing (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    (u : Z) : AbsorptionPieceOut hk P Z u := by
  classical
  have hpos : 0 < Fintype.card (AbsorptionPieceOut hk P Z u) := by
    rw [(hcycle u).2]
    norm_num
  exact Classical.choice (Fintype.card_pos_iff.mp hpos)

private noncomputable def absorptionCycleNext (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    (u : Z) : Z := (absorptionCycleOutgoing hk P Z hcycle u).1

private theorem absorptionCycleNext_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    (u : Z) :
    (pathForestAbsorptionGraph hk P).Adj u.1
      (absorptionCycleNext hk P Z hcycle u).1 :=
  (absorptionCycleOutgoing hk P Z hcycle u).2

private theorem absorptionCycleNext_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1) :
    Function.Injective (absorptionCycleNext hk P Z hcycle) := by
  intro u v huv
  apply Subtype.ext
  exact pathForestAbsorptionGraph_in_unique hk P
    (absorptionCycleNext_edge hk P Z hcycle u)
    (by simpa [huv] using absorptionCycleNext_edge hk P Z hcycle v)

private theorem absorptionCycle_orbit_closed_adj (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    {a b : Z} (hab : Z.toSimpleGraph.Adj a b)
    (ha : InAbsorptionOrbit (absorptionCycleNext hk P Z hcycle)
      (absorptionCycleNext_injective hk P Z hcycle)
      (absorptionPieceStart hk P Z) a) :
    InAbsorptionOrbit (absorptionCycleNext hk P Z hcycle)
      (absorptionCycleNext_injective hk P Z hcycle)
      (absorptionPieceStart hk P Z) b := by
  let f := absorptionCycleNext hk P Z hcycle
  let hf := absorptionCycleNext_injective hk P Z hcycle
  let start := absorptionPieceStart hk P Z
  have habBase : (pathForestAbsorptionUnderlyingGraph hk P).Adj a.1 b.1 :=
    (Z.toSimpleGraph_adj a.2 b.2).1 hab
  rcases habBase.2 with hforward | hbackward
  · have hnext : f a = b := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionCycleNext_edge hk P Z hcycle a) hforward
    simpa [f, hf, start, hnext] using
      absorption_orbit_closed_next f hf start ha
  · have hnext : f b = a := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionCycleNext_edge hk P Z hcycle b) hbackward
    exact absorption_orbit_closed_predecessor f hf start hnext ha

private theorem absorptionCycle_covers (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    (v : Z) :
    v ∈ absorptionOrbitList (absorptionCycleNext hk P Z hcycle)
      (absorptionCycleNext_injective hk P Z hcycle)
      (absorptionPieceStart hk P Z) := by
  let f := absorptionCycleNext hk P Z hcycle
  let hf := absorptionCycleNext_injective hk P Z hcycle
  let start := absorptionPieceStart hk P Z
  have hclosed : ∀ {a b : Z}, Z.toSimpleGraph.Walk a b →
      InAbsorptionOrbit f hf start a → InAbsorptionOrbit f hf start b := by
    intro a b w
    induction w with
    | nil => exact fun h => h
    | @cons u v z hadj rest ih =>
        intro hu
        exact ih (absorptionCycle_orbit_closed_adj hk P Z hcycle hadj hu)
  obtain ⟨w⟩ := Z.connected_toSimpleGraph start v
  apply (absorptionOrbitList_mem_iff f hf start v).mpr
  exact hclosed w (absorption_start_in_orbit f hf start)

private theorem absorptionCycle_consecutive_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1)
    (i : ℕ)
    (hi : i + 1 <
      (absorptionOrbitList (absorptionCycleNext hk P Z hcycle)
        (absorptionCycleNext_injective hk P Z hcycle)
        (absorptionPieceStart hk P Z)).length) :
    (pathForestAbsorptionGraph hk P).Adj
      (absorptionOrbitList (absorptionCycleNext hk P Z hcycle)
        (absorptionCycleNext_injective hk P Z hcycle)
        (absorptionPieceStart hk P Z))[i].1
      (absorptionOrbitList (absorptionCycleNext hk P Z hcycle)
        (absorptionCycleNext_injective hk P Z hcycle)
        (absorptionPieceStart hk P Z))[i + 1].1 := by
  let f := absorptionCycleNext hk P Z hcycle
  let hf := absorptionCycleNext_injective hk P Z hcycle
  let start := absorptionPieceStart hk P Z
  change i + 1 < (absorptionOrbitList f hf start).length at hi
  rw [absorptionOrbitList_getElem f hf start i (by omega),
    absorptionOrbitList_getElem f hf start (i + 1) hi]
  simpa [f, Function.iterate_succ_apply'] using
    absorptionCycleNext_edge hk P Z hcycle ((f^[i]) start)

private theorem absorptionCycle_closing_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1) :
    let f := absorptionCycleNext hk P Z hcycle
    let hf := absorptionCycleNext_injective hk P Z hcycle
    let start := absorptionPieceStart hk P Z
    let vertices := absorptionOrbitList f hf start
    (pathForestAbsorptionGraph hk P).Adj
      (vertices.getLast (by
        rw [List.ne_nil_iff_length_pos, absorptionOrbitList_length]
        exact absorptionPeriod_pos f hf start)).1
      (vertices.head (by
        rw [List.ne_nil_iff_length_pos, absorptionOrbitList_length]
        exact absorptionPeriod_pos f hf start)).1 := by
  dsimp only
  let f := absorptionCycleNext hk P Z hcycle
  let hf := absorptionCycleNext_injective hk P Z hcycle
  let start := absorptionPieceStart hk P Z
  have hedge := absorptionCycleNext_edge hk P Z hcycle
    ((f^[absorptionPeriod f hf start - 1]) start)
  rw [absorptionOrbitList_getLast f hf start,
    absorptionOrbitList_head f hf start]
  have hnext := absorptionOrbit_final_next f hf start
  simpa [f, hnext] using hedge

private noncomputable def absorptionCycleOrderOfPattern (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hcycle : ∀ v : Z,
      Fintype.card (AbsorptionPieceIn hk P Z v) = 1 ∧
      Fintype.card (AbsorptionPieceOut hk P Z v) = 1) :
    PathForestAbsorptionCycleOrder hk P Z := by
  let f := absorptionCycleNext hk P Z hcycle
  let hf := absorptionCycleNext_injective hk P Z hcycle
  let start := absorptionPieceStart hk P Z
  let vertices := absorptionOrbitList f hf start
  have hnonempty : vertices ≠ [] := by
    rw [List.ne_nil_iff_length_pos]
    change 0 < (absorptionOrbitList f hf start).length
    rw [absorptionOrbitList_length]
    exact absorptionPeriod_pos f hf start
  refine
    { vertices := vertices
      nonempty := hnonempty
      nodup := absorptionOrbitList_nodup f hf start
      covers := absorptionCycle_covers hk P Z hcycle
      edge_iff := ?_ }
  intro u v
  constructor
  · intro huv
    have hnext : f u = v := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionCycleNext_edge hk P Z hcycle u) huv
    have huMem : u ∈ vertices := absorptionCycle_covers hk P Z hcycle u
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp huMem
    by_cases hi : idx.1 + 1 < vertices.length
    · left
      refine ⟨idx.1, hi, hidx, ?_⟩
      have hpair : (pathForestAbsorptionGraph hk P).Adj
          vertices[idx.1].1 vertices[idx.1 + 1].1 := by
        simpa [vertices, f, hf, start] using
          absorptionCycle_consecutive_edge hk P Z hcycle idx.1 hi
      have hidx' : vertices[idx.1] = u := by simpa using hidx
      rw [hidx'] at hpair
      apply Subtype.ext
      exact (pathForestAbsorptionGraph_out_unique hk P huv hpair).symm
    · right
      have hiLast : idx.1 = vertices.length - 1 := by omega
      have huLast : u = vertices.getLast hnonempty := by
        calc
          u = vertices.get idx := hidx.symm
          _ = vertices.get ⟨vertices.length - 1, by omega⟩ := by
            congr 1
            exact Fin.ext hiLast
          _ = vertices.getLast hnonempty :=
            (List.getLast_eq_getElem hnonempty).symm
      refine ⟨huLast, ?_⟩
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P huv (by
        rw [huLast]
        exact absorptionCycle_closing_edge hk P Z hcycle)
  · rintro (⟨i, hi, hiu, hiv⟩ | ⟨hu, hv⟩)
    · have he : (pathForestAbsorptionGraph hk P).Adj
          vertices[i].1 vertices[i + 1].1 := by
        simpa [vertices, f, hf, start] using
          absorptionCycle_consecutive_edge hk P Z hcycle i hi
      simpa [hiu, hiv] using he
    · have he : (pathForestAbsorptionGraph hk P).Adj
          (vertices.getLast hnonempty).1 (vertices.head hnonempty).1 := by
        simpa [vertices, f, hf, start] using
          absorptionCycle_closing_edge hk P Z hcycle
      simpa [hu, hv] using he

private noncomputable def absorptionPathOutgoing (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (u : Z) (hu : u ≠ D.head) :
    AbsorptionPieceOut hk P Z u := by
  classical
  have hpos : 0 < Fintype.card (AbsorptionPieceOut hk P Z u) := by
    rw [D.other_out_one u hu]
    norm_num
  exact Classical.choice (Fintype.card_pos_iff.mp hpos)

private noncomputable def absorptionPathNext (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (u : Z) : Z := by
  classical
  by_cases hu : u = D.head
  · exact D.tail
  · exact (absorptionPathOutgoing hk P Z D u hu).1

@[simp] private theorem absorptionPathNext_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) :
    absorptionPathNext hk P Z D D.head = D.tail := by
  simp [absorptionPathNext]

private theorem absorptionPathNext_of_ne_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (u : Z) (hu : u ≠ D.head) :
    absorptionPathNext hk P Z D u =
      (absorptionPathOutgoing hk P Z D u hu).1 := by
  simp [absorptionPathNext, hu]

private theorem absorptionPathNext_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (u : Z) (hu : u ≠ D.head) :
    (pathForestAbsorptionGraph hk P).Adj u.1
      (absorptionPathNext hk P Z D u).1 := by
  rw [absorptionPathNext_of_ne_head hk P Z D u hu]
  exact (absorptionPathOutgoing hk P Z D u hu).2

private theorem absorptionPathNext_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) :
    Function.Injective (absorptionPathNext hk P Z D) := by
  intro u v huv
  by_cases hu : u = D.head
  · subst u
    by_cases hv : v = D.head
    · exact hv.symm
    · have htarget : absorptionPathNext hk P Z D v = D.tail := by
        simpa using huv.symm
      have hin : Nonempty (AbsorptionPieceIn hk P Z D.tail) :=
        ⟨⟨v, by
          simpa [htarget] using absorptionPathNext_edge hk P Z D v hv⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hin
      rw [D.tail_in_zero] at hpos
      omega
  · by_cases hv : v = D.head
    · subst v
      have htarget : absorptionPathNext hk P Z D u = D.tail := by
        simpa using huv
      have hin : Nonempty (AbsorptionPieceIn hk P Z D.tail) :=
        ⟨⟨u, by
          simpa [htarget] using absorptionPathNext_edge hk P Z D u hu⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hin
      rw [D.tail_in_zero] at hpos
      omega
    · apply Subtype.ext
      exact pathForestAbsorptionGraph_in_unique hk P
        (absorptionPathNext_edge hk P Z D u hu)
        (by simpa [huv] using absorptionPathNext_edge hk P Z D v hv)

private theorem absorptionPath_iterate_ne_head_before_period (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (i : ℕ)
    (hi : i + 1 < absorptionPeriod (absorptionPathNext hk P Z D)
      (absorptionPathNext_injective hk P Z D) D.tail) :
    ((absorptionPathNext hk P Z D)^[i]) D.tail ≠ D.head := by
  intro heq
  have hreturn : ((absorptionPathNext hk P Z D)^[i + 1]) D.tail =
      D.tail := by
    rw [Function.iterate_succ_apply', heq, absorptionPathNext_head]
  have hminimal := absorptionPeriod_minimal (absorptionPathNext hk P Z D)
    (absorptionPathNext_injective hk P Z D) D.tail (by omega) hreturn
  omega

private theorem absorptionPath_orbit_closed_adj (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) {a b : Z}
    (hab : Z.toSimpleGraph.Adj a b)
    (ha : InAbsorptionOrbit (absorptionPathNext hk P Z D)
      (absorptionPathNext_injective hk P Z D) D.tail a) :
    InAbsorptionOrbit (absorptionPathNext hk P Z D)
      (absorptionPathNext_injective hk P Z D) D.tail b := by
  let f := absorptionPathNext hk P Z D
  let hf := absorptionPathNext_injective hk P Z D
  have habBase : (pathForestAbsorptionUnderlyingGraph hk P).Adj a.1 b.1 :=
    (Z.toSimpleGraph_adj a.2 b.2).1 hab
  rcases habBase.2 with hforward | hbackward
  · have haNotHead : a ≠ D.head := by
      intro haHead
      have hout : Nonempty (AbsorptionPieceOut hk P Z D.head) :=
        ⟨⟨b, by simpa [haHead] using hforward⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hout
      rw [D.head_out_zero] at hpos
      omega
    have hnext : f a = b := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionPathNext_edge hk P Z D a haNotHead) hforward
    simpa [f, hf, hnext] using absorption_orbit_closed_next f hf D.tail ha
  · have hbNotHead : b ≠ D.head := by
      intro hbHead
      have hout : Nonempty (AbsorptionPieceOut hk P Z D.head) :=
        ⟨⟨a, by simpa [hbHead] using hbackward⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hout
      rw [D.head_out_zero] at hpos
      omega
    have hnext : f b = a := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionPathNext_edge hk P Z D b hbNotHead) hbackward
    exact absorption_orbit_closed_predecessor f hf D.tail hnext ha

private theorem absorptionPath_covers (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (v : Z) :
    v ∈ absorptionOrbitList (absorptionPathNext hk P Z D)
      (absorptionPathNext_injective hk P Z D) D.tail := by
  let f := absorptionPathNext hk P Z D
  let hf := absorptionPathNext_injective hk P Z D
  have hclosed : ∀ {a b : Z}, Z.toSimpleGraph.Walk a b →
      InAbsorptionOrbit f hf D.tail a → InAbsorptionOrbit f hf D.tail b := by
    intro a b w
    induction w with
    | nil => exact fun h => h
    | @cons u v z hadj rest ih =>
        intro hu
        exact ih (absorptionPath_orbit_closed_adj hk P Z D hadj hu)
  obtain ⟨w⟩ := Z.connected_toSimpleGraph D.tail v
  apply (absorptionOrbitList_mem_iff f hf D.tail v).mpr
  exact hclosed w (absorption_start_in_orbit f hf D.tail)

private theorem absorptionPath_final_eq_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) :
    ((absorptionPathNext hk P Z D)^[
      absorptionPeriod (absorptionPathNext hk P Z D)
        (absorptionPathNext_injective hk P Z D) D.tail - 1]) D.tail = D.head := by
  let f := absorptionPathNext hk P Z D
  let hf := absorptionPathNext_injective hk P Z D
  let d := absorptionPeriod f hf D.tail
  let last : Z := (f^[d - 1]) D.tail
  have hnext : f last = D.tail := by
    simpa [last, d] using absorptionOrbit_final_next f hf D.tail
  by_contra hne
  have hlastNe : last ≠ D.head := by simpa [last, d, f] using hne
  have hin : Nonempty (AbsorptionPieceIn hk P Z D.tail) :=
    ⟨⟨last, by
      simpa [f, hnext] using absorptionPathNext_edge hk P Z D last hlastNe⟩⟩
  have hpos := Fintype.card_pos_iff.mpr hin
  rw [D.tail_in_zero] at hpos
  omega

private theorem absorptionPath_consecutive_edge (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) (i : ℕ)
    (hi : i + 1 <
      (absorptionOrbitList (absorptionPathNext hk P Z D)
        (absorptionPathNext_injective hk P Z D) D.tail).length) :
    (pathForestAbsorptionGraph hk P).Adj
      (absorptionOrbitList (absorptionPathNext hk P Z D)
        (absorptionPathNext_injective hk P Z D) D.tail)[i].1
      (absorptionOrbitList (absorptionPathNext hk P Z D)
        (absorptionPathNext_injective hk P Z D) D.tail)[i + 1].1 := by
  let f := absorptionPathNext hk P Z D
  let hf := absorptionPathNext_injective hk P Z D
  change i + 1 < (absorptionOrbitList f hf D.tail).length at hi
  have hiPeriod : i + 1 < absorptionPeriod f hf D.tail := by
    simpa [absorptionOrbitList_length] using hi
  have hne : (f^[i]) D.tail ≠ D.head := by
    simpa [f, hf] using
      absorptionPath_iterate_ne_head_before_period hk P Z D i hiPeriod
  rw [absorptionOrbitList_getElem f hf D.tail i (by omega),
    absorptionOrbitList_getElem f hf D.tail (i + 1) hi]
  simpa [f, Function.iterate_succ_apply'] using
    absorptionPathNext_edge hk P Z D ((f^[i]) D.tail) hne

private noncomputable def absorptionPathOrderOfEndpoints (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (D : AbsorptionPathEndpoints hk P Z) :
    PathForestAbsorptionPathOrder hk P Z := by
  let f := absorptionPathNext hk P Z D
  let hf := absorptionPathNext_injective hk P Z D
  let vertices := absorptionOrbitList f hf D.tail
  have hnonempty : vertices ≠ [] := by
    rw [List.ne_nil_iff_length_pos]
    change 0 < (absorptionOrbitList f hf D.tail).length
    rw [absorptionOrbitList_length]
    exact absorptionPeriod_pos f hf D.tail
  refine
    { vertices := vertices
      nonempty := hnonempty
      nodup := absorptionOrbitList_nodup f hf D.tail
      covers := absorptionPath_covers hk P Z D
      edge_iff := ?_ }
  intro u v
  constructor
  · intro huv
    have huNotHead : u ≠ D.head := by
      intro huHead
      have hout : Nonempty (AbsorptionPieceOut hk P Z D.head) :=
        ⟨⟨v, by simpa [huHead] using huv⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hout
      rw [D.head_out_zero] at hpos
      omega
    have hnext : f u = v := by
      apply Subtype.ext
      exact pathForestAbsorptionGraph_out_unique hk P
        (absorptionPathNext_edge hk P Z D u huNotHead) huv
    have huMem : u ∈ vertices := absorptionPath_covers hk P Z D u
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp huMem
    have hi : idx.1 + 1 < vertices.length := by
      by_contra hnot
      have hiLast : idx.1 = vertices.length - 1 := by omega
      have huLast : u = vertices.getLast hnonempty := by
        calc
          u = vertices.get idx := hidx.symm
          _ = vertices.get ⟨vertices.length - 1, by omega⟩ := by
            congr 1
            exact Fin.ext hiLast
          _ = vertices.getLast hnonempty :=
            (List.getLast_eq_getElem hnonempty).symm
      have hlastHead : vertices.getLast hnonempty = D.head := by
        rw [absorptionOrbitList_getLast f hf D.tail]
        exact absorptionPath_final_eq_head hk P Z D
      exact huNotHead (huLast.trans hlastHead)
    refine ⟨idx.1, hi, hidx, ?_⟩
    have hpair : (pathForestAbsorptionGraph hk P).Adj
        vertices[idx.1].1 vertices[idx.1 + 1].1 := by
      simpa [vertices, f, hf] using
        absorptionPath_consecutive_edge hk P Z D idx.1 hi
    have hidx' : vertices[idx.1] = u := by simpa using hidx
    rw [hidx'] at hpair
    apply Subtype.ext
    exact (pathForestAbsorptionGraph_out_unique hk P huv hpair).symm
  · rintro ⟨i, hi, hiu, hiv⟩
    have he : (pathForestAbsorptionGraph hk P).Adj
        vertices[i].1 vertices[i + 1].1 := by
      simpa [vertices, f, hf] using
        absorptionPath_consecutive_edge hk P Z D i hi
    simpa [hiu, hiv] using he

/-- **Structure part of `def:absorptiongraph`.** Every genuine piece has an
actual duplicate-free directed path order or an actual duplicate-free directed
cycle order, with exact vertex and literal-edge coverage.  A one-vertex cycle
therefore carries a literal self-loop; a one-vertex path carries no edge. -/
theorem pathForestAbsorptionPiece_path_or_cycle (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Nonempty (PathForestAbsorptionPathOrder hk P Z) ∨
      Nonempty (PathForestAbsorptionCycleOrder hk P Z) := by
  rcases absorptionPiece_degreePattern hk P Z with hpath | hcycle
  · obtain ⟨D⟩ := hpath
    exact Or.inl ⟨absorptionPathOrderOfEndpoints hk P Z D⟩
  · exact Or.inr ⟨absorptionCycleOrderOfPattern hk P Z hcycle⟩

/-! ## Signed surplus estimates on ordered genuine pieces -/

/-- The genuine signed component-surplus sum over an actual piece. -/
noncomputable def pathForestAbsorptionPieceSurplus (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) : ℤ :=
  ∑ C : Z, pathForestComponentSurplus hk P C.1

private noncomputable def pathForestAbsorptionCorrection (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℤ :=
  if pathForestComponentZ (by omega) P C = 1 then
    max (0 : ℤ) ((pathForestComponentFirstDeficit hk P C : ℤ) - 4)
  else 0

private theorem pathForestAbsorptionCorrection_nonneg (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    0 ≤ pathForestAbsorptionCorrection hk P C := by
  classical
  simp only [pathForestAbsorptionCorrection]
  split
  · exact le_max_left _ _
  · exact le_rfl

private theorem pathForestAbsorptionCorrection_le (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestAbsorptionCorrection hk P C ≤ (k : ℤ) - 6 := by
  classical
  by_cases hz : pathForestComponentZ (by omega) P C = 1
  · rw [pathForestAbsorptionCorrection, if_pos hz]
    have hd := (pathForestComponentZOneData hk P C hz).2.2
    have hdInt : (pathForestComponentFirstDeficit hk P C : ℤ) ≤
        (k : ℤ) - 2 := by
      have : (pathForestComponentFirstDeficit hk P C : ℤ) ≤
          ((k - 2 : ℕ) : ℤ) := by exact_mod_cast hd
      have hkCast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by
        omega
      rwa [hkCast] at this
    apply max_le
    · omega
    · omega
  · simp [pathForestAbsorptionCorrection, hz]
    omega

private theorem pathForestAbsorptionCorrection_active (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hpos : 0 < pathForestAbsorptionCorrection hk P C) :
    pathForestComponentZ (by omega) P C = 1 ∧
      5 ≤ pathForestComponentFirstDeficit hk P C ∧
      pathForestAbsorptionCorrection hk P C =
        (pathForestComponentFirstDeficit hk P C : ℤ) - 4 := by
  classical
  by_cases hz : pathForestComponentZ (by omega) P C = 1
  · rw [pathForestAbsorptionCorrection, if_pos hz] at hpos
    have hx : (0 : ℤ) <
        (pathForestComponentFirstDeficit hk P C : ℤ) - 4 :=
      (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    have hd : 5 ≤ pathForestComponentFirstDeficit hk P C := by
      omega
    refine ⟨hz, hd, ?_⟩
    rw [pathForestAbsorptionCorrection, if_pos hz, max_eq_right hx.le]
  · rw [pathForestAbsorptionCorrection, if_neg hz] at hpos
    omega

private theorem pathForestCheapSurplus_B_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB
            (pathForestComponentLastDeficit hk P p.1) : ℤ) := by
  by_cases hz : pathForestComponentZ (by omega) P p.1 = 1
  · obtain ⟨_hfl, _hd, _heq, _hbase, hmin, _hboth⟩ :=
      pathForestCheapSurplus_z_one hk P p hpU hz
    exact hmin.trans (min_le_left _ _)
  · have hzPos := pathForestComponentZ_pos (by omega) P p.1
    have hzTwo : 2 ≤ pathForestComponentZ (by omega) P p.1 := by omega
    have hrow := pathForestCheapSurplus_ge_two_le hk P p hpU hzTwo
    have hlambda : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
    have hA : (0 : ℤ) ≤
        (endpointChargeA (pathForestComponentFirstDeficit hk P p.1) : ℤ) := by
      omega
    nlinarith

private theorem pathForestCheapSurplus_A_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeA
            (pathForestComponentFirstDeficit hk P p.1) : ℤ) := by
  by_cases hz : pathForestComponentZ (by omega) P p.1 = 1
  · obtain ⟨_hfl, _hd, _heq, _hbase, hmin, _hboth⟩ :=
      pathForestCheapSurplus_z_one hk P p hpU hz
    exact hmin.trans (min_le_right _ _)
  · have hzPos := pathForestComponentZ_pos (by omega) P p.1
    have hzTwo : 2 ≤ pathForestComponentZ (by omega) P p.1 := by omega
    have hrow := pathForestCheapSurplus_ge_two_le hk P p hpU hzTwo
    have hlambda : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
    have hB : (0 : ℤ) ≤
        (endpointChargeB (pathForestComponentLastDeficit hk P p.1) : ℤ) := by
      omega
    nlinarith

private theorem pathForestCheapSurplus_AB_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          ((endpointChargeA
              (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
            (endpointChargeB
              (pathForestComponentLastDeficit hk P p.1) : ℤ)) +
        (surplusLambda (k - 1) : ℤ) *
          pathForestAbsorptionCorrection hk P p.1 := by
  classical
  by_cases hz : pathForestComponentZ (by omega) P p.1 = 1
  · obtain ⟨_hfl, _hd, _heq, _hbase, _hmin, hboth⟩ :=
      pathForestCheapSurplus_z_one hk P p hpU hz
    simpa [pathForestAbsorptionCorrection, hz] using hboth
  · have hzPos := pathForestComponentZ_pos (by omega) P p.1
    have hzTwo : 2 ≤ pathForestComponentZ (by omega) P p.1 := by omega
    simpa [pathForestAbsorptionCorrection, hz] using
      pathForestCheapSurplus_ge_two_le hk P p hpU hzTwo

private theorem pathForestNonrootSurplus_B_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P) :
    pathForestComponentSurplus hk P C ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB (pathForestComponentLastDeficit hk P C) : ℤ) := by
  let p : PathForestNonrootComponent hk P := ⟨C, hnonroot⟩
  by_cases hpU : p ∈ pathForestU hk P
  · simpa [p] using pathForestCheapSurplus_B_bound hk P p hpU
  · have hmintoNe : pathForestNonrootMinto hk P p ≠ 2 := by
      intro hm
      exact hpU ((mem_pathForestU hk P p).mpr hm)
    have hmintoGe : 3 ≤ pathForestNonrootMinto hk P p := by
      have := (pathForestNonrootMinto_bounds hk P p).1
      omega
    have hminto : 3 ≤ pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hnonroot) := by
      simpa [pathForestNonrootMinto, p] using hmintoGe
    have hrow := (pathForestNoncheapSurplus_le hk P C hnonroot hminto).1
    have hkappa := (surplusKappa_int_forms (show 6 ≤ k - 1 by omega)).1
    have hnInt : (6 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
    nlinarith [sq_nonneg (((k - 1 : ℕ) : ℤ) - 2)]

/-- A type-(i) component has exactly the signed surplus from the TeX:
`s = 4 - n`, where `n = k - 1`. -/
theorem pathForestAbsorption_typeI_surplus_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (hI : PathForestAbsorptionEdgeTypeI hk P q C) :
    pathForestComponentSurplus hk P C =
      4 - ((k - 1 : ℕ) : ℤ) := by
  have hn : 6 ≤ k - 1 := by omega
  have hlambda := (surplusLambda_range hn).2
  have hkappa := (surplusKappa_int_forms hn).1
  have hblocksCast : ((k - 2 : ℕ) : ℤ) =
      ((k - 1 : ℕ) : ℤ) - 1 := by
    omega
  have hlambdaInt : (surplusLambda (k - 1) : ℤ) =
      ((k - 1 : ℕ) : ℤ) - 2 := by
    have hcast : (surplusLambda (k - 1) : ℤ) + 2 =
        ((k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hlambda
    omega
  rw [pathForestComponentSurplus_eq, hI.2.1, hI.2.2.1,
    hblocksCast, hlambdaInt, hkappa]
  ring

/-- The exact type-(i) component surplus is strictly negative for `n ≥ 6`. -/
theorem pathForestAbsorption_typeI_surplus_neg (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (hI : PathForestAbsorptionEdgeTypeI hk P q C) :
    pathForestComponentSurplus hk P C < 0 := by
  rw [pathForestAbsorption_typeI_surplus_eq hk P hI]
  have hn : (6 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
  omega

private theorem pathForestAbsorption_typeI_surplus_nonpos (hk : 7 ≤ k)
    (P : HamiltonianPath k) {q C : AbsorptionVertex hk P}
    (hI : PathForestAbsorptionEdgeTypeI hk P q C) :
    pathForestComponentSurplus hk P C ≤ 0 :=
  (pathForestAbsorption_typeI_surplus_neg hk P hI).le

/-- Every explicitly listed vertex after the first in a path order is an
actual absorption target, hence is nonroot and lies in `U`. -/
theorem pathForestAbsorptionPathOrder_afterFirst_target_data (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z) (i : ℕ)
    (hi : i + 1 < O.vertices.length) :
    O.vertices[i + 1].1 ≠ pathForestRootComponent (by omega) P ∧
      ∃ p : PathForestNonrootComponent hk P,
        p.1 = O.vertices[i + 1].1 ∧ p ∈ pathForestU hk P := by
  have hdata := pathForestAbsorption_target_data hk P
    ((O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
      ⟨i, hi, rfl, rfl⟩)
  let p : PathForestNonrootComponent hk P := ⟨O.vertices[i + 1].1, hdata.1⟩
  exact ⟨hdata.1, p, rfl, by simpa [p] using hdata.2⟩

private theorem pathForestAbsorptionPathOrder_nonfirst_target_data
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z) (v : Z)
    (hv : v ≠ O.vertices.head O.nonempty) :
    v.1 ≠ pathForestRootComponent (by omega) P ∧
      ∃ p : PathForestNonrootComponent hk P,
        p.1 = v.1 ∧ p ∈ pathForestU hk P := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (O.covers v)
  have hiPos : 0 < idx.1 := by
    by_contra hnot
    have hzero : idx.1 = 0 := by omega
    have hvFirst : v = O.vertices.head O.nonempty := by
      calc
        v = O.vertices.get idx := hidx.symm
        _ = O.vertices.get ⟨0, by omega⟩ := by
          congr 1
          exact Fin.ext hzero
        _ = O.vertices.head O.nonempty :=
          (List.head_eq_getElem_zero O.nonempty).symm
    exact hv hvFirst
  let i := idx.1 - 1
  have hi : i + 1 < O.vertices.length := by dsimp [i]; omega
  have hvAt : O.vertices[i + 1] = v := by
    have hieq : i + 1 = idx.1 := by dsimp [i]; omega
    simpa [hieq] using hidx
  obtain ⟨hnonroot, p, hpv, hpU⟩ :=
    pathForestAbsorptionPathOrder_afterFirst_target_data hk P Z O i hi
  exact ⟨by simpa [hvAt] using hnonroot, p,
    by simpa [hvAt] using hpv, hpU⟩

/-- Every vertex in a cycle order is an actual target, including the sole
vertex of a one-vertex self-loop cycle; consequently every such vertex lies
in `U`. -/
theorem pathForestAbsorptionCycleOrder_vertex_target_data (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionCycleOrder hk P Z) (v : Z) :
    v.1 ≠ pathForestRootComponent (by omega) P ∧
      ∃ p : PathForestNonrootComponent hk P,
        p.1 = v.1 ∧ p ∈ pathForestU hk P := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (O.covers v)
  by_cases hiZero : idx.1 = 0
  · have hvFirst : v = O.vertices.head O.nonempty := by
      calc
        v = O.vertices.get idx := hidx.symm
        _ = O.vertices.get ⟨0, by omega⟩ := by
          congr 1
          exact Fin.ext hiZero
        _ = O.vertices.head O.nonempty :=
          (List.head_eq_getElem_zero O.nonempty).symm
    have hdata := pathForestAbsorption_target_data hk P
      ((O.edge_iff (O.vertices.getLast O.nonempty)
        (O.vertices.head O.nonempty)).mpr (Or.inr ⟨rfl, rfl⟩))
    let p : PathForestNonrootComponent hk P :=
      ⟨(O.vertices.head O.nonempty).1, hdata.1⟩
    exact ⟨by simpa [hvFirst] using hdata.1, p,
      by simp [hvFirst, p], by simpa [p] using hdata.2⟩
  · let i := idx.1 - 1
    have hi : i + 1 < O.vertices.length := by dsimp [i]; omega
    have hvAt : O.vertices[i + 1] = v := by
      have hieq : i + 1 = idx.1 := by dsimp [i]; omega
      simpa [hieq] using hidx
    have hdata := pathForestAbsorption_target_data hk P
      ((O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
        (Or.inl ⟨i, hi, rfl, rfl⟩))
    let p : PathForestNonrootComponent hk P :=
      ⟨O.vertices[i + 1].1, hdata.1⟩
    exact ⟨by simpa [hvAt] using hdata.1, p,
      by simp [hvAt, p], by simpa [p] using hdata.2⟩

private theorem list_map_sum_eq_toFinset_sum_of_nodup
    {α : Type*} [DecidableEq α] (f : α → ℤ) :
    ∀ (l : List α), l.Nodup →
      (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
      have hparts := List.nodup_cons.mp hl
      simp [hparts.1, ih hparts.2]

private theorem pathForestAbsorptionPieceSurplus_eq_order_sum
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) (l : List Z)
    (hnodup : l.Nodup) (hcovers : ∀ v : Z, v ∈ l) :
    pathForestAbsorptionPieceSurplus hk P Z =
      (l.map fun C => pathForestComponentSurplus hk P C.1).sum := by
  classical
  have hfin : l.toFinset = (Finset.univ : Finset Z) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    exact List.mem_toFinset.mpr (hcovers v)
  rw [pathForestAbsorptionPieceSurplus, ← hfin]
  exact (list_map_sum_eq_toFinset_sum_of_nodup
    (fun C : Z => pathForestComponentSurplus hk P C.1) l hnodup).symm

private def absorptionListEdgeCharge {α : Type*}
    (A B : α → ℤ) : List α → ℤ
  | u :: v :: rest => B u + A v +
      absorptionListEdgeCharge A B (v :: rest)
  | _ => 0

private theorem absorptionListEdgeCharge_decompose {α : Type*}
    (A B : α → ℤ) (first last : α) (middle : List α) :
    absorptionListEdgeCharge A B (first :: (middle ++ [last])) =
      B first + (middle.map fun v => A v + B v).sum + A last := by
  induction middle generalizing first with
  | nil => simp [absorptionListEdgeCharge]
  | cons x xs ih =>
      rw [List.cons_append]
      simp only [absorptionListEdgeCharge, List.map_cons, List.sum_cons]
      rw [ih x]
      ring

private theorem absorptionListEdgeCharge_cycle_reindex {α : Type*}
    (A B : α → ℤ) (l : List α) (hne : l ≠ []) :
    absorptionListEdgeCharge A B l + A (l.head hne) + B (l.getLast hne) =
      (l.map fun v => A v + B v).sum := by
  obtain ⟨first, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  by_cases htail : tail = []
  · subst tail
    simp [absorptionListEdgeCharge]
  · let middle := tail.dropLast
    let last := tail.getLast htail
    have htailEq : middle ++ [last] = tail :=
      List.dropLast_append_getLast htail
    have hdecomp : absorptionListEdgeCharge A B (first :: tail) =
        B first + (middle.map fun v => A v + B v).sum + A last := by
      simpa [htailEq] using
        absorptionListEdgeCharge_decompose A B first last middle
    have hlast : (first :: tail).getLast (by simp) = last := by
      simp [last, htail]
    have hsum : ((first :: tail).map fun v => A v + B v).sum =
        A first + B first + (middle.map fun v => A v + B v).sum +
          (A last + B last) := by
      rw [← htailEq]
      simp only [List.map_cons, List.map_append, List.sum_cons,
        List.sum_append, List.map_nil, List.sum_nil]
      ring
    rw [hdecomp, hlast, hsum]
    simp only [List.head_cons]
    ring

private theorem absorption_list_sum_le_sum_of_mem {α : Type*}
    (f g : α → ℤ) : ∀ (l : List α),
    (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum := by
  intro l h
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := h a (by simp)
      have hl : ∀ x ∈ l, f x ≤ g x := by
        intro x hx
        exact h x (by simp [hx])
      exact add_le_add ha (ih hl)

private theorem absorption_internal_sum_bound {α : Type*}
    (s A B eta : α → ℤ) (n lambda etaMax : ℤ) (l : List α)
    (hrow : ∀ x ∈ l,
      s x ≤ n - lambda * (A x + B x) + lambda * eta x)
    (heta : ∀ x ∈ l, eta x ≤ etaMax)
    (hlambda : 0 ≤ lambda) :
    (l.map s).sum ≤
      (l.length : ℤ) * n - lambda * (l.map fun x => A x + B x).sum +
        lambda * (l.length : ℤ) * etaMax := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hrow a (by simp)
      have haEta := heta a (by simp)
      have htailRow : ∀ x ∈ l,
          s x ≤ n - lambda * (A x + B x) + lambda * eta x := by
        intro x hx
        exact hrow x (by simp [hx])
      have htailEta : ∀ x ∈ l, eta x ≤ etaMax := by
        intro x hx
        exact heta x (by simp [hx])
      have hrec := ih htailRow htailEta
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      have hetaScaled := Int.mul_le_mul_of_nonneg_left haEta hlambda
      nlinarith

private theorem absorptionListEdgeCharge_lower_of_typeII_chain
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    {Z : PathForestAbsorptionPiece hk P} {l : List Z}
    (hchain : l.IsChain fun u v =>
      PathForestAbsorptionEdgeTypeII hk P u.1 v.1) :
    ((l.length - 1 : ℕ) : ℤ) * ((k - 3 : ℕ) : ℤ) ≤
      absorptionListEdgeCharge
        (fun C : Z => (endpointChargeA
          (pathForestComponentFirstDeficit hk P C.1) : ℤ))
        (fun C : Z => (endpointChargeB
          (pathForestComponentLastDeficit hk P C.1) : ℤ)) l := by
  induction hchain with
  | nil => simp [absorptionListEdgeCharge]
  | singleton a => simp [absorptionListEdgeCharge]
  | @cons_cons u v rest huv _ ih =>
      obtain ⟨_hsep, _hfirst, _hlast, _hsum, _heq, hlower⟩ := huv
      have hlowerInt : ((k - 3 : ℕ) : ℤ) ≤
          (endpointChargeA
            (pathForestComponentFirstDeficit hk P v.1) : ℤ) +
          (endpointChargeB
            (pathForestComponentLastDeficit hk P u.1) : ℤ) := by
        exact_mod_cast hlower
      have hlenGoal : (u :: v :: rest).length - 1 = rest.length + 1 := by
        simp
      have hlenIH : (v :: rest).length - 1 = rest.length := by simp
      rw [hlenGoal]
      rw [hlenIH] at ih
      simp only [absorptionListEdgeCharge]
      push_cast at ih ⊢
      nlinarith

private theorem pathForestAbsorptionPathOrder_typeII_chain (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z) :
    O.vertices.IsChain fun u v =>
      PathForestAbsorptionEdgeTypeII hk P u.1 v.1 := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hedge : (pathForestAbsorptionGraph hk P).Adj
      O.vertices[i].1 O.vertices[i + 1].1 :=
    (O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
      ⟨i, by simpa using hi, rfl, rfl⟩
  rcases pathForestAbsorption_edgeTypes hk P hP hedge with
    ⟨hI, _hnII⟩ | ⟨hII, _hnI⟩
  · have heq : O.vertices[i] = O.vertices[i + 1] := by
      apply Subtype.ext
      exact hI.1.1.symm
    have hidx : i = i + 1 := O.nodup.getElem_inj_iff.mp heq
    omega
  · exact hII

private theorem pathForestAbsorptionCycleOrder_typeII_chain (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionCycleOrder hk P Z)
    (hnoI : ∀ u v : Z, (pathForestAbsorptionGraph hk P).Adj u.1 v.1 →
      ¬PathForestAbsorptionEdgeTypeI hk P u.1 v.1) :
    O.vertices.IsChain fun u v =>
      PathForestAbsorptionEdgeTypeII hk P u.1 v.1 := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hedge : (pathForestAbsorptionGraph hk P).Adj
      O.vertices[i].1 O.vertices[i + 1].1 :=
    (O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
      (Or.inl ⟨i, by simpa using hi, rfl, rfl⟩)
  rcases pathForestAbsorption_edgeTypes hk P hP hedge with
    ⟨hI, _hnII⟩ | ⟨hII, _hnI⟩
  · exact (hnoI _ _ hedge hI).elim
  · exact hII

private theorem pathForestAbsorptionCycleOrder_closing_typeII (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionCycleOrder hk P Z)
    (hnoI : ∀ u v : Z, (pathForestAbsorptionGraph hk P).Adj u.1 v.1 →
      ¬PathForestAbsorptionEdgeTypeI hk P u.1 v.1) :
    PathForestAbsorptionEdgeTypeII hk P
      (O.vertices.getLast O.nonempty).1
      (O.vertices.head O.nonempty).1 := by
  have hedge := (O.edge_iff (O.vertices.getLast O.nonempty)
    (O.vertices.head O.nonempty)).mpr (Or.inr ⟨rfl, rfl⟩)
  rcases pathForestAbsorption_edgeTypes hk P hP hedge with
    ⟨hI, _hnII⟩ | ⟨hII, _hnI⟩
  · exact (hnoI _ _ hedge hI).elim
  · exact hII

private theorem pathForestAbsorption_selfloop_piece_singleton (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (q : Z) (hloop : (pathForestAbsorptionGraph hk P).Adj q.1 q.1) :
    ∀ v : Z, v = q := by
  have hnoAdj : ∀ r : Z, ¬Z.toSimpleGraph.Adj q r := by
    intro r hqr
    have hbase : (pathForestAbsorptionUnderlyingGraph hk P).Adj q.1 r.1 :=
      (Z.toSimpleGraph_adj q.2 r.2).1 hqr
    rcases hbase.2 with hforward | hbackward
    · have heq := pathForestAbsorptionGraph_out_unique hk P hloop hforward
      exact hbase.1 heq
    · have heq := pathForestAbsorptionGraph_in_unique hk P hloop hbackward
      exact hbase.1 heq
  intro v
  obtain ⟨w⟩ := Z.connected_toSimpleGraph q v
  cases w with
  | nil => rfl
  | cons hadj rest => exact (hnoAdj _ hadj).elim

/-- The genuine singleton piece carrying a type-(i) loop has exactly
`s = 4 - n`, where `n = k - 1`. -/
theorem pathForestAbsorptionPieceSurplus_typeI_loop_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (q : Z) (hloop : (pathForestAbsorptionGraph hk P).Adj q.1 q.1)
    (hI : PathForestAbsorptionEdgeTypeI hk P q.1 q.1) :
    pathForestAbsorptionPieceSurplus hk P Z =
      4 - ((k - 1 : ℕ) : ℤ) := by
  classical
  have hall := pathForestAbsorption_selfloop_piece_singleton hk P Z q hloop
  have hcard : Fintype.card Z = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨q, hall⟩
  have huniv : (Finset.univ : Finset Z) = {q} :=
    univ_eq_singleton_of_card_one q hcard
  rw [pathForestAbsorptionPieceSurplus, huniv]
  simpa using pathForestAbsorption_typeI_surplus_eq hk P hI

/-- The genuine singleton piece carrying a type-(i) loop has strictly
negative signed surplus. -/
theorem pathForestAbsorptionPieceSurplus_typeI_loop_neg (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (q : Z) (hloop : (pathForestAbsorptionGraph hk P).Adj q.1 q.1)
    (hI : PathForestAbsorptionEdgeTypeI hk P q.1 q.1) :
    pathForestAbsorptionPieceSurplus hk P Z < 0 := by
  rw [pathForestAbsorptionPieceSurplus_typeI_loop_eq hk P Z q hloop hI]
  have hn : (6 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
  omega

private theorem pathForestAbsorptionPieceSurplus_typeI_loop (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (q : Z) (hloop : (pathForestAbsorptionGraph hk P).Adj q.1 q.1)
    (hI : PathForestAbsorptionEdgeTypeI hk P q.1 q.1) :
    pathForestAbsorptionPieceSurplus hk P Z ≤ 0 :=
  (pathForestAbsorptionPieceSurplus_typeI_loop_neg hk P Z q hloop hI).le

private theorem absorption_path_arithmetic_root (n m : ℤ)
    (hn : 6 ≤ n) (hm : 0 ≤ m) :
    (2 * n - 2) + (m + 1) * n -
        (n - 2) * ((m + 1) * (n - 2)) +
        (n - 2) * m * (n - 5) ≤ 0 := by
  have hstep : 0 ≤ m * (2 * n - 6) :=
    mul_nonneg hm (by nlinarith)
  have hroot : (n - 1) * (6 - n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  have hid :
      (2 * n - 2) + (m + 1) * n -
          (n - 2) * ((m + 1) * (n - 2)) +
          (n - 2) * m * (n - 5) =
        (n - 1) * (6 - n) - m * (2 * n - 6) := by ring
  rw [hid]
  nlinarith

private theorem absorption_path_arithmetic_nonroot (n m : ℤ)
    (hn : 6 ≤ n) (hm : 0 ≤ m) :
    n + (m + 1) * n -
        (n - 2) * ((m + 1) * (n - 2)) +
        (n - 2) * m * (n - 5) ≤ 0 := by
  have hstep : 0 ≤ m * (2 * n - 6) :=
    mul_nonneg hm (by nlinarith)
  have hbase : n - (n - 1) * (n - 4) < 0 := by
    nlinarith [sq_nonneg (n - 3)]
  have hid :
      n + (m + 1) * n -
          (n - 2) * ((m + 1) * (n - 2)) +
          (n - 2) * m * (n - 5) =
        (n - (n - 1) * (n - 4)) - m * (2 * n - 6) := by ring
  rw [hid]
  nlinarith

private theorem absorption_cycle_arithmetic (n j : ℤ)
    (hn : 6 ≤ n) (hj : 1 ≤ j) :
    j * n - (n - 2) * (j * (n - 2)) +
        (n - 2) * j * (n - 5) ≤ 0 := by
  have hid :
      j * n - (n - 2) * (j * (n - 2)) +
          (n - 2) * j * (n - 5) = -2 * j * (n - 3) := by ring
  rw [hid]
  have hprod : 0 ≤ j * (n - 3) :=
    mul_nonneg (by omega) (by omega)
  nlinarith

/-- An edge-carrying path piece has at least two genuinely distinct listed
vertices. -/
theorem pathForestAbsorptionPathOrder_length_ge_two_of_piece_edge
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z)
    (hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty) :
    2 ≤ O.vertices.length := by
  obtain ⟨e, he⟩ := hZedge
  have heData := (mem_pathForestAbsorptionPieceEdges hk P Z e).mp he
  let u : Z := ⟨e.1, heData.1⟩
  let v : Z := ⟨e.2, heData.2.1⟩
  have huv : (pathForestAbsorptionGraph hk P).Adj u.1 v.1 := heData.2.2
  obtain ⟨i, hi, _hu, _hv⟩ := (O.edge_iff u v).mp huv
  omega

private theorem pathForestAbsorptionPieceSurplus_path_nonpos
    (hk : 7 ≤ k) (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z)
    (hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty) :
    pathForestAbsorptionPieceSurplus hk P Z ≤ 0 := by
  classical
  let s : Z → ℤ := fun C => pathForestComponentSurplus hk P C.1
  let A : Z → ℤ := fun C =>
    (endpointChargeA (pathForestComponentFirstDeficit hk P C.1) : ℤ)
  let B : Z → ℤ := fun C =>
    (endpointChargeB (pathForestComponentLastDeficit hk P C.1) : ℤ)
  let eta : Z → ℤ := fun C => pathForestAbsorptionCorrection hk P C.1
  let n : ℤ := ((k - 1 : ℕ) : ℤ)
  let lambda : ℤ := (surplusLambda (k - 1) : ℤ)
  let etaMax : ℤ := (k : ℤ) - 6
  have hlenTwo :=
    pathForestAbsorptionPathOrder_length_ge_two_of_piece_edge hk P Z O hZedge
  obtain ⟨first, tail, hvertices⟩ := List.exists_cons_of_ne_nil O.nonempty
  have htailNonempty : tail ≠ [] := by
    intro htail
    subst tail
    rw [hvertices] at hlenTwo
    simp at hlenTwo
  let middle := tail.dropLast
  let last := tail.getLast htailNonempty
  have htailEq : middle ++ [last] = tail :=
    List.dropLast_append_getLast htailNonempty
  have hdecomp : O.vertices = first :: (middle ++ [last]) := by
    calc
      O.vertices = first :: tail := hvertices
      _ = first :: (middle ++ [last]) := congrArg (List.cons first) htailEq.symm
  have hhead : O.vertices.head O.nonempty = first := by
    rw [List.head_eq_getElem_zero O.nonempty]
    have hzero : O.vertices[0] = first := by
      simp [hvertices]
    exact hzero
  have hnodupForm : (first :: tail).Nodup := by
    rw [← hvertices]
    exact O.nodup
  have hfirstNotTail : first ∉ tail := (List.nodup_cons.mp hnodupForm).1
  have hlastTail : last ∈ tail := by
    exact List.getLast_mem htailNonempty
  have hlastNeFirst : last ≠ first := by
    intro heq
    exact hfirstNotTail (heq ▸ hlastTail)
  have hlastNeHead : last ≠ O.vertices.head O.nonempty := by
    simpa [hhead] using hlastNeFirst
  obtain ⟨_hlastNonroot, plast, hplast, hplastU⟩ :=
    pathForestAbsorptionPathOrder_nonfirst_target_data hk P Z O last hlastNeHead
  have hlastRow : s last ≤ n - lambda * A last := by
    have hraw := pathForestCheapSurplus_A_bound hk P plast hplastU
    simpa [s, n, lambda, A, hplast] using hraw
  have hmidRow : ∀ x ∈ middle,
      s x ≤ n - lambda * (A x + B x) + lambda * eta x := by
    intro x hx
    have hxTail : x ∈ tail := List.mem_of_mem_dropLast hx
    have hxNeFirst : x ≠ first := by
      intro heq
      exact hfirstNotTail (heq ▸ hxTail)
    have hxNeHead : x ≠ O.vertices.head O.nonempty := by
      simpa [hhead] using hxNeFirst
    obtain ⟨_hxNonroot, px, hpx, hpxU⟩ :=
      pathForestAbsorptionPathOrder_nonfirst_target_data hk P Z O x hxNeHead
    have hraw := pathForestCheapSurplus_AB_bound hk P px hpxU
    simpa [s, n, lambda, A, B, eta, hpx] using hraw
  have hmidEta : ∀ x ∈ middle, eta x ≤ etaMax := by
    intro x _hx
    simpa [eta, etaMax] using pathForestAbsorptionCorrection_le hk P x.1
  have hlambdaNonneg : 0 ≤ lambda := by
    dsimp [lambda]
    omega
  have hmidSum := absorption_internal_sum_bound s A B eta n lambda etaMax
    middle hmidRow hmidEta hlambdaNonneg
  have hsumEq := pathForestAbsorptionPieceSurplus_eq_order_sum
    hk P Z O.vertices O.nodup O.covers
  have hmapDecomp : (O.vertices.map s).sum =
      s first + (middle.map s).sum + s last := by
    rw [hdecomp]
    simp only [List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, List.map_nil, List.sum_nil]
    ring
  have hchargeDecomp : absorptionListEdgeCharge A B O.vertices =
      B first + (middle.map fun x => A x + B x).sum + A last := by
    rw [hdecomp]
    exact absorptionListEdgeCharge_decompose A B first last middle
  have hchain := pathForestAbsorptionPathOrder_typeII_chain hk P hP Z O
  have hchargeLowerRaw :=
    absorptionListEdgeCharge_lower_of_typeII_chain hk P hchain
  have hlenEdges : O.vertices.length - 1 = middle.length + 1 := by
    rw [hdecomp]
    simp
  rw [hlenEdges] at hchargeLowerRaw
  have hunit : ((k - 3 : ℕ) : ℤ) = lambda := by
    have hlambdaNat := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
    have hcast : (lambda : ℤ) + 2 = n := by
      dsimp [lambda, n]
      exact_mod_cast hlambdaNat
    dsimp [lambda, n] at hcast ⊢
    omega
  rw [hunit] at hchargeLowerRaw
  push_cast at hchargeLowerRaw
  have hchargeScaled := Int.mul_le_mul_of_nonneg_left
    hchargeLowerRaw hlambdaNonneg
  have hn : 6 ≤ n := by dsimp [n]; omega
  have hlambdaN : lambda = n - 2 := by
    have hlambdaNat := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
    have hcast : lambda + 2 = n := by
      dsimp [lambda, n]
      exact_mod_cast hlambdaNat
    omega
  have hetaN : etaMax = n - 5 := by
    dsimp [etaMax, n]
    omega
  have hm : 0 ≤ (middle.length : ℤ) := by omega
  by_cases hroot : first.1 = pathForestRootComponent (by omega) P
  · have hfirstRow : s first ≤ 2 * n - 2 - lambda * B first := by
      have hraw := pathForestRootSurplus_le hk P
      simpa [s, n, lambda, B, hroot] using hraw
    have hrows : pathForestAbsorptionPieceSurplus hk P Z ≤
        (2 * n - 2) + ((middle.length : ℤ) + 1) * n -
          lambda * absorptionListEdgeCharge A B O.vertices +
          lambda * (middle.length : ℤ) * etaMax := by
      rw [hsumEq, hmapDecomp, hchargeDecomp]
      nlinarith
    have hbound : pathForestAbsorptionPieceSurplus hk P Z ≤
        (2 * n - 2) + ((middle.length : ℤ) + 1) * n -
          lambda * (((middle.length : ℤ) + 1) * lambda) +
          lambda * (middle.length : ℤ) * etaMax := by
      nlinarith
    rw [hlambdaN, hetaN] at hbound
    exact hbound.trans (absorption_path_arithmetic_root n middle.length hn hm)
  · have hfirstRow : s first ≤ n - lambda * B first := by
      have hraw := pathForestNonrootSurplus_B_bound hk P first.1 hroot
      simpa [s, n, lambda, B] using hraw
    have hrows : pathForestAbsorptionPieceSurplus hk P Z ≤
        n + ((middle.length : ℤ) + 1) * n -
          lambda * absorptionListEdgeCharge A B O.vertices +
          lambda * (middle.length : ℤ) * etaMax := by
      rw [hsumEq, hmapDecomp, hchargeDecomp]
      nlinarith
    have hbound : pathForestAbsorptionPieceSurplus hk P Z ≤
        n + ((middle.length : ℤ) + 1) * n -
          lambda * (((middle.length : ℤ) + 1) * lambda) +
          lambda * (middle.length : ℤ) * etaMax := by
      nlinarith
    rw [hlambdaN, hetaN] at hbound
    exact hbound.trans (absorption_path_arithmetic_nonroot n middle.length hn hm)

private theorem pathForestAbsorptionPieceSurplus_cycle_nonpos
    (hk : 7 ≤ k) (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionCycleOrder hk P Z) :
    pathForestAbsorptionPieceSurplus hk P Z ≤ 0 := by
  classical
  by_cases hIExists : ∃ u v : Z,
      (pathForestAbsorptionGraph hk P).Adj u.1 v.1 ∧
        PathForestAbsorptionEdgeTypeI hk P u.1 v.1
  · obtain ⟨u, v, huv, hI⟩ := hIExists
    have huvEq : u = v := by
      apply Subtype.ext
      exact hI.1.1.symm
    subst v
    exact pathForestAbsorptionPieceSurplus_typeI_loop hk P Z u huv hI
  · have hnoI : ∀ u v : Z,
        (pathForestAbsorptionGraph hk P).Adj u.1 v.1 →
          ¬PathForestAbsorptionEdgeTypeI hk P u.1 v.1 := by
      intro u v huv hI
      exact hIExists ⟨u, v, huv, hI⟩
    let s : Z → ℤ := fun C => pathForestComponentSurplus hk P C.1
    let A : Z → ℤ := fun C =>
      (endpointChargeA (pathForestComponentFirstDeficit hk P C.1) : ℤ)
    let B : Z → ℤ := fun C =>
      (endpointChargeB (pathForestComponentLastDeficit hk P C.1) : ℤ)
    let eta : Z → ℤ := fun C => pathForestAbsorptionCorrection hk P C.1
    let n : ℤ := ((k - 1 : ℕ) : ℤ)
    let lambda : ℤ := (surplusLambda (k - 1) : ℤ)
    let etaMax : ℤ := (k : ℤ) - 6
    have hrow : ∀ x ∈ O.vertices,
        s x ≤ n - lambda * (A x + B x) + lambda * eta x := by
      intro x _hx
      obtain ⟨_hxNonroot, px, hpx, hpxU⟩ :=
        pathForestAbsorptionCycleOrder_vertex_target_data hk P Z O x
      have hraw := pathForestCheapSurplus_AB_bound hk P px hpxU
      simpa [s, n, lambda, A, B, eta, hpx] using hraw
    have heta : ∀ x ∈ O.vertices, eta x ≤ etaMax := by
      intro x _hx
      simpa [eta, etaMax] using pathForestAbsorptionCorrection_le hk P x.1
    have hlambdaNonneg : 0 ≤ lambda := by
      dsimp [lambda]
      omega
    have hsumRows := absorption_internal_sum_bound s A B eta n lambda etaMax
      O.vertices hrow heta hlambdaNonneg
    have hsumEq := pathForestAbsorptionPieceSurplus_eq_order_sum
      hk P Z O.vertices O.nodup O.covers
    have hreindex := absorptionListEdgeCharge_cycle_reindex A B
      O.vertices O.nonempty
    have hchain := pathForestAbsorptionCycleOrder_typeII_chain
      hk P hP Z O hnoI
    have hpathLower := absorptionListEdgeCharge_lower_of_typeII_chain
      hk P hchain
    have hclosingII := pathForestAbsorptionCycleOrder_closing_typeII
      hk P hP Z O hnoI
    obtain ⟨_hsep, _hfirst, _hlast, _hsum, _heq, hclosingLower⟩ := hclosingII
    have hclosingLowerInt : ((k - 3 : ℕ) : ℤ) ≤
        A (O.vertices.head O.nonempty) +
          B (O.vertices.getLast O.nonempty) := by
      dsimp [A, B]
      exact_mod_cast hclosingLower
    have hunit : ((k - 3 : ℕ) : ℤ) = lambda := by
      have hlambdaNat := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
      have hcast : lambda + 2 = n := by
        dsimp [lambda, n]
        exact_mod_cast hlambdaNat
      dsimp [lambda, n] at hcast ⊢
      omega
    rw [hunit] at hpathLower hclosingLowerInt
    have htotalLower : (O.vertices.length : ℤ) * lambda ≤
        absorptionListEdgeCharge A B O.vertices +
          A (O.vertices.head O.nonempty) +
          B (O.vertices.getLast O.nonempty) := by
      have hlenPos : 1 ≤ O.vertices.length :=
        by
          have := List.length_pos_of_ne_nil O.nonempty
          omega
      have hlenSub : ((O.vertices.length - 1 : ℕ) : ℤ) =
          (O.vertices.length : ℤ) - 1 := by omega
      rw [hlenSub] at hpathLower
      nlinarith
    have htotalScaled := Int.mul_le_mul_of_nonneg_left
      htotalLower hlambdaNonneg
    have hrows : pathForestAbsorptionPieceSurplus hk P Z ≤
        (O.vertices.length : ℤ) * n -
          lambda * (absorptionListEdgeCharge A B O.vertices +
            A (O.vertices.head O.nonempty) +
            B (O.vertices.getLast O.nonempty)) +
          lambda * (O.vertices.length : ℤ) * etaMax := by
      rw [hsumEq]
      rw [hreindex]
      exact hsumRows
    have hbound : pathForestAbsorptionPieceSurplus hk P Z ≤
        (O.vertices.length : ℤ) * n -
          lambda * ((O.vertices.length : ℤ) * lambda) +
          lambda * (O.vertices.length : ℤ) * etaMax := by
      nlinarith
    have hn : 6 ≤ n := by dsimp [n]; omega
    have hlambdaN : lambda = n - 2 := by
      have hlambdaNat := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
      have hcast : lambda + 2 = n := by
        dsimp [lambda, n]
        exact_mod_cast hlambdaNat
      omega
    have hetaN : etaMax = n - 5 := by
      dsimp [etaMax, n]
      omega
    have hj : 1 ≤ (O.vertices.length : ℤ) := by
      have := List.length_pos_of_ne_nil O.nonempty
      omega
    rw [hlambdaN, hetaN] at hbound
    exact hbound.trans (absorption_cycle_arithmetic n O.vertices.length hn hj)

/-- **Pieces carrying an edge (`lem:pieces`).** For `n=k-1≥6`, the
genuine signed surplus over every actual edge-carrying absorption piece is
nonpositive.  The proof separately handles a type-(i) self-loop, a path of
at least two vertices with type-(ii) edges, and a type-(ii) directed cycle,
including a one-vertex type-(ii) self-loop. -/
theorem pathForestAbsorptionPieceSurplus_le_zero (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty) :
    pathForestAbsorptionPieceSurplus hk P Z ≤ 0 := by
  rcases pathForestAbsorptionPiece_path_or_cycle hk P Z with hpath | hcycle
  · obtain ⟨O⟩ := hpath
    exact pathForestAbsorptionPieceSurplus_path_nonpos hk P hP Z O hZedge
  · obtain ⟨O⟩ := hcycle
    exact pathForestAbsorptionPieceSurplus_cycle_nonpos hk P hP Z O

end SuperpermutationLowerBound
