module

public import SuperpermutationLowerBound.Section10.AbsorptionPieces

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Theorem `thm:assembly`.  All sums below range over the actual
components of the transformed forest and the genuine connected pieces of the
literal absorption digraph. -/

variable {k : ℕ}

private abbrev AssemblyVertex (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  WeakComponent (pathForest (by omega) P)

/-! ## The genuine partition into pieces -/

/-- The genuine absorption piece containing an actual forest component. -/
noncomputable def pathForestAbsorptionPieceOf (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : AssemblyVertex hk P) :
    PathForestAbsorptionPiece hk P :=
  (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk C

@[simp] theorem pathForestAbsorptionPieceOf_mem (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : AssemblyVertex hk P) :
    C ∈ (pathForestAbsorptionPieceOf hk P C).supp :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- The dependent union of the genuine pieces is exactly the type of actual
forest components.  This is the partition statement, including uniqueness. -/
noncomputable def pathForestAbsorptionPiecesEquivComponents (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (Σ Z : PathForestAbsorptionPiece hk P, Z) ≃ AssemblyVertex hk P where
  toFun x := x.2.1
  invFun C := ⟨pathForestAbsorptionPieceOf hk P C,
    ⟨C, pathForestAbsorptionPieceOf_mem hk P C⟩⟩
  left_inv x := by
    rcases x with ⟨Z, ⟨C, hC⟩⟩
    change pathForestAbsorptionPieceOf hk P C = Z at hC
    subst Z
    rfl
  right_inv _ := rfl

/-- Summing the actual piece surpluses recovers the actual global component
surplus, with every forest component counted exactly once. -/
theorem pathForestAbsorptionPieces_surplus_sum (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (∑ Z : PathForestAbsorptionPiece hk P,
        pathForestAbsorptionPieceSurplus hk P Z) =
      pathForestTotalSurplus hk P := by
  classical
  rw [pathForestTotalSurplus, Fintype.sum_equiv
    (pathForestAbsorptionPiecesEquivComponents hk P).symm
    (fun C : AssemblyVertex hk P => pathForestComponentSurplus hk P C)
    (fun x => pathForestComponentSurplus hk P x.2.1)]
  · rw [Fintype.sum_sigma]
    rfl
  · intro x
    rfl

/-! ## Unabsorbed members of `U` and `U`-headed directed paths -/

/-- An actual member of `U` is absorbed exactly when it has a literal incoming
edge in the absorption digraph. -/
theorem pathForest_mem_MFour_iff_absorption_incoming (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestMFour hk P ↔
      ∃ q : AssemblyVertex hk P,
        (pathForestAbsorptionGraph hk P).Adj q p.1 := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := pathForestAbsorber_exists hk P hp
    exact ⟨q, p, rfl, hq⟩
  · rintro ⟨q, r, hr, hqr⟩
    have hpr : p = r := by
      apply Subtype.ext
      exact hr.symm
    simpa [hpr] using hqr.1

/-- The actual unabsorbed members of `U`. -/
noncomputable def pathForestUnabsorbedU (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Finset (PathForestNonrootComponent hk P) := by
  classical
  exact (pathForestU hk P).filter (fun p => p ∉ pathForestMFour hk P)

@[simp] theorem mem_pathForestUnabsorbedU (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P) :
    p ∈ pathForestUnabsorbedU hk P ↔
      p ∈ pathForestU hk P ∧
        ¬∃ q : AssemblyVertex hk P,
          (pathForestAbsorptionGraph hk P).Adj q p.1 := by
  classical
  simp only [pathForestUnabsorbedU, Finset.mem_filter]
  rw [pathForest_mem_MFour_iff_absorption_incoming]

/-- Exactly `f` members of `U` are absorbed. -/
theorem pathForest_absorbedU_card (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestMFour hk P).card = pathForestF hk P := rfl

/-- Exactly `V=M-f` members of `U` are unabsorbed. -/
theorem pathForestUnabsorbedU_card (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestUnabsorbedU hk P).card = pathForestV hk P := by
  classical
  have hsub : pathForestMFour hk P ⊆ pathForestU hk P := by
    intro p hp
    exact ((mem_pathForestMFour hk P p).mp hp).1
  rw [pathForestUnabsorbedU,
    ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hsub]
  rfl

/-- A genuine piece is `U`-headed when it admits an honest directed-path
order whose first actual component is a member of `U`. -/
def IsPathForestUHeadedPiece (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) : Prop :=
  ∃ O : PathForestAbsorptionPathOrder hk P Z,
    ∃ p : PathForestNonrootComponent hk P,
      p ∈ pathForestU hk P ∧
        (O.vertices.head O.nonempty).1 = p.1

/-- The genuine finite collection of `U`-headed directed-path pieces. -/
noncomputable def pathForestUHeadedPieces (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Finset (PathForestAbsorptionPiece hk P) := by
  classical
  exact (pathForestAbsorptionPieces hk P).filter
    (IsPathForestUHeadedPiece hk P)

@[simp] theorem mem_pathForestUHeadedPieces (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P) :
    Z ∈ pathForestUHeadedPieces hk P ↔
      IsPathForestUHeadedPiece hk P Z := by
  classical
  simp [pathForestUHeadedPieces, pathForestAbsorptionPieces]

private theorem absorptionPathOrder_first_of_no_incoming
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z) (v : Z)
    (hv : ∀ q : Z,
      ¬(pathForestAbsorptionGraph hk P).Adj q.1 v.1) :
    v = O.vertices.head O.nonempty := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (O.covers v)
  have hiZero : idx.1 = 0 := by
    by_contra hne
    let i := idx.1 - 1
    have hi : i + 1 < O.vertices.length := by
      dsimp [i]
      omega
    have hvAt : O.vertices[i + 1] = v := by
      have hieq : i + 1 = idx.1 := by
        dsimp [i]
        omega
      simpa [hieq] using hidx
    have hedge := (O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
      ⟨i, hi, rfl, rfl⟩
    exact hv O.vertices[i] (by simpa [hvAt] using hedge)
  calc
    v = O.vertices.get idx := hidx.symm
    _ = O.vertices.get ⟨0, by omega⟩ := by
      congr 1
      exact Fin.ext hiZero
    _ = O.vertices.head O.nonempty :=
      (List.head_eq_getElem_zero O.nonempty).symm

private theorem absorptionCycleOrder_has_incoming
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionCycleOrder hk P Z) (v : Z) :
    ∃ q : Z, (pathForestAbsorptionGraph hk P).Adj q.1 v.1 := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp (O.covers v)
  by_cases hiZero : idx.1 = 0
  · refine ⟨O.vertices.getLast O.nonempty, ?_⟩
    have hvHead : v = O.vertices.head O.nonempty := by
      calc
        v = O.vertices.get idx := hidx.symm
        _ = O.vertices.get ⟨0, by omega⟩ := by
          congr 1
          exact Fin.ext hiZero
        _ = O.vertices.head O.nonempty :=
          (List.head_eq_getElem_zero O.nonempty).symm
    simpa [hvHead] using
      (O.edge_iff (O.vertices.getLast O.nonempty)
        (O.vertices.head O.nonempty)).mpr (Or.inr ⟨rfl, rfl⟩)
  · let i := idx.1 - 1
    have hi : i + 1 < O.vertices.length := by
      dsimp [i]
      omega
    have hvAt : O.vertices[i + 1] = v := by
      have hieq : i + 1 = idx.1 := by
        dsimp [i]
        omega
      simpa [hieq] using hidx
    refine ⟨O.vertices[i], ?_⟩
    simpa [hvAt] using
      (O.edge_iff O.vertices[i] O.vertices[i + 1]).mpr
        (Or.inl ⟨i, hi, rfl, rfl⟩)

private theorem absorptionPiece_local_no_incoming_of_global
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P) (v : Z)
    (hv : ¬∃ q : AssemblyVertex hk P,
      (pathForestAbsorptionGraph hk P).Adj q v.1) :
    ∀ q : Z, ¬(pathForestAbsorptionGraph hk P).Adj q.1 v.1 := by
  intro q hq
  exact hv ⟨q.1, hq⟩

private theorem absorptionPiece_global_no_incoming_of_path_head
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (O : PathForestAbsorptionPathOrder hk P Z) :
    ¬∃ q : AssemblyVertex hk P,
      (pathForestAbsorptionGraph hk P).Adj q
        (O.vertices.head O.nonempty).1 := by
  rintro ⟨q, hq⟩
  let first := O.vertices.head O.nonempty
  have hqPiece : q ∈ Z.supp := by
    by_cases hqfirst : q = first.1
    · subst q
      exact first.2
    · have hadj : (pathForestAbsorptionUnderlyingGraph hk P).Adj q first.1 :=
        ⟨hqfirst, Or.inl hq⟩
      have hcomp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hfirstComp :
          (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk
              first.1 = Z := first.2
      exact hcomp.trans hfirstComp
  let qZ : Z := ⟨q, hqPiece⟩
  obtain ⟨i, hi, _hsource, htarget⟩ :=
    (O.edge_iff qZ first).mp (by simpa [qZ, first] using hq)
  have heq : O.vertices[i + 1] = O.vertices[0] := by
    simpa [first, List.head_eq_getElem_zero O.nonempty] using htarget
  have hindices := O.nodup.getElem_inj_iff.mp heq
  omega

private theorem unabsorbed_piece_is_UHeaded (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hp : p ∈ pathForestUnabsorbedU hk P) :
    IsPathForestUHeadedPiece hk P
      (pathForestAbsorptionPieceOf hk P p.1) := by
  have hpData := (mem_pathForestUnabsorbedU hk P p).mp hp
  let Z := pathForestAbsorptionPieceOf hk P p.1
  let vp : Z := ⟨p.1, pathForestAbsorptionPieceOf_mem hk P p.1⟩
  rcases pathForestAbsorptionPiece_path_or_cycle hk P Z with hpath | hcycle
  · obtain ⟨O⟩ := hpath
    have hvNo := absorptionPiece_local_no_incoming_of_global hk P Z vp hpData.2
    have hvFirst := absorptionPathOrder_first_of_no_incoming hk P Z O vp hvNo
    exact ⟨O, p, hpData.1, by simpa [vp] using congrArg Subtype.val hvFirst.symm⟩
  · obtain ⟨O⟩ := hcycle
    obtain ⟨q, hq⟩ := absorptionCycleOrder_has_incoming hk P Z O vp
    exact (hpData.2 ⟨q.1, by simpa [vp] using hq⟩).elim

private theorem UHeaded_has_unabsorbed_head (hk : 7 ≤ k)
    (P : HamiltonianPath k) (Z : PathForestAbsorptionPiece hk P)
    (hZ : IsPathForestUHeadedPiece hk P Z) :
    ∃ p : PathForestNonrootComponent hk P,
      p ∈ pathForestUnabsorbedU hk P ∧
        pathForestAbsorptionPieceOf hk P p.1 = Z := by
  obtain ⟨O, p, hpU, hhead⟩ := hZ
  have hnone := absorptionPiece_global_no_incoming_of_path_head hk P Z O
  have hpNone : ¬∃ q : AssemblyVertex hk P,
      (pathForestAbsorptionGraph hk P).Adj q p.1 := by
    simpa [hhead] using hnone
  have hpUn : p ∈ pathForestUnabsorbedU hk P :=
    (mem_pathForestUnabsorbedU hk P p).mpr ⟨hpU, hpNone⟩
  have hpiece : pathForestAbsorptionPieceOf hk P p.1 = Z := by
    have hm := (O.vertices.head O.nonempty).2
    change (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk
      (O.vertices.head O.nonempty).1 = Z at hm
    rw [hhead] at hm
    exact hm
  exact ⟨p, hpUn, hpiece⟩

private theorem unabsorbed_piece_map_injective (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Set.InjOn (fun p : PathForestNonrootComponent hk P =>
      pathForestAbsorptionPieceOf hk P p.1)
      {p | p ∈ pathForestUnabsorbedU hk P} := by
  intro p hp q hq hpq
  have hpData := (mem_pathForestUnabsorbedU hk P p).mp hp
  have hqData := (mem_pathForestUnabsorbedU hk P q).mp hq
  let Z := pathForestAbsorptionPieceOf hk P p.1
  let vp : Z := ⟨p.1, pathForestAbsorptionPieceOf_mem hk P p.1⟩
  let vq : Z := ⟨q.1, by
    change q.1 ∈ (pathForestAbsorptionPieceOf hk P p.1).supp
    change (pathForestAbsorptionUnderlyingGraph hk P).connectedComponentMk q.1 =
      pathForestAbsorptionPieceOf hk P p.1
    exact hpq.symm⟩
  rcases pathForestAbsorptionPiece_path_or_cycle hk P Z with hpath | hcycle
  · obtain ⟨O⟩ := hpath
    have hpFirst := absorptionPathOrder_first_of_no_incoming hk P Z O vp
      (absorptionPiece_local_no_incoming_of_global hk P Z vp hpData.2)
    have hqFirst := absorptionPathOrder_first_of_no_incoming hk P Z O vq
      (absorptionPiece_local_no_incoming_of_global hk P Z vq hqData.2)
    have hpqVal : vp.1 = vq.1 :=
      congrArg (fun x : Z => x.1) (hpFirst.trans hqFirst.symm)
    apply Subtype.ext
    exact hpqVal
  · obtain ⟨O⟩ := hcycle
    obtain ⟨r, hr⟩ := absorptionCycleOrder_has_incoming hk P Z O vp
    exact (hpData.2 ⟨r.1, by simpa [vp] using hr⟩).elim

abbrev PathForestUnabsorbedUMember (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  {p : PathForestNonrootComponent hk P // p ∈ pathForestUnabsorbedU hk P}

abbrev PathForestUHeadedPiece (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  {Z : PathForestAbsorptionPiece hk P // Z ∈ pathForestUHeadedPieces hk P}

/-- The literal bijection from unabsorbed members of `U` to genuine
`U`-headed directed-path pieces. -/
noncomputable def pathForestUnabsorbedUEquivUHeadedPieces (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    PathForestUnabsorbedUMember hk P ≃ PathForestUHeadedPiece hk P := by
  classical
  let f : PathForestUnabsorbedUMember hk P → PathForestUHeadedPiece hk P :=
    fun p => ⟨pathForestAbsorptionPieceOf hk P p.1.1,
      (mem_pathForestUHeadedPieces hk P _).mpr
        (unabsorbed_piece_is_UHeaded hk P p.1 p.2)⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply unabsorbed_piece_map_injective hk P p.2 q.2
    exact congrArg Subtype.val hpq
  · intro Z
    obtain ⟨p, hp, hpZ⟩ := UHeaded_has_unabsorbed_head hk P Z.1
      ((mem_pathForestUHeadedPieces hk P Z.1).mp Z.2)
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hpZ

/-- Therefore the number of genuine `U`-headed path pieces is exactly
`V=M-f`, not merely bounded by it. -/
theorem pathForestUHeadedPieces_card (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    (pathForestUHeadedPieces hk P).card = pathForestV hk P := by
  classical
  have hcard := Fintype.card_congr
    (pathForestUnabsorbedUEquivUHeadedPieces hk P)
  calc
    (pathForestUHeadedPieces hk P).card =
        Fintype.card (PathForestUHeadedPiece hk P) := by simp
    _ = Fintype.card (PathForestUnabsorbedUMember hk P) := hcard.symm
    _ = (pathForestUnabsorbedU hk P).card := by simp
    _ = pathForestV hk P := pathForestUnabsorbedU_card hk P

/-! ## The root piece and isolated pieces -/

/-- The genuine absorption piece containing the actual root component. -/
noncomputable def pathForestRootAbsorptionPiece (hk : 7 ≤ k)
    (P : HamiltonianPath k) : PathForestAbsorptionPiece hk P :=
  pathForestAbsorptionPieceOf hk P
    (pathForestRootComponent (by omega) P)

/-- The root piece is distinct from every `U`-headed piece. -/
theorem pathForestRootAbsorptionPiece_not_UHeaded (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    pathForestRootAbsorptionPiece hk P ∉
      pathForestUHeadedPieces hk P := by
  rw [mem_pathForestUHeadedPieces]
  rintro ⟨O, p, hpU, hhead⟩
  let root := pathForestRootComponent (by omega) P
  let Z := pathForestRootAbsorptionPiece hk P
  let vr : Z := ⟨root, pathForestAbsorptionPieceOf_mem hk P root⟩
  have hrootNone : ¬∃ q : AssemblyVertex hk P,
      (pathForestAbsorptionGraph hk P).Adj q root := by
    rintro ⟨q, hq⟩
    exact pathForestAbsorption_root_not_target hk P q hq
  have hfirst := absorptionPathOrder_first_of_no_incoming hk P Z O vr
    (absorptionPiece_local_no_incoming_of_global hk P Z vr hrootNone)
  have hrootEq : root = p.1 := by
    calc
      root = (O.vertices.head O.nonempty).1 :=
        congrArg (fun x : Z => x.1) hfirst
      _ = p.1 := hhead
  exact p.2 hrootEq.symm

private theorem absorptionPiece_singleton_of_no_edges
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (hno : ¬(pathForestAbsorptionPieceEdges hk P Z).Nonempty)
    (q : Z) : ∀ v : Z, v = q := by
  have hnoAdj : ∀ r : Z, ¬Z.toSimpleGraph.Adj q r := by
    intro r hqr
    have hbase : (pathForestAbsorptionUnderlyingGraph hk P).Adj q.1 r.1 :=
      (Z.toSimpleGraph_adj q.2 r.2).1 hqr
    rcases hbase.2 with hforward | hbackward
    · exact hno ⟨(q.1, r.1),
        (mem_pathForestAbsorptionPieceEdges hk P Z _).mpr
          ⟨q.2, r.2, hforward⟩⟩
    · exact hno ⟨(r.1, q.1),
        (mem_pathForestAbsorptionPieceEdges hk P Z _).mpr
          ⟨r.2, q.2, hbackward⟩⟩
  intro v
  obtain ⟨w⟩ := Z.connected_toSimpleGraph q v
  cases w with
  | nil => rfl
  | cons hadj rest => exact (hnoAdj _ hadj).elim

private theorem absorptionPieceSurplus_eq_component_of_no_edges
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (hno : ¬(pathForestAbsorptionPieceEdges hk P Z).Nonempty)
    (q : Z) :
    pathForestAbsorptionPieceSurplus hk P Z =
      pathForestComponentSurplus hk P q.1 := by
  classical
  have hall := absorptionPiece_singleton_of_no_edges hk P Z hno q
  have hcard : Fintype.card Z = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨q, hall⟩
  have huniv : (Finset.univ : Finset Z) = {q} :=
    univ_eq_singleton_of_card_one q hcard
  rw [pathForestAbsorptionPieceSurplus, huniv]
  simp

private theorem absorptionPiece_no_incoming_of_no_edges
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (Z : PathForestAbsorptionPiece hk P)
    (hno : ¬(pathForestAbsorptionPieceEdges hk P Z).Nonempty)
    (v : Z) :
    ¬∃ q : AssemblyVertex hk P,
      (pathForestAbsorptionGraph hk P).Adj q v.1 := by
  rintro ⟨q, hq⟩
  have hqPiece : q ∈ Z.supp := by
    by_cases hqv : q = v.1
    · subst q
      exact v.2
    · have hadj : (pathForestAbsorptionUnderlyingGraph hk P).Adj q v.1 :=
        ⟨hqv, Or.inl hq⟩
      have hcomp :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      exact hcomp.trans v.2
  exact hno ⟨(q, v.1),
    (mem_pathForestAbsorptionPieceEdges hk P Z _).mpr
      ⟨hqPiece, v.2, hq⟩⟩

private theorem pathForestCheapSurplus_le_n (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentSurplus hk P p.1 ≤ ((k - 1 : ℕ) : ℤ) := by
  by_cases hz : pathForestComponentZ (by omega) P p.1 = 1
  · have hrow := pathForestCheapSurplus_z_one hk P p hpU hz
    have hlambda : (4 : ℤ) ≤ surplusLambda (k - 1) := by
      exact_mod_cast (surplusLambda_range (show 6 ≤ k - 1 by omega)).1
    have hd : (1 : ℤ) ≤
        pathForestComponentFirstDeficit hk P p.1 := by
      exact_mod_cast hrow.2.1
    rw [hrow.2.2.1]
    nlinarith
  · have hzPos := pathForestComponentZ_pos (by omega) P p.1
    have hzTwo : 2 ≤ pathForestComponentZ (by omega) P p.1 := by omega
    have hrow := pathForestCheapSurplus_ge_two_le hk P p hpU hzTwo
    have hlambda : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
    have hcharges : (0 : ℤ) ≤
        (endpointChargeA (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
          (endpointChargeB (pathForestComponentLastDeficit hk P p.1) : ℤ) := by
      omega
    nlinarith

private theorem pathForestRootComponentSurplus_le (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    pathForestComponentSurplus hk P
        (pathForestRootComponent (by omega) P) ≤
      2 * ((k - 1 : ℕ) : ℤ) - 2 := by
  have hrow := pathForestRootSurplus_le hk P
  have hlambda : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
  have hcharge : (0 : ℤ) ≤
      (endpointChargeB
        (pathForestComponentLastDeficit hk P
          (pathForestRootComponent (by omega) P)) : ℤ) := by omega
  nlinarith

/-- Every genuine `U`-headed piece contributes at most `n`, separating
the edge-carrying and isolated cases. -/
theorem pathForestUHeadedPieceSurplus_le (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (hZ : Z ∈ pathForestUHeadedPieces hk P) :
    pathForestAbsorptionPieceSurplus hk P Z ≤
      ((k - 1 : ℕ) : ℤ) := by
  by_cases hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty
  · exact (pathForestAbsorptionPieceSurplus_le_zero hk P hP Z hZedge).trans
      (by omega)
  · obtain ⟨p, hpUn, hpZ⟩ := UHeaded_has_unabsorbed_head hk P Z
      ((mem_pathForestUHeadedPieces hk P Z).mp hZ)
    let vp : Z := ⟨p.1, by
      change pathForestAbsorptionPieceOf hk P p.1 = Z
      exact hpZ⟩
    rw [absorptionPieceSurplus_eq_component_of_no_edges hk P Z hZedge vp]
    exact pathForestCheapSurplus_le_n hk P p
      ((mem_pathForestUnabsorbedU hk P p).mp hpUn).1

/-- The possible root piece contributes at most `2n-2`, again separating
the edge-carrying and isolated cases. -/
theorem pathForestRootAbsorptionPieceSurplus_le (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestAbsorptionPieceSurplus hk P
        (pathForestRootAbsorptionPiece hk P) ≤
      2 * ((k - 1 : ℕ) : ℤ) - 2 := by
  let Z := pathForestRootAbsorptionPiece hk P
  by_cases hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty
  · exact (pathForestAbsorptionPieceSurplus_le_zero hk P hP Z hZedge).trans
      (by omega)
  · let root := pathForestRootComponent (by omega) P
    let vr : Z := ⟨root, pathForestAbsorptionPieceOf_mem hk P root⟩
    rw [absorptionPieceSurplus_eq_component_of_no_edges hk P Z hZedge vr]
    exact pathForestRootComponentSurplus_le hk P

/-- Every piece other than the root piece and the `U`-headed pieces has
nonpositive surplus. -/
theorem pathForestRemainingAbsorptionPieceSurplus_le_zero (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (Z : PathForestAbsorptionPiece hk P)
    (hroot : Z ≠ pathForestRootAbsorptionPiece hk P)
    (hU : Z ∉ pathForestUHeadedPieces hk P) :
    pathForestAbsorptionPieceSurplus hk P Z ≤ 0 := by
  by_cases hZedge : (pathForestAbsorptionPieceEdges hk P Z).Nonempty
  · exact pathForestAbsorptionPieceSurplus_le_zero hk P hP Z hZedge
  · obtain ⟨C, hC⟩ := Z.nonempty_supp
    let q : Z := ⟨C, hC⟩
    have hCpiece : pathForestAbsorptionPieceOf hk P C = Z := hC
    have hCNonroot : C ≠ pathForestRootComponent (by omega) P := by
      intro hEq
      apply hroot
      calc
        Z = pathForestAbsorptionPieceOf hk P C := hCpiece.symm
        _ = pathForestAbsorptionPieceOf hk P
            (pathForestRootComponent (by omega) P) := by rw [hEq]
        _ = pathForestRootAbsorptionPiece hk P := rfl
    let p : PathForestNonrootComponent hk P := ⟨C, hCNonroot⟩
    have hpNotU : p ∉ pathForestU hk P := by
      intro hpU
      have hpUn : p ∈ pathForestUnabsorbedU hk P :=
        (mem_pathForestUnabsorbedU hk P p).mpr ⟨hpU,
          absorptionPiece_no_incoming_of_no_edges hk P Z hZedge q⟩
      apply hU
      rw [mem_pathForestUHeadedPieces]
      have hheaded := unabsorbed_piece_is_UHeaded hk P p hpUn
      change IsPathForestUHeadedPiece hk P Z
      have hpPiece : pathForestAbsorptionPieceOf hk P p.1 = Z := by
        exact hCpiece
      simpa [hpPiece] using hheaded
    have hmintoNonroot : 3 ≤ pathForestNonrootMinto hk P p := by
      have htwo := (pathForestNonrootMinto_bounds hk P p).1
      have hne : pathForestNonrootMinto hk P p ≠ 2 := by
        intro heq
        exact hpNotU ((mem_pathForestU hk P p).mpr heq)
      omega
    have hminto : 3 ≤ pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hCNonroot) := by
      simpa [p, pathForestNonrootMinto] using hmintoNonroot
    rw [absorptionPieceSurplus_eq_component_of_no_edges hk P Z hZedge q]
    exact (pathForestNoncheapSurplus_le hk P C hCNonroot hminto).2.le

/-! ## Summing the distinguished pieces -/

private theorem pathForestTotalSurplus_le_UHeads_add_root (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestTotalSurplus hk P ≤
      ((pathForestUHeadedPieces hk P).card : ℤ) *
          ((k - 1 : ℕ) : ℤ) +
        (2 * ((k - 1 : ℕ) : ℤ) - 2) := by
  classical
  let root := pathForestRootAbsorptionPiece hk P
  let n : ℤ := ((k - 1 : ℕ) : ℤ)
  let rootBound : ℤ := 2 * n - 2
  have hpoint : ∀ Z : PathForestAbsorptionPiece hk P,
      pathForestAbsorptionPieceSurplus hk P Z ≤
        (if Z ∈ pathForestUHeadedPieces hk P then n else 0) +
          (if Z = root then rootBound else 0) := by
    intro Z
    by_cases hZU : Z ∈ pathForestUHeadedPieces hk P
    · have hZroot : Z ≠ root := by
        intro hEq
        apply pathForestRootAbsorptionPiece_not_UHeaded hk P
        simpa [root, hEq] using hZU
      simp only [if_pos hZU, if_neg hZroot]
      simpa [n] using pathForestUHeadedPieceSurplus_le hk P hP Z hZU
    · by_cases hZroot : Z = root
      · subst Z
        simp only [if_neg hZU, zero_add]
        simpa [root, rootBound, n] using
          pathForestRootAbsorptionPieceSurplus_le hk P hP
      · simp only [if_neg hZU, if_neg hZroot, add_zero]
        exact pathForestRemainingAbsorptionPieceSurplus_le_zero hk P hP Z
          (by simpa [root] using hZroot) hZU
  have hsum :
      (∑ Z : PathForestAbsorptionPiece hk P,
          pathForestAbsorptionPieceSurplus hk P Z) ≤
        (∑ Z : PathForestAbsorptionPiece hk P,
          ((if Z ∈ pathForestUHeadedPieces hk P then n else 0) +
            (if Z = root then rootBound else 0))) := by
    exact Finset.sum_le_sum fun Z _hZ => hpoint Z
  rw [pathForestAbsorptionPieces_surplus_sum hk P] at hsum
  have hheadSum :
      (∑ Z : PathForestAbsorptionPiece hk P,
        if Z ∈ pathForestUHeadedPieces hk P then n else 0) =
        ((pathForestUHeadedPieces hk P).card : ℤ) * n := by
    rw [Finset.sum_ite_mem_eq]
    simp [Finset.sum_const]
  have hrootSum :
      (∑ Z : PathForestAbsorptionPiece hk P,
        if Z = root then rootBound else 0) = rootBound := by
    simp
  rw [Finset.sum_add_distrib, hheadSum, hrootSum] at hsum
  simpa [n, rootBound] using hsum

private theorem pathForestTotalSurplus_le_actual_exceptions (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestTotalSurplus hk P ≤
      (∑ Z ∈ pathForestUHeadedPieces hk P,
          pathForestAbsorptionPieceSurplus hk P Z) +
        pathForestAbsorptionPieceSurplus hk P
          (pathForestRootAbsorptionPiece hk P) := by
  classical
  let root := pathForestRootAbsorptionPiece hk P
  have hpoint : ∀ Z : PathForestAbsorptionPiece hk P,
      pathForestAbsorptionPieceSurplus hk P Z ≤
        (if Z ∈ pathForestUHeadedPieces hk P then
          pathForestAbsorptionPieceSurplus hk P Z else 0) +
        (if Z = root then
          pathForestAbsorptionPieceSurplus hk P root else 0) := by
    intro Z
    by_cases hZU : Z ∈ pathForestUHeadedPieces hk P
    · have hZroot : Z ≠ root := by
        intro hEq
        apply pathForestRootAbsorptionPiece_not_UHeaded hk P
        simpa [root, hEq] using hZU
      simp [hZU, hZroot]
    · by_cases hZroot : Z = root
      · subst Z
        simp [hZU]
      · simpa [hZU, hZroot] using
          pathForestRemainingAbsorptionPieceSurplus_le_zero hk P hP Z
            (by simpa [root] using hZroot) hZU
  have hsum :
      (∑ Z : PathForestAbsorptionPiece hk P,
          pathForestAbsorptionPieceSurplus hk P Z) ≤
        (∑ Z : PathForestAbsorptionPiece hk P,
          ((if Z ∈ pathForestUHeadedPieces hk P then
            pathForestAbsorptionPieceSurplus hk P Z else 0) +
            (if Z = root then
              pathForestAbsorptionPieceSurplus hk P root else 0))) := by
    exact Finset.sum_le_sum fun Z _hZ => hpoint Z
  rw [pathForestAbsorptionPieces_surplus_sum hk P] at hsum
  have hheadSum :
      (∑ Z : PathForestAbsorptionPiece hk P,
        if Z ∈ pathForestUHeadedPieces hk P then
          pathForestAbsorptionPieceSurplus hk P Z else 0) =
        ∑ Z ∈ pathForestUHeadedPieces hk P,
          pathForestAbsorptionPieceSurplus hk P Z := by
    rw [Finset.sum_ite_mem_eq]
  have hrootSum :
      (∑ Z : PathForestAbsorptionPiece hk P,
        if Z = root then pathForestAbsorptionPieceSurplus hk P root else 0) =
        pathForestAbsorptionPieceSurplus hk P root := by
    simp
  rw [Finset.sum_add_distrib, hheadSum, hrootSum] at hsum
  simpa [root] using hsum

/-- In the case `V≥2`, summing the actual distinguished pieces gives the
exact intermediate bound `Vn+2n-2`. -/
theorem pathForestTotalSurplus_le_of_two_le_V (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (_hV : 2 ≤ pathForestV hk P) :
    pathForestTotalSurplus hk P ≤
      (pathForestV hk P : ℤ) * ((k - 1 : ℕ) : ℤ) +
        2 * ((k - 1 : ℕ) : ℤ) - 2 := by
  have hsum := pathForestTotalSurplus_le_UHeads_add_root hk P hP
  rw [pathForestUHeadedPieces_card hk P] at hsum
  linarith

/-- The exact `Vn+2n-2` bound is below the charged target for `V≥2`.
The proof formalizes the `V=2` base and the strict `κ>n` increment. -/
theorem pathForest_V_ge_two_comparison (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hV : 2 ≤ pathForestV hk P) :
    (pathForestV hk P : ℤ) * ((k - 1 : ℕ) : ℤ) +
        2 * ((k - 1 : ℕ) : ℤ) - 2 ≤
      2 * ((k - 1 : ℕ) : ℤ) +
        (surplusKappa (k - 1) : ℤ) *
          (max
            (max 0 (pathForestTerminalFullCount hk P - 1))
            (pathForestV hk P - 1) : ℕ) := by
  let n : ℤ := ((k - 1 : ℕ) : ℤ)
  let kappa : ℤ := (surplusKappa (k - 1) : ℤ)
  let V := pathForestV hk P
  let m := V - 2
  let Q := max (max 0 (pathForestTerminalFullCount hk P - 1)) (V - 1)
  have hVdecompNat : m + 2 = V := by
    dsimp [m, V]
    omega
  have hVdecomp : (V : ℤ) = (m : ℤ) + 2 := by
    exact_mod_cast hVdecompNat.symm
  have hkappaLarge := surplusKappa_gt_two_mul_sub_two
    (show 6 ≤ k - 1 by omega)
  have hbase : 2 * n - 2 ≤ kappa := by
    dsimp [n, kappa]
    omega
  have hincrement : n ≤ kappa := by
    dsimp [n, kappa] at hkappaLarge ⊢
    omega
  have hmNonnegative : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hscaledIncrement : (m : ℤ) * n ≤ (m : ℤ) * kappa :=
    Int.mul_le_mul_of_nonneg_left hincrement hmNonnegative
  have huncharged :
      (V : ℤ) * n + 2 * n - 2 ≤
        2 * n + kappa * ((V - 1 : ℕ) : ℤ) := by
    have hVminusNat : V - 1 = m + 1 := by
      dsimp [m]
      omega
    have hVminus : ((V - 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by
      exact_mod_cast hVminusNat
    rw [hVdecomp, hVminus]
    nlinarith
  have hQ : V - 1 ≤ Q := by
    exact Nat.le_max_right _ _
  have hQInt : ((V - 1 : ℕ) : ℤ) ≤ (Q : ℤ) := by
    exact_mod_cast hQ
  have hkappaNonnegative : (0 : ℤ) ≤ kappa := by
    dsimp [kappa]
    omega
  have hcharge := Int.mul_le_mul_of_nonneg_left hQInt hkappaNonnegative
  dsimp [V, Q, n, kappa] at huncharged hcharge ⊢
  exact huncharged.trans (by nlinarith [hcharge])

/-! ## The case `V≤1` -/

private theorem endpointChargeB_ge_one_of_pos {y : ℕ} (hy : 1 ≤ y) :
    1 ≤ endpointChargeB y := by
  by_cases hyOne : y = 1
  · simp [hyOne]
  · have hyTwo : 2 ≤ y := by omega
    rw [endpointChargeB_eq_sub_one hyTwo]
    omega

private theorem pathForestCheapSurplus_B_bound_J3 (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB
            (pathForestComponentLastDeficit hk P p.1) : ℤ) := by
  by_cases hz : pathForestComponentZ (by omega) P p.1 = 1
  · have hrow := pathForestCheapSurplus_z_one hk P p hpU hz
    exact hrow.2.2.2.2.1.trans (min_le_left _ _)
  · have hzPos := pathForestComponentZ_pos (by omega) P p.1
    have hzTwo : 2 ≤ pathForestComponentZ (by omega) P p.1 := by omega
    have hrow := pathForestCheapSurplus_ge_two_le hk P p hpU hzTwo
    have hlambda : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
    have hA : (0 : ℤ) ≤
        (endpointChargeA
          (pathForestComponentFirstDeficit hk P p.1) : ℤ) := by omega
    nlinarith

/-- For `V≤1`, only an isolated root and at most one isolated unabsorbed
`U`-component can contribute positively.  This proof includes all three
endpoint-deficit subcases in the TeX. -/
theorem pathForestTotalSurplus_le_of_V_le_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    (hV : pathForestV hk P ≤ 1) :
    pathForestTotalSurplus hk P ≤
      2 * ((k - 1 : ℕ) : ℤ) +
        (surplusKappa (k - 1) : ℤ) *
          (max
            (max 0 (pathForestTerminalFullCount hk P - 1))
            (pathForestV hk P - 1) : ℕ) := by
  classical
  let heads := pathForestUHeadedPieces hk P
  let rootPiece := pathForestRootAbsorptionPiece hk P
  let n : ℤ := ((k - 1 : ℕ) : ℤ)
  let kappa : ℤ := (surplusKappa (k - 1) : ℤ)
  let Q := max (max 0 (pathForestTerminalFullCount hk P - 1))
    (pathForestV hk P - 1)
  change pathForestTotalSurplus hk P ≤ 2 * n + kappa * (Q : ℤ)
  have hheadsCard : heads.card ≤ 1 := by
    dsimp [heads]
    rw [pathForestUHeadedPieces_card hk P]
    exact hV
  have hkappaNonnegative : (0 : ℤ) ≤ kappa := by
    dsimp [kappa]
    omega
  have hQNonnegative : (0 : ℤ) ≤ (Q : ℤ) := by omega
  have hchargeNonnegative : (0 : ℤ) ≤ kappa * (Q : ℤ) :=
    mul_nonneg hkappaNonnegative hQNonnegative
  have hexceptions := pathForestTotalSurplus_le_actual_exceptions hk P hP
  by_cases hheadsEmpty : heads = ∅
  · have htotalRoot : pathForestTotalSurplus hk P ≤
        pathForestAbsorptionPieceSurplus hk P rootPiece := by
      simpa [heads, rootPiece, hheadsEmpty] using hexceptions
    have hrootBound := pathForestRootAbsorptionPieceSurplus_le hk P hP
    nlinarith
  · have hheadsPos : 0 < heads.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hheadsEmpty)
    have hheadsOne : heads.card = 1 := by omega
    obtain ⟨Zstar, hheadsEq⟩ := Finset.card_eq_one.mp hheadsOne
    have hZstar : Zstar ∈ pathForestUHeadedPieces hk P := by
      change Zstar ∈ heads
      simp [hheadsEq]
    have htotalTwo : pathForestTotalSurplus hk P ≤
        pathForestAbsorptionPieceSurplus hk P Zstar +
          pathForestAbsorptionPieceSurplus hk P rootPiece := by
      simpa [heads, rootPiece, hheadsEq] using hexceptions
    by_cases hrootEdge :
        (pathForestAbsorptionPieceEdges hk P rootPiece).Nonempty
    · have hrootNonpos :=
        pathForestAbsorptionPieceSurplus_le_zero hk P hP rootPiece hrootEdge
      have hstarBound := pathForestUHeadedPieceSurplus_le hk P hP Zstar hZstar
      nlinarith
    · by_cases hstarEdge :
          (pathForestAbsorptionPieceEdges hk P Zstar).Nonempty
      · have hstarNonpos :=
          pathForestAbsorptionPieceSurplus_le_zero hk P hP Zstar hstarEdge
        have hrootBound := pathForestRootAbsorptionPieceSurplus_le hk P hP
        nlinarith
      · obtain ⟨pstar, hpstarUn, hpstarPiece⟩ :=
          UHeaded_has_unabsorbed_head hk P Zstar
            ((mem_pathForestUHeadedPieces hk P Zstar).mp hZstar)
        have hpstarU := (mem_pathForestUnabsorbedU hk P pstar).mp hpstarUn |>.1
        let vstar : Zstar := ⟨pstar.1, by
          change pathForestAbsorptionPieceOf hk P pstar.1 = Zstar
          exact hpstarPiece⟩
        have hstarEq : pathForestAbsorptionPieceSurplus hk P Zstar =
            pathForestComponentSurplus hk P pstar.1 := by
          simpa [vstar] using
            absorptionPieceSurplus_eq_component_of_no_edges
              hk P Zstar hstarEdge vstar
        let root := pathForestRootComponent (by omega) P
        let vroot : rootPiece :=
          ⟨root, pathForestAbsorptionPieceOf_mem hk P root⟩
        have hrootEq : pathForestAbsorptionPieceSurplus hk P rootPiece =
            pathForestComponentSurplus hk P root := by
          simpa [vroot] using
            absorptionPieceSurplus_eq_component_of_no_edges
              hk P rootPiece hrootEdge vroot
        let y0 := pathForestComponentLastDeficit hk P root
        let ystar := pathForestComponentLastDeficit hk P pstar.1
        by_cases hy0 : y0 = 0
        · by_cases hystar : ystar = 0
          · have hrootTerminal : root ∈
                pathForestTerminalFullComponents hk P := by
              simp [pathForestTerminalFullComponents,
                IsTerminalFullComponent, y0, hy0, root]
            have hstarTerminal : pstar.1 ∈
                pathForestTerminalFullComponents hk P := by
              simp [pathForestTerminalFullComponents,
                IsTerminalFullComponent, ystar, hystar]
            have hrootNe : root ≠ pstar.1 := by
              simpa [root] using pstar.2.symm
            have hpairSubset : ({root, pstar.1} :
                Finset (AssemblyVertex hk P)) ⊆
                pathForestTerminalFullComponents hk P := by
              intro C hC
              simp only [Finset.mem_insert, Finset.mem_singleton] at hC
              rcases hC with rfl | rfl
              · exact hrootTerminal
              · exact hstarTerminal
            have hpairCard := Finset.card_le_card hpairSubset
            have hCtwo : 2 ≤ pathForestTerminalFullCount hk P := by
              have hpCard : ({root, pstar.1} :
                  Finset (AssemblyVertex hk P)).card = 2 := by
                simp [hrootNe]
              rw [pathForestTerminalFullCount]
              omega
            have hQone : 1 ≤ Q := by
              dsimp [Q]
              have : 1 ≤ pathForestTerminalFullCount hk P - 1 := by omega
              exact this.trans (Nat.le_max_left _ _)
            have hQoneInt : (1 : ℤ) ≤ (Q : ℤ) := by
              exact_mod_cast hQone
            have hkappaLeCharge : kappa ≤ kappa * (Q : ℤ) := by
              have := Int.mul_le_mul_of_nonneg_left hQoneInt hkappaNonnegative
              simpa using this
            have hrootBound : pathForestComponentSurplus hk P root ≤
                2 * n - 2 := by
              exact pathForestRootComponentSurplus_le hk P
            have hstarBound := pathForestCheapSurplus_le_n hk P pstar hpstarU
            have hkappaLarge := surplusKappa_gt_two_mul_sub_two
              (show 6 ≤ k - 1 by omega)
            rw [hstarEq, hrootEq] at htotalTwo
            nlinarith
          · have hystarPos : 1 ≤ ystar := by omega
            have hBstar : 1 ≤ endpointChargeB ystar :=
              endpointChargeB_ge_one_of_pos hystarPos
            have hstarB := pathForestCheapSurplus_B_bound_J3
              hk P pstar hpstarU
            have hlambdaNat :=
              (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
            have hlambdaCast : (surplusLambda (k - 1) : ℤ) + 2 =
                ((k - 1 : ℕ) : ℤ) := by
              exact_mod_cast hlambdaNat
            have hstarTwo : pathForestComponentSurplus hk P pstar.1 ≤ 2 := by
              dsimp [ystar] at hBstar
              nlinarith
            have hrootBound : pathForestComponentSurplus hk P root ≤
                2 * n - 2 := by
              exact pathForestRootComponentSurplus_le hk P
            rw [hstarEq, hrootEq] at htotalTwo
            nlinarith
        · have hy0Pos : 1 ≤ y0 := by omega
          have hB0 : 1 ≤ endpointChargeB y0 :=
            endpointChargeB_ge_one_of_pos hy0Pos
          have hrootRow := pathForestRootSurplus_le hk P
          have hlambdaNat :=
            (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
          have hlambdaCast : (surplusLambda (k - 1) : ℤ) + 2 =
              ((k - 1 : ℕ) : ℤ) := by
            exact_mod_cast hlambdaNat
          have hrootN : pathForestComponentSurplus hk P root ≤ n := by
            dsimp [y0, root] at hB0
            nlinarith
          have hstarBound := pathForestCheapSurplus_le_n hk P pstar hpstarU
          rw [hstarEq, hrootEq] at htotalTwo
          nlinarith

/-! ## The signed assembly inequality and the literal theorem -/

/-- The signed surplus form equivalent to Theorem `thm:assembly`, with
every `max` and natural subtraction left literal. -/
theorem pathForestTotalSurplus_assembly_bound (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestTotalSurplus hk P ≤
      2 * ((k - 1 : ℕ) : ℤ) +
        (surplusKappa (k - 1) : ℤ) *
          (max
            (max 0 (pathForestTerminalFullCount hk P - 1))
            (pathForestV hk P - 1) : ℕ) := by
  by_cases hV : 2 ≤ pathForestV hk P
  · exact (pathForestTotalSurplus_le_of_two_le_V hk P hP hV).trans
      (pathForest_V_ge_two_comparison hk P hV)
  · have hVone : pathForestV hk P ≤ 1 := by omega
    exact pathForestTotalSurplus_le_of_V_le_one hk P hP hVone

/-- **Assembly (`thm:assembly`).**  For `n=k-1`, `T=n!`, and the exact
Gate-I residual quantity `W`,
`(n-2)T ≤ (n²-2n-2)W+2n`.

The final `exact_mod_cast` transports an ordinary `Int` inequality between
casts of naturals; no truncated subtraction is used in this conversion. -/
theorem pathForest_assembly (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    (k - 1 - 2) * (k - 1).factorial ≤
      ((k - 1) ^ 2 - 2 * (k - 1) - 2) *
          pathForestResidualW hk P +
        2 * (k - 1) := by
  let n := k - 1
  let R := pathForestTotalBudget (by omega) P
  let C := pathForestTerminalFullCount hk P
  let V := pathForestV hk P
  let Q := max (max 0 (C - 1)) (V - 1)
  let W := pathForestResidualW hk P
  have hsigned := pathForestTotalSurplus_assembly_bound hk P hP
  rw [pathForest_surplusSum hk P] at hsigned
  have hWInt : (W : ℤ) = (R : ℤ) + (Q : ℤ) := by
    dsimp [W, R, Q, C, V]
    rw [pathForestResidualW_eq]
    push_cast
    rfl
  have hInt :
      (surplusLambda n : ℤ) * (n.factorial : ℤ) ≤
        (surplusKappa n : ℤ) * (W : ℤ) + 2 * (n : ℤ) := by
    have hsigned' :
        (surplusLambda n : ℤ) * (n.factorial : ℤ) -
            (surplusKappa n : ℤ) * (R : ℤ) ≤
          2 * (n : ℤ) + (surplusKappa n : ℤ) * (Q : ℤ) := by
      simpa only [n, R, C, V, Q] using hsigned
    rw [hWInt]
    nlinarith [hsigned']
  have hNat :
      surplusLambda n * n.factorial ≤
        surplusKappa n * W + 2 * n := by
    exact_mod_cast hInt
  have hn : 6 ≤ n := by
    dsimp [n]
    omega
  dsimp [n, W] at hNat ⊢
  rw [surplusKappa_eq_square_sub hn] at hNat
  simpa [surplusLambda] using hNat

end SuperpermutationLowerBound
