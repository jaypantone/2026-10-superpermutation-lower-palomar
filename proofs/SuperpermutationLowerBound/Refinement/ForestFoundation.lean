module

public import SuperpermutationLowerBound.Section08.ComponentCapacity

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-! Public reconstruction of the accepted concrete segment bookkeeping.
The proofs use the same definitions; no abstract realization assumption is added. -/

open PermutationVertex
variable {k : ℕ}

/-- Sum `weight(xᵢ,xᵢ₊₁)-base` over every adjacent pair of a list. -/
def adjacentExcess {α : Type*} (weight : α → α → ℕ) (base : ℕ) :
    List α → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
      weight x y - base + adjacentExcess weight base (y :: rest)

/-- The boundary weight between two lists, totalized only to make the
generic flattening identity convenient.  All mathematical uses have two
nonempty lists. -/
def listBoundaryWeight {α : Type*} (weight : α → α → ℕ)
    (left right : List α) : ℕ :=
  match left.getLast?, right.head? with
  | some x, some y => weight x y
  | _, _ => 0

theorem adjacentExcess_append {α : Type*}
    (weight : α → α → ℕ) (base : ℕ)
    {left right : List α} (hleft : left ≠ []) (hright : right ≠ []) :
    adjacentExcess weight base (left ++ right) =
      adjacentExcess weight base left +
        (listBoundaryWeight weight left right - base) +
          adjacentExcess weight base right := by
  induction left with
  | nil => exact (hleft rfl).elim
  | cons x tail ih =>
      cases tail with
      | nil =>
          cases right with
          | nil => exact (hright rfl).elim
          | cons y rest => simp [adjacentExcess, listBoundaryWeight]
      | cons y rest =>
          have htail : y :: rest ≠ [] := List.cons_ne_nil _ _
          change weight x y - base +
              adjacentExcess weight base ((y :: rest) ++ right) = _
          rw [ih htail]
          simp [adjacentExcess, listBoundaryWeight]
          omega

theorem listBoundaryWeight_flatten_cons {α : Type*}
    (weight : α → α → ℕ) {left first : List α}
    {rest : List (List α)} (hleft : left ≠ []) (hfirst : first ≠ []) :
    listBoundaryWeight weight left ((first :: rest).flatten) =
      listBoundaryWeight weight left first := by
  simp [listBoundaryWeight, hleft, hfirst,
    List.getLast?_eq_some_getLast, List.head?_eq_some_head]

theorem adjacentExcess_flatten {α : Type*}
    (weight : α → α → ℕ) (base : ℕ)
    (parts : List (List α)) (hnil : [] ∉ parts) :
    adjacentExcess weight base parts.flatten =
      (parts.map (adjacentExcess weight base)).sum +
        adjacentExcess (listBoundaryWeight weight) base parts := by
  induction parts with
  | nil => simp [adjacentExcess]
  | cons first rest ih =>
      have hfirst : first ≠ [] := by
        intro h
        apply hnil
        simp [h]
      have hrestNil : [] ∉ rest := by
        intro h
        exact hnil (by simp [h])
      cases rest with
      | nil => simp [adjacentExcess]
      | cons second tail =>
          have hsecond : second ≠ [] := by
            intro h
            apply hrestNil
            simp [h]
          have hflatTail : (second :: tail).flatten ≠ [] := by
            simp [hsecond]
          rw [List.flatten_cons,
            adjacentExcess_append weight base hfirst hflatTail]
          rw [ih hrestNil]
          rw [listBoundaryWeight_flatten_cons weight hfirst hsecond]
          simp [adjacentExcess, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

theorem adjacentExcess_eq_zero_of_chain {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => weight x y = base) :
    adjacentExcess weight base xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
      cases tail with
      | nil => rfl
      | cons y rest =>
          rw [List.isChain_cons] at hchain
          simp only [List.head?_cons, Option.mem_def] at hchain
          simp [adjacentExcess, hchain.1, ih hchain.2]

theorem adjacentExcess_shift_one {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => base + 1 ≤ weight x y) :
    adjacentExcess weight base xs =
      (xs.length - 1) + adjacentExcess weight (base + 1) xs := by
  induction xs with
  | nil => simp [adjacentExcess]
  | cons x tail ih =>
      cases tail with
      | nil => simp [adjacentExcess]
      | cons y rest =>
          rw [List.isChain_cons] at hchain
          simp only [List.head?_cons, Option.mem_def] at hchain
          have hxy : base + 1 ≤ weight x y := by
            simpa using hchain.1
          have htail := ih hchain.2
          have htail' : adjacentExcess weight base (y :: rest) =
              rest.length + adjacentExcess weight (base + 1) (y :: rest) := by
            simpa using htail
          have hweight : weight x y - base =
              1 + (weight x y - (base + 1)) := by omega
          simp only [adjacentExcess, List.length_cons]
          rw [htail', hweight]
          simp only [Nat.add_sub_cancel]
          omega

theorem adjacentExcess_ge_length_sub_one {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => base + 1 ≤ weight x y) :
    xs.length - 1 ≤ adjacentExcess weight base xs := by
  rw [adjacentExcess_shift_one weight base hchain]
  omega


theorem blockAlignedLightSegments_nonempty (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLightSegments hk p hp ≠ [] := by
  unfold blockAlignedLightSegments
  exact List.splitBy_ne_nil.mpr (blockAlignedRuns_nonempty hk p hp)

theorem blockAlignedLightSegmentLengths_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    ((blockAlignedLightSegments hk p hp).map List.length).sum =
      blockAlignedRunCount hk p hp := by
  have hlength := congrArg List.length
    (blockAlignedLightSegments_spec hk p hp).1
  simpa [blockAlignedRunCount] using hlength

theorem blockAlignedLightSegmentLengths_fin_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (∑ i : Fin (blockAlignedLightSegments hk p hp).length,
      (blockAlignedLightSegmentAt hk p hp i).length) =
      blockAlignedRunCount hk p hp := by
  let segments := blockAlignedLightSegments hk p hp
  rw [← blockAlignedLightSegmentLengths_sum hk p hp]
  rw [← List.sum_ofFn]
  change (List.ofFn (fun i : Fin segments.length => segments[i].length)).sum =
    (segments.map List.length).sum
  exact congrArg List.sum
    (List.ofFn_getElem_eq_map segments List.length)

theorem blockAlignedRunBoundaryExcess_eq_adjacentExcess
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedRunBoundaryExcess hk p hp =
      adjacentExcess runBoundaryWeight 3 (blockAlignedRuns hk p hp) := by
  unfold blockAlignedRunBoundaryExcess
  generalize blockAlignedRuns hk p hp = xs
  induction xs with
  | nil => rfl
  | cons x tail ih =>
      cases tail with
      | nil => rfl
      | cons y rest =>
          exact congrArg (fun z => runBoundaryWeight x y - 3 + z) ih

theorem blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegments hk p hp).length - 1 ≤
      blockAlignedRunBoundaryExcess hk p hp := by
  let segments := blockAlignedLightSegments hk p hp
  let runs := blockAlignedRuns hk p hp
  have hparts := adjacentExcess_flatten runBoundaryWeight 3 segments
    (blockAlignedLightSegments_spec hk p hp).2.1
  have hflatten : segments.flatten = runs :=
    (blockAlignedLightSegments_spec hk p hp).1
  have hinternal :
      (segments.map (adjacentExcess runBoundaryWeight 3)).sum = 0 := by
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨segment, hsegment, rfl⟩ := List.mem_map.mp hvalue
    apply adjacentExcess_eq_zero_of_chain runBoundaryWeight 3
    exact ((blockAlignedLightSegments_spec hk p hp).2.2.1
      segment hsegment).imp (by
        intro left right hlight
        exact hlight)
  have hbetween : segments.IsChain
      (fun left right =>
        4 ≤ listBoundaryWeight runBoundaryWeight left right) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi0 : i < segments.length := by omega
    let left := blockAlignedLightSegmentAt hk p hp
      ⟨i, by simpa [segments] using hi0⟩
    let right := blockAlignedLightSegmentAt hk p hp
      ⟨i + 1, by simpa [segments] using hi⟩
    have hweight :=
      (blockAlignedLightSegmentAt_adjacent_boundary hk p hp i hi).2
    have hweight' := (Nat.succ_le_iff).2 hweight
    have hleft : left.runs ≠ [] := by
      exact List.ne_nil_of_mem_splitBy left.isSegment
    have hright : right.runs ≠ [] := by
      exact List.ne_nil_of_mem_splitBy right.isSegment
    change 4 ≤ listBoundaryWeight runBoundaryWeight left.runs right.runs
    simp [listBoundaryWeight, hleft, hright,
      List.getLast?_eq_some_getLast, List.head?_eq_some_head]
    simpa [left, right, BlockAlignedLightSegment.lastRun,
      BlockAlignedLightSegment.firstRun,
      BlockAlignedLightSegment.runAt, BlockAlignedLightSegment.length,
      List.getLast_eq_getElem, List.head_eq_getElem_zero] using hweight'
  have hbetweenLower := adjacentExcess_ge_length_sub_one
    (listBoundaryWeight runBoundaryWeight) 3 hbetween
  rw [blockAlignedRunBoundaryExcess_eq_adjacentExcess]
  change segments.length - 1 ≤ adjacentExcess runBoundaryWeight 3 runs
  rw [← hflatten, hparts, hinternal, zero_add]
  exact hbetweenLower

theorem blockAlignedTotalDeficit_eq_sum_lightSegments
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedTotalDeficit hk p hp =
      ∑ i : Fin (blockAlignedLightSegments hk p hp).length,
        (blockAlignedLightSegmentAt hk p hp i).totalDeficit := by
  let segments := blockAlignedLightSegments hk p hp
  unfold blockAlignedTotalDeficit
  rw [blockAlignedDeficitString_eq_lightSegments hk p hp]
  change (segments.flatMap
      (fun segment => segment.map (fun run => (k - 1) - run.length))).sum = _
  have hsumFlat :
      (segments.flatMap
        (fun segment => segment.map (fun run => (k - 1) - run.length))).sum =
      (segments.map (fun segment =>
        (segment.map (fun run => (k - 1) - run.length)).sum)).sum := by
    induction segments with
    | nil => simp
    | cons segment segments ih => simp [ih]
  rw [hsumFlat]
  rw [← List.sum_ofFn]
  change (segments.map (fun segment =>
      (segment.map (fun run => (k - 1) - run.length)).sum)).sum =
    (List.ofFn (fun i : Fin segments.length =>
      ((segments[i]).map (fun run => (k - 1) - run.length)).sum)).sum
  exact congrArg List.sum
    (List.ofFn_getElem_eq_map segments (fun segment =>
      (segment.map (fun run => (k - 1) - run.length)).sum)).symm

theorem blockAlignedLightSegment_deficitAt_eq_global
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp)
    (j : ℕ) (hj : j < segment.length) :
    deficitAt segment.deficitString j =
      deficitAt (blockAlignedDeficitString hk p hp)
        (segment.globalStart + j) := by
  rw [deficitAt_eq_get _ _ (by
      simpa using hj), deficitAt_eq_get _ _ (by
        have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        simpa [blockAlignedDeficitString] using (show
          segment.globalStart + j < (blockAlignedRuns hk p hp).length by omega))]
  have hlocal := blockAlignedLightSegment_deficitString_get hk p hp segment
    ⟨j, hj⟩
  simpa [blockAlignedDeficitString, blockAlignedRunAt,
    BlockAlignedRun.deficit, BlockAlignedRun.length] using hlocal

theorem blockAlignedFirstDeficit_eq_deficitAt_zero
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedFirstDeficit hk p hp =
      deficitAt (blockAlignedDeficitString hk p hp) 0 := by
  let d := blockAlignedDeficitString hk p hp
  have hd : d ≠ [] := by
    simpa [d, blockAlignedDeficitString] using
      blockAlignedRuns_nonempty hk p hp
  rw [deficitAt_eq_get d 0 (List.length_pos_of_ne_nil hd)]
  change d.head hd = d.get ⟨0, List.length_pos_of_ne_nil hd⟩
  exact List.head_eq_getElem_zero hd

theorem blockAlignedLastDeficit_eq_deficitAt_last
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLastDeficit hk p hp =
      deficitAt (blockAlignedDeficitString hk p hp)
        (blockAlignedRunCount hk p hp - 1) := by
  let d := blockAlignedDeficitString hk p hp
  have hd : d ≠ [] := by
    simpa [d, blockAlignedDeficitString] using
      blockAlignedRuns_nonempty hk p hp
  have hlen : d.length = blockAlignedRunCount hk p hp := by
    exact blockAlignedDeficitString_length hk p hp
  rw [show blockAlignedRunCount hk p hp - 1 = d.length - 1 by rw [hlen]]
  rw [deficitAt_eq_get d (d.length - 1) (by
    exact Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega))]
  change d.getLast hd = d.get
    ⟨d.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega)⟩
  exact List.getLast_eq_getElem hd

theorem firstLightSegment_globalStart_zero
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegmentAt hk p hp
      ⟨0, List.length_pos_of_ne_nil
        (blockAlignedLightSegments_nonempty hk p hp)⟩).globalStart = 0 := by
  rw [blockAlignedLightSegmentAt_globalStart]
  simp

theorem lastLightSegment_end_eq_runCount
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let segments := blockAlignedLightSegments hk p hp
    let last : Fin segments.length :=
      ⟨segments.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil
          (blockAlignedLightSegments_nonempty hk p hp)) (by omega)⟩
    (blockAlignedLightSegmentAt hk p hp last).globalStart +
        (blockAlignedLightSegmentAt hk p hp last).length =
      blockAlignedRunCount hk p hp := by
  dsimp only
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  change (blockAlignedLightSegmentAt hk p hp last).globalStart +
      (blockAlignedLightSegmentAt hk p hp last).length =
    blockAlignedRunCount hk p hp
  rw [blockAlignedLightSegmentAt_globalStart]
  change (segments.take last).flatten.length +
      (segments.get last).length = blockAlignedRunCount hk p hp
  have htake := List.take_concat_get' segments last.1 last.2
  have hlast : last.1 + 1 = segments.length := by
    dsimp [last]
    omega
  rw [hlast, List.take_length] at htake
  have hlength := congrArg (fun xs => xs.flatten.length) htake
  have hflat := congrArg List.length
    (blockAlignedLightSegments_spec hk p hp).1
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append] at hlength
  simpa [segments, blockAlignedRunCount] using hlength.trans hflat

theorem firstLightSegment_firstDeficit
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let first : Fin (blockAlignedLightSegments hk p hp).length :=
      ⟨0, List.length_pos_of_ne_nil
        (blockAlignedLightSegments_nonempty hk p hp)⟩
    deficitAt (blockAlignedLightSegmentAt hk p hp first).deficitString 0 =
      blockAlignedFirstDeficit hk p hp := by
  dsimp only
  let first : Fin (blockAlignedLightSegments hk p hp).length :=
    ⟨0, List.length_pos_of_ne_nil
      (blockAlignedLightSegments_nonempty hk p hp)⟩
  let segment := blockAlignedLightSegmentAt hk p hp first
  have hpos : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hglobal := blockAlignedLightSegment_deficitAt_eq_global
    hk p hp segment 0 hpos
  have hstart : segment.globalStart = 0 := by
    simp [segment, first]
  calc
    deficitAt segment.deficitString 0 =
        deficitAt (blockAlignedDeficitString hk p hp) 0 := by
      simpa [hstart] using hglobal
    _ = blockAlignedFirstDeficit hk p hp :=
      (blockAlignedFirstDeficit_eq_deficitAt_zero hk p hp).symm

theorem lastLightSegment_lastDeficit
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let segments := blockAlignedLightSegments hk p hp
    let last : Fin segments.length :=
      ⟨segments.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil
          (blockAlignedLightSegments_nonempty hk p hp)) (by omega)⟩
    deficitAt (blockAlignedLightSegmentAt hk p hp last).deficitString
        ((blockAlignedLightSegmentAt hk p hp last).length - 1) =
      blockAlignedLastDeficit hk p hp := by
  dsimp only
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  let segment := blockAlignedLightSegmentAt hk p hp last
  have hpos : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hglobal := blockAlignedLightSegment_deficitAt_eq_global
    hk p hp segment (segment.length - 1) (by omega)
  have hend : segment.globalStart + segment.length =
      blockAlignedRunCount hk p hp := by
    simpa [segments, last, segment] using
      lastLightSegment_end_eq_runCount hk p hp
  have hindex : segment.globalStart + (segment.length - 1) =
      blockAlignedRunCount hk p hp - 1 := by omega
  calc
    deficitAt segment.deficitString (segment.length - 1) =
        deficitAt (blockAlignedDeficitString hk p hp)
          (blockAlignedRunCount hk p hp - 1) := by
      simpa only [hindex] using hglobal
    _ = blockAlignedLastDeficit hk p hp :=
      (blockAlignedLastDeficit_eq_deficitAt_last hk p hp).symm


theorem pathForestComponentFirstDeficit_eq_deficitAt_zero
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentFirstDeficit hk P C =
      deficitAt (pathForestComponentDeficitString hk P C) 0 := by
  let d := pathForestComponentDeficitString hk P C
  have hd : d ≠ [] := by
    simpa [d, pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C
  rw [deficitAt_eq_get d 0 (List.length_pos_of_ne_nil hd)]
  change d.head hd = d.get ⟨0, List.length_pos_of_ne_nil hd⟩
  exact List.head_eq_getElem_zero hd

theorem pathForestComponentLastDeficit_eq_deficitAt_last
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentLastDeficit hk P C =
      deficitAt (pathForestComponentDeficitString hk P C)
        (pathForestComponentRunCount hk P C - 1) := by
  let d := pathForestComponentDeficitString hk P C
  have hd : d ≠ [] := by
    simpa [d, pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C
  have hlength : d.length = pathForestComponentRunCount hk P C := by
    simp [d, pathForestComponentDeficitString,
      pathForestComponentRunCount]
  rw [show pathForestComponentRunCount hk P C - 1 = d.length - 1 by
    rw [hlength]]
  rw [deficitAt_eq_get d (d.length - 1) (by
    exact Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega))]
  change d.getLast hd = d.get
    ⟨d.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega)⟩
  exact List.getLast_eq_getElem hd


theorem pathForestComponentLastDeficit_eq_blockAlignedLastDeficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentLastDeficit hk P C =
      blockAlignedLastDeficit hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  rw [pathForestComponentLastDeficit_eq_deficitAt_last hk P C,
    blockAlignedLastDeficit_eq_deficitAt_last hk
      (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C),
    pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C,
    pathForestComponentRunCount_eq_blockAlignedRunCount hk P C]

theorem pathForestComponentFirstDeficit_eq_blockAlignedFirstDeficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentFirstDeficit hk P C =
      blockAlignedFirstDeficit hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  rw [pathForestComponentFirstDeficit_eq_deficitAt_zero hk P C,
    blockAlignedFirstDeficit_eq_deficitAt_zero hk
      (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C),
    pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C]


end SuperpermutationLowerBound.Refinement
