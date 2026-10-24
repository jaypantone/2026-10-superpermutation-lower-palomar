module

public import SuperpermutationLowerBound.Section04.Doors
public import Mathlib.Data.List.SplitBy
public import Mathlib.Data.List.Nodup

@[expose] public section

namespace SuperpermutationLowerBound

/-! The frozen beginning of Section 5: light and heavy run boundaries,
maximal light segments, and the full-run chart through the sandwich lemma.
The primary interface is for an arbitrary block-aligned exitless path.
-/

open PermutationVertex

variable {k : ℕ}

/-! ## Light and heavy boundaries and maximal light segments -/

/-- The weight of a boundary between two nonempty run lists.  The value is
defined to be zero outside that genuine-boundary domain; every use below is
accompanied by the nonemptiness supplied by the canonical run partition. -/
noncomputable def runBoundaryWeight (left right : List (PermutationVertex k)) : ℕ :=
  match left.getLast?, right.head? with
  | some u, some v => overlapWeight (blockExit u) v
  | _, _ => 0

/-- A genuine boundary between runs is light exactly when its weight is
three. -/
def IsLightRunBoundary (left right : List (PermutationVertex k)) : Prop :=
  runBoundaryWeight left right = 3

/-- A genuine boundary between runs is heavy exactly when it is not light.
The theorem `blockAlignedRunBoundary_heavy_iff_weight_gt_three` identifies
this complementary case with weight strictly greater than three on actual
canonical run boundaries. -/
def IsHeavyRunBoundary (left right : List (PermutationVertex k)) : Prop :=
  runBoundaryWeight left right ≠ 3

/-- Boolean form used to split the ordered run list into maximal light
segments. -/
noncomputable def isLightRunBoundary
    (left right : List (PermutationVertex k)) : Bool :=
  by classical exact decide (IsLightRunBoundary left right)

/-- The canonical maximal chains of runs joined by light boundaries. -/
noncomputable def blockAlignedLightSegments (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    List (List (List (PermutationVertex k))) :=
  (blockAlignedRuns hk p hp).splitBy isLightRunBoundary

/-- One genuine maximal light segment of an arbitrary block-aligned path. -/
structure BlockAlignedLightSegment (hk : 7 ≤ k) (p : OverlapPath k)
    (hp : IsBlockAligned p) where
  runs : List (List (PermutationVertex k))
  isSegment : runs ∈ blockAlignedLightSegments hk p hp

/-- The light segment at an exact position in the canonical ordered
decomposition. -/
noncomputable def blockAlignedLightSegmentAt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : Fin (blockAlignedLightSegments hk p hp).length) :
    BlockAlignedLightSegment hk p hp :=
  ⟨(blockAlignedLightSegments hk p hp).get i, List.get_mem _ i⟩

namespace BlockAlignedLightSegment

/-- The number of runs in a light segment. -/
def length {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp) : ℕ :=
  s.runs.length

/-- The ordered deficit string belonging to a light segment. -/
def deficitString {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp) : List ℕ :=
  s.runs.map (fun run => (k - 1) - run.length)

/-- The total deficit of a light segment. -/
def totalDeficit {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp) : ℕ :=
  s.deficitString.sum

/-- The canonical position of a light segment in the ordered segment
decomposition. -/
noncomputable def segmentIndex {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp) : ℕ := by
  classical
  exact (blockAlignedLightSegments hk p hp).idxOf s.runs

/-- The global run index at which a light segment starts.  It is computed
from the canonical ordered decomposition, rather than chosen from an
existence proof. -/
noncomputable def globalStart {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp) : ℕ :=
  ((blockAlignedLightSegments hk p hp).take s.segmentIndex).flatten.length

/-- Exact placement of a light segment at a proposed global run index. -/
def StartsAt {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp) (start : ℕ) : Prop :=
  start + s.length ≤ (blockAlignedRuns hk p hp).length ∧
    ((blockAlignedRuns hk p hp).drop start).take s.length = s.runs

/-- The run at an exact local position in a light segment. -/
def runAt {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp) (j : Fin s.length) :
    List (PermutationVertex k) :=
  s.runs.get ⟨j, by simpa [length] using j.2⟩

end BlockAlignedLightSegment

private theorem blockAlignedBlockEntries_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedBlockEntries hk p hp).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (blockAlignedBlockEntries_pairwiseDistinct hk p hp).imp (by
    intro u v hclasses huv
    exact hclasses (congrArg rotationClass huv))

private theorem adjacentRuns_disjoint (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length) :
    List.Disjoint
      ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
      ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩) := by
  let runs := blockAlignedRuns hk p hp
  have hflat : runs.flatten = blockAlignedBlockEntries hk p hp :=
    (blockAlignedRuns_spec hk p hp).1
  have hnodup : runs.flatten.Nodup := by
    rw [hflat]
    exact blockAlignedBlockEntries_nodup hk p hp
  have hpair : runs.Pairwise List.Disjoint := (List.nodup_flatten.mp hnodup).2
  have hj0 : j < runs.length := by
    simpa [runs] using (show j < j + 1 from by omega).trans hj
  have hj1 : j + 1 < runs.length := by simpa [runs] using hj
  have hdis := hpair.rel_get_of_lt
    (a := ⟨j, hj0⟩) (b := ⟨j + 1, hj1⟩)
    (Fin.mk_lt_mk.mpr (by omega))
  simpa [runs] using hdis

private theorem rotationClasses_ne_of_entries_mem (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    {u v : PermutationVertex k}
    (hu : u ∈ blockAlignedBlockEntries hk p hp)
    (hv : v ∈ blockAlignedBlockEntries hk p hp)
    (huv : u ≠ v) : rotationClass u ≠ rotationClass v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have hpair := blockAlignedBlockEntries_pairwiseDistinct hk p hp
  by_cases hij : i.1 < j.1
  · have hrel :=
      List.pairwise_iff_getElem.mp hpair i.1 j.1 i.2 j.2 hij
    change rotationClass ((blockAlignedBlockEntries hk p hp).get i) ≠
      rotationClass ((blockAlignedBlockEntries hk p hp).get j) at hrel
    rw [hi, hj] at hrel
    exact hrel
  · by_cases hji : j.1 < i.1
    · have hrel :=
        List.pairwise_iff_getElem.mp hpair j.1 i.1 j.2 i.2 hji
      change rotationClass ((blockAlignedBlockEntries hk p hp).get j) ≠
        rotationClass ((blockAlignedBlockEntries hk p hp).get i) at hrel
      rw [hj, hi] at hrel
      exact fun hclasses => hrel hclasses.symm
    · have hindex : i = j := Fin.ext (by omega)
      subst j
      exact (huv (hi.symm.trans hj)).elim

private theorem runBoundaryWeight_eq (left right : List (PermutationVertex k))
    (hleft : left ≠ []) (hright : right ≠ []) :
    runBoundaryWeight left right =
      overlapWeight (blockExit (left.getLast hleft)) (right.head hright) := by
  simp [runBoundaryWeight, List.getLast?_eq_some_getLast hleft,
    List.head?_eq_some_head hright]

/-- Every boundary between consecutive canonical runs has weight at least
three. -/
theorem blockAlignedRunBoundary_weight_ge_three (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length) :
    3 ≤ runBoundaryWeight
      ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
      ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩) := by
  let runs := blockAlignedRuns hk p hp
  have hj0 : j < runs.length := by simpa [runs] using (show j < j + 1 from by omega).trans hj
  have hj1 : j + 1 < runs.length := by simpa [runs] using hj
  let left := runs.get ⟨j, hj0⟩
  let right := runs.get ⟨j + 1, hj1⟩
  have hleft : left ≠ [] := by
    have hmem : left ∈ runs := by
      simpa [left] using List.get_mem runs ⟨j, hj0⟩
    exact fun heq => (blockAlignedRuns_spec hk p hp).2.1
      (by simpa [runs, heq] using hmem)
  have hright : right ≠ [] := by
    have hmem : right ∈ runs := by
      simpa [right] using List.get_mem runs ⟨j + 1, hj1⟩
    exact fun heq => (blockAlignedRuns_spec hk p hp).2.1
      (by simpa [runs, heq] using hmem)
  have hnotTwo :
      overlapWeight (blockExit (left.getLast hleft)) (right.head hright) ≠ 2 := by
    have hchain := (blockAlignedRuns_spec hk p hp).2.2.2
    rw [List.isChain_iff_getElem] at hchain
    simpa [runs, left, right] using
      (hchain j (by simpa [runs] using hj)).2.2
  have hdisjoint : List.Disjoint left right := by
    simpa [runs, left, right] using adjacentRuns_disjoint hk p hp j hj
  have hendNe : left.getLast hleft ≠ right.head hright := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint
      (List.getLast_mem hleft) (heq ▸ List.head_mem hright))
  have hsourceNe : blockExit (left.getLast hleft) ≠ right.head hright := by
    intro heq
    have hblockMem : blockExit (left.getLast hleft) ∈
        rotationClass (left.getLast hleft) := by
      change blockExit (left.getLast hleft) ∈
        rotationClass (left.getLast hleft)
      have hk1 : 1 ≤ k := by omega
      rw [← rotationPower_pred_eq_blockExit hk1]
      exact rotationPower_mem_rotationClass hk1 (k - 1)
        (left.getLast hleft)
    have hclass :
        rotationClass (left.getLast hleft) =
          rotationClass (right.head hright) := by
      calc
        rotationClass (left.getLast hleft) =
            rotationClass (blockExit (left.getLast hleft)) :=
          (rotationClass_eq_of_mem (by omega) hblockMem).symm
        _ = rotationClass (right.head hright) := congrArg rotationClass heq
    have hflat := (blockAlignedRuns_spec hk p hp).1
    have hleftMemRuns : left ∈ runs := by
      simpa [left] using List.get_mem runs ⟨j, hj0⟩
    have hrightMemRuns : right ∈ runs := by
      simpa [right] using List.get_mem runs ⟨j + 1, hj1⟩
    have hleftMem : left.getLast hleft ∈ blockAlignedBlockEntries hk p hp := by
      rw [← hflat]
      exact List.mem_flatten.mpr ⟨left, hleftMemRuns, List.getLast_mem hleft⟩
    have hrightMem : right.head hright ∈ blockAlignedBlockEntries hk p hp := by
      rw [← hflat]
      exact List.mem_flatten.mpr ⟨right, hrightMemRuns, List.head_mem hright⟩
    exact (rotationClasses_ne_of_entries_mem hk p hp
      hleftMem hrightMem hendNe) hclass
  have hnotOne :
      overlapWeight (blockExit (left.getLast hleft)) (right.head hright) ≠ 1 := by
    intro hone
    have htarget := (unique_weight_one_successor
      (blockExit (left.getLast hleft)) (right.head hright)
      (by omega) hsourceNe).mp hone
    apply hendNe
    calc
      left.getLast hleft = rotation (blockExit (left.getLast hleft)) := by
        symm
        exact rotation_inverseRotation (by omega) _
      _ = right.head hright := htarget.symm
  rw [runBoundaryWeight_eq left right hleft hright]
  have hpos := (overlapWeight_spec
    (blockExit (left.getLast hleft)) (right.head hright)).1
  omega

/-- On an actual run boundary, light means exactly weight three and heavy is
the complementary case. -/
theorem blockAlignedRunBoundary_light_xor_heavy (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length) :
    Xor
      (IsLightRunBoundary
        ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
        ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩))
      (IsHeavyRunBoundary
        ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
        ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩)) := by
  by_cases hlight : IsLightRunBoundary
      ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
      ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩)
  · unfold Xor
    exact Or.inl ⟨hlight, by
      intro hheavy
      exact hheavy hlight⟩
  · unfold Xor
    exact Or.inr ⟨(by
      simpa [IsHeavyRunBoundary, IsLightRunBoundary] using hlight), hlight⟩

/-- On actual canonical run boundaries, the complementary heavy case is
exactly weight strictly greater than three. -/
theorem blockAlignedRunBoundary_heavy_iff_weight_gt_three (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length) :
    IsHeavyRunBoundary
        ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
        ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩) ↔
      3 < runBoundaryWeight
        ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
        ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩) := by
  have hge := blockAlignedRunBoundary_weight_ge_three hk p hp j hj
  unfold IsHeavyRunBoundary
  omega

/-- The light-segment decomposition is ordered and exhaustive, contains no
empty segment, is light inside each segment, and is maximal (hence heavy)
between adjacent segments. -/
theorem blockAlignedLightSegments_spec (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegments hk p hp).flatten = blockAlignedRuns hk p hp ∧
      [] ∉ blockAlignedLightSegments hk p hp ∧
      (∀ segment ∈ blockAlignedLightSegments hk p hp,
        segment.IsChain IsLightRunBoundary) ∧
      (blockAlignedLightSegments hk p hp).IsChain (fun a b =>
        ∃ ha : a ≠ [], ∃ hb : b ≠ [],
          IsHeavyRunBoundary (a.getLast ha) (b.head hb)) := by
  let runs := blockAlignedRuns hk p hp
  let segments := blockAlignedLightSegments hk p hp
  have hflatten : segments.flatten = runs := by
    change (runs.splitBy isLightRunBoundary).flatten = runs
    exact List.flatten_splitBy isLightRunBoundary runs
  have hnonempty : [] ∉ segments :=
    List.nil_notMem_splitBy isLightRunBoundary runs
  have hinsides : ∀ segment ∈ segments,
      segment.IsChain IsLightRunBoundary := by
    intro segment hsegment
    exact (List.isChain_of_mem_splitBy hsegment).imp (by
      intro left right hlight
      simpa [isLightRunBoundary] using hlight)
  have hbetweenRaw := List.isChain_getLast_head_splitBy
    isLightRunBoundary runs
  have hbetween : segments.IsChain (fun a b =>
      ∃ ha : a ≠ [], ∃ hb : b ≠ [],
        IsHeavyRunBoundary (a.getLast ha) (b.head hb)) := by
    exact hbetweenRaw.imp (by
      rintro a b ⟨ha, hb, hnotLight⟩
      exact ⟨ha, hb, by
        classical
        exact of_decide_eq_false
          (p := IsLightRunBoundary (a.getLast ha) (b.head hb)) hnotLight⟩)
  simpa [segments, runs] using ⟨hflatten, hnonempty, hinsides, hbetween⟩

/-- Every light segment contains at least one run. -/
theorem blockAlignedLightSegment_length_pos (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    0 < s.length := by
  exact List.length_pos_of_ne_nil
    (List.ne_nil_of_mem_splitBy s.isSegment)

/-- The first run of a genuine light segment. -/
noncomputable def BlockAlignedLightSegment.firstRun (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) : List (PermutationVertex k) :=
  s.runAt ⟨0, blockAlignedLightSegment_length_pos hk p hp s⟩

/-- The last run of a genuine light segment. -/
noncomputable def BlockAlignedLightSegment.lastRun (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) : List (PermutationVertex k) :=
  s.runAt ⟨s.length - 1, by
    have := blockAlignedLightSegment_length_pos hk p hp s
    omega⟩

/-- Every light segment is a genuine contiguous interval of the ordered
global run list (not merely an arbitrary subcollection of runs). -/
theorem blockAlignedLightSegment_infix_runs (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.runs <:+: blockAlignedRuns hk p hp := by
  rw [← (blockAlignedLightSegments_spec hk p hp).1]
  exact List.infix_of_mem_flatten s.isSegment

private theorem nodup_of_flatten_nodup_of_nil_not_mem {α : Type*}
    {parts : List (List α)} (hflat : parts.flatten.Nodup)
    (hnil : [] ∉ parts) : parts.Nodup := by
  have hpair : parts.Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hflat).2
  rw [List.nodup_iff_injective_get]
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hiNonempty : parts.get i ≠ [] := by
      intro hempty
      apply hnil
      rw [← hempty]
      exact List.get_mem parts i
    have hdisjoint := hpair.rel_get_of_lt
      (a := i) (b := j) (Fin.mk_lt_mk.mpr hijlt)
    exact List.disjoint_left.mp hdisjoint (List.head_mem hiNonempty)
      (by rw [← hij]; exact List.head_mem hiNonempty)
  · have hjNonempty : parts.get j ≠ [] := by
      intro hempty
      apply hnil
      rw [← hempty]
      exact List.get_mem parts j
    have hdisjoint := hpair.rel_get_of_lt
      (a := j) (b := i) (Fin.mk_lt_mk.mpr hjilt)
    exact List.disjoint_left.mp hdisjoint (List.head_mem hjNonempty)
      (by rw [hij]; exact List.head_mem hjNonempty)

private theorem blockAlignedRuns_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedRuns hk p hp).Nodup := by
  have hflat : (blockAlignedRuns hk p hp).flatten.Nodup := by
    rw [(blockAlignedRuns_spec hk p hp).1]
    exact blockAlignedBlockEntries_nodup hk p hp
  exact nodup_of_flatten_nodup_of_nil_not_mem hflat
    (blockAlignedRuns_spec hk p hp).2.1

private theorem blockAlignedLightSegments_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegments hk p hp).Nodup := by
  have hflat : (blockAlignedLightSegments hk p hp).flatten.Nodup := by
    rw [(blockAlignedLightSegments_spec hk p hp).1]
    exact blockAlignedRuns_nodup hk p hp
  exact nodup_of_flatten_nodup_of_nil_not_mem hflat
    (blockAlignedLightSegments_spec hk p hp).2.1

/-- Every member segment is light at each of its internal boundaries. -/
theorem blockAlignedLightSegment_isChain (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.runs.IsChain IsLightRunBoundary :=
  (blockAlignedLightSegments_spec hk p hp).2.2.1 s.runs s.isSegment

/-- The canonical segment index is in range. -/
theorem blockAlignedLightSegment_segmentIndex_lt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.segmentIndex < (blockAlignedLightSegments hk p hp).length := by
  classical
  exact List.idxOf_lt_length_iff.mpr s.isSegment

@[simp]
theorem blockAlignedLightSegmentAt_runs (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : Fin (blockAlignedLightSegments hk p hp).length) :
    (blockAlignedLightSegmentAt hk p hp i).runs =
      (blockAlignedLightSegments hk p hp).get i := rfl

/-- Exact inverse behavior of the indexed segment accessor. -/
@[simp]
theorem blockAlignedLightSegmentAt_segmentIndex (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : Fin (blockAlignedLightSegments hk p hp).length) :
    (blockAlignedLightSegmentAt hk p hp i).segmentIndex = i := by
  classical
  exact List.get_idxOf (blockAlignedLightSegments_nodup hk p hp) i

/-- The canonical global start has the exact bounds and slice behavior. -/
theorem blockAlignedLightSegment_globalStart_spec (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.StartsAt s.globalStart := by
  classical
  let segments := blockAlignedLightSegments hk p hp
  let i := s.segmentIndex
  have hi : i < segments.length := by
    simpa [segments, i] using
      blockAlignedLightSegment_segmentIndex_lt hk p hp s
  have hget : segments.get ⟨i, hi⟩ = s.runs := by
    simpa [segments, i, BlockAlignedLightSegment.segmentIndex] using
      (List.idxOf_get hi)
  have hdrop : segments.drop i = s.runs :: segments.drop (i + 1) := by
    calc
      segments.drop i =
          segments.get ⟨i, hi⟩ :: segments.drop (i + 1) :=
        List.drop_eq_getElem_cons hi
      _ = s.runs :: segments.drop (i + 1) := by rw [hget]
  have hdecomp : segments.flatten =
      (segments.take i).flatten ++ s.runs ++
        (segments.drop (i + 1)).flatten := by
    calc
      segments.flatten =
          (segments.take i ++ segments.drop i).flatten := by
        rw [List.take_append_drop]
      _ = (segments.take i).flatten ++ (segments.drop i).flatten := by
        exact List.flatten_append
      _ = (segments.take i).flatten ++ s.runs ++
          (segments.drop (i + 1)).flatten := by
        rw [hdrop, List.flatten_cons, List.append_assoc]
  have hruns : blockAlignedRuns hk p hp =
      (segments.take i).flatten ++ s.runs ++
        (segments.drop (i + 1)).flatten :=
    (blockAlignedLightSegments_spec hk p hp).1.symm.trans hdecomp
  change ((segments.take i).flatten.length + s.length ≤
      (blockAlignedRuns hk p hp).length) ∧
    ((blockAlignedRuns hk p hp).drop
      (segments.take i).flatten.length).take s.length = s.runs
  rw [hruns]
  simp [BlockAlignedLightSegment.length, List.append_assoc]

/-- Bounds for the canonical global starting index of a light segment. -/
theorem blockAlignedLightSegment_globalStart_bounds (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.globalStart + s.length ≤ (blockAlignedRuns hk p hp).length :=
  (blockAlignedLightSegment_globalStart_spec hk p hp s).1

/-- The segment is exactly the consecutive slice of global runs beginning
at its canonical start. -/
theorem blockAlignedLightSegment_globalStart_slice (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    ((blockAlignedRuns hk p hp).drop s.globalStart).take s.length =
      s.runs :=
  (blockAlignedLightSegment_globalStart_spec hk p hp s).2

/-- Indexed local/global run equality at any exact placement. -/
theorem blockAlignedLightSegment_runAt_eq_globalRun_of_startsAt
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) (start : ℕ)
    (hstart : s.StartsAt start) (j : Fin s.length) :
    s.runAt j = (blockAlignedRuns hk p hp).get
      ⟨start + j, by have := hstart.1; omega⟩ := by
  rcases hstart with ⟨hbound, hslice⟩
  have hlocal : j.1 < s.runs.length := by
    simpa [BlockAlignedLightSegment.length] using j.2
  have hglobal : start + j < (blockAlignedRuns hk p hp).length := by
    omega
  have hget := congrArg (fun runs => runs[j.1]?) hslice
  have hsome : some (s.runs.get ⟨j, hlocal⟩) =
      some ((blockAlignedRuns hk p hp).get ⟨start + j, hglobal⟩) := by
    simpa [hlocal, hglobal] using hget.symm
  simpa [BlockAlignedLightSegment.runAt] using Option.some.inj hsome

/-- Indexed equality between each local segment run and the corresponding
globally indexed canonical run. -/
theorem blockAlignedLightSegment_runAt_eq_globalRun (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) (j : Fin s.length) :
    s.runAt j = (blockAlignedRuns hk p hp).get
      ⟨s.globalStart + j, by
        have := blockAlignedLightSegment_globalStart_bounds hk p hp s
        omega⟩ :=
  blockAlignedLightSegment_runAt_eq_globalRun_of_startsAt hk p hp s
    s.globalStart (blockAlignedLightSegment_globalStart_spec hk p hp s) j

/-- Exact placement is unique; in particular the canonical start does not
depend on any proof witnessing segment membership or contiguity. -/
theorem blockAlignedLightSegment_startsAt_unique (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) (start : ℕ)
    (hstart : s.StartsAt start) :
    start = s.globalStart := by
  have hpos := blockAlignedLightSegment_length_pos hk p hp s
  let j : Fin s.length := ⟨0, hpos⟩
  have hplaced :=
    blockAlignedLightSegment_runAt_eq_globalRun_of_startsAt
      hk p hp s start hstart j
  have hcanonical :=
    blockAlignedLightSegment_runAt_eq_globalRun hk p hp s j
  have heq : (blockAlignedRuns hk p hp).get
      ⟨start, by have := hstart.1; omega⟩ =
      (blockAlignedRuns hk p hp).get
        ⟨s.globalStart, by
          have := blockAlignedLightSegment_globalStart_bounds hk p hp s
          omega⟩ := by
    simpa [j] using hplaced.symm.trans hcanonical
  have hfin := (blockAlignedRuns_nodup hk p hp).get_inj_iff.mp heq
  exact congrArg Fin.val hfin

/-- Direct local accessor for an internal light boundary of a segment. -/
theorem blockAlignedLightSegment_runAt_light (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (j : ℕ) (hj : j + 1 < s.length) :
    IsLightRunBoundary
      (s.runAt ⟨j, by omega⟩) (s.runAt ⟨j + 1, hj⟩) := by
  have hchain := blockAlignedLightSegment_isChain hk p hp s
  rw [List.isChain_iff_getElem] at hchain
  have hj' : j + 1 < s.runs.length := by
    simpa [BlockAlignedLightSegment.length] using hj
  simpa [BlockAlignedLightSegment.runAt,
    BlockAlignedLightSegment.length] using hchain j hj'

/-- The indexed segment accessor starts after exactly the flattened prefix
of preceding canonical light segments. -/
@[simp]
theorem blockAlignedLightSegmentAt_globalStart (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : Fin (blockAlignedLightSegments hk p hp).length) :
    (blockAlignedLightSegmentAt hk p hp i).globalStart =
      ((blockAlignedLightSegments hk p hp).take i).flatten.length := by
  unfold BlockAlignedLightSegment.globalStart
  rw [blockAlignedLightSegmentAt_segmentIndex hk p hp i]

/-- Adjacent canonical light segments occupy consecutive global run
intervals. -/
theorem blockAlignedLightSegmentAt_next_globalStart (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : ℕ) (hi : i + 1 < (blockAlignedLightSegments hk p hp).length) :
    (blockAlignedLightSegmentAt hk p hp ⟨i + 1, hi⟩).globalStart =
      (blockAlignedLightSegmentAt hk p hp ⟨i, by omega⟩).globalStart +
        (blockAlignedLightSegmentAt hk p hp ⟨i, by omega⟩).length := by
  rw [blockAlignedLightSegmentAt_globalStart,
    blockAlignedLightSegmentAt_globalStart]
  change ((blockAlignedLightSegments hk p hp).take (i + 1)).flatten.length =
    ((blockAlignedLightSegments hk p hp).take i).flatten.length +
      ((blockAlignedLightSegments hk p hp).get ⟨i, by omega⟩).length
  have htake := List.take_concat_get'
    (blockAlignedLightSegments hk p hp) i (by omega)
  have hlength := congrArg (fun segments => segments.flatten.length) htake
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append] at hlength
  convert hlength.symm using 1

/-- Direct indexed accessor for the heavy boundary between adjacent
canonical light segments.  Besides complementarity, it exposes the exact
strict weight inequality on this genuine run boundary. -/
theorem blockAlignedLightSegmentAt_adjacent_boundary (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i : ℕ) (hi : i + 1 < (blockAlignedLightSegments hk p hp).length) :
    let left := blockAlignedLightSegmentAt hk p hp ⟨i, by omega⟩
    let right := blockAlignedLightSegmentAt hk p hp ⟨i + 1, hi⟩
    IsHeavyRunBoundary (left.lastRun hk p hp) (right.firstRun hk p hp) ∧
      3 < runBoundaryWeight (left.lastRun hk p hp)
        (right.firstRun hk p hp) := by
  let left := blockAlignedLightSegmentAt hk p hp ⟨i, by omega⟩
  let right := blockAlignedLightSegmentAt hk p hp ⟨i + 1, hi⟩
  have hleftPos := blockAlignedLightSegment_length_pos hk p hp left
  have hrightPos := blockAlignedLightSegment_length_pos hk p hp right
  have hbetween := (blockAlignedLightSegments_spec hk p hp).2.2.2
  rw [List.isChain_iff_getElem] at hbetween
  obtain ⟨ha, hb, hheavy⟩ := hbetween i hi
  have hheavyLocal : IsHeavyRunBoundary
      (left.lastRun hk p hp) (right.firstRun hk p hp) := by
    simpa [left, right, BlockAlignedLightSegment.lastRun,
      BlockAlignedLightSegment.firstRun, BlockAlignedLightSegment.runAt,
      BlockAlignedLightSegment.length,
      List.getLast_eq_getElem, List.head_eq_getElem_zero] using hheavy
  let j := left.globalStart + left.length - 1
  have hnextStart :=
    blockAlignedLightSegmentAt_next_globalStart hk p hp i hi
  have hnextStartLocal :
      right.globalStart = left.globalStart + left.length := by
    simpa [left, right] using hnextStart
  have hrightBound :=
    blockAlignedLightSegment_globalStart_bounds hk p hp right
  have hjNext : j + 1 = right.globalStart := by
    dsimp [j]
    omega
  have hj : j + 1 < (blockAlignedRuns hk p hp).length := by
    rw [hjNext]
    omega
  have hleftGlobal : left.lastRun hk p hp =
      (blockAlignedRuns hk p hp).get ⟨j, by omega⟩ := by
    have hrun := blockAlignedLightSegment_runAt_eq_globalRun hk p hp left
      ⟨left.length - 1, by omega⟩
    have hleftIndex :
        left.globalStart + (left.length - 1) = j := by
      dsimp [j]
      omega
    unfold BlockAlignedLightSegment.lastRun
    simpa [hleftIndex] using hrun
  have hrightGlobal : right.firstRun hk p hp =
      (blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩ := by
    have hrun := blockAlignedLightSegment_runAt_eq_globalRun hk p hp right
      ⟨0, hrightPos⟩
    have hrightIndex : right.globalStart + 0 = j + 1 := by
      omega
    unfold BlockAlignedLightSegment.firstRun
    simpa [hrightIndex] using hrun
  have hheavyGlobal : IsHeavyRunBoundary
      ((blockAlignedRuns hk p hp).get ⟨j, by omega⟩)
      ((blockAlignedRuns hk p hp).get ⟨j + 1, hj⟩) := by
    rw [← hleftGlobal, ← hrightGlobal]
    exact hheavyLocal
  have hweightGlobal :=
    (blockAlignedRunBoundary_heavy_iff_weight_gt_three hk p hp j hj).mp
      hheavyGlobal
  have hweightLocal : 3 < runBoundaryWeight
      (left.lastRun hk p hp) (right.firstRun hk p hp) := by
    rw [hleftGlobal, hrightGlobal]
    exact hweightGlobal
  exact ⟨hheavyLocal, hweightLocal⟩

/-- The complete ordered deficit string is the concatenation of the light
segments' ordered deficit strings. -/
theorem blockAlignedDeficitString_eq_lightSegments (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedDeficitString hk p hp =
      (blockAlignedLightSegments hk p hp).flatMap
        (fun segment => segment.map (fun run => (k - 1) - run.length)) := by
  unfold blockAlignedDeficitString
  rw [← (blockAlignedLightSegments_spec hk p hp).1]
  induction blockAlignedLightSegments hk p hp with
  | nil => rfl
  | cons segment segments ih => simp [List.flatMap, ih]

/-! ## The full-run map `τ₃` -/

/-- The full-continuation map `τ₃`: rotate the first `k-2` letters
left once and fix the final two letters. -/
def fullRunMap (hk : 3 ≤ k) (u : PermutationVertex k) : PermutationVertex k :=
  ⟨(u.1.take (k - 2)).rotate 1 ++ u.1.drop (k - 2), by
    exact ((List.rotate_perm _ _).append_right _).trans
      ((List.Perm.of_eq (u.1.take_append_drop (k - 2))).trans u.2)⟩

/-- Iterated notation for `τ₃`. -/
def fullRunMapPower (hk : 3 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    PermutationVertex k :=
  ((fullRunMap hk)^[i]) u

/-- Exact word orientation of `τ₃`. -/
@[simp]
theorem fullRunMap_word (hk : 3 ≤ k) (u : PermutationVertex k) :
    (fullRunMap hk u).1 =
      (u.1.take (k - 2)).rotate 1 ++ u.1.drop (k - 2) := rfl

/-- Exact iterate formula: only the first `m=k-2` letters rotate. -/
theorem fullRunMapPower_word (hk : 3 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    (fullRunMapPower hk i u).1 =
      (u.1.take (k - 2)).rotate i ++ u.1.drop (k - 2) := by
  induction i with
  | zero =>
      simpa [fullRunMapPower] using (u.1.take_append_drop (k - 2)).symm
  | succ i ih =>
      rw [fullRunMapPower, Function.iterate_succ_apply']
      change (fullRunMap hk (fullRunMapPower hk i u)).1 = _
      rw [fullRunMap_word, ih]
      have hprefixLength : (u.1.take (k - 2)).length = k - 2 := by
        simp [u.length]
      have htake :
          ((u.1.take (k - 2)).rotate i ++ u.1.drop (k - 2)).take (k - 2) =
            (u.1.take (k - 2)).rotate i := by
        rw [List.take_append_of_le_length (by simp [hprefixLength])]
        exact (List.take_eq_self_iff _).2 (by simp [hprefixLength])
      have hdrop :
          ((u.1.take (k - 2)).rotate i ++ u.1.drop (k - 2)).drop (k - 2) =
            u.1.drop (k - 2) := by
        rw [List.drop_append_of_le_length (by simp [hprefixLength])]
        simp [hprefixLength]
      rw [htake, hdrop, List.rotate_rotate]

/-- `τ₃` has exact order `m=k-2`. -/
theorem fullRunMap_order_exact (hk : 3 ≤ k) (u : PermutationVertex k) :
    fullRunMapPower hk (k - 2) u = u ∧
      ∀ i, 0 < i → i < k - 2 → fullRunMapPower hk i u ≠ u := by
  have hprefixLength : (u.1.take (k - 2)).length = k - 2 := by
    simp [u.length]
  have hprefixNonempty : u.1.take (k - 2) ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    rw [hprefixLength] at this
    simp at this
    omega
  have hprefixNodup : (u.1.take (k - 2)).Nodup :=
    (List.take_sublist (k - 2) u.1).nodup u.nodup
  constructor
  · apply PermutationVertex.ext
    calc
      (fullRunMapPower hk (k - 2) u).1 =
          (u.1.take (k - 2)).rotate (k - 2) ++
            u.1.drop (k - 2) := fullRunMapPower_word hk (k - 2) u
      _ = (u.1.take (k - 2)).rotate
            (u.1.take (k - 2)).length ++ u.1.drop (k - 2) := by
          rw [hprefixLength]
      _ = u.1.take (k - 2) ++ u.1.drop (k - 2) := by
          rw [List.rotate_length]
      _ = u.1 := u.1.take_append_drop (k - 2)
  · intro i hi hilt heq
    have hword := congrArg Subtype.val heq
    rw [fullRunMapPower_word] at hword
    have hprefixEq : (u.1.take (k - 2)).rotate i = u.1.take (k - 2) := by
      have htakeLeft :
          ((u.1.take (k - 2)).rotate i ++ u.1.drop (k - 2)).take (k - 2) =
            (u.1.take (k - 2)).rotate i := by
        rw [List.take_append_of_le_length (by simp [hprefixLength])]
        simpa [hprefixLength]
      calc
        (u.1.take (k - 2)).rotate i =
            ((u.1.take (k - 2)).rotate i ++
              u.1.drop (k - 2)).take (k - 2) := htakeLeft.symm
        _ = u.1.take (k - 2) := congrArg (fun l => l.take (k - 2)) hword
    rcases (hprefixNodup.rotate_eq_self_iff.mp hprefixEq) with hmod | hnil
    · rw [hprefixLength, Nat.mod_eq_of_lt hilt] at hmod
      omega
    · exact hprefixNonempty hnil

/-! ## The six-entry full-run chart -/

/-- The final block entry of the formal full run entered at `u`. -/
noncomputable def fullRunChartLastEntry (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  runMapPower (by omega) (k - 2) u

/-- The exit from the final block of the formal full run entered at `u`. -/
noncomputable def fullRunChartExit (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  blockExit (fullRunChartLastEntry hk u)

private theorem take_prefix_length (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    (u.1.take (k - 2)).length = k - 2 := by
  simp [u.length]

private theorem drop_suffix_length (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    (u.1.drop (k - 2)).length = 2 := by
  simp [u.length]
  omega

/-- Exact final entry formula: if `u=A b c`, the last entry is `b A c`. -/
theorem fullRunChartLastEntry_word (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    (fullRunChartLastEntry hk u).1 =
      ((u.1.drop (k - 2)).take 1 ++
        u.1.take (k - 2) ++ u.1.drop (k - 1)) := by
  let pre := u.1.take (k - 2)
  let tail := u.1.drop (k - 2)
  have hpreLength : pre.length = k - 2 := by
    simpa [pre] using take_prefix_length (by omega) u
  have htailLength : tail.length = 2 := by
    simpa [tail] using drop_suffix_length (by omega) u
  obtain ⟨b, c, htail⟩ := List.length_eq_two.mp htailLength
  have hu : u.1 = pre ++ [b, c] := by
    calc
      u.1 = u.1.take (k - 2) ++ u.1.drop (k - 2) :=
        (u.1.take_append_drop (k - 2)).symm
      _ = pre ++ [b, c] := by
        change pre ++ tail = pre ++ [b, c]
        rw [htail]
  have hk1 : 1 ≤ k := by omega
  have hsatellite : entrySatellite hk1 u = c := by
    have hlast : u.1.getLast? = some c := by
      rw [hu]
      simp
    simpa [entrySatellite] using
      (List.getLast_of_getLast?_eq_some hlast)
  rw [fullRunChartLastEntry, runMapPower_word (by omega), hu]
  have hcore : (pre ++ [b, c]).dropLast = pre ++ [b] := by simp
  rw [hcore]
  rw [hsatellite]
  have hrotate : (pre ++ [b]).rotate (k - 2) = b :: pre := by
    rw [show k - 2 = pre.length by omega]
    rw [List.rotate_eq_drop_append_take (by simp)]
    simp
  rw [hrotate]
  have hdropFinal : (pre ++ [b, c]).drop (k - 1) = [c] := by
    rw [show k - 1 = pre.length + 1 by omega]
    simp
  rw [hdropFinal]
  simp [hpreLength]

/-- Exact final-exit orientation: if `u=A b c`, the exit is `c b A`. -/
theorem fullRunChartExit_word (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    (fullRunChartExit hk u).1 =
      ((u.1.drop (k - 2)).reverse ++ u.1.take (k - 2)) := by
  let pre := u.1.take (k - 2)
  let tail := u.1.drop (k - 2)
  have hpreLength : pre.length = k - 2 := by
    simpa [pre] using take_prefix_length (by omega) u
  have htailLength : tail.length = 2 := by
    simpa [tail] using drop_suffix_length (by omega) u
  obtain ⟨b, c, htail⟩ := List.length_eq_two.mp htailLength
  have hlast : (fullRunChartLastEntry hk u).1 = b :: pre ++ [c] := by
    rw [fullRunChartLastEntry_word hk u]
    have hu : u.1 = pre ++ [b, c] := by
      calc
        u.1 = u.1.take (k - 2) ++ u.1.drop (k - 2) :=
          (u.1.take_append_drop (k - 2)).symm
        _ = pre ++ [b, c] := by
          change pre ++ tail = pre ++ [b, c]
          rw [htail]
    rw [hu]
    have hdropFinal : (pre ++ [b, c]).drop (k - 1) = [c] := by
      rw [show k - 1 = pre.length + 1 by omega]
      simp
    rw [hdropFinal]
    simp [hpreLength]
  rw [fullRunChartExit, blockExit, inverseRotation_word, hlast]
  have hlength : (b :: pre ++ [c]).length = k := by
    simp [hpreLength]
    omega
  have hpred : k - 1 = (b :: pre).length := by
    simp [hpreLength]
    omega
  rw [hpred]
  simp
  simp [tail, htail, pre]

/-- The `i`th exact block entry of a full run is `τ₂^i(u)`. -/
theorem fullRunChart_entries (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) (hfull : r.IsFull)
    (i : ℕ) (hi : i < k - 1) :
    r.blocks.get ⟨i, by
      change i < r.length
      have hfull' : r.length = k - 1 := hfull
      rw [hfull']
      exact hi⟩ =
      runMapPower (by omega) i r.entry := by
  have hiRun : i < r.length := by
    have hfull' : r.length = k - 1 := hfull
    rw [hfull']
    exact hi
  exact blockAlignedRun_entrySequence hk p hp r i
    hiRun

/-- The final entry of an actual full run is the chart's final entry. -/
theorem fullRunChart_lastEntry (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) (hfull : r.IsFull) :
    r.lastEntry = fullRunChartLastEntry hk r.entry := by
  rw [blockAlignedRun_lastEntry_eq_runMapPower hk p hp r]
  unfold fullRunChartLastEntry
  have hfull' : r.length = k - 1 := hfull
  have hindex : r.length - 1 = k - 2 := by omega
  rw [hindex]

/-- Consequently the actual final exit has the exact chart word. -/
theorem fullRunChart_actualExit_word (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) (hfull : r.IsFull) :
    (blockExit r.lastEntry).1 =
      (r.entry.1.drop (k - 2)).reverse ++ r.entry.1.take (k - 2) := by
  calc
    (blockExit r.lastEntry).1 =
        (fullRunChartExit hk r.entry).1 := by
      simpa [fullRunChartExit] using congrArg
        (fun x : PermutationVertex k => (blockExit x).1)
        (fullRunChart_lastEntry hk p hp r hfull)
    _ = _ := fullRunChartExit_word hk r.entry

/-- The canonical list of all weight-three cut targets from a vertex.  Its
source list is literally the permutation list of the first three symbols. -/
noncomputable def weightThreeTargetList (u : PermutationVertex k) :
    List (PermutationVertex k) :=
  (u.1.take 3).permutations.attach.map fun suffix =>
    PermutationVertex.cutAppend u 3 suffix.1
      (List.mem_permutations.mp suffix.2)

private theorem cutAppend_three_ne (hk : 4 ≤ k)
    (u : PermutationVertex k) (suffix : Word k)
    (hsuffix : suffix.Perm (u.1.take 3)) :
    u ≠ PermutationVertex.cutAppend u 3 suffix hsuffix := by
  intro heq
  have hword := congrArg Subtype.val heq
  have hzero : 0 < u.1.length := by simp [u.length]; omega
  have hthree : 3 < u.1.length := by simp [u.length]; omega
  have hheadLeft : u.1.head? = some u.1[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hzero]
  have hheadRight :
      (u.1.drop 3 ++ suffix).head? = some u.1[3] := by
    rw [List.head?_append, List.head?_drop,
      List.getElem?_eq_getElem hthree]
    simp
  have hhead := congrArg List.head? hword
  change u.1.head? = (u.1.drop 3 ++ suffix).head? at hhead
  rw [hheadLeft, hheadRight] at hhead
  have helem : u.1[0] = u.1[3] := Option.some.inj hhead
  have hindex : (0 : ℕ) = 3 := u.nodup.getElem_inj_iff.mp helem
  omega

private theorem overlapWeight_self_ne_three (hk : 4 ≤ k)
    (u : PermutationVertex k) : overlapWeight u u ≠ 3 := by
  intro hweight
  have hoverlap := (overlapWeight_spec u u).2
  rw [hweight] at hoverlap
  unfold OverlapsAt at hoverlap
  have hthree : 3 < u.1.length := by simp [u.length]; omega
  have hzero : 0 < u.1.length := by simp [u.length]; omega
  have hremain : k - 3 ≠ 0 := by omega
  have hhead := congrArg List.head? hoverlap
  rw [List.head?_drop, List.getElem?_eq_getElem hthree,
    List.head?_take, if_neg hremain, List.head?_eq_getElem?,
    List.getElem?_eq_getElem hzero] at hhead
  have helem : u.1[3] = u.1[0] := Option.some.inj hhead
  have hindex : (3 : ℕ) = 0 := u.nodup.getElem_inj_iff.mp helem
  omega

/-- The canonical target list has exactly six distinct entries. -/
theorem weightThreeTargetList_exactly_six (hk : 4 ≤ k)
    (u : PermutationVertex k) :
    (weightThreeTargetList u).length = 6 ∧
      (weightThreeTargetList u).Nodup := by
  classical
  let source := (u.1.take 3).permutations.attach
  let target : {suffix // suffix ∈ (u.1.take 3).permutations} →
      PermutationVertex k := fun suffix =>
    PermutationVertex.cutAppend u 3 suffix.1
      (List.mem_permutations.mp suffix.2)
  have hsourceNodup : source.Nodup := by
    exact List.nodup_attach.mpr
      (first_three_arrangements_exactly_six u (by omega)).2
  have htargetInjective : Function.Injective target := by
    intro a b hab
    apply Subtype.ext
    have hword := congrArg Subtype.val hab
    change u.1.drop 3 ++ a.1 = u.1.drop 3 ++ b.1 at hword
    exact List.append_right_injective (u.1.drop 3) hword
  constructor
  · simp [weightThreeTargetList, first_three_arrangements_count u (by omega)]
  · change (source.map target).Nodup
    exact hsourceNodup.map htargetInjective

/-- All and only the six canonical targets are the weight-three successors. -/
theorem weightThreeTargetList_iff (hk : 4 ≤ k)
    (u v : PermutationVertex k) :
    overlapWeight u v = 3 ↔ v ∈ weightThreeTargetList u := by
  classical
  by_cases huv : u = v
  · subst v
    constructor
    · intro hweight
      exfalso
      exact overlapWeight_self_ne_three hk u hweight
    · intro hmem
      exfalso
      unfold weightThreeTargetList at hmem
      obtain ⟨suffix, _hsuffixMem, heq⟩ := List.mem_map.mp hmem
      exact (cutAppend_three_ne hk u suffix.1
        (List.mem_permutations.mp suffix.2)) heq.symm
  · rw [weight_three_successors u v hk huv]
    constructor
    · rintro ⟨suffix, hsuffix, hword⟩
      unfold weightThreeTargetList
      apply List.mem_map.mpr
      let attached : {s // s ∈ (u.1.take 3).permutations} :=
        ⟨suffix, hsuffix⟩
      refine ⟨attached, List.mem_attach _ _, ?_⟩
      apply PermutationVertex.ext
      change u.1.drop 3 ++ suffix = v.1
      exact hword.symm
    · intro hmem
      unfold weightThreeTargetList at hmem
      obtain ⟨suffix, hsuffixMem, rfl⟩ := List.mem_map.mp hmem
      exact ⟨suffix.1, suffix.2, rfl⟩

/-- Total cut-target constructor used to name the six chart entries.  The
fallback branch is never used by the six suffixes below. -/
noncomputable def chartTargetOfSuffix (u : PermutationVertex k)
    (suffix : Word k) : PermutationVertex k :=
  if h : suffix.Perm (u.1.take 3) then
    PermutationVertex.cutAppend u 3 suffix h
  else u

/-- The six suffix orders `T₁,…,T₆`, expressed from the cut triple
`(c,b,a₁)` of the final exit. -/
noncomputable def fullRunChartSuffixes (hk : 7 ≤ k)
    (u : PermutationVertex k) : List (Word k) :=
  let triple := (fullRunChartExit hk u).1.take 3
  [triple.reverse, triple.rotate 2, triple.rotate 1,
    triple.reverse.rotate 1, triple.reverse.rotate 2, triple]

/-- The six named chart targets in the frozen order `T₁,…,T₆`. -/
noncomputable def fullRunChartTargets (hk : 7 ≤ k)
    (u : PermutationVertex k) : List (PermutationVertex k) :=
  (fullRunChartSuffixes hk u).map
    (chartTargetOfSuffix (fullRunChartExit hk u))

/-- The first chart target `T₁`, which will be identified with `τ₃(u)`. -/
noncomputable def fullRunChartTarget1 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e (e.1.take 3).reverse

/-- The second chart target `T₂`. -/
noncomputable def fullRunChartTarget2 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e ((e.1.take 3).rotate 2)

/-- The third chart target `T₃`. -/
noncomputable def fullRunChartTarget3 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e ((e.1.take 3).rotate 1)

/-- The fourth chart target `T₄`. -/
noncomputable def fullRunChartTarget4 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e ((e.1.take 3).reverse.rotate 1)

/-- The fifth chart target `T₅`. -/
noncomputable def fullRunChartTarget5 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e ((e.1.take 3).reverse.rotate 2)

/-- The sixth chart target `T₆`. -/
noncomputable def fullRunChartTarget6 (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  let e := fullRunChartExit hk u
  chartTargetOfSuffix e (e.1.take 3)

/-- The chart list is literally ordered as `T₁,…,T₆`. -/
theorem fullRunChartTargets_eq_named (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTargets hk u =
      [fullRunChartTarget1 hk u, fullRunChartTarget2 hk u,
        fullRunChartTarget3 hk u, fullRunChartTarget4 hk u,
        fullRunChartTarget5 hk u, fullRunChartTarget6 hk u] := rfl

private theorem fullRunChartSuffixes_valid (hk : 7 ≤ k)
    (u : PermutationVertex k) (suffix : Word k)
    (hsuffix : suffix ∈ fullRunChartSuffixes hk u) :
    suffix.Perm ((fullRunChartExit hk u).1.take 3) := by
  let triple := (fullRunChartExit hk u).1.take 3
  change suffix ∈ [triple.reverse, triple.rotate 2, triple.rotate 1,
    triple.reverse.rotate 1, triple.reverse.rotate 2, triple] at hsuffix
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsuffix
  rcases hsuffix with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.reverse_perm triple
  · exact List.rotate_perm triple 2
  · exact List.rotate_perm triple 1
  · exact (List.rotate_perm triple.reverse 1).trans
      (List.reverse_perm triple)
  · exact (List.rotate_perm triple.reverse 2).trans
      (List.reverse_perm triple)
  · exact .refl triple

private theorem fullRunChartSuffixes_nodup (hk : 7 ≤ k)
    (u : PermutationVertex k) : (fullRunChartSuffixes hk u).Nodup := by
  let e := fullRunChartExit hk u
  let triple := e.1.take 3
  have htripleLength : triple.length = 3 := by
    have hthree : 3 ≤ k := by omega
    simp [triple, e, PermutationVertex.length, hthree]
  have htripleNodup : triple.Nodup :=
    (List.take_sublist 3 e.1).nodup e.nodup
  obtain ⟨a, b, c, htriple⟩ := List.length_eq_three.mp htripleLength
  change [triple.reverse, triple.rotate 2, triple.rotate 1,
    triple.reverse.rotate 1, triple.reverse.rotate 2, triple].Nodup
  rw [htriple] at htripleNodup ⊢
  simp_all

private theorem chartTargetOfSuffix_eq_cutAppend
    (u : PermutationVertex k) (suffix : Word k)
    (hsuffix : suffix.Perm (u.1.take 3)) :
    chartTargetOfSuffix u suffix =
      PermutationVertex.cutAppend u 3 suffix hsuffix := by
  simp [chartTargetOfSuffix, hsuffix]

private theorem chartTargetOfSuffix_word
    (u : PermutationVertex k) (suffix : Word k)
    (hsuffix : suffix.Perm (u.1.take 3)) :
    (chartTargetOfSuffix u suffix).1 = u.1.drop 3 ++ suffix := by
  rw [chartTargetOfSuffix_eq_cutAppend u suffix hsuffix]
  rfl

private theorem chartTargetOfSuffix_injective_on_valid
    (u : PermutationVertex k) {a b : Word k}
    (ha : a.Perm (u.1.take 3)) (hb : b.Perm (u.1.take 3))
    (h : chartTargetOfSuffix u a = chartTargetOfSuffix u b) : a = b := by
  rw [chartTargetOfSuffix_eq_cutAppend u a ha,
    chartTargetOfSuffix_eq_cutAppend u b hb] at h
  have hword := congrArg Subtype.val h
  change u.1.drop 3 ++ a = u.1.drop 3 ++ b at hword
  exact List.append_right_injective (u.1.drop 3) hword

/-- The six named targets are pairwise distinct and the list has length six. -/
theorem fullRunChartTargets_exactly_six (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    (fullRunChartTargets hk u).length = 6 ∧
      (fullRunChartTargets hk u).Nodup := by
  let e := fullRunChartExit hk u
  have hsuffixNodup := fullRunChartSuffixes_nodup hk u
  constructor
  · simp [fullRunChartTargets, fullRunChartSuffixes]
  · unfold fullRunChartTargets
    apply hsuffixNodup.map_on
    intro a ha b hb hab
    exact chartTargetOfSuffix_injective_on_valid e
      (fullRunChartSuffixes_valid hk u a ha)
      (fullRunChartSuffixes_valid hk u b hb) hab

private theorem fullRunChartTargets_subset_canonical (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTargets hk u ⊆
      weightThreeTargetList (fullRunChartExit hk u) := by
  intro v hv
  unfold fullRunChartTargets at hv
  obtain ⟨suffix, hsuffix, rfl⟩ := List.mem_map.mp hv
  have hperm := fullRunChartSuffixes_valid hk u suffix hsuffix
  rw [chartTargetOfSuffix_eq_cutAppend _ suffix hperm]
  unfold weightThreeTargetList
  apply List.mem_map.mpr
  let attached : {s // s ∈
      ((fullRunChartExit hk u).1.take 3).permutations} :=
    ⟨suffix, List.mem_permutations.mpr hperm⟩
  exact ⟨attached, List.mem_attach _ _, rfl⟩

private theorem fullRunChartTargets_perm_canonical (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    (fullRunChartTargets hk u).Perm
      (weightThreeTargetList (fullRunChartExit hk u)) := by
  have hsub := List.subperm_of_subset
    (fullRunChartTargets_exactly_six hk u).2
    (fullRunChartTargets_subset_canonical hk u)
  apply hsub.perm_of_length_le
  rw [(fullRunChartTargets_exactly_six hk u).1,
    (weightThreeTargetList_exactly_six (by omega)
      (fullRunChartExit hk u)).1]

/-- Full-run chart classification: all six and only the six named targets
are the weight-three successors of the final exit. -/
theorem fullRunChart_weightThree_successors (hk : 7 ≤ k)
    (u v : PermutationVertex k) :
    overlapWeight (fullRunChartExit hk u) v = 3 ↔
      v ∈ fullRunChartTargets hk u := by
  rw [weightThreeTargetList_iff (by omega)]
  exact (fullRunChartTargets_perm_canonical hk u).mem_iff.symm

private theorem permutationVertex_chart_split (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    ∃ a rest b c, rest.length = k - 3 ∧
      u.1 = a :: rest ++ [b, c] := by
  let pre := u.1.take (k - 2)
  let tail := u.1.drop (k - 2)
  have hpreLength : pre.length = k - 2 := by
    simpa [pre] using take_prefix_length (by omega) u
  have htailLength : tail.length = 2 := by
    simpa [tail] using drop_suffix_length (by omega) u
  cases hpreEq : pre with
  | nil =>
      rw [hpreEq] at hpreLength
      simp at hpreLength
      omega
  | cons a rest =>
      obtain ⟨b, c, htail⟩ := List.length_eq_two.mp htailLength
      refine ⟨a, rest, b, c, ?_, ?_⟩
      · rw [hpreEq] at hpreLength
        simp at hpreLength
        omega
      · calc
          u.1 = u.1.take (k - 2) ++ u.1.drop (k - 2) :=
            (u.1.take_append_drop (k - 2)).symm
          _ = a :: rest ++ [b, c] := by
            change pre ++ tail = _
            rw [hpreEq, htail]

private theorem entrySatellite_eq_of_word_append_singleton (hk : 1 ≤ k)
    (u : PermutationVertex k) (preword : Word k) (c : Alphabet k)
    (hu : u.1 = preword ++ [c]) :
    entrySatellite hk u = c := by
  have hlast : u.1.getLast? = some c := by rw [hu]; simp
  simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast

private theorem rotate_append_left_length (left right : List α) :
    (left ++ right).rotate left.length = right ++ left := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- Exact frozen words of all six named targets when
`u=a₁ A b c`. -/
theorem fullRunChart_target_words_of_split (hk : 7 ≤ k)
    (u : PermutationVertex k) (a b c : Alphabet k) (rest : Word k)
    (hrest : rest.length = k - 3)
    (hu : u.1 = a :: rest ++ [b, c]) :
    (fullRunChartTarget1 hk u).1 = rest ++ [a, b, c] ∧
    (fullRunChartTarget2 hk u).1 = rest ++ [a, c, b] ∧
    (fullRunChartTarget3 hk u).1 = rest ++ [b, a, c] ∧
    (fullRunChartTarget4 hk u).1 = rest ++ [b, c, a] ∧
    (fullRunChartTarget5 hk u).1 = rest ++ [c, a, b] ∧
    (fullRunChartTarget6 hk u).1 = rest ++ [c, b, a] := by
  have hexit : (fullRunChartExit hk u).1 = [c, b, a] ++ rest := by
    rw [fullRunChartExit_word hk u, hu]
    change
      (((a :: rest) ++ [b, c]).drop (k - 2)).reverse ++
          ((a :: rest) ++ [b, c]).take (k - 2) = _
    rw [show k - 2 = (a :: rest).length by simp [hrest]; omega]
    simp
  have hvalid1 :
      ((fullRunChartExit hk u).1.take 3).reverse.Perm
        ((fullRunChartExit hk u).1.take 3) :=
    List.reverse_perm _
  have hvalid2 :
      ((fullRunChartExit hk u).1.take 3).rotate 2 |>.Perm
        ((fullRunChartExit hk u).1.take 3) :=
    List.rotate_perm _ _
  have hvalid3 :
      ((fullRunChartExit hk u).1.take 3).rotate 1 |>.Perm
        ((fullRunChartExit hk u).1.take 3) :=
    List.rotate_perm _ _
  have hvalid4 :
      ((fullRunChartExit hk u).1.take 3).reverse.rotate 1 |>.Perm
        ((fullRunChartExit hk u).1.take 3) :=
    (List.rotate_perm _ _).trans (List.reverse_perm _)
  have hvalid5 :
      ((fullRunChartExit hk u).1.take 3).reverse.rotate 2 |>.Perm
        ((fullRunChartExit hk u).1.take 3) :=
    (List.rotate_perm _ _).trans (List.reverse_perm _)
  have hvalid6 :
      ((fullRunChartExit hk u).1.take 3).Perm
        ((fullRunChartExit hk u).1.take 3) := .refl _
  unfold fullRunChartTarget1 fullRunChartTarget2 fullRunChartTarget3
    fullRunChartTarget4 fullRunChartTarget5 fullRunChartTarget6
  rw [chartTargetOfSuffix_word _ _ hvalid1,
    chartTargetOfSuffix_word _ _ hvalid2,
    chartTargetOfSuffix_word _ _ hvalid3,
    chartTargetOfSuffix_word _ _ hvalid4,
    chartTargetOfSuffix_word _ _ hvalid5,
    chartTargetOfSuffix_word _ _ hvalid6]
  rw [hexit]
  simp

/-- The sole chart target not immediately forced into an occupied class is
exactly `τ₃(u)` with the frozen orientation. -/
theorem fullRunChart_target1_eq_fullRunMap (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget1 hk u = fullRunMap (by omega) u := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  apply PermutationVertex.ext
  rw [(fullRunChart_target_words_of_split hk u a b c rest hrest hu).1,
    fullRunMap_word, hu]
  change rest ++ [a, b, c] =
    (((a :: rest) ++ [b, c]).take (k - 2)).rotate 1 ++
      ((a :: rest) ++ [b, c]).drop (k - 2)
  rw [show k - 2 = (a :: rest).length by simp [hrest]; omega]
  simp

/-- Chart identity `T₃=Δ₁`. -/
theorem fullRunChart_target3_eq_runMap (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget3 hk u = runMap (by omega) u := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have hsatellite : entrySatellite (by omega) u = c :=
    entrySatellite_eq_of_word_append_singleton (by omega) u
      (a :: rest ++ [b]) c (by simpa [List.append_assoc] using hu)
  apply PermutationVertex.ext
  rw [(fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.1,
    runMap_word, hsatellite, hu]
  rw [show a :: rest ++ [b, c] =
    (a :: rest ++ [b]) ++ [c] by simp [List.append_assoc]]
  rw [List.dropLast_concat]
  simp

/-- Chart identity `T₄=σ(Δ₀)`. -/
theorem fullRunChart_target4_eq_rotation (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget4 hk u = rotation u := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  apply PermutationVertex.ext
  rw [(fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.2.1,
    rotation_word_eq_rotate (by omega), hu]
  simp [List.rotate_cons_succ]

/-- Chart identity `T₆=σ²(Δ_m)`. -/
theorem fullRunChart_target6_eq_rotationPower_lastEntry (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget6 hk u =
      rotationPower 2 (fullRunChartLastEntry hk u) := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have hlast : (fullRunChartLastEntry hk u).1 =
      b :: a :: rest ++ [c] := by
    rw [fullRunChartLastEntry_word, hu]
    change
      ((a :: rest ++ [b, c]).drop (k - 2)).take 1 ++
          (a :: rest ++ [b, c]).take (k - 2) ++
          (a :: rest ++ [b, c]).drop (k - 1) = _
    rw [show k - 2 = (a :: rest).length by simp [hrest]; omega]
    rw [show k - 1 = (a :: rest).length + 1 by simp [hrest]; omega]
    simp
  apply PermutationVertex.ext
  rw [(fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.2.2.2,
    rotationPower_word (by omega), hlast]
  simp

/-- The delayed collision identity for `T₂`:
`τ₂^(m-1)(T₂)=σ^m(Δ₁)`. -/
theorem fullRunChart_target2_delayed (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    runMapPower (by omega) (k - 3) (fullRunChartTarget2 hk u) =
      rotationPower (k - 2) (runMap (by omega) u) := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have htarget2 :=
    (fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.1
  have hsatelliteU : entrySatellite (by omega) u = c :=
    entrySatellite_eq_of_word_append_singleton (by omega) u
      (a :: rest ++ [b]) c (by simpa [List.append_assoc] using hu)
  have hrun : (runMap (by omega) u).1 = rest ++ [b, a, c] := by
    rw [runMap_word, hsatelliteU, hu]
    rw [show a :: rest ++ [b, c] =
      (a :: rest ++ [b]) ++ [c] by simp [List.append_assoc]]
    rw [List.dropLast_concat]
    simp
  have hsatelliteTarget :
      entrySatellite (by omega) (fullRunChartTarget2 hk u) = b :=
    entrySatellite_eq_of_word_append_singleton (by omega)
      (fullRunChartTarget2 hk u) (rest ++ [a, c]) b
      (by simpa [List.append_assoc] using htarget2)
  have hcoreTarget : (fullRunChartTarget2 hk u).1.dropLast =
      rest ++ [a, c] := by
    rw [htarget2]
    rw [show rest ++ [a, c, b] =
      (rest ++ [a, c]) ++ [b] by simp [List.append_assoc]]
    rw [List.dropLast_concat]
  have hrotateCore : (rest ++ [a, c]).rotate rest.length =
      [a, c] ++ rest := rotate_append_left_length rest [a, c]
  have hrotateRun : (rest ++ [b, a, c]).rotate (rest.length + 1) =
      [a, c] ++ rest ++ [b] := by
    rw [show rest ++ [b, a, c] =
      (rest ++ [b]) ++ [a, c] by simp [List.append_assoc]]
    rw [show rest.length + 1 = (rest ++ [b]).length by simp]
    rw [rotate_append_left_length]
    simp [List.append_assoc]
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), rotationPower_word (by omega),
    hcoreTarget, hrun, hsatelliteTarget]
  rw [show k - 3 = rest.length by omega]
  rw [show k - 2 = rest.length + 1 by omega]
  rw [hrotateCore, hrotateRun]

/-- The delayed collision identity for `T₅`:
`τ₂^(m-1)(T₅)=σ^(m+1)(Δ₀)`. -/
theorem fullRunChart_target5_delayed (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    runMapPower (by omega) (k - 3) (fullRunChartTarget5 hk u) =
      rotationPower (k - 1) u := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have htarget5 :=
    (fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.2.2.1
  have hsatelliteTarget :
      entrySatellite (by omega) (fullRunChartTarget5 hk u) = b :=
    entrySatellite_eq_of_word_append_singleton (by omega)
      (fullRunChartTarget5 hk u) (rest ++ [c, a]) b
      (by simpa [List.append_assoc] using htarget5)
  have hcoreTarget : (fullRunChartTarget5 hk u).1.dropLast =
      rest ++ [c, a] := by
    rw [htarget5]
    rw [show rest ++ [c, a, b] =
      (rest ++ [c, a]) ++ [b] by simp [List.append_assoc]]
    rw [List.dropLast_concat]
  have hrotateCore : (rest ++ [c, a]).rotate rest.length =
      [c, a] ++ rest := rotate_append_left_length rest [c, a]
  have hrotateU : (a :: rest ++ [b, c]).rotate (rest.length + 2) =
      [c, a] ++ rest ++ [b] := by
    rw [show a :: rest ++ [b, c] =
      (a :: rest ++ [b]) ++ [c] by simp [List.append_assoc]]
    rw [show rest.length + 2 = (a :: rest ++ [b]).length by simp]
    rw [rotate_append_left_length]
    simp [List.append_assoc]
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), rotationPower_word (by omega),
    hcoreTarget, hu, hsatelliteTarget]
  rw [show k - 3 = rest.length by omega]
  rw [show k - 1 = rest.length + 2 by omega]
  rw [hrotateCore, hrotateU]

/-- The five occupied-class chart identities, packaged in the TeX order. -/
theorem fullRunChart_five_occupied_identities (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget3 hk u = runMap (by omega) u ∧
    fullRunChartTarget4 hk u = rotation u ∧
    fullRunChartTarget6 hk u =
      rotationPower 2 (fullRunChartLastEntry hk u) ∧
    runMapPower (by omega) (k - 3) (fullRunChartTarget2 hk u) =
      rotationPower (k - 2) (runMap (by omega) u) ∧
    runMapPower (by omega) (k - 3) (fullRunChartTarget5 hk u) =
      rotationPower (k - 1) u :=
  ⟨fullRunChart_target3_eq_runMap hk u,
    fullRunChart_target4_eq_rotation hk u,
    fullRunChart_target6_eq_rotationPower_lastEntry hk u,
    fullRunChart_target2_delayed hk u,
    fullRunChart_target5_delayed hk u⟩

/-! ## Chart forcing for arbitrary generic runs -/

/-- The run at an exact position in the canonical ordered run list. -/
noncomputable def blockAlignedRunAt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : Fin (blockAlignedRuns hk p hp).length) :
    BlockAlignedRun hk p hp :=
  ⟨(blockAlignedRuns hk p hp).get j, List.get_mem _ j⟩

@[simp]
theorem blockAlignedRunAt_blocks (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : Fin (blockAlignedRuns hk p hp).length) :
    (blockAlignedRunAt hk p hp j).blocks =
      (blockAlignedRuns hk p hp).get j := rfl

/-- A segment deficit string has one entry for each of its runs. -/
@[simp]
theorem blockAlignedLightSegment_deficitString_length (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    s.deficitString.length = s.length := by
  simp [BlockAlignedLightSegment.deficitString,
    BlockAlignedLightSegment.length]

/-- A local deficit-string entry is exactly the deficit of the
corresponding globally indexed canonical run. -/
theorem blockAlignedLightSegment_deficitString_get (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) (j : Fin s.length) :
    s.deficitString.get ⟨j, by simpa using j.2⟩ =
      (blockAlignedRunAt hk p hp
        ⟨s.globalStart + j, by
          have := blockAlignedLightSegment_globalStart_bounds hk p hp s
          omega⟩).deficit := by
  have hrun := blockAlignedLightSegment_runAt_eq_globalRun hk p hp s j
  have hdeficit := congrArg (fun run => (k - 1) - run.length) hrun
  simpa [BlockAlignedLightSegment.deficitString,
    BlockAlignedLightSegment.runAt, BlockAlignedRun.deficit,
    BlockAlignedRun.length] using hdeficit

/-- The local deficit string is the exact consecutive slice of the global
deficit string at the segment's canonical start. -/
theorem blockAlignedLightSegment_deficitString_slice (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    ((blockAlignedDeficitString hk p hp).drop s.globalStart).take s.length =
      s.deficitString := by
  have hslice := blockAlignedLightSegment_globalStart_slice hk p hp s
  have hmapped := congrArg
    (List.map (fun run => (k - 1) - run.length)) hslice
  simpa [blockAlignedDeficitString,
    BlockAlignedLightSegment.deficitString] using hmapped

/-- The sum over the corresponding global deficit slice is the segment's
total deficit. -/
theorem blockAlignedLightSegment_deficitString_slice_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    (((blockAlignedDeficitString hk p hp).drop s.globalStart).take
      s.length).sum = s.totalDeficit := by
  rw [blockAlignedLightSegment_deficitString_slice hk p hp s]
  rfl

private theorem blockAlignedRun_block_mem_entries (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) {u : PermutationVertex k}
    (hu : u ∈ r.blocks) :
    u ∈ blockAlignedBlockEntries hk p hp := by
  rw [← (blockAlignedRuns_spec hk p hp).1]
  exact List.mem_flatten.mpr ⟨r.blocks, r.isRun, hu⟩

private theorem adjacentRunAt_rotationClasses_ne (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length)
    {u v : PermutationVertex k}
    (hu : u ∈ (blockAlignedRunAt hk p hp ⟨j, by omega⟩).blocks)
    (hv : v ∈ (blockAlignedRunAt hk p hp ⟨j + 1, hj⟩).blocks) :
    rotationClass u ≠ rotationClass v := by
  have hdisjoint := adjacentRuns_disjoint hk p hp j hj
  have huv : u ≠ v := by
    intro heq
    exact (List.disjoint_left.mp hdisjoint hu (heq ▸ hv))
  exact rotationClasses_ne_of_entries_mem hk p hp
    (blockAlignedRun_block_mem_entries hk p hp _ hu)
    (blockAlignedRun_block_mem_entries hk p hp _ hv) huv

/-- **Chart forcing.**  For two consecutive generic runs of an arbitrary
block-aligned exitless path, a full first run, a light boundary, and at
least `n-1=k-2` blocks in the second force its entry to be `τ₃(u)`. -/
theorem blockAlignedChartForcing (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length)
    (hfull : (blockAlignedRunAt hk p hp ⟨j, by omega⟩).IsFull)
    (hlight : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨j, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨j + 1, hj⟩).blocks)
    (hlong : k - 2 ≤
      (blockAlignedRunAt hk p hp ⟨j + 1, hj⟩).length) :
    (blockAlignedRunAt hk p hp ⟨j + 1, hj⟩).entry =
      fullRunMap (by omega)
        (blockAlignedRunAt hk p hp ⟨j, by omega⟩).entry := by
  let left := blockAlignedRunAt hk p hp ⟨j, by omega⟩
  let right := blockAlignedRunAt hk p hp ⟨j + 1, hj⟩
  have hfullLeft : left.IsFull := by simpa [left] using hfull
  have hfullLength : left.length = k - 1 := hfullLeft
  have hlongRight : k - 2 ≤ right.length := by simpa [right] using hlong
  have hleftNonempty : left.blocks ≠ [] := by
    exact List.ne_nil_of_mem_splitBy left.isRun
  have hrightNonempty : right.blocks ≠ [] := by
    exact List.ne_nil_of_mem_splitBy right.isRun
  have hweight :
      overlapWeight (blockExit left.lastEntry) right.entry = 3 := by
    have hraw : runBoundaryWeight left.blocks right.blocks = 3 := by
      simpa [IsLightRunBoundary, left, right] using hlight
    rw [runBoundaryWeight_eq left.blocks right.blocks
      hleftNonempty hrightNonempty] at hraw
    simpa [BlockAlignedRun.lastEntry, BlockAlignedRun.entry] using hraw
  have hchartWeight :
      overlapWeight (fullRunChartExit hk left.entry) right.entry = 3 := by
    have hweight' := hweight
    rw [fullRunChart_lastEntry hk p hp left hfullLeft] at hweight'
    simpa [fullRunChartExit] using hweight'
  have htargets : right.entry ∈ fullRunChartTargets hk left.entry :=
    (fullRunChart_weightThree_successors hk left.entry right.entry).mp
      hchartWeight
  rw [fullRunChartTargets_eq_named] at htargets
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htargets
  rcases htargets with hT1 | hT2 | hT3 | hT4 | hT5 | hT6
  · calc
      right.entry = fullRunChartTarget1 hk left.entry := hT1
      _ = fullRunMap (by omega) left.entry :=
        fullRunChart_target1_eq_fullRunMap hk left.entry
  · have hindexRight : k - 3 < right.length := by omega
    have hindexLeft : 1 < left.length := by
      omega
    let y := right.blocks.get ⟨k - 3, hindexRight⟩
    let x := left.blocks.get ⟨1, hindexLeft⟩
    have hy : y = runMapPower (by omega) (k - 3) right.entry :=
      blockAlignedRun_entrySequence hk p hp right (k - 3) hindexRight
    have hx : x = runMap (by omega) left.entry := by
      calc
        x = runMapPower (by omega) 1 left.entry :=
          blockAlignedRun_entrySequence hk p hp left 1 hindexLeft
        _ = runMap (by omega) left.entry := by
          simp [runMapPower, Function.iterate_one]
    have hyCollision : y =
        rotationPower (k - 2) (runMap (by omega) left.entry) := by
      calc
        y = runMapPower (by omega) (k - 3) right.entry := hy
        _ = runMapPower (by omega) (k - 3)
              (fullRunChartTarget2 hk left.entry) := congrArg _ hT2
        _ = rotationPower (k - 2) (runMap (by omega) left.entry) :=
          fullRunChart_target2_delayed hk left.entry
    have hclasses : rotationClass x = rotationClass y := by
      calc
        rotationClass x = rotationClass (runMap (by omega) left.entry) :=
          congrArg rotationClass hx
        _ = rotationClass
              (rotationPower (k - 2) (runMap (by omega) left.entry)) :=
          (rotationClass_rotationPower (by omega) (k - 2)
            (runMap (by omega) left.entry)).symm
        _ = rotationClass y := congrArg rotationClass hyCollision.symm
    exfalso
    exact (adjacentRunAt_rotationClasses_ne hk p hp j hj
      (by exact List.get_mem _ _) (by exact List.get_mem _ _)) hclasses
  · have hindexLeft : 1 < left.length := by
      omega
    let x := left.blocks.get ⟨1, hindexLeft⟩
    have hx : x = runMap (by omega) left.entry := by
      calc
        x = runMapPower (by omega) 1 left.entry :=
          blockAlignedRun_entrySequence hk p hp left 1 hindexLeft
        _ = runMap (by omega) left.entry := by
          simp [runMapPower, Function.iterate_one]
    have hclasses : rotationClass x = rotationClass right.entry := by
      rw [hx, hT3, fullRunChart_target3_eq_runMap]
    exfalso
    exact (adjacentRunAt_rotationClasses_ne hk p hp j hj
      (by exact List.get_mem _ _) (List.head_mem hrightNonempty)) hclasses
  · have hclasses : rotationClass left.entry = rotationClass right.entry := by
      rw [hT4, fullRunChart_target4_eq_rotation]
      simpa [rotationPower, Function.iterate_one] using
        (rotationClass_rotationPower (by omega) 1 left.entry).symm
    exfalso
    exact (adjacentRunAt_rotationClasses_ne hk p hp j hj
      (List.head_mem hleftNonempty) (List.head_mem hrightNonempty)) hclasses
  · have hindexRight : k - 3 < right.length := by omega
    let y := right.blocks.get ⟨k - 3, hindexRight⟩
    have hy : y = runMapPower (by omega) (k - 3) right.entry :=
      blockAlignedRun_entrySequence hk p hp right (k - 3) hindexRight
    have hyCollision : y = rotationPower (k - 1) left.entry := by
      calc
        y = runMapPower (by omega) (k - 3) right.entry := hy
        _ = runMapPower (by omega) (k - 3)
              (fullRunChartTarget5 hk left.entry) := congrArg _ hT5
        _ = rotationPower (k - 1) left.entry :=
          fullRunChart_target5_delayed hk left.entry
    have hclasses : rotationClass left.entry = rotationClass y := by
      calc
        rotationClass left.entry =
            rotationClass (rotationPower (k - 1) left.entry) :=
          (rotationClass_rotationPower (by omega) (k - 1) left.entry).symm
        _ = rotationClass y := congrArg rotationClass hyCollision.symm
    exfalso
    exact (adjacentRunAt_rotationClasses_ne hk p hp j hj
      (List.head_mem hleftNonempty) (by exact List.get_mem _ _)) hclasses
  · have hclasses : rotationClass left.lastEntry = rotationClass right.entry := by
      calc
        rotationClass left.lastEntry =
            rotationClass (fullRunChartLastEntry hk left.entry) :=
          congrArg rotationClass
            (fullRunChart_lastEntry hk p hp left hfullLeft)
        _ = rotationClass
            (rotationPower 2 (fullRunChartLastEntry hk left.entry)) :=
          (rotationClass_rotationPower (by omega) 2
            (fullRunChartLastEntry hk left.entry)).symm
        _ = rotationClass (fullRunChartTarget6 hk left.entry) :=
          congrArg rotationClass
            (fullRunChart_target6_eq_rotationPower_lastEntry hk left.entry).symm
        _ = rotationClass right.entry := congrArg rotationClass hT6.symm
    exfalso
    exact (adjacentRunAt_rotationClasses_ne hk p hp j hj
      (List.getLast_mem hleftNonempty) (List.head_mem hrightNonempty)) hclasses

/-! ## Chart closure -/

/-- A rotation class is occupied by one of the first `q` formal full runs
in the `τ₃` orbit of `u`. -/
def FullRunChainOccupies (hk : 7 ≤ k) (u : PermutationVertex k)
    (q : ℕ) (v : PermutationVertex k) : Prop :=
  ∃ j < q, ∃ i < k - 1,
    rotationClass v =
      rotationClass
        (runMapPower (by omega) i (fullRunMapPower (by omega) j u))

/-- The weight-one target of a full-run exit is its final block entry. -/
theorem fullRunChart_weightOne_target (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    rotation (fullRunChartExit hk u) = fullRunChartLastEntry hk u := by
  unfold fullRunChartExit blockExit
  exact rotation_inverseRotation (by omega) _

/-- The two weight-two targets of a full-run exit are respectively the
run entry and a rotation of its final block entry. -/
theorem fullRunChart_weightTwo_targets (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    door (fullRunChartExit hk u) = u ∧
      doubleRotation (fullRunChartExit hk u) =
        rotation (fullRunChartLastEntry hk u) := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have hexit : (fullRunChartExit hk u).1 = [c, b, a] ++ rest := by
    rw [fullRunChartExit_word, hu]
    change
      ((a :: rest ++ [b, c]).drop (k - 2)).reverse ++
        (a :: rest ++ [b, c]).take (k - 2) = _
    rw [show k - 2 = (a :: rest).length by simp [hrest]; omega]
    simp
  have hlast : (fullRunChartLastEntry hk u).1 = b :: a :: rest ++ [c] := by
    rw [fullRunChartLastEntry_word, hu]
    change
      ((a :: rest ++ [b, c]).drop (k - 2)).take 1 ++
          (a :: rest ++ [b, c]).take (k - 2) ++
          (a :: rest ++ [b, c]).drop (k - 1) = _
    rw [show k - 2 = (a :: rest).length by simp [hrest]; omega]
    rw [show k - 1 = (a :: rest).length + 1 by simp [hrest]; omega]
    simp
  constructor
  · apply PermutationVertex.ext
    rw [door_word, hexit, hu]
    simp
  · apply PermutationVertex.ext
    rw [doubleRotation_word, hexit, rotation_word_eq_rotate (by omega), hlast]
    simp

private theorem chart_split_last_symbol (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    ∃ a middle z b c,
      middle.length = k - 4 ∧
      u.1 = a :: middle ++ [z, b, c] := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have hrestNonempty : rest ≠ [] := by
    intro hnil
    rw [hnil] at hrest
    simp at hrest
    omega
  let z := rest.getLast hrestNonempty
  let middle := rest.dropLast
  have hsplit : middle ++ [z] = rest := by
    exact List.dropLast_append_getLast hrestNonempty
  refine ⟨a, middle, z, b, c, ?_, ?_⟩
  · change rest.dropLast.length = k - 4
    simp [hrest]
    omega
  · rw [← hsplit] at hu
    simpa [List.append_assoc] using hu

/-- At the final point of the length-`m` `τ₃` orbit, the three
weight-three targets not covered by the current-run identities close into
the first full run, with the exact TeX orientations. -/
theorem fullRunChart_cycle_closing_identities (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    let w := fullRunMapPower (by omega) (k - 3) u
    fullRunChartTarget1 hk w = u ∧
    fullRunChartTarget2 hk w =
      rotation (fullRunChartLastEntry hk u) ∧
    fullRunChartTarget5 hk w =
      rotationPower 2 (runMapPower (by omega) (k - 3) u) := by
  dsimp only
  obtain ⟨a, middle, z, b, c, hmiddle, hu⟩ :=
    chart_split_last_symbol hk u
  have hprefixLength : (a :: middle ++ [z]).length = k - 2 := by
    simp [hmiddle]
    omega
  have hwordNorm : a :: middle ++ [z, b, c] =
      (a :: middle ++ [z]) ++ [b, c] := by
    simp [List.append_assoc]
  have htake : (a :: middle ++ [z, b, c]).take (k - 2) =
      a :: middle ++ [z] := by
    calc
      (a :: middle ++ [z, b, c]).take (k - 2) =
          (a :: middle ++ [z, b, c]).take
            (a :: middle ++ [z]).length := by rw [hprefixLength]
      _ = (((a :: middle ++ [z]) ++ [b, c]).take
            (a :: middle ++ [z]).length) :=
        congrArg (fun l => l.take (a :: middle ++ [z]).length) hwordNorm
      _ = a :: middle ++ [z] := by
        simp only [List.take_append_of_le_length (le_refl _), List.take_length]
  have hdrop : (a :: middle ++ [z, b, c]).drop (k - 2) = [b, c] := by
    calc
      (a :: middle ++ [z, b, c]).drop (k - 2) =
          (a :: middle ++ [z, b, c]).drop
            (a :: middle ++ [z]).length := by rw [hprefixLength]
      _ = (((a :: middle ++ [z]) ++ [b, c]).drop
            (a :: middle ++ [z]).length) :=
        congrArg (fun l => l.drop (a :: middle ++ [z]).length) hwordNorm
      _ = [b, c] := by simp
  have hdropFinal : (a :: middle ++ [z, b, c]).drop (k - 1) = [c] := by
    have hkm : k - 1 = (k - 2) + 1 := by omega
    calc
      (a :: middle ++ [z, b, c]).drop (k - 1) =
          (a :: middle ++ [z, b, c]).drop
            ((a :: middle ++ [z]).length + 1) := by
              rw [hkm, hprefixLength]
      _ = (((a :: middle ++ [z]) ++ [b, c]).drop
            ((a :: middle ++ [z]).length + 1)) :=
        congrArg (fun l => l.drop ((a :: middle ++ [z]).length + 1))
          hwordNorm
      _ = [c] := by simp
  have hfinal :
      (fullRunMapPower (by omega) (k - 3) u).1 =
        z :: a :: middle ++ [b, c] := by
    rw [fullRunMapPower_word, hu]
    rw [htake, hdrop]
    rw [show k - 3 = (a :: middle).length by simp [hmiddle]; omega]
    have hrotate := rotate_append_left_length (a :: middle) [z]
    simpa [List.append_assoc] using congrArg (fun l => l ++ [b, c]) hrotate
  have hfinalRest : (a :: middle).length = k - 3 := by
    simp [hmiddle]
    omega
  have htargets := fullRunChart_target_words_of_split hk
    (fullRunMapPower (by omega) (k - 3) u) z b c (a :: middle)
    hfinalRest hfinal
  have hlast : (fullRunChartLastEntry hk u).1 =
      b :: a :: middle ++ [z, c] := by
    rw [fullRunChartLastEntry_word, hu]
    rw [hdrop, htake, hdropFinal]
    simp
  have hpenultimate :
      (runMapPower (by omega) (k - 3) u).1 =
        z :: b :: a :: middle ++ [c] := by
    rw [runMapPower_word (by omega), hu]
    have hsatellite : entrySatellite (by omega) u = c :=
      entrySatellite_eq_of_word_append_singleton (by omega) u
        (a :: middle ++ [z, b]) c
        (by simpa [List.append_assoc] using hu)
    rw [hsatellite]
    have hcore : (a :: middle ++ [z, b, c]).dropLast =
        a :: middle ++ [z, b] := by
      rw [show a :: middle ++ [z, b, c] =
        (a :: middle ++ [z, b]) ++ [c] by simp [List.append_assoc]]
      rw [List.dropLast_concat]
    rw [hcore]
    rw [show k - 3 = (a :: middle).length by simp [hmiddle]; omega]
    have hrotate := rotate_append_left_length (a :: middle) [z, b]
    simpa [List.append_assoc] using congrArg (fun l => l ++ [c]) hrotate
  constructor
  · apply PermutationVertex.ext
    rw [htargets.1, hu]
  constructor
  · apply PermutationVertex.ext
    rw [htargets.2.1, rotation_word_eq_rotate (by omega), hlast]
    simp
  · apply PermutationVertex.ext
    rw [htargets.2.2.2.2.1, rotationPower_word (by omega), hpenultimate]
    simp

private theorem overlapWeight_self_gt_three (hk : 7 ≤ k)
    (u : PermutationVertex k) : 3 < overlapWeight u u := by
  let t := overlapWeight u u
  have htpos : 1 ≤ t := (overlapWeight_spec u u).1
  by_contra hnot
  have htle : t ≤ 3 := by omega
  have htlt : t < u.1.length := by simp [u.length]; omega
  have hzero : 0 < u.1.length := by simp [u.length]; omega
  have hremain : k - t ≠ 0 := by omega
  have hoverlap := (overlapWeight_spec u u).2
  unfold OverlapsAt at hoverlap
  have hhead := congrArg List.head? hoverlap
  rw [List.head?_drop, List.getElem?_eq_getElem htlt,
    List.head?_take, if_neg hremain, List.head?_eq_getElem?,
    List.getElem?_eq_getElem hzero] at hhead
  have helem : u.1[t] = u.1[0] := Option.some.inj hhead
  have hindex : t = 0 := u.nodup.getElem_inj_iff.mp helem
  omega

/-- **Chart closure, occupied-class form.**  After the complete `m=k-2`
cycle of full runs, every successor of weight at most three from the final
exit lies in a rotation class occupied by one of those runs. -/
theorem fullRunChart_cycleClosure (hk : 7 ≤ k)
    (u v : PermutationVertex k)
    (hweight : overlapWeight
      (fullRunChartExit hk
        (fullRunMapPower (by omega) (k - 3) u)) v ≤ 3) :
    FullRunChainOccupies hk u (k - 2) v := by
  let w := fullRunMapPower (by omega) (k - 3) u
  let x := fullRunChartExit hk w
  have hpositive : 1 ≤ overlapWeight x v :=
    (overlapWeight_spec x v).1
  have hne : x ≠ v := by
    intro heq
    have hle : overlapWeight x v ≤ 3 := by simpa [x, w] using hweight
    have hselfle := hle
    rw [← heq] at hselfle
    exact (not_lt_of_ge hselfle) (overlapWeight_self_gt_three hk x)
  have hor : overlapWeight x v = 1 ∨
      overlapWeight x v = 2 ∨ overlapWeight x v = 3 := by
    have : overlapWeight x v ≤ 3 := by simpa [x, w] using hweight
    omega
  rcases hor with hone | htwo | hthree
  · have hv : v = rotation x :=
      (unique_weight_one_successor x v (by omega) hne).mp hone
    have hvLast : v = fullRunChartLastEntry hk w :=
      hv.trans (fullRunChart_weightOne_target hk w)
    refine ⟨k - 3, by omega, k - 2, by omega, ?_⟩
    rw [hvLast]
    rfl
  · rcases (weight_two_successors x v (by omega) hne).mp htwo with
      hvDouble | hvDoor
    · have hvRot : v = rotation (fullRunChartLastEntry hk w) :=
        hvDouble.trans (fullRunChart_weightTwo_targets hk w).2
      refine ⟨k - 3, by omega, k - 2, by omega, ?_⟩
      rw [hvRot]
      change rotationClass (rotation (fullRunChartLastEntry hk w)) =
        rotationClass (fullRunChartLastEntry hk w)
      simpa [rotationPower, Function.iterate_one] using
        rotationClass_rotationPower (by omega) 1
          (fullRunChartLastEntry hk w)
    · have hvEntry : v = w :=
      hvDoor.trans (fullRunChart_weightTwo_targets hk w).1
      refine ⟨k - 3, by omega, 0, by omega, ?_⟩
      simp [hvEntry, w, fullRunMapPower, runMapPower]
  · have htargets : v ∈ fullRunChartTargets hk w :=
      (fullRunChart_weightThree_successors hk w v).mp hthree
    rw [fullRunChartTargets_eq_named] at htargets
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htargets
    have hclosing := fullRunChart_cycle_closing_identities hk u
    rcases htargets with hT1 | hT2 | hT3 | hT4 | hT5 | hT6
    · refine ⟨0, by omega, 0, by omega, ?_⟩
      rw [hT1, hclosing.1]
      simp [fullRunMapPower, runMapPower]
    · refine ⟨0, by omega, k - 2, by omega, ?_⟩
      rw [hT2, hclosing.2.1]
      change rotationClass (rotation (fullRunChartLastEntry hk u)) =
        rotationClass (fullRunChartLastEntry hk u)
      simpa [rotationPower, Function.iterate_one] using
        rotationClass_rotationPower (by omega) 1
          (fullRunChartLastEntry hk u)
    · refine ⟨k - 3, by omega, 1, by omega, ?_⟩
      rw [hT3, fullRunChart_target3_eq_runMap]
      simp [w, runMapPower, Function.iterate_one]
    · refine ⟨k - 3, by omega, 0, by omega, ?_⟩
      rw [hT4, fullRunChart_target4_eq_rotation]
      change rotationClass (rotation w) = rotationClass w
      simpa [rotationPower, Function.iterate_one] using
        rotationClass_rotationPower (by omega) 1 w
    · refine ⟨0, by omega, k - 3, by omega, ?_⟩
      rw [hT5, hclosing.2.2]
      exact rotationClass_rotationPower (by omega) 2
        (runMapPower (by omega) (k - 3) u)
    · refine ⟨k - 3, by omega, k - 2, by omega, ?_⟩
      rw [hT6, fullRunChart_target6_eq_rotationPower_lastEntry]
      exact rotationClass_rotationPower (by omega) 2
        (fullRunChartLastEntry hk w)

/-- A specified interval of the global ordered run list consisting of full
runs joined by light boundaries.  No maximality or forest hypothesis is
part of this structure. -/
structure BlockAlignedFullLightChain (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) where
  start : ℕ
  runCount : ℕ
  inBounds : start + runCount ≤ (blockAlignedRuns hk p hp).length
  full : ∀ j, ∀ hj : j < runCount,
    (blockAlignedRunAt hk p hp ⟨start + j, by omega⟩).IsFull
  light : ∀ j, ∀ hj : j + 1 < runCount,
    IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨start + j, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨start + j + 1, by omega⟩).blocks

namespace BlockAlignedFullLightChain

/-- A class occupied by an actual full-light chain. -/
def Occupies {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (chain : BlockAlignedFullLightChain hk p hp)
    (v : PermutationVertex k) : Prop :=
  ∃ j, ∃ hj : j < chain.runCount,
    ∃ y ∈ (blockAlignedRunAt hk p hp
      ⟨chain.start + j, by have := chain.inBounds; omega⟩).blocks,
      rotationClass v = rotationClass y

end BlockAlignedFullLightChain

private theorem runAt_rotationClasses_ne_of_lt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i j : ℕ) (hi : i < (blockAlignedRuns hk p hp).length)
    (hj : j < (blockAlignedRuns hk p hp).length) (hij : i < j)
    {u v : PermutationVertex k}
    (hu : u ∈ (blockAlignedRunAt hk p hp ⟨i, hi⟩).blocks)
    (hv : v ∈ (blockAlignedRunAt hk p hp ⟨j, hj⟩).blocks) :
    rotationClass u ≠ rotationClass v := by
  let runs := blockAlignedRuns hk p hp
  have hflat : runs.flatten = blockAlignedBlockEntries hk p hp :=
    (blockAlignedRuns_spec hk p hp).1
  have hnodup : runs.flatten.Nodup := by
    rw [hflat]
    exact blockAlignedBlockEntries_nodup hk p hp
  have hpair : runs.Pairwise List.Disjoint := (List.nodup_flatten.mp hnodup).2
  have hdisjoint := hpair.rel_get_of_lt
    (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (Fin.mk_lt_mk.mpr hij)
  have huv : u ≠ v := by
    intro heq
    exact List.disjoint_left.mp hdisjoint hu (heq ▸ hv)
  exact rotationClasses_ne_of_entries_mem hk p hp
    (blockAlignedRun_block_mem_entries hk p hp _ hu)
    (blockAlignedRun_block_mem_entries hk p hp _ hv) huv

/-- Entries in a full-light chain are the successive exact `τ₃`
iterates of the first entry. -/
theorem blockAlignedFullLightChain_entry_formula (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (chain : BlockAlignedFullLightChain hk p hp)
    (j : ℕ) (hj : j < chain.runCount) :
    (blockAlignedRunAt hk p hp
      ⟨chain.start + j, by have := chain.inBounds; omega⟩).entry =
      fullRunMapPower (by omega) j
        (blockAlignedRunAt hk p hp
          ⟨chain.start, by have := chain.inBounds; omega⟩).entry := by
  induction j with
  | zero => simp [fullRunMapPower]
  | succ j ih =>
      have hjThis : j < chain.runCount := by omega
      have hjBoundary : j + 1 < chain.runCount := by omega
      have hcurrentFull := chain.full j hjThis
      have hnextFull := chain.full (j + 1) hjBoundary
      have hnextLong : k - 2 ≤
          (blockAlignedRunAt hk p hp
            ⟨chain.start + j + 1, by
              have := chain.inBounds; omega⟩).length := by
        have hlength : (blockAlignedRunAt hk p hp
            ⟨chain.start + (j + 1), by
              have := chain.inBounds; omega⟩).length = k - 1 :=
          hnextFull
        have hlength' : (blockAlignedRunAt hk p hp
            ⟨chain.start + j + 1, by
              have := chain.inBounds; omega⟩).length = k - 1 := by
          simpa [Nat.add_assoc] using hlength
        rw [hlength']
        omega
      have hforced := blockAlignedChartForcing hk p hp
        (chain.start + j) (by have := chain.inBounds; omega) hcurrentFull
        (chain.light j hjBoundary) hnextLong
      calc
        (blockAlignedRunAt hk p hp
            ⟨chain.start + (j + 1), by
              have := chain.inBounds; omega⟩).entry =
            fullRunMap (by omega)
              (blockAlignedRunAt hk p hp
                ⟨chain.start + j, by
                  have := chain.inBounds; omega⟩).entry := by
          simpa [Nat.add_assoc] using hforced
        _ = fullRunMap (by omega)
              (fullRunMapPower (by omega) j
                (blockAlignedRunAt hk p hp
                  ⟨chain.start, by
                    have := chain.inBounds; omega⟩).entry) :=
          congrArg (fullRunMap (by omega)) (ih hjThis)
        _ = fullRunMapPower (by omega) (j + 1)
              (blockAlignedRunAt hk p hp
                ⟨chain.start, by
                  have := chain.inBounds; omega⟩).entry := by
          simp [fullRunMapPower, Function.iterate_succ_apply']

/-- **Chart closure, run-count form.**  Every consecutive full chain in a
light segment has at most `n-1=k-2` runs. -/
theorem blockAlignedFullLightChain_runCount_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (chain : BlockAlignedFullLightChain hk p hp) :
    chain.runCount ≤ k - 2 := by
  by_contra hnot
  have hlate : k - 2 < chain.runCount := by omega
  let first := blockAlignedRunAt hk p hp
    ⟨chain.start, by have := chain.inBounds; omega⟩
  let late := blockAlignedRunAt hk p hp
    ⟨chain.start + (k - 2), by
      have := chain.inBounds; omega⟩
  have hfirstNonempty : first.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy first.isRun
  have hlateNonempty : late.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy late.isRun
  have hentryLate := blockAlignedFullLightChain_entry_formula
    hk p hp chain (k - 2) hlate
  have heq : late.entry = first.entry := by
    calc
      late.entry = fullRunMapPower (by omega) (k - 2) first.entry := by
        simpa [late, first] using hentryLate
      _ = first.entry := (fullRunMap_order_exact (by omega) first.entry).1
  have hclasses : rotationClass first.entry = rotationClass late.entry :=
    congrArg rotationClass heq.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    chain.start (chain.start + (k - 2))
    (by have := chain.inBounds; omega)
    (by have := chain.inBounds; omega) (by omega)
    (List.head_mem hfirstNonempty) (List.head_mem hlateNonempty)) hclasses

/-- **Chart closure, frozen occupied-class conclusion for actual runs.**
For exactly `n-1` consecutive full runs, every successor of weight at most
three from the actual final exit lies in a class occupied by the chain. -/
theorem blockAlignedFullLightChain_cycleClosure (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (chain : BlockAlignedFullLightChain hk p hp)
    (hcount : chain.runCount = k - 2)
    (v : PermutationVertex k)
    (hweight : overlapWeight
      (blockExit (blockAlignedRunAt hk p hp
        ⟨chain.start + (k - 3), by
          have := chain.inBounds; omega⟩).lastEntry) v ≤ 3) :
    chain.Occupies v := by
  let first := blockAlignedRunAt hk p hp
    ⟨chain.start, by have := chain.inBounds; omega⟩
  let final := blockAlignedRunAt hk p hp
    ⟨chain.start + (k - 3), by
      have := chain.inBounds; omega⟩
  have hfinalIndex : k - 3 < chain.runCount := by omega
  have hfinalFull : final.IsFull := by
    simpa [final] using chain.full (k - 3) hfinalIndex
  have hfinalEntry : final.entry =
      fullRunMapPower (by omega) (k - 3) first.entry := by
    simpa [final, first] using
      blockAlignedFullLightChain_entry_formula hk p hp chain
        (k - 3) hfinalIndex
  have hrawWeight : overlapWeight
      (fullRunChartExit hk
        (fullRunMapPower (by omega) (k - 3) first.entry)) v ≤ 3 := by
    have hlast := fullRunChart_lastEntry hk p hp final hfinalFull
    simpa [fullRunChartExit, final, hfinalEntry, hlast] using hweight
  obtain ⟨j, hj, i, hi, hclass⟩ :=
    fullRunChart_cycleClosure hk first.entry v hrawWeight
  have hjChain : j < chain.runCount := by omega
  let rj := blockAlignedRunAt hk p hp
    ⟨chain.start + j, by have := chain.inBounds; omega⟩
  have hrjFull : rj.IsFull := by simpa [rj] using chain.full j hjChain
  have hiRun : i < rj.length := by
    have hlength : rj.length = k - 1 := hrjFull
    omega
  let y := rj.blocks.get ⟨i, hiRun⟩
  have hy : y = runMapPower (by omega) i
      (fullRunMapPower (by omega) j first.entry) := by
    calc
      y = runMapPower (by omega) i rj.entry :=
        blockAlignedRun_entrySequence hk p hp rj i hiRun
      _ = runMapPower (by omega) i
          (fullRunMapPower (by omega) j first.entry) := by
        congr 1
        simpa [rj, first] using
          blockAlignedFullLightChain_entry_formula hk p hp chain j hjChain
  refine ⟨j, hjChain, y, List.get_mem _ _, ?_⟩
  exact hclass.trans (congrArg rotationClass hy.symm)

/-- After exactly `n-1` full runs, no further run joined by a light
boundary can follow. -/
theorem blockAlignedFullLightChain_no_light_successor (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (chain : BlockAlignedFullLightChain hk p hp)
    (hcount : chain.runCount = k - 2)
    (hnext : chain.start + chain.runCount <
      (blockAlignedRuns hk p hp).length)
    (hlight : IsLightRunBoundary
      (blockAlignedRunAt hk p hp
        ⟨chain.start + (chain.runCount - 1), by omega⟩).blocks
      (blockAlignedRunAt hk p hp
        ⟨chain.start + chain.runCount, hnext⟩).blocks) : False := by
  let final := blockAlignedRunAt hk p hp
    ⟨chain.start + (chain.runCount - 1), by omega⟩
  let next := blockAlignedRunAt hk p hp
    ⟨chain.start + chain.runCount, hnext⟩
  have hfinalNonempty : final.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy final.isRun
  have hnextNonempty : next.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy next.isRun
  have hboundary : overlapWeight (blockExit final.lastEntry) next.entry = 3 := by
    have hraw : runBoundaryWeight final.blocks next.blocks = 3 := by
      simpa [IsLightRunBoundary, final, next] using hlight
    rw [runBoundaryWeight_eq final.blocks next.blocks
      hfinalNonempty hnextNonempty] at hraw
    simpa [BlockAlignedRun.lastEntry, BlockAlignedRun.entry] using hraw
  have hoccupied : chain.Occupies next.entry := by
    apply blockAlignedFullLightChain_cycleClosure hk p hp chain hcount next.entry
    have hpred : chain.runCount - 1 = k - 3 := by omega
    simpa [final, hpred] using (show
      overlapWeight (blockExit final.lastEntry) next.entry ≤ 3 from
        by omega)
  obtain ⟨j, hj, y, hy, hclasses⟩ := hoccupied
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (chain.start + j) (chain.start + chain.runCount)
    (by omega) hnext (by omega) hy (List.head_mem hnextNonempty)) hclasses.symm

/-- A locally indexed consecutive interval of full runs inside a light
segment, transported to the corresponding global indices.  Internal
lightness is obtained from segment membership. -/
noncomputable def BlockAlignedLightSegment.fullIntervalChain (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (localStart runCount : ℕ)
    (hin : localStart + runCount ≤ s.length)
    (hfull : ∀ j, ∀ hj : j < runCount,
      (s.runAt ⟨localStart + j, by omega⟩).length = k - 1) :
    BlockAlignedFullLightChain hk p hp where
  start := s.globalStart + localStart
  runCount := runCount
  inBounds := by
    have hsegment := blockAlignedLightSegment_globalStart_bounds hk p hp s
    omega
  full := by
    intro j hj
    have hrun := blockAlignedLightSegment_runAt_eq_globalRun hk p hp s
      ⟨localStart + j, by omega⟩
    have hlength := congrArg List.length hrun
    have hglobal : ((blockAlignedRuns hk p hp).get
        ⟨s.globalStart + (localStart + j), by
          have hsegment :=
            blockAlignedLightSegment_globalStart_bounds hk p hp s
          omega⟩).length = k - 1 :=
      hlength.symm.trans (hfull j hj)
    simpa [BlockAlignedRun.IsFull, BlockAlignedRun.length,
      Nat.add_assoc] using hglobal
  light := by
    intro j hj
    have hlocal := blockAlignedLightSegment_runAt_light hk p hp s
      (localStart + j) (by omega)
    rw [blockAlignedLightSegment_runAt_eq_globalRun,
      blockAlignedLightSegment_runAt_eq_globalRun] at hlocal
    simpa [Nat.add_assoc] using hlocal

@[simp]
theorem BlockAlignedLightSegment.fullIntervalChain_start (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (localStart runCount : ℕ)
    (hin : localStart + runCount ≤ s.length)
    (hfull : ∀ j, ∀ hj : j < runCount,
      (s.runAt ⟨localStart + j, by omega⟩).length = k - 1) :
    (s.fullIntervalChain hk p hp localStart runCount hin hfull).start =
      s.globalStart + localStart := rfl

@[simp]
theorem BlockAlignedLightSegment.fullIntervalChain_runCount (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (localStart runCount : ℕ)
    (hin : localStart + runCount ≤ s.length)
    (hfull : ∀ j, ∀ hj : j < runCount,
      (s.runAt ⟨localStart + j, by omega⟩).length = k - 1) :
    (s.fullIntervalChain hk p hp localStart runCount hin hfull).runCount =
      runCount := rfl

/-- Every consecutive locally indexed full interval in a light segment has
at most `k-2` runs. -/
theorem blockAlignedLightSegment_fullInterval_runCount_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (localStart runCount : ℕ)
    (hin : localStart + runCount ≤ s.length)
    (hfull : ∀ j, ∀ hj : j < runCount,
      (s.runAt ⟨localStart + j, by omega⟩).length = k - 1) :
    runCount ≤ k - 2 := by
  simpa using blockAlignedFullLightChain_runCount_le hk p hp
    (s.fullIntervalChain hk p hp localStart runCount hin hfull)

/-- After exactly `k-2` consecutive full runs, no further run of the same
light segment follows. -/
theorem blockAlignedLightSegment_fullInterval_no_successor (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp)
    (localStart : ℕ)
    (hin : localStart + (k - 2) ≤ s.length)
    (hfull : ∀ j, ∀ hj : j < k - 2,
      (s.runAt ⟨localStart + j, by omega⟩).length = k - 1) :
    ¬localStart + (k - 2) < s.length := by
  intro hnextLocal
  let chain := s.fullIntervalChain hk p hp localStart (k - 2) hin hfull
  have hsegmentBound :=
    blockAlignedLightSegment_globalStart_bounds hk p hp s
  have hnextGlobal : chain.start + chain.runCount <
      (blockAlignedRuns hk p hp).length := by
    dsimp [chain, BlockAlignedLightSegment.fullIntervalChain]
    omega
  let q := localStart + (k - 2) - 1
  have hlocal := blockAlignedLightSegment_runAt_light hk p hp s q (by
    dsimp [q]
    omega)
  rw [blockAlignedLightSegment_runAt_eq_globalRun,
    blockAlignedLightSegment_runAt_eq_globalRun] at hlocal
  have hleftIndex : s.globalStart + q =
      chain.start + (chain.runCount - 1) := by
    dsimp [q, chain, BlockAlignedLightSegment.fullIntervalChain]
    omega
  have hrightIndex : s.globalStart + (q + 1) =
      chain.start + chain.runCount := by
    dsimp [q, chain, BlockAlignedLightSegment.fullIntervalChain]
    omega
  have hlightGlobal : IsLightRunBoundary
      (blockAlignedRunAt hk p hp
        ⟨chain.start + (chain.runCount - 1), by omega⟩).blocks
      (blockAlignedRunAt hk p hp
        ⟨chain.start + chain.runCount, hnextGlobal⟩).blocks := by
    simpa only [blockAlignedRunAt_blocks, hleftIndex, hrightIndex] using hlocal
  exact blockAlignedFullLightChain_no_light_successor hk p hp chain
    (by simp [chain]) hnextGlobal hlightGlobal

/-! ## The sandwich -/

/-- The final entry of the intervening `n-1=k-2` block run in the
sandwich configuration. -/
noncomputable def sandwichMiddleLastEntry (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  runMapPower (by omega) (k - 3) (fullRunMap (by omega) u)

/-- Its exact exit. -/
noncomputable def sandwichMiddleExit (hk : 7 ≤ k)
    (u : PermutationVertex k) : PermutationVertex k :=
  blockExit (sandwichMiddleLastEntry hk u)

/-- Exact sandwich-exit orientation: if `u=a₁ A b c`, the exit is
`c a₁ b A`. -/
theorem sandwichMiddleExit_word (hk : 7 ≤ k)
    (u : PermutationVertex k) (a b c : Alphabet k) (rest : Word k)
    (hrest : rest.length = k - 3)
    (hu : u.1 = a :: rest ++ [b, c]) :
    (sandwichMiddleExit hk u).1 = [c, a, b] ++ rest := by
  have hfullWord : (fullRunMap (by omega) u).1 = rest ++ [a, b, c] := by
    rw [← fullRunChart_target1_eq_fullRunMap hk u]
    exact (fullRunChart_target_words_of_split hk u a b c rest hrest hu).1
  have hmiddle : (sandwichMiddleLastEntry hk u).1 =
      a :: b :: rest ++ [c] := by
    rw [sandwichMiddleLastEntry, runMapPower_word (by omega), hfullWord]
    have hsat : entrySatellite (by omega) (fullRunMap (by omega) u) = c := by
      have hlast : (fullRunMap (by omega) u).1.getLast? = some c := by
        rw [hfullWord]
        simp
      simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast
    rw [hsat]
    have hcore : (rest ++ [a, b, c]).dropLast = rest ++ [a, b] := by
      rw [show rest ++ [a, b, c] =
        (rest ++ [a, b]) ++ [c] by simp [List.append_assoc]]
      rw [List.dropLast_concat]
    rw [hcore, show k - 3 = rest.length by omega,
      rotate_append_left_length rest [a, b]]
    simp [List.append_assoc]
  rw [sandwichMiddleExit, blockExit, inverseRotation_word, hmiddle]
  rw [show k - 1 = (a :: b :: rest).length by simp [hrest]; omega]
  simp

private theorem weightThreeTargetList_mem_of_word
    (source target : PermutationVertex k) (suffix : Word k)
    (hperm : suffix.Perm (source.1.take 3))
    (hword : target.1 = source.1.drop 3 ++ suffix) :
    target ∈ weightThreeTargetList source := by
  unfold weightThreeTargetList
  apply List.mem_map.mpr
  let attached : {s // s ∈ (source.1.take 3).permutations} :=
    ⟨suffix, List.mem_permutations.mpr hperm⟩
  refine ⟨attached, List.mem_attach _ _, ?_⟩
  apply PermutationVertex.ext
  exact hword.symm

/-- The fifth named chart target is a double rotation of the intervening
run's final entry, hence its class is already occupied. -/
theorem fullRunChart_target5_eq_sandwichMiddleLast (hk : 7 ≤ k)
    (u : PermutationVertex k) :
    fullRunChartTarget5 hk u =
      rotationPower 2 (sandwichMiddleLastEntry hk u) := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
  have htarget :=
    (fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.2.2.1
  have hfullWord : (fullRunMap (by omega) u).1 = rest ++ [a, b, c] := by
    rw [← fullRunChart_target1_eq_fullRunMap hk u]
    exact (fullRunChart_target_words_of_split hk u a b c rest hrest hu).1
  have hmiddle : (sandwichMiddleLastEntry hk u).1 =
      a :: b :: rest ++ [c] := by
    rw [sandwichMiddleLastEntry, runMapPower_word (by omega), hfullWord]
    have hsat : entrySatellite (by omega) (fullRunMap (by omega) u) = c := by
      have hlast : (fullRunMap (by omega) u).1.getLast? = some c := by
        rw [hfullWord]
        simp
      simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast
    rw [hsat]
    have hcore : (rest ++ [a, b, c]).dropLast = rest ++ [a, b] := by
      rw [show rest ++ [a, b, c] =
        (rest ++ [a, b]) ++ [c] by simp [List.append_assoc]]
      rw [List.dropLast_concat]
    rw [hcore, show k - 3 = rest.length by omega,
      rotate_append_left_length rest [a, b]]
    simp [List.append_assoc]
  apply PermutationVertex.ext
  rw [htarget, rotationPower_word (by omega), hmiddle]
  simp

/-- The weight-three successors of the intervening run's exit are exactly
the same six named words `T₁,…,T₆` from the full-run chart. -/
theorem sandwichMiddleExit_weightThree_successors (hk : 7 ≤ k)
    (u v : PermutationVertex k) :
    overlapWeight (sandwichMiddleExit hk u) v = 3 ↔
      v ∈ fullRunChartTargets hk u := by
  rw [weightThreeTargetList_iff (by omega)]
  have hcanonical := weightThreeTargetList_exactly_six (by omega)
    (sandwichMiddleExit hk u)
  have hchart := fullRunChartTargets_exactly_six hk u
  have hsubset : fullRunChartTargets hk u ⊆
      weightThreeTargetList (sandwichMiddleExit hk u) := by
    obtain ⟨a, rest, b, c, hrest, hu⟩ := permutationVertex_chart_split hk u
    have hmiddleExit : (sandwichMiddleExit hk u).1 = [c, a, b] ++ rest :=
      sandwichMiddleExit_word hk u a b c rest hrest hu
    have htake : (sandwichMiddleExit hk u).1.take 3 = [c, a, b] := by
      rw [hmiddleExit]
      simp
    have hdrop : (sandwichMiddleExit hk u).1.drop 3 = rest := by
      rw [hmiddleExit]
      simp
    have htargets := fullRunChart_target_words_of_split hk u
      a b c rest hrest hu
    intro target htarget
    rw [fullRunChartTargets_eq_named] at htarget
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htarget
    rcases htarget with rfl | rfl | rfl | rfl | rfl | rfl
    · apply weightThreeTargetList_mem_of_word _ _ [a, b, c]
      · rw [htake]
        simpa using List.rotate_perm [c, a, b] 1
      · rw [htargets.1, hdrop]
    · apply weightThreeTargetList_mem_of_word _ _ [a, c, b]
      · rw [htake]
        exact (List.rotate_perm [c, a, b].reverse 1).trans
          (List.reverse_perm [c, a, b])
      · rw [htargets.2.1, hdrop]
    · apply weightThreeTargetList_mem_of_word _ _ [b, a, c]
      · rw [htake]
        exact List.reverse_perm [c, a, b]
      · rw [htargets.2.2.1, hdrop]
    · apply weightThreeTargetList_mem_of_word _ _ [b, c, a]
      · rw [htake]
        simpa using List.rotate_perm [c, a, b] 2
      · rw [htargets.2.2.2.1, hdrop]
    · apply weightThreeTargetList_mem_of_word _ _ [c, a, b]
      · rw [htake]
      · rw [htargets.2.2.2.2.1, hdrop]
    · apply weightThreeTargetList_mem_of_word _ _ [c, b, a]
      · rw [htake]
        exact (List.rotate_perm [c, a, b].reverse 2).trans
          (List.reverse_perm [c, a, b])
      · rw [htargets.2.2.2.2.2, hdrop]
  have hsubperm := List.subperm_of_subset hchart.2 hsubset
  have hperm : (fullRunChartTargets hk u).Perm
      (weightThreeTargetList (sandwichMiddleExit hk u)) := by
    apply hsubperm.perm_of_length_le
    rw [hchart.1, hcanonical.1]
  exact hperm.mem_iff.symm

/-- **The sandwich.**  A full run, a light boundary, exactly `n-1`
blocks, another light boundary, and a further run force that further run
to have at most `n-2=k-3` blocks, equivalently deficit at least two. -/
theorem blockAlignedSandwich (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 2 < (blockAlignedRuns hk p hp).length)
    (hfull : (blockAlignedRunAt hk p hp ⟨j, by omega⟩).IsFull)
    (hlight₁ : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨j, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨j + 1, by omega⟩).blocks)
    (hmiddleLength :
      (blockAlignedRunAt hk p hp ⟨j + 1, by omega⟩).length = k - 2)
    (hlight₂ : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨j + 1, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨j + 2, hj⟩).blocks) :
    (blockAlignedRunAt hk p hp ⟨j + 2, hj⟩).length ≤ k - 3 ∧
      2 ≤ (blockAlignedRunAt hk p hp ⟨j + 2, hj⟩).deficit := by
  let first := blockAlignedRunAt hk p hp ⟨j, by omega⟩
  let middle := blockAlignedRunAt hk p hp ⟨j + 1, by omega⟩
  let next := blockAlignedRunAt hk p hp ⟨j + 2, hj⟩
  have hfullFirst : first.IsFull := by simpa [first] using hfull
  have hfirstLength : first.length = k - 1 := hfullFirst
  have hmiddleLength' : middle.length = k - 2 := by
    simpa [middle] using hmiddleLength
  have hmiddleEntry : middle.entry = fullRunMap (by omega) first.entry := by
    have hforcing := blockAlignedChartForcing hk p hp j (by omega)
      hfull hlight₁ (by simpa [middle] using
        (show k - 2 ≤ middle.length from by omega))
    simpa [first, middle] using hforcing
  have hmiddleLast : middle.lastEntry =
      sandwichMiddleLastEntry hk first.entry := by
    rw [blockAlignedRun_lastEntry_eq_runMapPower hk p hp middle,
      sandwichMiddleLastEntry]
    have hindex : middle.length - 1 = k - 3 := by omega
    rw [hindex, hmiddleEntry]
  have hfirstNonempty : first.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy first.isRun
  have hmiddleNonempty : middle.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy middle.isRun
  have hnextNonempty : next.blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy next.isRun
  have hweight : overlapWeight (sandwichMiddleExit hk first.entry)
      next.entry = 3 := by
    have hraw : runBoundaryWeight middle.blocks next.blocks = 3 := by
      simpa [IsLightRunBoundary, middle, next] using hlight₂
    rw [runBoundaryWeight_eq middle.blocks next.blocks
      hmiddleNonempty hnextNonempty] at hraw
    have hactual : overlapWeight (blockExit middle.lastEntry) next.entry = 3 := by
      simpa [BlockAlignedRun.lastEntry, BlockAlignedRun.entry] using hraw
    rw [hmiddleLast] at hactual
    simpa [sandwichMiddleExit] using hactual
  have htargets : next.entry ∈ fullRunChartTargets hk first.entry :=
    (sandwichMiddleExit_weightThree_successors hk first.entry next.entry).mp
      hweight
  have hlengthBound : next.length ≤ k - 3 := by
    by_contra hnot
    have hnextLong : k - 2 ≤ next.length := by omega
    rw [fullRunChartTargets_eq_named] at htargets
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htargets
    rcases htargets with hT1 | hT2 | hT3 | hT4 | hT5 | hT6
    · have hclasses : rotationClass middle.entry = rotationClass next.entry := by
        rw [hT1, fullRunChart_target1_eq_fullRunMap, hmiddleEntry]
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        (j + 1) (j + 2) (by omega) hj (by omega)
        (List.head_mem hmiddleNonempty) (List.head_mem hnextNonempty)) hclasses
    · have hindexNext : k - 3 < next.length := by omega
      have hindexFirst : 1 < first.length := by omega
      let y := next.blocks.get ⟨k - 3, hindexNext⟩
      let x := first.blocks.get ⟨1, hindexFirst⟩
      have hy : y = runMapPower (by omega) (k - 3) next.entry :=
        blockAlignedRun_entrySequence hk p hp next (k - 3) hindexNext
      have hx : x = runMap (by omega) first.entry := by
        calc
          x = runMapPower (by omega) 1 first.entry :=
            blockAlignedRun_entrySequence hk p hp first 1 hindexFirst
          _ = runMap (by omega) first.entry := by simp [runMapPower]
      have hyCollision : y =
          rotationPower (k - 2) (runMap (by omega) first.entry) := by
        calc
          y = runMapPower (by omega) (k - 3) next.entry := hy
          _ = runMapPower (by omega) (k - 3)
              (fullRunChartTarget2 hk first.entry) := congrArg _ hT2
          _ = rotationPower (k - 2) (runMap (by omega) first.entry) :=
            fullRunChart_target2_delayed hk first.entry
      have hclasses : rotationClass x = rotationClass y := by
        calc
          rotationClass x = rotationClass (runMap (by omega) first.entry) :=
            congrArg rotationClass hx
          _ = rotationClass
              (rotationPower (k - 2) (runMap (by omega) first.entry)) :=
            (rotationClass_rotationPower (by omega) (k - 2)
              (runMap (by omega) first.entry)).symm
          _ = rotationClass y := congrArg rotationClass hyCollision.symm
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        j (j + 2) (by omega) hj (by omega)
        (List.get_mem _ _) (List.get_mem _ _)) hclasses
    · have hindexFirst : 1 < first.length := by omega
      let x := first.blocks.get ⟨1, hindexFirst⟩
      have hx : x = runMap (by omega) first.entry := by
        calc
          x = runMapPower (by omega) 1 first.entry :=
            blockAlignedRun_entrySequence hk p hp first 1 hindexFirst
          _ = runMap (by omega) first.entry := by simp [runMapPower]
      have hclasses : rotationClass x = rotationClass next.entry := by
        rw [hx, hT3, fullRunChart_target3_eq_runMap]
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        j (j + 2) (by omega) hj (by omega)
        (List.get_mem _ _) (List.head_mem hnextNonempty)) hclasses
    · have hclasses : rotationClass first.entry = rotationClass next.entry := by
        rw [hT4, fullRunChart_target4_eq_rotation]
        simpa [rotationPower, Function.iterate_one] using
          (rotationClass_rotationPower (by omega) 1 first.entry).symm
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        j (j + 2) (by omega) hj (by omega)
        (List.head_mem hfirstNonempty) (List.head_mem hnextNonempty)) hclasses
    · have hclasses : rotationClass middle.lastEntry =
          rotationClass next.entry := by
        calc
          rotationClass middle.lastEntry =
              rotationClass (sandwichMiddleLastEntry hk first.entry) :=
            congrArg rotationClass hmiddleLast
          _ = rotationClass
              (rotationPower 2 (sandwichMiddleLastEntry hk first.entry)) :=
            (rotationClass_rotationPower (by omega) 2 _).symm
          _ = rotationClass (fullRunChartTarget5 hk first.entry) :=
            congrArg rotationClass
              (fullRunChart_target5_eq_sandwichMiddleLast hk first.entry).symm
          _ = rotationClass next.entry := congrArg rotationClass hT5.symm
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        (j + 1) (j + 2) (by omega) hj (by omega)
        (List.getLast_mem hmiddleNonempty) (List.head_mem hnextNonempty)) hclasses
    · have hclasses : rotationClass first.lastEntry =
          rotationClass next.entry := by
        calc
          rotationClass first.lastEntry =
              rotationClass (fullRunChartLastEntry hk first.entry) :=
            congrArg rotationClass
              (fullRunChart_lastEntry hk p hp first hfullFirst)
          _ = rotationClass
              (rotationPower 2 (fullRunChartLastEntry hk first.entry)) :=
            (rotationClass_rotationPower (by omega) 2 _).symm
          _ = rotationClass (fullRunChartTarget6 hk first.entry) :=
            congrArg rotationClass
              (fullRunChart_target6_eq_rotationPower_lastEntry hk first.entry).symm
          _ = rotationClass next.entry := congrArg rotationClass hT6.symm
      exact (runAt_rotationClasses_ne_of_lt hk p hp
        j (j + 2) (by omega) hj (by omega)
        (List.getLast_mem hfirstNonempty) (List.head_mem hnextNonempty)) hclasses
  constructor
  · simpa [next] using hlengthBound
  · change 2 ≤ (k - 1) - next.length
    omega

end SuperpermutationLowerBound
