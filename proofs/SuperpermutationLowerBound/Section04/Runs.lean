module

public import SuperpermutationLowerBound.Section04.TwoLoops
public import Mathlib.Data.List.SplitBy
public import Mathlib.Data.List.Nodup

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 4 from Definition `runs` through Definition `doors`.
The decomposition is literally `List.splitBy` at the weight-two block
boundaries, so singleton runs and one-run components require no exceptional
convention.  The primary run theory is stated for an arbitrary block-aligned
exitless path; forest components are an explicit specialization. -/

open PermutationVertex

variable {k : ℕ}

/-- The Boolean boundary predicate used by the canonical maximal run
partition. -/
noncomputable def isWeightTwoBoundary (u v : PermutationVertex k) : Bool :=
  decide (overlapWeight (blockExit u) v = 2)

/-- Canonical maximal chains of consecutive entries joined by boundaries of
weight exactly two. -/
noncomputable def weightTwoRuns (entries : List (PermutationVertex k)) :
    List (List (PermutationVertex k)) :=
  entries.splitBy isWeightTwoBoundary

/-- The ordered entries of all complete blocks of an arbitrary block-aligned
path. -/
noncomputable def blockAlignedBlockEntries (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    List (PermutationVertex k) :=
  List.ofFn fun j : Fin (pathBlockCount p) =>
    p.vertex ⟨k * j.1, by
      rw [blockAligned_length_eq hp]
      exact Nat.mul_lt_mul_of_pos_left j.2 (by omega)⟩

/-- The canonical maximal weight-two run decomposition of an arbitrary
block-aligned path. -/
noncomputable def blockAlignedRuns (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    List (List (PermutationVertex k)) :=
  weightTwoRuns (blockAlignedBlockEntries hk p hp)

/-- A generic run is one member of the canonical ordered decomposition of a
specified block-aligned path. -/
structure BlockAlignedRun (hk : 7 ≤ k) (p : OverlapPath k)
    (hp : IsBlockAligned p) where
  blocks : List (PermutationVertex k)
  isRun : blocks ∈ blockAlignedRuns hk p hp

namespace BlockAlignedRun

/-- The number `ℓ` of complete blocks in a generic run. -/
def length {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    (r : BlockAlignedRun hk p hp) : ℕ :=
  r.blocks.length

private theorem blocks_nonempty {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) :
    r.blocks ≠ [] := by
  exact List.ne_nil_of_mem_splitBy r.isRun

/-- The entry `Y` of a generic run. -/
noncomputable def entry {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) :
    PermutationVertex k :=
  r.blocks.head (blocks_nonempty r)

/-- The final complete-block entry of a generic run. -/
noncomputable def lastEntry {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) :
    PermutationVertex k :=
  r.blocks.getLast (blocks_nonempty r)

/-- The frozen deficit `n-ℓ`, where `n=k-1`. -/
def deficit {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) : ℕ :=
  (k - 1) - r.length

/-- A generic run is full when it has all `n=k-1` possible blocks. -/
def IsFull {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) : Prop :=
  r.length = k - 1

/-- The rotation classes occupied by a generic run. -/
noncomputable def occupiedClasses {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (r : BlockAlignedRun hk p hp) :
    Finset (Finset (PermutationVertex k)) := by
  classical
  exact r.blocks.toFinset.image rotationClass

end BlockAlignedRun

/-- The ordered run decomposition of a component of `F(P)`. -/
noncomputable def pathForestComponentRuns (hk : 7 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest (by omega) P)) :
    List (List (PermutationVertex k)) :=
  weightTwoRuns (pathForestComponentBlockEntries (by omega) P C)

/-- A run of the whole forest remembers its component and one member of that
component's canonical ordered run decomposition. -/
structure PathForestRun (hk : 7 ≤ k) (P : HamiltonianPath k) where
  component : WeakComponent (pathForest (by omega) P)
  blocks : List (PermutationVertex k)
  isRun : blocks ∈ pathForestComponentRuns hk P component

namespace PathForestRun

/-- The number of complete blocks in a run. -/
def length {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : ℕ := r.blocks.length

private theorem blocks_nonempty {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : r.blocks ≠ [] := by
  exact List.ne_nil_of_mem_splitBy r.isRun

/-- The entry `Y` of a run. -/
noncomputable def entry {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : PermutationVertex k :=
  r.blocks.head (blocks_nonempty r)

/-- The final block entry of a run. -/
noncomputable def lastEntry {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : PermutationVertex k :=
  r.blocks.getLast (blocks_nonempty r)

/-- The deficit `n-ℓ`, with `n=k-1`. -/
def deficit {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : ℕ :=
  (k - 1) - r.length

/-- A full run has all `n=k-1` possible blocks. -/
def IsFull {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : Prop :=
  r.length = k - 1

/-- The rotation classes occupied by a run. -/
noncomputable def occupiedClasses {hk : 7 ≤ k} {P : HamiltonianPath k}
    (r : PathForestRun hk P) : Finset (Finset (PermutationVertex k)) := by
  classical
  exact r.blocks.toFinset.image rotationClass

end PathForestRun

private theorem mem_weightTwoRuns_infix
    {entries run : List (PermutationVertex k)}
    (hrun : run ∈ weightTwoRuns entries) : run <:+: entries := by
  unfold weightTwoRuns at hrun
  rw [← List.flatten_splitBy isWeightTwoBoundary entries]
  exact List.infix_of_mem_flatten hrun

/-- The generic entry list has one element for each complete block. -/
@[simp]
theorem blockAlignedBlockEntries_length (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedBlockEntries hk p hp).length = pathBlockCount p := by
  simp [blockAlignedBlockEntries]

/-- A block-aligned path has at least one complete-block entry. -/
theorem blockAlignedBlockEntries_nonempty (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedBlockEntries hk p hp ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [blockAlignedBlockEntries_length, List.length_nil] at hlength
  exact (Nat.ne_of_gt (blockAligned_blockCount_pos hp)) hlength

/-- The generic entry at block index `j` is the path vertex at index `kj`. -/
theorem blockAlignedBlockEntry_eq_vertex (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j < pathBlockCount p) :
    (blockAlignedBlockEntries hk p hp).get
        ⟨j, by simpa using hj⟩ =
      p.vertex ⟨k * j, by
        rw [blockAligned_length_eq hp]
        exact Nat.mul_lt_mul_of_pos_left hj (by omega)⟩ := by
  simp [blockAlignedBlockEntries]

/-- Complete-block entries of an arbitrary block-aligned path occupy
pairwise distinct rotation classes. -/
theorem blockAlignedBlockEntries_pairwiseDistinct (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    PairwiseDistinctRotationClasses (blockAlignedBlockEntries hk p hp) := by
  rw [PairwiseDistinctRotationClasses, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hiB : i < pathBlockCount p := by simpa using hi
  have hjB : j < pathBlockCount p := by simpa using hj
  have hjPos : k * j < p.length := by
    rw [blockAligned_length_eq hp]
    exact Nat.mul_lt_mul_of_pos_left hjB (by omega)
  simpa [blockAlignedBlockEntries] using
    exitless_block_entries_distinct hp.1 (by omega) hij hjPos

private theorem blockAlignedRun_infix_entries (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.blocks <:+: blockAlignedBlockEntries hk p hp :=
  mem_weightTwoRuns_infix r.isRun

private theorem blockAligned_boundary_index_lt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    k * j + (k - 1) + 1 < p.length := by
  rw [blockAligned_length_eq hp]
  have hmul := Nat.mul_lt_mul_of_pos_left hj (show 0 < k by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

private noncomputable def blockAlignedBoundaryEdge (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    DirectedOverlapEdge k :=
  p.edgeAt (k * j + (k - 1))
    (blockAligned_boundary_index_lt hk p hp j hj)

private theorem blockAlignedBoundaryEdge_source (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    (blockAlignedBoundaryEdge hk p hp j hj).source =
      blockExit ((blockAlignedBlockEntries hk p hp).get
        ⟨j, by simp; omega⟩) := by
  let entries := blockAlignedBlockEntries hk p hp
  have hposPlus : k * j + (k - 1) + 1 < p.length :=
    blockAligned_boundary_index_lt hk p hp j hj
  have hpos : k * j + (k - 1) < p.length := by omega
  have hbase : k * j < p.length := by omega
  have hentry : entries.get ⟨j, by simp [entries]; omega⟩ =
      p.vertex ⟨k * j, hbase⟩ := by
    simpa [entries] using blockAlignedBlockEntry_eq_vertex hk p hp j (by omega)
  have hblock := exitless_block_vertex hp.1 (by omega : 3 ≤ k)
    j (k - 1) (by omega) hpos
  change p.vertex ⟨k * j + (k - 1), hpos⟩ =
    blockExit (entries.get ⟨j, by simp [entries]; omega⟩)
  calc
    p.vertex ⟨k * j + (k - 1), hpos⟩ =
        rotationPower (k - 1) (p.vertex ⟨k * j, hbase⟩) := hblock
    _ = rotationPower (k - 1)
        (entries.get ⟨j, by simp [entries]; omega⟩) :=
      congrArg (rotationPower (k - 1)) hentry.symm
    _ = blockExit (entries.get ⟨j, by simp [entries]; omega⟩) :=
      rotationPower_pred_eq_blockExit (by omega) _

private theorem blockAlignedBoundaryEdge_target (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    (blockAlignedBoundaryEdge hk p hp j hj).target =
      (blockAlignedBlockEntries hk p hp).get
        ⟨j + 1, by simp; exact hj⟩ := by
  let entries := blockAlignedBlockEntries hk p hp
  have htarget : k * j + (k - 1) + 1 < p.length :=
    blockAligned_boundary_index_lt hk p hp j hj
  have hindex : k * j + (k - 1) + 1 = k * (j + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hentry := blockAlignedBlockEntry_eq_vertex hk p hp (j + 1) hj
  change p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ =
    entries.get ⟨j + 1, by simp [entries]; exact hj⟩
  calc
    p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ =
        p.vertex ⟨k * (j + 1), by rw [← hindex]; exact htarget⟩ := by
      apply congrArg p.vertex
      exact Fin.ext hindex
    _ = entries.get ⟨j + 1, by simp [entries]; exact hj⟩ := by
      simpa [entries] using hentry.symm

/-- The boundary between generic entries `j` and `j+1` is exactly the
corresponding indexed Section 1 `blockBoundaryWeights` entry. -/
theorem blockAlignedBoundaryWeight_eq (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    (blockBoundaryWeights p hp).get ⟨j, by simp; omega⟩ =
      overlapWeight
        (blockExit ((blockAlignedBlockEntries hk p hp).get
          ⟨j, by simp; omega⟩))
        ((blockAlignedBlockEntries hk p hp).get
          ⟨j + 1, by simp; exact hj⟩) := by
  have hboundary : k * (j + 1) - 1 = k * j + (k - 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [show (blockBoundaryWeights p hp).get ⟨j, by simp; omega⟩ =
      pathEdgeWeight p (k * (j + 1) - 1) by
    simp [blockBoundaryWeights]]
  rw [pathEdgeWeight_of_lt p _ (by
    rw [hboundary]
    exact blockAligned_boundary_index_lt hk p hp j hj)]
  calc
    overlapWeight
        (p.vertex ⟨k * (j + 1) - 1, by
          rw [hboundary]
          exact Nat.lt_of_succ_lt
            (blockAligned_boundary_index_lt hk p hp j hj)⟩)
        (p.vertex ⟨k * (j + 1) - 1 + 1, by
          rw [hboundary]
          exact blockAligned_boundary_index_lt hk p hp j hj⟩) =
        overlapWeight (blockAlignedBoundaryEdge hk p hp j hj).source
          (blockAlignedBoundaryEdge hk p hp j hj).target := by
      change overlapWeight _ _ =
        overlapWeight
          (p.vertex ⟨k * j + (k - 1),
            Nat.lt_of_succ_lt
              (blockAligned_boundary_index_lt hk p hp j hj)⟩)
          (p.vertex ⟨k * j + (k - 1) + 1,
            blockAligned_boundary_index_lt hk p hp j hj⟩)
      congr 2
      · exact Fin.ext hboundary
      · exact Fin.ext (congrArg (fun x => x + 1) hboundary)
    _ = _ := by
      rw [blockAlignedBoundaryEdge_source, blockAlignedBoundaryEdge_target]

/-- The Boolean run-splitting predicate agrees exactly with the corresponding
indexed Section 1 boundary weight. -/
theorem blockAlignedIsWeightTwoBoundary_iff (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p) :
    isWeightTwoBoundary
        ((blockAlignedBlockEntries hk p hp).get
          ⟨j, by simp; omega⟩)
        ((blockAlignedBlockEntries hk p hp).get
          ⟨j + 1, by simp; exact hj⟩) = true ↔
      (blockBoundaryWeights p hp).get ⟨j, by simp; omega⟩ = 2 := by
  simp only [isWeightTwoBoundary, decide_eq_true_eq]
  rw [blockAlignedBoundaryWeight_eq hk p hp j hj]

private theorem blockAligned_weightTwo_boundary_eq_runMap (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < pathBlockCount p)
    (hweight : overlapWeight
      (blockExit ((blockAlignedBlockEntries hk p hp).get
        ⟨j, by simp; omega⟩))
      ((blockAlignedBlockEntries hk p hp).get
        ⟨j + 1, by simp; exact hj⟩) = 2) :
    (blockAlignedBlockEntries hk p hp).get
        ⟨j + 1, by simp; exact hj⟩ =
      runMap (by omega)
        ((blockAlignedBlockEntries hk p hp).get
          ⟨j, by simp; omega⟩) := by
  let entries := blockAlignedBlockEntries hk p hp
  let u := entries.get ⟨j, by simp [entries]; omega⟩
  let v := entries.get ⟨j + 1, by simp [entries]; exact hj⟩
  let e := blockAlignedBoundaryEdge hk p hp j hj
  have heSource : e.source = blockExit u := by
    simpa [e, u, entries] using blockAlignedBoundaryEdge_source hk p hp j hj
  have heTarget : e.target = v := by
    simpa [e, v, entries] using blockAlignedBoundaryEdge_target hk p hp j hj
  have huv : blockExit u ≠ v := by
    intro huv
    apply e.ne
    rw [heSource, heTarget, huv]
  have hsuccessors :=
    (blockExit_weight_two_successors (by omega) u v huv).mp (by
      simpa [u, v, entries] using hweight)
  rcases hsuccessors with hrotation | hrunMap
  · exfalso
    have hpair := blockAlignedBlockEntries_pairwiseDistinct hk p hp
    rw [PairwiseDistinctRotationClasses, List.pairwise_iff_getElem] at hpair
    have hclasses := hpair j (j + 1)
      (by simp; omega) (by simp; exact hj) (by omega)
    apply hclasses
    change rotationClass u = rotationClass v
    rw [hrotation]
    exact (rotationClass_eq_of_mem (by omega)
      (rotation_mem_entryClass (by omega) u)).symm
  · simpa [u, v, entries] using hrunMap

private theorem blockAligned_entries_weightTwo_imp_runMap (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedBlockEntries hk p hp).IsChain
      (fun u v => overlapWeight (blockExit u) v = 2 →
        v = runMap (by omega) u) := by
  rw [List.isChain_iff_getElem]
  intro j hj hweight
  exact blockAligned_weightTwo_boundary_eq_runMap hk p hp j
    (by simpa using hj) hweight

/-- The generic decomposition is ordered, exhaustive, nonempty in every
part, weight-two inside each part, and maximal across adjacent parts.  This
includes singleton runs and one-run paths. -/
theorem blockAlignedRuns_spec (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedRuns hk p hp).flatten =
        blockAlignedBlockEntries hk p hp ∧
      [] ∉ blockAlignedRuns hk p hp ∧
      (∀ run ∈ blockAlignedRuns hk p hp,
        run.IsChain (fun u v => overlapWeight (blockExit u) v = 2)) ∧
      (blockAlignedRuns hk p hp).IsChain (fun a b =>
        ∃ ha : a ≠ [], ∃ hb : b ≠ [],
          overlapWeight (blockExit (a.getLast ha)) (b.head hb) ≠ 2) := by
  let entries := blockAlignedBlockEntries hk p hp
  let runs := blockAlignedRuns hk p hp
  have hflatten : runs.flatten = entries := by
    change (entries.splitBy isWeightTwoBoundary).flatten = entries
    exact List.flatten_splitBy isWeightTwoBoundary entries
  have hnonempty : [] ∉ runs :=
    List.nil_notMem_splitBy isWeightTwoBoundary entries
  have hinsides : ∀ run ∈ runs,
      run.IsChain (fun u v => overlapWeight (blockExit u) v = 2) := by
    intro run hrun
    exact (List.isChain_of_mem_splitBy hrun).imp (by
      intro u v huv
      simpa [isWeightTwoBoundary] using huv)
  have hbetween : runs.IsChain (fun a b =>
      ∃ ha : a ≠ [], ∃ hb : b ≠ [],
        overlapWeight (blockExit (a.getLast ha)) (b.head hb) ≠ 2) := by
    exact (List.isChain_getLast_head_splitBy
      isWeightTwoBoundary entries).imp (by
        rintro a b ⟨ha, hb, hab⟩
        exact ⟨ha, hb, by simpa [isWeightTwoBoundary] using hab⟩)
  simpa [runs, entries] using ⟨hflatten, hnonempty, hinsides, hbetween⟩

/-- Every block-aligned path has at least one generic run. -/
theorem blockAlignedRuns_nonempty (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedRuns hk p hp ≠ [] := by
  unfold blockAlignedRuns weightTwoRuns
  exact List.splitBy_ne_nil.mpr (blockAlignedBlockEntries_nonempty hk p hp)

/-- A generic path has one run exactly when every consecutive complete-block
boundary has weight two. -/
theorem blockAlignedRuns_eq_singleton_iff (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedRuns hk p hp = [blockAlignedBlockEntries hk p hp] ↔
      (blockAlignedBlockEntries hk p hp).IsChain
        (fun u v => overlapWeight (blockExit u) v = 2) := by
  let entries := blockAlignedBlockEntries hk p hp
  constructor
  · intro hruns
    have hspec := (blockAlignedRuns_spec hk p hp).2.2.1
    exact hspec entries (by simp [entries, hruns])
  · intro hchain
    have hbool : entries.IsChain
        (fun u v => isWeightTwoBoundary u v = true) :=
      hchain.imp (by
        intro u v huv
        simpa [isWeightTwoBoundary] using huv)
    simpa [blockAlignedRuns, weightTwoRuns, entries] using
      List.splitBy_of_isChain (blockAlignedBlockEntries_nonempty hk p hp) hbool

/-- A one-block generic path is represented by the single singleton run. -/
theorem blockAlignedRuns_singleton (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (u : PermutationVertex k)
    (hentries : blockAlignedBlockEntries hk p hp = [u]) :
    blockAlignedRuns hk p hp = [[u]] := by
  have hruns := (blockAlignedRuns_eq_singleton_iff hk p hp).mpr (by
    rw [hentries]
    exact List.isChain_singleton u)
  simpa [hentries] using hruns

/-- Every generic run has at least one complete block. -/
theorem blockAlignedRun_length_pos (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    0 < r.length := by
  exact List.length_pos_of_ne_nil (BlockAlignedRun.blocks_nonempty r)

/-- Consecutive entries of every generic run are related by exactly one
application of `τ₂`. -/
theorem blockAlignedRun_isChain_runMap (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.blocks.IsChain (fun u v => v = runMap (by omega) u) := by
  have himp := (blockAligned_entries_weightTwo_imp_runMap hk p hp).infix
    (blockAlignedRun_infix_entries hk p hp r)
  have hweight := (List.isChain_of_mem_splitBy r.isRun).imp (by
    intro u v huv
    simpa [isWeightTwoBoundary] using huv)
  rw [List.isChain_iff_getElem] at himp hweight ⊢
  intro i hi
  exact himp i hi (hweight i hi)

private theorem run_get_eq_runMapPower_of_chain (hk : 7 ≤ k)
    {l : List (PermutationVertex k)} (hne : l ≠ [])
    (hchain : l.IsChain (fun u v => v = runMap (by omega) u))
    (i : ℕ) (hi : i < l.length) :
    l.get ⟨i, hi⟩ = runMapPower (by omega) i (l.head hne) := by
  induction i with
  | zero =>
      cases l with
      | nil => exact (hne rfl).elim
      | cons a tail => rfl
  | succ i ih =>
      have hi0 : i < l.length := by omega
      have hstep := (List.isChain_iff_getElem.mp hchain) i hi
      calc
        l.get ⟨i + 1, hi⟩ = runMap (by omega) (l.get ⟨i, hi0⟩) := hstep
        _ = runMap (by omega) (runMapPower (by omega) i (l.head hne)) :=
          congrArg (runMap (by omega)) (ih hi0)
        _ = runMapPower (by omega) (i + 1) (l.head hne) := by
          simpa [runMapPower, Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply' (runMap (by omega)) i
              (l.head hne)).symm

/-- Exact generic entry sequence: block `i` of a run entered at `Y` is
entered at `τ₂^i(Y)`. -/
theorem blockAlignedRun_entrySequence (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) (i : ℕ) (hi : i < r.length) :
    r.blocks.get ⟨i, hi⟩ = runMapPower (by omega) i r.entry := by
  exact run_get_eq_runMapPower_of_chain hk
    (BlockAlignedRun.blocks_nonempty r)
    (blockAlignedRun_isChain_runMap hk p hp r) i hi

private theorem blockAligned_entries_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedBlockEntries hk p hp).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (blockAlignedBlockEntries_pairwiseDistinct hk p hp).imp (by
    intro u v hclasses huv
    exact hclasses (congrArg rotationClass huv))

private theorem blockAlignedRun_blocks_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.blocks.Nodup :=
  (blockAlignedRun_infix_entries hk p hp r).nodup
    (blockAligned_entries_nodup hk p hp)

/-- Every generic run satisfies the exact frozen bounds `1 ≤ ℓ ≤ n`. -/
theorem blockAlignedRun_length_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.length ≤ k - 1 := by
  by_contra hnot
  have hn : k - 1 < r.length := Nat.lt_of_not_ge hnot
  have hzero : 0 < r.length := blockAlignedRun_length_pos hk p hp r
  have hentryZero := blockAlignedRun_entrySequence hk p hp r 0 hzero
  have hentryN := blockAlignedRun_entrySequence hk p hp r (k - 1) hn
  have heq : r.blocks.get ⟨k - 1, hn⟩ = r.blocks.get ⟨0, hzero⟩ := by
    calc
      r.blocks.get ⟨k - 1, hn⟩ = r.entry :=
        hentryN.trans (runMap_order_exact (by omega) r.entry).1
      _ = r.blocks.get ⟨0, hzero⟩ := by
        simpa [runMapPower] using hentryZero.symm
  have hfin := (blockAlignedRun_blocks_nodup hk p hp r).get_inj_iff.mp heq
  have hval := congrArg Fin.val hfin
  simp at hval
  omega

/-- The final entry of a generic run is `τ₂^(ℓ-1)(Y)`. -/
theorem blockAlignedRun_lastEntry_eq_runMapPower (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.lastEntry = runMapPower (by omega) (r.length - 1) r.entry := by
  have hpos := blockAlignedRun_length_pos hk p hp r
  have hlast : r.length - 1 < r.length := Nat.sub_lt hpos (by omega)
  rw [BlockAlignedRun.lastEntry, List.getLast_eq_getElem]
  exact blockAlignedRun_entrySequence hk p hp r (r.length - 1) hlast

/-- A generic run is full exactly when its deficit is zero. -/
theorem blockAlignedRun_isFull_iff_deficit_zero (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.IsFull ↔ r.deficit = 0 := by
  have hle := blockAlignedRun_length_le hk p hp r
  simp only [BlockAlignedRun.IsFull, BlockAlignedRun.deficit]
  omega

/-- The frozen generic run count `q`. -/
noncomputable def blockAlignedRunCount (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  (blockAlignedRuns hk p hp).length

/-- The ordered generic deficit string `(d₁,…,d_q)`. -/
noncomputable def blockAlignedDeficitString (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : List ℕ :=
  (blockAlignedRuns hk p hp).map (fun run => (k - 1) - run.length)

/-- The total generic deficit `D`. -/
noncomputable def blockAlignedTotalDeficit (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  (blockAlignedDeficitString hk p hp).sum

/-- The first generic deficit. -/
noncomputable def blockAlignedFirstDeficit (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  (blockAlignedDeficitString hk p hp).head (by
    simpa [blockAlignedDeficitString] using blockAlignedRuns_nonempty hk p hp)

/-- The last generic deficit. -/
noncomputable def blockAlignedLastDeficit (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  (blockAlignedDeficitString hk p hp).getLast (by
    simpa [blockAlignedDeficitString] using blockAlignedRuns_nonempty hk p hp)

/-- The generic deficit string has exactly `q` terms. -/
@[simp]
theorem blockAlignedDeficitString_length (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedDeficitString hk p hp).length =
      blockAlignedRunCount hk p hp := by
  simp [blockAlignedDeficitString, blockAlignedRunCount]

private theorem generic_sum_deficits_add_lengths
    (n : ℕ) (runs : List (List (PermutationVertex k)))
    (hle : ∀ run ∈ runs, run.length ≤ n) :
    (runs.map (fun run => n - run.length)).sum +
        (runs.map List.length).sum = n * runs.length := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hrun : run.length ≤ n := hle run (by simp)
      have htail : ∀ tail ∈ runs, tail.length ≤ n := by
        intro tail htail
        exact hle tail (by simp [htail])
      have hih := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega

private theorem generic_run_length_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (run : List (PermutationVertex k))
    (hrun : run ∈ blockAlignedRuns hk p hp) :
    run.length ≤ k - 1 := by
  let r : BlockAlignedRun hk p hp := ⟨run, hrun⟩
  exact blockAlignedRun_length_le hk p hp r

private theorem blockAligned_run_lengths_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    ((blockAlignedRuns hk p hp).map List.length).sum =
      pathBlockCount p := by
  have hlength := congrArg List.length (blockAlignedRuns_spec hk p hp).1
  simpa using hlength

/-- Natural subtraction is justified generically: `D ≤ nq`. -/
theorem blockAlignedTotalDeficit_le_capacity (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedTotalDeficit hk p hp ≤
      (k - 1) * blockAlignedRunCount hk p hp := by
  let runs := blockAlignedRuns hk p hp
  have hbalance := generic_sum_deficits_add_lengths (k - 1) runs (by
    intro run hrun
    exact generic_run_length_le hk p hp run hrun)
  change (runs.map (fun run => (k - 1) - run.length)).sum ≤
    (k - 1) * runs.length
  omega

/-- The exact generic frozen identity `b=nq-D`; the preceding theorem
separately rules out truncated natural subtraction. -/
theorem pathBlockCount_eq_runCount_sub_totalDeficit (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    pathBlockCount p =
      (k - 1) * blockAlignedRunCount hk p hp -
        blockAlignedTotalDeficit hk p hp := by
  let runs := blockAlignedRuns hk p hp
  have hbalance := generic_sum_deficits_add_lengths (k - 1) runs (by
    intro run hrun
    exact generic_run_length_le hk p hp run hrun)
  have hlengths : (runs.map List.length).sum = pathBlockCount p := by
    simpa [runs] using blockAligned_run_lengths_sum hk p hp
  have hcapacity := blockAlignedTotalDeficit_le_capacity hk p hp
  unfold blockAlignedRunCount blockAlignedTotalDeficit
    blockAlignedDeficitString
  change pathBlockCount p =
    (k - 1) * runs.length -
      (runs.map (fun run => (k - 1) - run.length)).sum
  rw [hlengths] at hbalance
  omega

/-- First sentence of Lemma `arc`, exact set form: a generic run entered at
`Y` occupies precisely orbit slots `0,…,ℓ-1`. -/
theorem blockAlignedRun_occupiedClasses_eq_slots (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.occupiedClasses =
      (Finset.range r.length).image
        (fun i => rotationClass (runMapPower (by omega) i r.entry)) := by
  classical
  ext B
  constructor
  · intro hB
    change B ∈ r.blocks.toFinset.image rotationClass at hB
    obtain ⟨u, huSet, huB⟩ := Finset.mem_image.mp hB
    have hu : u ∈ r.blocks := List.mem_toFinset.mp huSet
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    apply Finset.mem_image.mpr
    refine ⟨i.1, Finset.mem_range.mpr i.2, ?_⟩
    have hsequence := blockAlignedRun_entrySequence hk p hp r i.1 i.2
    calc
      rotationClass (runMapPower (by omega) i.1 r.entry) =
          rotationClass (r.blocks.get i) := congrArg rotationClass hsequence.symm
      _ = rotationClass u := congrArg rotationClass hi
      _ = B := huB
  · intro hB
    obtain ⟨i, hiRange, hiB⟩ := Finset.mem_image.mp hB
    have hi : i < r.length := Finset.mem_range.mp hiRange
    change B ∈ r.blocks.toFinset.image rotationClass
    apply Finset.mem_image.mpr
    refine ⟨r.blocks.get ⟨i, hi⟩,
      List.mem_toFinset.mpr (List.get_mem _ _), ?_⟩
    calc
      rotationClass (r.blocks.get ⟨i, hi⟩) =
          rotationClass (runMapPower (by omega) i r.entry) :=
        congrArg rotationClass (blockAlignedRun_entrySequence hk p hp r i hi)
      _ = B := hiB

/-- Those exact occupied slots lie in the two-loop determined by the run
entry's satellite and cyclic core. -/
theorem blockAlignedRun_occupiedClasses_subset_twoLoop (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) :
    r.occupiedClasses ⊆
      twoLoop (by omega) (entrySatellite (by omega) r.entry)
        (entryCore r.entry) := by
  intro B hB
  rw [blockAlignedRun_occupiedClasses_eq_slots hk p hp r] at hB
  obtain ⟨i, hiRange, hiB⟩ := Finset.mem_image.mp hB
  have hiLength : i < r.length := Finset.mem_range.mp hiRange
  have hi : i < k - 1 :=
    hiLength.trans_le (blockAlignedRun_length_le hk p hp r)
  rw [twoLoop_eq_runMapOrbitClasses (by omega)]
  apply (mem_runMapOrbitClasses (by omega) r.entry B).mpr
  exact ⟨i, hi, hiB⟩

/-- Exact predecessor orientation for the generic arc statement: its `i`th
block occupies the slot after `x_i`, with `x₀=x_n`. -/
theorem blockAlignedRun_slot (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (r : BlockAlignedRun hk p hp) (i : ℕ) (hi : i < r.length) :
    rotationClassSlot (r.blocks.get ⟨i, hi⟩)
        (entrySatellite (by omega) r.entry) =
      coreSlotLetter (by omega) r.entry
        ⟨i, hi.trans_le (blockAlignedRun_length_le hk p hp r)⟩ := by
  rw [blockAlignedRun_entrySequence hk p hp r i hi]
  exact runMapPower_slot (by omega) r.entry
    ⟨i, hi.trans_le (blockAlignedRun_length_le hk p hp r)⟩

/-- Component complete-block entries are literally the generic entries of
the component's block-aligned path. -/
theorem pathForestComponentBlockEntries_eq_blockAlignedBlockEntries
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentBlockEntries (by omega) P C =
      blockAlignedBlockEntries hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  rfl

/-- Consequently the component run decomposition is exactly the generic
canonical decomposition, so the two interfaces cannot diverge. -/
theorem pathForestComponentRuns_eq_blockAlignedRuns
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentRuns hk P C =
      blockAlignedRuns hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  unfold pathForestComponentRuns blockAlignedRuns
  rw [pathForestComponentBlockEntries_eq_blockAlignedBlockEntries hk P C]

/-- The component run-splitting predicate is the corresponding indexed
Section 1 `blockBoundaryWeights` test. -/
theorem pathForestComponentIsWeightTwoBoundary_iff (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      pathBlockCount (pathForestComponentPath (by omega) P C)) :
    isWeightTwoBoundary
        ((pathForestComponentBlockEntries (by omega) P C).get
          ⟨j, by simp; omega⟩)
        ((pathForestComponentBlockEntries (by omega) P C).get
          ⟨j + 1, by simp; exact hj⟩) = true ↔
      (blockBoundaryWeights
          (pathForestComponentPath (by omega) P C)
          (pathForestComponentPath_blockAligned (by omega) P C)).get
        ⟨j, by simp; omega⟩ = 2 := by
  change isWeightTwoBoundary
      ((blockAlignedBlockEntries hk
          (pathForestComponentPath (by omega) P C)
          (pathForestComponentPath_blockAligned (by omega) P C)).get
        ⟨j, by simp; omega⟩)
      ((blockAlignedBlockEntries hk
          (pathForestComponentPath (by omega) P C)
          (pathForestComponentPath_blockAligned (by omega) P C)).get
        ⟨j + 1, by simp; exact hj⟩) = true ↔ _
  exact blockAlignedIsWeightTwoBoundary_iff hk
    (pathForestComponentPath (by omega) P C)
    (pathForestComponentPath_blockAligned (by omega) P C) j hj

namespace PathForestRun

/-- Regard a forest run as the corresponding generic run of its component
path.  The block list is unchanged. -/
noncomputable def toBlockAlignedRun {hk : 7 ≤ k}
    {P : HamiltonianPath k} (r : PathForestRun hk P) :
    BlockAlignedRun hk
      (pathForestComponentPath (by omega) P r.component)
      (pathForestComponentPath_blockAligned (by omega) P r.component) :=
  ⟨r.blocks, by
    rw [← pathForestComponentRuns_eq_blockAlignedRuns hk P r.component]
    exact r.isRun⟩

end PathForestRun

private theorem pathForestRun_infix_entries (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    r.blocks <:+:
      pathForestComponentBlockEntries (by omega) P r.component :=
  mem_weightTwoRuns_infix r.isRun

private theorem component_length_eq_entries_length (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentPath (by omega) P C).length =
      k * (pathForestComponentBlockEntries (by omega) P C).length := by
  rw [blockAligned_length_eq
    (pathForestComponentPath_blockAligned (by omega) P C)]
  congr 1
  exact (pathForestComponentBlockEntries_length (by omega) P C).symm

private theorem component_boundary_index_lt (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    k * j + (k - 1) + 1 <
      (pathForestComponentPath (by omega) P C).length := by
  rw [component_length_eq_entries_length hk P C]
  have hmul := Nat.mul_lt_mul_of_pos_left hj (show 0 < k by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

private noncomputable def componentBoundaryEdge (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    DirectedOverlapEdge k :=
  (pathForestComponentPath (by omega) P C).edgeAt
    (k * j + (k - 1)) (component_boundary_index_lt hk P C j hj)

private theorem component_entry_eq_vertex (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (pathForestComponentBlockEntries (by omega) P C).get ⟨j, hj⟩ =
      (pathForestComponentPath (by omega) P C).vertex
        ⟨k * j, by
          rw [component_length_eq_entries_length hk P C]
          exact Nat.mul_lt_mul_of_pos_left hj (by omega)⟩ := by
  simp [pathForestComponentBlockEntries]

private theorem componentBoundaryEdge_source (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (componentBoundaryEdge hk P C j hj).source =
      blockExit ((pathForestComponentBlockEntries (by omega) P C).get
        ⟨j, by omega⟩) := by
  let p := pathForestComponentPath (by omega) P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hposPlus : k * j + (k - 1) + 1 < p.length := by
    simpa [p] using component_boundary_index_lt hk P C j hj
  have hpos : k * j + (k - 1) < p.length := by
    omega
  have hbase : k * j < p.length := by omega
  have hj0 : j < entries.length := by
    change j < (pathForestComponentBlockEntries (by omega) P C).length
    omega
  have hblock := exitless_block_vertex
    (pathForestComponentPath_blockAligned (by omega) P C).1
    (by omega : 3 ≤ k) j (k - 1) (by omega) hpos
  have hentry : entries.get ⟨j, hj0⟩ =
      p.vertex ⟨k * j, hbase⟩ := by
    simpa [p, entries] using component_entry_eq_vertex hk P C j (by omega)
  change p.vertex ⟨k * j + (k - 1), hpos⟩ = blockExit (entries.get ⟨j, hj0⟩)
  calc
    p.vertex ⟨k * j + (k - 1), hpos⟩ =
        rotationPower (k - 1)
          (p.vertex ⟨k * j, hbase⟩) := hblock
    _ = rotationPower (k - 1) (entries.get ⟨j, hj0⟩) :=
      congrArg (rotationPower (k - 1)) hentry.symm
    _ = blockExit (entries.get ⟨j, hj0⟩) :=
      rotationPower_pred_eq_blockExit (by omega) _

private theorem componentBoundaryEdge_target (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (componentBoundaryEdge hk P C j hj).target =
      (pathForestComponentBlockEntries (by omega) P C).get
        ⟨j + 1, hj⟩ := by
  let p := pathForestComponentPath (by omega) P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  have htarget : k * j + (k - 1) + 1 < p.length :=
    component_boundary_index_lt hk P C j hj
  have hindex : k * j + (k - 1) + 1 = k * (j + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hentry := component_entry_eq_vertex hk P C (j + 1) hj
  change p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ = entries.get ⟨j + 1, hj⟩
  calc
    p.vertex ⟨k * j + (k - 1) + 1, htarget⟩ =
        p.vertex ⟨k * (j + 1), by rw [← hindex]; exact htarget⟩ := by
      apply congrArg p.vertex
      exact Fin.ext hindex
    _ = entries.get ⟨j + 1, hj⟩ := hentry.symm

private theorem componentBoundaryEdge_mem_forest (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    componentBoundaryEdge hk P C j hj ∈ pathForest (by omega) P := by
  have hePath : componentBoundaryEdge hk P C j hj ∈
      (pathForestComponentPath (by omega) P C).edgeSet := by
    apply OverlapPath.mem_edgeSet_iff.mpr
    exact ⟨k * j + (k - 1),
      component_boundary_index_lt hk P C j hj, rfl⟩
  have heWeak : componentBoundaryEdge hk P C j hj ∈ weakComponentEdges C := by
    rw [← pathForestComponentPath_edgeSet (by omega) P C]
    exact hePath
  exact (mem_weakComponentEdges.mp heWeak).1

private theorem component_entry_zero_eq_tail (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).get
        ⟨0, by
          exact (pathForestComponentBlockEntries_nonempty (by omega) P C |>
            List.length_pos_of_ne_nil)⟩ =
      pathForestComponentTail (by omega) P C := by
  have hentry := component_entry_eq_vertex hk P C 0
    (pathForestComponentBlockEntries_nonempty (by omega) P C |>
      List.length_pos_of_ne_nil)
  simpa [pathForestComponentTail] using hentry

private theorem component_entry_mem_firstVisited (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    (pathForestComponentBlockEntries (by omega) P C).get ⟨j, hj⟩ ∈
      firstVisitedVertices (by omega) P := by
  induction j with
  | zero =>
      rw [component_entry_zero_eq_tail hk P C]
      exact pathForestComponentTail_mem_firstVisited (by omega) P C
  | succ j ih =>
      have hj0 : j <
          (pathForestComponentBlockEntries (by omega) P C).length := by omega
      let e := componentBoundaryEdge hk P C j hj
      have heForest : e ∈ pathForest (by omega) P := by
        simpa [e] using componentBoundaryEdge_mem_forest hk P C j hj
      have heSource : e.source =
          blockExit ((pathForestComponentBlockEntries (by omega) P C).get
            ⟨j, hj0⟩) := by
        simpa [e] using componentBoundaryEdge_source hk P C j hj
      have heTarget : e.target =
          (pathForestComponentBlockEntries (by omega) P C).get
            ⟨j + 1, hj⟩ := by
        simpa [e] using componentBoundaryEdge_target hk P C j hj
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

private theorem componentBoundaryEdge_mem_path (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length) :
    componentBoundaryEdge hk P C j hj ∈ P.edgeSet := by
  let e := componentBoundaryEdge hk P C j hj
  have heForest : e ∈ pathForest (by omega) P := by
    simpa [e] using componentBoundaryEdge_mem_forest hk P C j hj
  have hj0 : j <
      (pathForestComponentBlockEntries (by omega) P C).length := by omega
  have heSource : e.source =
      blockExit ((pathForestComponentBlockEntries (by omega) P C).get
        ⟨j, hj0⟩) := by
    simpa [e] using componentBoundaryEdge_source hk P C j hj
  have hfirst := component_entry_mem_firstVisited hk P C j hj0
  have hsourcePred : e.source ∈ firstVisitedPredecessors (by omega) P := by
    rw [heSource]
    apply (mem_firstVisitedPredecessors_iff (by omega) P _).mpr
    rw [rotation_blockExit (by omega)]
    exact hfirst
  exact (pathForest_edge_from_predecessor (by omega) P heForest hsourcePred).1

private theorem component_weightTwo_boundary_eq_runMap (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (j : ℕ)
    (hj : j + 1 <
      (pathForestComponentBlockEntries (by omega) P C).length)
    (hweight : overlapWeight
      (blockExit ((pathForestComponentBlockEntries (by omega) P C).get
        ⟨j, by omega⟩))
      ((pathForestComponentBlockEntries (by omega) P C).get
        ⟨j + 1, hj⟩) = 2) :
    (pathForestComponentBlockEntries (by omega) P C).get
        ⟨j + 1, hj⟩ =
      runMap (by omega)
        ((pathForestComponentBlockEntries (by omega) P C).get
          ⟨j, by omega⟩) := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hj0 : j < entries.length := by
    change j < (pathForestComponentBlockEntries (by omega) P C).length
    omega
  let u := entries.get ⟨j, hj0⟩
  let v := entries.get ⟨j + 1, hj⟩
  let e := componentBoundaryEdge hk P C j hj
  have heSource : e.source = blockExit u := by
    simpa [e, u, entries] using componentBoundaryEdge_source hk P C j hj
  have heTarget : e.target = v := by
    simpa [e, v, entries] using componentBoundaryEdge_target hk P C j hj
  have huv : blockExit u ≠ v := by
    intro huv
    apply e.ne
    rw [heSource, heTarget, huv]
  have hsuccessors :=
    (blockExit_weight_two_successors (by omega) u v huv).mp (by
      simpa [u, v, entries] using hweight)
  rcases hsuccessors with hrotation | hrunMap
  · exfalso
    have hpair :=
      pathForestComponentBlockEntries_pairwiseDistinct (by omega) P C
    rw [PairwiseDistinctRotationClasses, List.pairwise_iff_getElem] at hpair
    have hclasses := hpair j (j + 1) (by omega) hj (by omega)
    apply hclasses
    change rotationClass u = rotationClass v
    rw [hrotation]
    exact (rotationClass_eq_of_mem (by omega)
      (rotation_mem_entryClass (by omega) u)).symm
  · simpa [u, v, entries] using hrunMap

private theorem component_entries_weightTwo_imp_runMap (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).IsChain
      (fun u v => overlapWeight (blockExit u) v = 2 →
        v = runMap (by omega) u) := by
  rw [List.isChain_iff_getElem]
  intro j hj
  exact component_weightTwo_boundary_eq_runMap hk P C j hj

/-- The decomposition is ordered, exhaustive, nonempty in every part,
weight-two inside each part, and separated by non-weight-two boundaries.
This is the maximal-partition specification, including singleton parts. -/
theorem pathForestComponentRuns_spec (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentRuns hk P C).flatten =
        pathForestComponentBlockEntries (by omega) P C ∧
      [] ∉ pathForestComponentRuns hk P C ∧
      (∀ run ∈ pathForestComponentRuns hk P C,
        run.IsChain (fun u v => overlapWeight (blockExit u) v = 2)) ∧
      (pathForestComponentRuns hk P C).IsChain (fun a b =>
        ∃ ha : a ≠ [], ∃ hb : b ≠ [],
          overlapWeight (blockExit (a.getLast ha)) (b.head hb) ≠ 2) := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  let runs := pathForestComponentRuns hk P C
  have hflatten : runs.flatten = entries := by
    change (entries.splitBy isWeightTwoBoundary).flatten = entries
    exact List.flatten_splitBy isWeightTwoBoundary entries
  have hnonempty : [] ∉ runs := by
    exact List.nil_notMem_splitBy isWeightTwoBoundary entries
  have hinsides : ∀ run ∈ runs,
      run.IsChain (fun u v => overlapWeight (blockExit u) v = 2) := by
    intro run hrun
    have hchain := List.isChain_of_mem_splitBy hrun
    exact hchain.imp (by
      intro u v huv
      simpa [isWeightTwoBoundary] using huv)
  have hbetween : runs.IsChain (fun a b =>
      ∃ ha : a ≠ [], ∃ hb : b ≠ [],
        overlapWeight (blockExit (a.getLast ha)) (b.head hb) ≠ 2) := by
    have hchain := List.isChain_getLast_head_splitBy
      isWeightTwoBoundary entries
    exact hchain.imp (by
      rintro a b ⟨ha, hb, hab⟩
      exact ⟨ha, hb, by simpa [isWeightTwoBoundary] using hab⟩)
  simpa [runs, entries] using ⟨hflatten, hnonempty, hinsides, hbetween⟩

/-- A nonempty component has at least one run. -/
theorem pathForestComponentRuns_nonempty (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentRuns hk P C ≠ [] := by
  unfold pathForestComponentRuns weightTwoRuns
  exact List.splitBy_ne_nil.mpr
    (pathForestComponentBlockEntries_nonempty (by omega) P C)

/-- A component has one run exactly when every consecutive block boundary has
weight two. -/
theorem pathForestComponentRuns_eq_singleton_iff (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentRuns hk P C =
        [pathForestComponentBlockEntries (by omega) P C] ↔
      (pathForestComponentBlockEntries (by omega) P C).IsChain
        (fun u v => overlapWeight (blockExit u) v = 2) := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  constructor
  · intro hruns
    have hspec := (pathForestComponentRuns_spec hk P C).2.2.1
    exact hspec entries (by simp [entries, hruns])
  · intro hchain
    have hbool : entries.IsChain
        (fun u v => isWeightTwoBoundary u v = true) :=
      hchain.imp (by
        intro u v huv
        simpa [isWeightTwoBoundary] using huv)
    simpa [pathForestComponentRuns, weightTwoRuns, entries] using
      List.splitBy_of_isChain
        (pathForestComponentBlockEntries_nonempty (by omega) P C) hbool

/-- A one-block component is represented by the single singleton run. -/
theorem pathForestComponentRuns_singleton (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (u : PermutationVertex k)
    (hentries : pathForestComponentBlockEntries (by omega) P C = [u]) :
    pathForestComponentRuns hk P C = [[u]] := by
  have hruns := (pathForestComponentRuns_eq_singleton_iff hk P C).mpr (by
    rw [hentries]
    exact List.isChain_singleton u)
  simpa [hentries] using hruns

/-- Every run has at least one complete block. -/
theorem pathForestRun_length_pos (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    0 < r.length := by
  exact List.length_pos_of_ne_nil (PathForestRun.blocks_nonempty r)

/-- Consecutive component-run entries are exactly related by one application
of `τ₂`; no reducedness hypothesis is needed. -/
theorem pathForestRun_isChain_runMap (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) :
    r.blocks.IsChain (fun u v => v = runMap (by omega) u) := by
  have himp := (component_entries_weightTwo_imp_runMap hk P r.component).infix
    (pathForestRun_infix_entries hk P r)
  have hweightBool := List.isChain_of_mem_splitBy r.isRun
  have hweight : r.blocks.IsChain
      (fun u v => overlapWeight (blockExit u) v = 2) :=
    hweightBool.imp (by
      intro u v huv
      simpa [isWeightTwoBoundary] using huv)
  rw [List.isChain_iff_getElem] at himp hweight ⊢
  intro i hi
  exact himp i hi (hweight i hi)

private theorem get_eq_runMapPower_of_chain (hk : 7 ≤ k)
    {l : List (PermutationVertex k)} (hne : l ≠ [])
    (hchain : l.IsChain (fun u v => v = runMap (by omega) u))
    (i : ℕ) (hi : i < l.length) :
    l.get ⟨i, hi⟩ = runMapPower (by omega) i (l.head hne) := by
  induction i with
  | zero =>
      cases l with
      | nil => exact (hne rfl).elim
      | cons a tail => rfl
  | succ i ih =>
      have hi0 : i < l.length := by omega
      have hstep := (List.isChain_iff_getElem.mp hchain) i hi
      calc
        l.get ⟨i + 1, hi⟩ = runMap (by omega) (l.get ⟨i, hi0⟩) := hstep
        _ = runMap (by omega) (runMapPower (by omega) i (l.head hne)) :=
          congrArg (runMap (by omega)) (ih hi0)
        _ = runMapPower (by omega) (i + 1) (l.head hne) := by
          simpa [runMapPower, Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply' (runMap (by omega)) i
              (l.head hne)).symm

/-- Exact entry sequence of a run: its `i`th block is entered at
`τ₂^i(Y)`. -/
theorem pathForestRun_entrySequence (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) (i : ℕ) (hi : i < r.length) :
    r.blocks.get ⟨i, hi⟩ =
      runMapPower (by omega) i r.entry := by
  exact get_eq_runMapPower_of_chain hk (PathForestRun.blocks_nonempty r)
    (pathForestRun_isChain_runMap hk P r) i hi

/-- A component run's final entry is `τ₂^(ℓ-1)` of its entry. -/
theorem pathForestRun_lastEntry_eq_runMapPower (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    r.lastEntry = runMapPower (by omega) (r.length - 1) r.entry := by
  have hpos := pathForestRun_length_pos hk P r
  have hlast : r.length - 1 < r.length := Nat.sub_lt hpos (by omega)
  rw [PathForestRun.lastEntry, List.getLast_eq_getElem]
  exact pathForestRun_entrySequence hk P r (r.length - 1) hlast

private theorem component_entries_nodup (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (pathForestComponentBlockEntries_pairwiseDistinct (by omega) P C).imp
    (by
      intro u v hclasses huv
      exact hclasses (congrArg rotationClass huv))

private theorem pathForestRun_blocks_nodup (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P) :
    r.blocks.Nodup :=
  (pathForestRun_infix_entries hk P r).nodup
    (component_entries_nodup hk P r.component)

/-- A run has at most `n=k-1` blocks; otherwise the exact order of `τ₂`
would repeat its entry. -/
theorem pathForestRun_length_le (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) :
    r.length ≤ k - 1 := by
  by_contra hnot
  have hn : k - 1 < r.length := Nat.lt_of_not_ge hnot
  have hzero : 0 < r.length := pathForestRun_length_pos hk P r
  have hentryZero := pathForestRun_entrySequence hk P r 0 hzero
  have hentryN := pathForestRun_entrySequence hk P r (k - 1) hn
  have heq : r.blocks.get ⟨k - 1, hn⟩ = r.blocks.get ⟨0, hzero⟩ := by
    calc
      r.blocks.get ⟨k - 1, hn⟩ = r.entry :=
        hentryN.trans (runMap_order_exact (by omega) r.entry).1
      _ = r.blocks.get ⟨0, hzero⟩ := by
        simpa [runMapPower] using hentryZero.symm
  have hfin := (pathForestRun_blocks_nodup hk P r).get_inj_iff.mp heq
  have hval := congrArg Fin.val hfin
  simp at hval
  omega

/-- The frozen full-run condition is equivalent to zero deficit. -/
theorem pathForestRun_isFull_iff_deficit_zero (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) :
    r.IsFull ↔ r.deficit = 0 := by
  have hle := pathForestRun_length_le hk P r
  simp only [PathForestRun.IsFull, PathForestRun.deficit]
  omega

/-- The first run of a component, in the component's canonical order. -/
noncomputable def pathForestComponentFirstRun (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    PathForestRun hk P := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  exact ⟨C, runs.head hruns, List.head_mem hruns⟩

/-- The last run of a component, in the component's canonical order. -/
noncomputable def pathForestComponentLastRun (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    PathForestRun hk P := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  exact ⟨C, runs.getLast hruns, List.getLast_mem hruns⟩

/-- The first run starts at the component tail `v_p`. -/
theorem pathForestComponentFirstRun_entry_eq_tail (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentFirstRun hk P C).entry =
      pathForestComponentTail (by omega) P C := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hentries : entries ≠ [] :=
    pathForestComponentBlockEntries_nonempty (by omega) P C
  have hsplit := List.head_head_splitBy isWeightTwoBoundary hentries
  change (((entries.splitBy isWeightTwoBoundary).head _).head _) = _
  calc
    ((entries.splitBy isWeightTwoBoundary).head _).head _ =
        entries.head hentries := hsplit
    _ = entries.get ⟨0, List.length_pos_of_ne_nil hentries⟩ :=
      List.head_eq_getElem_zero hentries
    _ = pathForestComponentTail (by omega) P C := by
      simpa [entries] using component_entry_zero_eq_tail hk P C

/-- The last run ends at the component's final block entry `ω_p`. -/
theorem pathForestComponentLastRun_lastEntry_eq_lastBlockEntry
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentLastRun hk P C).lastEntry =
      pathForestComponentLastBlockEntry (by omega) P C := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hentries : entries ≠ [] :=
    pathForestComponentBlockEntries_nonempty (by omega) P C
  have hsplit := List.getLast_getLast_splitBy isWeightTwoBoundary hentries
  change (((entries.splitBy isWeightTwoBoundary).getLast _).getLast _) = _
  calc
    ((entries.splitBy isWeightTwoBoundary).getLast _).getLast _ =
        entries.getLast hentries := hsplit
    _ = pathForestComponentLastBlockEntry (by omega) P C := by
      rfl

/-- The frozen run count `q` for a component path. -/
noncomputable def pathForestComponentRunCount (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℕ :=
  (pathForestComponentRuns hk P C).length

/-- The ordered deficit string `(d₁,…,d_q)` of a component path. -/
noncomputable def pathForestComponentDeficitString (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : List ℕ :=
  (pathForestComponentRuns hk P C).map
    (fun run => (k - 1) - run.length)

/-- The total deficit `D` of a component path. -/
noncomputable def pathForestComponentTotalDeficit (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℕ :=
  (pathForestComponentDeficitString hk P C).sum

/-- The first deficit `d⁻_p`. -/
noncomputable def pathForestComponentFirstDeficit (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℕ :=
  (pathForestComponentDeficitString hk P C).head (by
    simpa [pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C)

/-- The last deficit `d⁺_p`. -/
noncomputable def pathForestComponentLastDeficit (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℕ :=
  (pathForestComponentDeficitString hk P C).getLast (by
    simpa [pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C)

/-- Component run count is the generic run count of the component path. -/
theorem pathForestComponentRunCount_eq_blockAlignedRunCount
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentRunCount hk P C =
      blockAlignedRunCount hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  unfold pathForestComponentRunCount blockAlignedRunCount
  rw [pathForestComponentRuns_eq_blockAlignedRuns hk P C]

/-- Component deficit strings are the generic deficit strings of their
component paths. -/
theorem pathForestComponentDeficitString_eq_blockAlignedDeficitString
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentDeficitString hk P C =
      blockAlignedDeficitString hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  unfold pathForestComponentDeficitString blockAlignedDeficitString
  rw [pathForestComponentRuns_eq_blockAlignedRuns hk P C]

/-- The first component deficit is the deficit of its first run. -/
theorem pathForestComponentFirstDeficit_eq_firstRun_deficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentFirstDeficit hk P C =
      (pathForestComponentFirstRun hk P C).deficit := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  change (runs.map (fun run => (k - 1) - run.length)).head _ =
    (k - 1) - (runs.head hruns).length
  exact List.head_map
    (f := fun run : List (PermutationVertex k) => (k - 1) - run.length)
    (l := runs) (by simp [hruns])

/-- The last component deficit is the deficit of its last run. -/
theorem pathForestComponentLastDeficit_eq_lastRun_deficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentLastDeficit hk P C =
      (pathForestComponentLastRun hk P C).deficit := by
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := pathForestComponentRuns_nonempty hk P C
  change (runs.map (fun run => (k - 1) - run.length)).getLast _ =
    (k - 1) - (runs.getLast hruns).length
  exact List.getLast_map
    (f := fun run : List (PermutationVertex k) => (k - 1) - run.length)
    (l := runs) (by simp [hruns])

/-- A component is terminal-full when its last run has deficit zero. -/
def IsTerminalFullComponent (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : Prop :=
  pathForestComponentLastDeficit hk P C = 0

/-- The terminal-full components of the forest. -/
noncomputable def pathForestTerminalFullComponents (hk : 7 ≤ k)
    (P : HamiltonianPath k) :
    Finset (WeakComponent (pathForest (by omega) P)) := by
  classical
  exact Finset.univ.filter (IsTerminalFullComponent hk P)

/-- The frozen count `C` of terminal-full components. -/
noncomputable def pathForestTerminalFullCount (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℕ :=
  (pathForestTerminalFullComponents hk P).card

/-- The deficit string has exactly `q` terms. -/
@[simp]
theorem pathForestComponentDeficitString_length (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentDeficitString hk P C).length =
      pathForestComponentRunCount hk P C := by
  simp [pathForestComponentDeficitString, pathForestComponentRunCount]

private theorem component_run_length_le (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (run : List (PermutationVertex k))
    (hrun : run ∈ pathForestComponentRuns hk P C) :
    run.length ≤ k - 1 := by
  let r : PathForestRun hk P := ⟨C, run, hrun⟩
  exact pathForestRun_length_le hk P r

private theorem sum_deficits_add_lengths
    (n : ℕ) (runs : List (List (PermutationVertex k)))
    (hle : ∀ run ∈ runs, run.length ≤ n) :
    (runs.map (fun run => n - run.length)).sum +
        (runs.map List.length).sum = n * runs.length := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hrun : run.length ≤ n := hle run (by simp)
      have htail : ∀ tail ∈ runs, tail.length ≤ n := by
        intro tail htail
        exact hle tail (by simp [htail])
      have hih := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega

private theorem component_run_lengths_sum (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    ((pathForestComponentRuns hk P C).map List.length).sum =
      (pathForestComponentBlockEntries (by omega) P C).length := by
  have hlength := congrArg List.length
    (pathForestComponentRuns_spec hk P C).1
  simpa using hlength

/-- The natural subtraction in `b=nq-D` is justified: total deficit never
exceeds the `nq` capacity. -/
theorem pathForestComponentTotalDeficit_le_capacity (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentTotalDeficit hk P C ≤
      (k - 1) * pathForestComponentRunCount hk P C := by
  let runs := pathForestComponentRuns hk P C
  have hbalance := sum_deficits_add_lengths (k - 1) runs (by
    intro run hrun
    exact component_run_length_le hk P C run hrun)
  change (runs.map (fun run => (k - 1) - run.length)).sum ≤
    (k - 1) * runs.length
  omega

/-- Frozen equation `b = nq-D`, with the preceding capacity theorem ruling
out truncated natural subtraction. -/
theorem pathForestComponentBlockCount_eq_runCount_sub_totalDeficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentBlockCount (by omega) P C =
      (k - 1) * pathForestComponentRunCount hk P C -
        pathForestComponentTotalDeficit hk P C := by
  let runs := pathForestComponentRuns hk P C
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hbalance := sum_deficits_add_lengths (k - 1) runs (by
    intro run hrun
    exact component_run_length_le hk P C run hrun)
  have hlengths : (runs.map List.length).sum = entries.length := by
    simpa [runs, entries] using component_run_lengths_sum hk P C
  have hcap := pathForestComponentTotalDeficit_le_capacity hk P C
  unfold pathForestComponentBlockCount pathForestComponentRunCount
    pathForestComponentTotalDeficit pathForestComponentDeficitString
  rw [← pathForestComponentBlockEntries_length (by omega) P C]
  change entries.length =
    (k - 1) * runs.length -
      (runs.map (fun run => (k - 1) - run.length)).sum
  rw [hlengths] at hbalance
  omega

/-- First half of Lemma `arc`: a run entered at `Y` occupies exactly the
classes numbered `0,…,ℓ-1` in the `τ₂` orbit. -/
theorem pathForestRun_occupiedClasses_eq_slots (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) :
    r.occupiedClasses =
      (Finset.range r.length).image
        (fun i => rotationClass (runMapPower (by omega) i r.entry)) := by
  classical
  ext B
  constructor
  · intro hB
    change B ∈ r.blocks.toFinset.image rotationClass at hB
    obtain ⟨u, huSet, huB⟩ := Finset.mem_image.mp hB
    have hu : u ∈ r.blocks := List.mem_toFinset.mp huSet
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
    apply Finset.mem_image.mpr
    refine ⟨i.1, Finset.mem_range.mpr i.2, ?_⟩
    have hsequence := pathForestRun_entrySequence hk P r i.1 i.2
    calc
      rotationClass (runMapPower (by omega) i.1 r.entry) =
          rotationClass (r.blocks.get i) := congrArg rotationClass hsequence.symm
      _ = rotationClass u := congrArg rotationClass hi
      _ = B := huB
  · intro hB
    obtain ⟨i, hiRange, hiB⟩ := Finset.mem_image.mp hB
    have hi : i < r.length := Finset.mem_range.mp hiRange
    change B ∈ r.blocks.toFinset.image rotationClass
    apply Finset.mem_image.mpr
    refine ⟨r.blocks.get ⟨i, hi⟩,
      List.mem_toFinset.mpr (List.get_mem _ _), ?_⟩
    calc
      rotationClass (r.blocks.get ⟨i, hi⟩) =
          rotationClass (runMapPower (by omega) i r.entry) :=
        congrArg rotationClass (pathForestRun_entrySequence hk P r i hi)
      _ = B := hiB

/-- Every occupied class really lies in the two-loop determined by the run
entry's satellite and cyclic core. -/
theorem pathForestRun_occupiedClasses_subset_twoLoop (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) :
    r.occupiedClasses ⊆
      twoLoop (by omega) (entrySatellite (by omega) r.entry)
        (entryCore r.entry) := by
  intro B hB
  rw [pathForestRun_occupiedClasses_eq_slots hk P r] at hB
  obtain ⟨i, hiRange, hiB⟩ := Finset.mem_image.mp hB
  have hiLength : i < r.length := Finset.mem_range.mp hiRange
  have hi : i < k - 1 :=
    hiLength.trans_le (pathForestRun_length_le hk P r)
  rw [twoLoop_eq_runMapOrbitClasses (by omega)]
  apply (mem_runMapOrbitClasses (by omega) r.entry B).mpr
  exact ⟨i, hi, hiB⟩

/-- Literal slot orientation for Lemma `arc`: the `i`th occupied block sits
after core letter `x_i`, with index zero using `x₀=xₙ`. -/
theorem pathForestRun_slot (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r : PathForestRun hk P) (i : ℕ) (hi : i < r.length) :
    rotationClassSlot (r.blocks.get ⟨i, hi⟩)
        (entrySatellite (by omega) r.entry) =
      coreSlotLetter (by omega) r.entry
        ⟨i, hi.trans_le (pathForestRun_length_le hk P r)⟩ := by
  rw [pathForestRun_entrySequence hk P r i hi]
  exact runMapPower_slot (by omega) r.entry
    ⟨i, hi.trans_le (pathForestRun_length_le hk P r)⟩

private theorem component_block_entry_mem (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u : PermutationVertex k}
    (hu : u ∈ pathForestComponentBlockEntries (by omega) P C) :
    u ∈ weakComponentVertices C := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  have hentry := component_entry_eq_vertex hk P C i.1 i.2
  have huPath : u ∈ (pathForestComponentPath (by omega) P C).vertices := by
    rw [← hi, hentry]
    exact (pathForestComponentPath (by omega) P C).vertex_mem _
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  exact List.mem_toFinset.mpr huPath

private theorem run_block_mem_component (hk : 7 ≤ k)
    (P : HamiltonianPath k) (r : PathForestRun hk P)
    {u : PermutationVertex k} (hu : u ∈ r.blocks) :
    u ∈ weakComponentVertices r.component := by
  apply component_block_entry_mem hk P r.component
  exact (pathForestRun_infix_entries hk P r).sublist.mem hu

private theorem component_entries_eq_of_same_class (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u v : PermutationVertex k}
    (hu : u ∈ pathForestComponentBlockEntries (by omega) P C)
    (hv : v ∈ pathForestComponentBlockEntries (by omega) P C)
    (hclass : rotationClass u = rotationClass v) : u = v := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  obtain ⟨iu, hiu⟩ := List.mem_iff_get.mp hu
  obtain ⟨iv, hiv⟩ := List.mem_iff_get.mp hv
  by_cases hindices : iu = iv
  · subst iv
    exact hiu.symm.trans hiv
  · rcases lt_or_gt_of_ne hindices with hlt | hgt
    · have hne :=
        (pathForestComponentBlockEntries_pairwiseDistinct (by omega) P C).rel_get_of_lt hlt
      exfalso
      apply hne
      rw [hiu, hiv]
      exact hclass
    · have hne :=
        (pathForestComponentBlockEntries_pairwiseDistinct (by omega) P C).rel_get_of_lt hgt
      exfalso
      apply hne
      rw [hiu, hiv]
      exact hclass.symm

private theorem component_runs_eq_of_common_block (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {r s : List (PermutationVertex k)}
    (hr : r ∈ pathForestComponentRuns hk P C)
    (hs : s ∈ pathForestComponentRuns hk P C)
    {u : PermutationVertex k} (hur : u ∈ r) (hus : u ∈ s) :
    r = s := by
  by_contra hne
  have hflattenNodup : (pathForestComponentRuns hk P C).flatten.Nodup := by
    rw [(pathForestComponentRuns_spec hk P C).1]
    exact component_entries_nodup hk P C
  have hpairwise := (List.nodup_flatten.mp hflattenNodup).2
  obtain ⟨ir, hir⟩ := List.mem_iff_get.mp hr
  obtain ⟨is, his⟩ := List.mem_iff_get.mp hs
  have hindices : ir ≠ is := by
    intro heq
    subst is
    exact hne (hir.symm.trans his)
  have hdisjoint : List.Disjoint r s := by
    rcases lt_or_gt_of_ne hindices with hlt | hgt
    · have hd := hpairwise.rel_get_of_lt hlt
      rw [hir, his] at hd
      exact hd
    · have hd := hpairwise.rel_get_of_lt hgt
      rw [List.disjoint_comm]
      rw [his, hir] at hd
      exact hd
  exact (List.disjoint_left.mp hdisjoint hur) hus

/-- Strong form of Lemma `arc`: two runs anywhere in `F(P)` that share a
rotation class are the same run, including when they lie in one component. -/
theorem pathForestRun_eq_of_shared_rotationClass (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r s : PathForestRun hk P)
    {B : Finset (PermutationVertex k)}
    (hrB : B ∈ r.occupiedClasses) (hsB : B ∈ s.occupiedClasses) :
    r = s := by
  classical
  rcases r with ⟨C, r, hr⟩
  rcases s with ⟨D, s, hs⟩
  change B ∈ r.toFinset.image rotationClass at hrB
  change B ∈ s.toFinset.image rotationClass at hsB
  obtain ⟨u, huSet, huB⟩ := Finset.mem_image.mp hrB
  obtain ⟨v, hvSet, hvB⟩ := Finset.mem_image.mp hsB
  have hu : u ∈ r := List.mem_toFinset.mp huSet
  have hv : v ∈ s := List.mem_toFinset.mp hvSet
  have huC : u ∈ weakComponentVertices C := by
    apply component_block_entry_mem hk P C
    exact (mem_weightTwoRuns_infix hr).sublist.mem hu
  have hvD : v ∈ weakComponentVertices D := by
    apply component_block_entry_mem hk P D
    exact (mem_weightTwoRuns_infix hs).sublist.mem hv
  have huvClass : rotationClass u = rotationClass v := huB.trans hvB.symm
  have hvInUClass : v ∈ rotationClass u := by
    rw [huvClass]
    exact self_mem_rotationClass (by omega) v
  have hvC : v ∈ weakComponentVertices C :=
    pathForest_component_contains_rotationClass (by omega) P C
      (mem_weakComponentVertices.mp huC) hvInUClass
  have hCD : C = D :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (mem_weakComponentVertices.mp hvC)
      (mem_weakComponentVertices.mp hvD)
  subst D
  have huEntries : u ∈ pathForestComponentBlockEntries (by omega) P C :=
    (mem_weightTwoRuns_infix hr).sublist.mem hu
  have hvEntries : v ∈ pathForestComponentBlockEntries (by omega) P C :=
    (mem_weightTwoRuns_infix hs).sublist.mem hv
  have huv := component_entries_eq_of_same_class hk P C
    huEntries hvEntries huvClass
  have huvInS : u ∈ s := by simpa [huv] using hv
  have hrs : r = s := component_runs_eq_of_common_block hk P C hr hs hu huvInS
  subst s
  rfl

/-- Equivalent disjointness formulation of Lemma `arc`: any two forest runs
coincide, or their occupied rotation-class sets are disjoint. -/
theorem pathForestRun_eq_or_disjoint_occupiedClasses (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (r s : PathForestRun hk P) :
    r = s ∨ Disjoint r.occupiedClasses s.occupiedClasses := by
  by_cases hrs : r = s
  · exact Or.inl hrs
  · right
    rw [Finset.disjoint_left]
    intro B hrB hsB
    exact hrs (pathForestRun_eq_of_shared_rotationClass hk P r s hrB hsB)

/-- The entrance door `α_p=τ₂⁻¹(v_p)`. -/
noncomputable def pathForestComponentEntranceDoor (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    PermutationVertex k :=
  runMapInverse (by omega) (pathForestComponentTail (by omega) P C)

/-- The exit door `β_p=τ₂(ω_p)`. -/
noncomputable def pathForestComponentExitDoor (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    PermutationVertex k :=
  runMap (by omega) (pathForestComponentLastBlockEntry (by omega) P C)

/-- Public inverse-orientation accessor for the entrance door. -/
@[simp]
theorem pathForestComponentEntranceDoor_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentEntranceDoor hk P C =
      runMapInverse (by omega) (pathForestComponentTail (by omega) P C) := rfl

/-- Public forward-orientation accessor for the exit door. -/
@[simp]
theorem pathForestComponentExitDoor_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentExitDoor hk P C =
      runMap (by omega)
        (pathForestComponentLastBlockEntry (by omega) P C) := rfl

/-- The explicit frozen word formula
`α_p=v_{k-1}v₁⋯v_{k-2}v_k`; in zero-based list notation the first
displayed letter is entry `k-2`. -/
theorem pathForestComponentEntranceDoor_word (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    let v := pathForestComponentTail (by omega) P C
    (pathForestComponentEntranceDoor hk P C).1 =
      [v.1.get ⟨k - 2, by simp [v.length]; omega⟩] ++
        v.1.take (k - 2) ++ [entrySatellite (by omega) v] := by
  let v := pathForestComponentTail (by omega) P C
  let core := v.1.dropLast
  have hcoreLength : core.length = k - 1 := by
    simp [core, v.length]
  have hrotate : core.rotate (k - 2) =
      core.drop (k - 2) ++ core.take (k - 2) := by
    apply List.rotate_eq_drop_append_take
    rw [hcoreLength]
    omega
  have hindexCore : k - 2 < core.length := by
    rw [hcoreLength]
    omega
  have hdrop : core.drop (k - 2) =
      [v.1.get ⟨k - 2, by simp [v.length]; omega⟩] := by
    rw [List.drop_eq_getElem_cons hindexCore]
    have htailIndex : k - 2 + 1 = core.length := by
      rw [hcoreLength]
      omega
    rw [htailIndex]
    simp only [List.drop_length]
    congr 1
    exact List.getElem_dropLast hindexCore
  have htake : core.take (k - 2) = v.1.take (k - 2) := by
    change v.1.dropLast.take (k - 2) = v.1.take (k - 2)
    rw [List.dropLast_eq_take, List.take_take]
    congr 1
    simp [v.length]
    omega
  rw [pathForestComponentEntranceDoor_eq, runMapInverse_word]
  change core.rotate (k - 2) ++ [entrySatellite (by omega) v] = _
  rw [hrotate, hdrop, htake]

/-- The exit door uses the forward `τ₂` orientation and hence has the
literal frozen run-map word. -/
theorem pathForestComponentExitDoor_word (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    let omegaEntry := pathForestComponentLastBlockEntry (by omega) P C
    (pathForestComponentExitDoor hk P C).1 =
      omegaEntry.1.dropLast.rotate 1 ++
        [entrySatellite (by omega) omegaEntry] := by
  rw [pathForestComponentExitDoor_eq, runMap_word]

end SuperpermutationLowerBound
