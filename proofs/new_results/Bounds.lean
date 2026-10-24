module

public import new_results.ForestRigidity
public import new_results.ScalarRigidity
public import new_results.PivotRigidity
public import new_results.GlobalPartition
public import bridge.NumericalEvaluations

@[expose] public section

/-! The fourteen-letter refinement. Every hypothesis used below is obtained
from an actual reduced minimum overlap path. The scalar rigidity theorem and
satellite propagation force a complete path to partition its insertion loops
into full rows, contradicting its positive total deficit. -/
namespace SuperpermutationLowerBound.NewResults

open Refinement

private theorem regular_render_zero_two (chain : PositiveClusterChain)
    (hregular : ∀ K ∈ chain.clusters, K = [2]) :
    ∀ x ∈ chain.render, x = 0 ∨ x = 2 := by
  induction chain with
  | last K =>
      have hK := hregular K (by simp [PositiveClusterChain.clusters])
      simp [PositiveClusterChain.render, hK]
  | cons K gap tail ih =>
      have hK := hregular K (by simp [PositiveClusterChain.clusters])
      have ht : ∀ L ∈ tail.clusters, L = [2] := by
        intro L hL
        exact hregular L (by simp [PositiveClusterChain.clusters, hL])
      intro x hx
      have hx' : x = 2 ∨ x ∈ List.replicate gap 0 ∨ x ∈ tail.render := by
        simpa [PositiveClusterChain.render, hK, or_assoc] using hx
      rcases hx' with hx | hx | hx
      · exact Or.inr hx
      · exact Or.inl (List.mem_replicate.mp hx).2
      · exact ih ht x hx

private theorem regular_decomposition_zero_two {d : List ℕ}
    (dec : PositiveClusterDecomposition d)
    (hregular : ∀ K ∈ dec.chain.clusters, K = [2]) :
    ∀ x ∈ d, x = 0 ∨ x = 2 := by
  intro x hx
  rw [dec.rebuild] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (List.mem_replicate.mp hx).2
    · exact regular_render_zero_two dec.chain hregular x hx
  · exact Or.inl (List.mem_replicate.mp hx).2

private theorem whole_segment_actualRun {k : ℕ} {hk : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    (s : BlockAlignedLightSegment hk p hp)
    (hs : s.runs = blockAlignedRuns hk p hp) (j : Fin s.length) :
    s.actualRun j = blockAlignedRunAt hk p hp
      ⟨j.val, by simpa [BlockAlignedLightSegment.length, hs] using j.isLt⟩ := by
  have hb := blockAlignedLightSegment_globalStart_bounds hk p hp s
  have hl : s.length = (blockAlignedRuns hk p hp).length := by
    simp [BlockAlignedLightSegment.length, hs]
  have hz : s.globalStart = 0 := by omega
  simp [BlockAlignedLightSegment.actualRun, hz]

/-- The integer attained by the old bound is impossible for a reduced
minimum path. No separate normalization or occurrence hypothesis is used. -/
theorem fourteen_minimum_weight_ne
    (P : HamiltonianPath 14) (hP : IsReducedMinimumPath P) :
    P.weight ≠ 93891141135 := by
  intro hweight
  obtain ⟨p, hp, s, hc, hs, hlen, hsum, hhead, hlast, hlegal, hpacking, henergy⟩ :=
    exists_fourteen_rigid_segment_of_weight P hP hweight
  obtain ⟨dec, hregular, hlead, htrail, hgaps⟩ := deficitString14_rigid
    hlegal hpacking hhead hlast (by omega) (by rw [henergy])
  have hconstant := segment_satellite_constant_of_rigid s dec hregular
    (by omega) (by omega) (by intro u hu; have := hgaps u hu; omega)
  have hpositive := blockAlignedLightSegment_length_pos (by omega : 7 ≤ 14) p hp s
  let first : Fin s.length := ⟨0, hpositive⟩
  let satellite : Alphabet 14 := segmentSatellite s first
  have hcomplete : ∀ u : PermutationVertex 14, u ∈ p.vertices := by
    intro u
    have hu : u ∈ p.vertexSet := by rw [hc]; exact Finset.mem_univ _
    simpa only [OverlapPath.vertexSet, List.mem_toFinset] using hu
  have hsat : ∀ i : Fin (blockAlignedRuns (by omega : 7 ≤ 14) p hp).length,
      entrySatellite (by omega) (blockAlignedRunAt (by omega) p hp i).entry =
        satellite := by
    intro i
    let j : Fin s.length :=
      ⟨i.val, by simpa [BlockAlignedLightSegment.length, hs] using i.isLt⟩
    have hj := whole_segment_actualRun s hs j
    have hh := hconstant j first
    simpa only [segmentSatellite, hj, j, satellite] using hh
  have hdef : ∀ i : Fin (blockAlignedRuns (by omega : 7 ≤ 14) p hp).length,
      (blockAlignedRunAt (by omega) p hp i).deficit = 0 ∨
      (blockAlignedRunAt (by omega) p hp i).deficit = 2 := by
    intro i
    let j : Fin s.length :=
      ⟨i.val, by simpa [BlockAlignedLightSegment.length, hs] using i.isLt⟩
    have hj := whole_segment_actualRun s hs j
    have hd := regular_decomposition_zero_two dec hregular _
      (List.get_mem s.deficitString ⟨j.val, by simpa using j.isLt⟩)
    rw [s.deficitString_get_eq j] at hd
    have hb := s.actualRun_blocks j
    rw [← hb] at hd
    change (s.actualRun j).deficit = 0 ∨ (s.actualRun j).deficit = 2 at hd
    simpa only [hj] using hd
  have hfull := complete_aligned_zero_two_full (by omega : 7 ≤ 14)
    p hp hcomplete satellite hsat hdef
  have hall : ∀ x ∈ s.deficitString, x = 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    let j : Fin s.length := ⟨i.val, by simpa using i.isLt⟩
    have hj := whole_segment_actualRun s hs j
    have hf : (s.actualRun j).IsFull := by rw [hj]; exact hfull _
    have hz : s.deficitString.get ⟨j.val, by simpa using j.isLt⟩ = 0 := by
      apply (s.deficitString_get_eq_zero_iff j).mpr
      rw [← s.actualRun_blocks j]
      exact hf
    have hi' : s.deficitString.get ⟨j.val, by simpa using j.isLt⟩ = x := hi
    omega
  have hrep : s.deficitString = List.replicate s.deficitString.length 0 :=
    List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  have hz : s.deficitString.sum = 0 := by rw [hrep]; simp
  omega

/-- Every superpermutation on fourteen letters has at least 93,891,141,150
letters. This improves the frozen bound by one. -/
theorem shortest_fourteen : 93891141150 ≤ shortestSuperpermutationLength 14 := by
  have ha : _root_.SuperpermutationLowerBound.ChainReturns.Admissible 13 36 (569 / 15) := by
    constructor <;> norm_num
  have hold : 93891141149 ≤ shortestSuperpermutationLength 14 := by
    have hh := _root_.SuperpermutationLowerBound.ChainReturns.shortest_bound_of_actualPacking
      (by omega : 8 ≤ 14) ha actualPacking_fourteen_explicit
    simpa only [_root_.SuperpermutationLowerBound.ChainReturns.bound_14] using hh
  by_contra hnew
  have heq : shortestSuperpermutationLength 14 = 93891141149 := by omega
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by omega : 3 ≤ 14)
  have htransport := shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight
    14 (by omega : 3 ≤ 14)
  have hweight : P.weight = 93891141135 := by
    rw [heq, ← hP.1] at htransport
    omega
  exact fourteen_minimum_weight_ne P hP hweight

/-- The same bound for the project's original contiguous-coverage predicate
on unrestricted words over `Fin 14`. -/
theorem word_fourteen (w : List (Fin 14)) (hw : SuperpermutationBounds.Covers w) :
    93891141150 ≤ w.length := by
  classical
  let e : Alphabet 14 ≃ Fin 14 := Fintype.equivFinOfCardEq (by simp [Alphabet])
  let W : Word 14 := w.map e.symm
  have hW : IsSuperpermutation W := by
    intro P
    have hlength : (P.1.map e).length = 14 := by
      simpa only [List.length_map] using P.length
    have hnodup : (P.1.map e).Nodup := P.nodup.map e.injective
    obtain ⟨u, v, heq⟩ := hw (P.1.map e) hlength hnodup
    refine ⟨u.map e.symm, v.map e.symm, ?_⟩
    have hmapped := congrArg (List.map e.symm) heq
    simpa [W, List.map_append, List.map_map, Function.comp_def] using hmapped.symm
  have hmin := shortestSuperpermutationLength_le W hW
  simpa only [W, List.length_map] using le_trans shortest_fourteen hmin

#print axioms shortest_fourteen
#print axioms word_fourteen

end SuperpermutationLowerBound.NewResults
