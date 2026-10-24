module

public import SuperpermutationLowerBound.Refinement.ScalarClusters

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PositiveClusterChain

theorem gap_sum_identity {a : ℕ} (ha : 1 ≤ a) (us : List ℕ)
    (hbound : ∀ u ∈ us, u ≤ a) :
    us.sum + (us.map (fun u => a - 1 - u)).sum =
      (a - 1) * us.length + us.count a := by
  induction us with
  | nil => simp
  | cons u us ih =>
      have hu := hbound u (by simp)
      have htail := ih (by intro v hv; exact hbound v (by simp [hv]))
      by_cases heq : u = a
      · simp [heq, Nat.mul_add] at *
        omega
      · have hu' : u ≤ a - 1 := by omega
        simp [heq, Nat.mul_add] at *
        omega

theorem reserveSum_identity (a : ℕ) (p t : ℚ) (chain : PositiveClusterChain) :
    reserveSum a p t chain =
      chainLambda a t * (((chain.clusters.map List.sum).sum : ℚ) -
        2 * chain.clusters.length) -
      2 * t * (((chain.clusters.map List.length).sum : ℚ) - chain.clusters.length) -
      4 * (p + 1) * exceptionalClusterCount chain := by
  induction chain with
  | last K =>
      by_cases hK : K = [2] <;>
        simp [reserveSum, clusters, exceptionalClusterCount, clusterReserve, hK] <;> ring
  | cons K gap tail ih =>
      by_cases hK : K = [2] <;>
        simp [reserveSum, clusters, exceptionalClusterCount, clusterReserve, hK] at * <;>
        linarith

/-- Exact position and reserve bookkeeping for a zero-ended core. -/
theorem zeroEndedCore_slack_identity {a lead trail : ℕ} (ha : 1 ≤ a)
    (p t : ℚ) (chain : PositiveClusterChain)
    (hbound : ∀ u ∈ chain.gaps, u ≤ a) :
    chainLambda a t *
        ((List.replicate lead 0 ++ chain.render ++ List.replicate trail 0).sum : ℚ) -
      2 * t * ((List.replicate lead 0 ++ chain.render ++ List.replicate trail 0).length : ℚ) +
      chainIntercept a p t =
      (4 * p + 4 * (p + 1) * exceptionalClusterCount chain +
        2 * t * shortGapMass a chain - 4 * chain.clusters.length) +
      reserveSum a p t chain - 2 * t * (chain.gaps.count a : ℚ) +
      2 * t * (2 * a - lead - trail) := by
  have hgap := gap_sum_identity ha chain.gaps hbound
  have hgapQ : (chain.gaps.sum : ℚ) + shortGapMass a chain =
      ((a : ℚ) - 1) * chain.gaps.length + chain.gaps.count a := by
    have hanat : a - 1 + 1 = a := by omega
    have haQ : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by exact_mod_cast (show (a - 1 : ℤ) = (a : ℤ) - 1 by omega)
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hgap
    simpa [shortGapMass, haQ] using hcast
  have hcountQ : (chain.gaps.length : ℚ) + 1 = chain.clusters.length := by
    exact_mod_cast chain.gaps_length
  rw [reserveSum_identity]
  simp only [List.length_append, List.length_replicate, render_length,
    render_prepend_zero, Nat.cast_add]
  dsimp [chainLambda, chainIntercept]
  have hgapUse := congrArg (fun q : ℚ => 2 * t * q) hgapQ
  have hcountUse := congrArg (fun q : ℚ => 2 * t * ((a : ℚ) - 1) * q) hcountQ
  nlinarith

theorem zeroEndedCore_bound {a lead trail : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (hpt : p ≤ t) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (chain : PositiveClusterChain)
    (hlegal : IsLegalDeficitSequence (a + 2)
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hpacking : ChainPacking a p t
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hGap : ∀ u ∈ chain.gaps, 0 < u) :
    0 ≤ chainLambda a t *
        ((List.replicate lead 0 ++ chain.render ++ List.replicate trail 0).sum : ℚ) -
      2 * t * ((List.replicate lead 0 ++ chain.render ++ List.replicate trail 0).length : ℚ) +
      chainIntercept a p t := by
  have hgapBound : ∀ u ∈ chain.gaps, u ≤ a := by
    simpa using internalClusterGaps_le hlegal hNe hPos hGap
  have hpair : StrongCriticalPairBounds a chain := by
    simpa using strongCriticalPairBounds_of_legal hlegal hNe hPos hGap
  have hmass := clusterMassBounds_of_legal hlegal hlead htrail hNe hPos hGap
  have hpref := prefixPacking_of_chainPacking hpacking hp hlead htrail hGap
  have hcount := cluster_count_with_initial_value ha hp hpt chain hpref hgapBound
    (noMaxRegularGap_of_strong ha hpair)
  have hfirst := hpref.first
  have hreserve := reserve_degree_two_bound ha hp ht hmargin chain hNe hmass hpair
  have hfirstNe := hNe chain.firstCluster chain.firstCluster_mem_clusters
  have hfirstMass := hmass chain.firstCluster chain.firstCluster_mem_clusters
  have hlastNe := hNe (lastCluster chain) (lastCluster_mem chain)
  have hlastMass := hmass (lastCluster chain) (lastCluster_mem chain)
  have hfirstPhi := clusterReserve_nonnegative hp ht hmargin hfirstMass
    (cluster_exceptional_mass hfirstNe hfirstMass)
  have hlastPhi := clusterReserve_nonnegative hp ht hmargin hlastMass
    (cluster_exceptional_mass hlastNe hlastMass)
  have hend := endpointZeroBlocks_bound hlegal hNe hPos
  have hex : clusterExceptionCount lead chain trail ≤ 2 := clusterExceptionCount_le_two _ _ _
  have hend' : lead + trail ≤ 2 * a := by
    have hmul := Nat.mul_le_mul_left a (show 2 - clusterExceptionCount lead chain trail ≤ 2 by omega)
    simp only [Nat.add_sub_cancel] at hend
    omega
  have hendQ : (lead : ℚ) + trail ≤ 2 * a := by exact_mod_cast hend'
  have hendPay := mul_nonneg (show 0 ≤ 2 * t by positivity)
    (show 0 ≤ 2 * (a : ℚ) - lead - trail by linarith)
  rw [zeroEndedCore_slack_identity (by omega : 1 ≤ a) p t chain hgapBound]
  linarith

end SuperpermutationLowerBound.Refinement
