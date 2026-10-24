module

public import SuperpermutationLowerBound.Refinement.ScalarSequence

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PositiveClusterChain

/-! Exact scalar rigidity for the K=14 parameters. The inputs are the
existing legal sequence and hereditary geometric chain-packing predicates. -/

theorem clusterReserve14_nonnegative {K : List ℕ}
    (hne : K ≠ []) (hmass : K.length + 1 ≤ K.sum) :
    0 ≤ clusterReserve 11 36 (569 / 15) K := by
  exact clusterReserve_nonnegative (by norm_num) (by norm_num) (by norm_num)
    hmass (cluster_exceptional_mass hne hmass)

theorem clusterReserve14_exceptional {K : List ℕ}
    (hmass : K.length + 1 ≤ K.sum) (hthree : 3 ≤ K.sum)
    (hnot : K ≠ [2]) :
    (957 / 5 : ℚ) ≤ clusterReserve 11 36 (569 / 15) K := by
  have hm : (K.length : ℚ) + 1 ≤ K.sum := by exact_mod_cast hmass
  have ht : (3 : ℚ) ≤ K.sum := by exact_mod_cast hthree
  simp only [clusterReserve, if_neg hnot]
  norm_num [chainLambda] at hm ht ⊢
  linarith

theorem clusterReserve14_pair {K L : List ℕ}
    (hK : 1 ≤ K.length) (hL : 1 ≤ L.length)
    (hboundary : 11 + K.length + L.length ≤ K.sum + L.sum) :
    (17207 / 5 : ℚ) ≤
      clusterReserve 11 36 (569 / 15) K +
      clusterReserve 11 36 (569 / 15) L := by
  have hm : (2 : ℚ) ≤ (K.length : ℚ) + L.length := by
    exact_mod_cast (by omega : 2 ≤ K.length + L.length)
  have hb : (11 : ℚ) + K.length + L.length ≤ (K.sum : ℚ) + L.sum := by
    exact_mod_cast hboundary
  unfold clusterReserve
  split_ifs <;> norm_num [chainLambda] at hm hb ⊢ <;> linarith

theorem reserve14_degree_two (chain : PositiveClusterChain)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hMass : ∀ K ∈ chain.clusters, K.length + 1 ≤ K.sum)
    (hPair : StrongCriticalPairBounds 11 chain) :
    (17207 / 5 : ℚ) * (chain.gaps.count 11 : ℚ) +
      clusterReserve 11 36 (569 / 15) chain.firstCluster +
      clusterReserve 11 36 (569 / 15) (lastCluster chain) ≤
        2 * reserveSum 11 36 (569 / 15) chain := by
  induction chain with
  | last K =>
      simp [gaps, firstCluster, lastCluster, reserveSum, clusters]
      ring_nf
      rfl
  | cons K gap tail ih =>
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL; exact hNe L (by simp [clusters, hL])
      have htailMass : ∀ L ∈ tail.clusters, L.length + 1 ≤ L.sum := by
        intro L hL; exact hMass L (by simp [clusters, hL])
      have htail := ih htailNe htailMass hPair.2
      have hKne := hNe K (by simp [clusters])
      have hKmass := hMass K (by simp [clusters])
      have hLne := htailNe tail.firstCluster tail.firstCluster_mem_clusters
      have hLmass := htailMass tail.firstCluster tail.firstCluster_mem_clusters
      have hKpos := clusterReserve14_nonnegative hKne hKmass
      have hLpos := clusterReserve14_nonnegative hLne hLmass
      by_cases hgap : gap = 11
      · have hpay := clusterReserve14_pair
          (List.length_pos_iff.mpr hKne) (List.length_pos_iff.mpr hLne) (hPair.1 hgap)
        simp [gaps, hgap, lastCluster, reserveSum, clusters] at *
        linarith
      · simp [gaps, hgap, lastCluster, reserveSum, clusters] at *
        linarith

theorem reserve14_nonnegative (chain : PositiveClusterChain)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hMass : ∀ K ∈ chain.clusters, K.length + 1 ≤ K.sum) :
    0 ≤ reserveSum 11 36 (569 / 15) chain := by
  unfold reserveSum
  apply List.sum_nonneg
  intro x hx
  obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hx
  exact clusterReserve14_nonnegative (hNe K hK) (hMass K hK)

theorem clusterReserve14_le_sum {chain : PositiveClusterChain} {K : List ℕ}
    (hNe : ∀ L ∈ chain.clusters, L ≠ [])
    (hMass : ∀ L ∈ chain.clusters, L.length + 1 ≤ L.sum)
    (hK : K ∈ chain.clusters) :
    clusterReserve 11 36 (569 / 15) K ≤ reserveSum 11 36 (569 / 15) chain := by
  induction chain with
  | last L =>
      have heq : K = L := by simpa [clusters] using hK
      simp [heq, reserveSum, clusters]
  | cons L gap tail ih =>
      have htailNe : ∀ J ∈ tail.clusters, J ≠ [] := by
        intro J hJ; exact hNe J (by simp [clusters, hJ])
      have htailMass : ∀ J ∈ tail.clusters, J.length + 1 ≤ J.sum := by
        intro J hJ; exact hMass J (by simp [clusters, hJ])
      have hLpos := clusterReserve14_nonnegative
        (hNe L (by simp [clusters])) (hMass L (by simp [clusters]))
      have htailPos := reserve14_nonnegative tail htailNe htailMass
      rcases List.mem_cons.mp hK with rfl | hK
      · simp only [reserveSum, clusters, List.map_cons, List.sum_cons] at *
        linarith
      · have h := ih htailNe htailMass hK
        simp only [reserveSum, clusters, List.map_cons, List.sum_cons] at *
        linarith

/-- Low energy rules out every exceptional positive cluster. -/
theorem zeroEndedCore14_regular {lead trail : ℕ}
    (chain : PositiveClusterChain)
    (hlegal : IsLegalDeficitSequence 13
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hpacking : ChainPacking 11 36 (569 / 15)
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hGap : ∀ u ∈ chain.gaps, 0 < u)
    (henergy : scalarEnergy 11 36 (569 / 15)
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0) ≤ 1398 / 15) :
    ∀ K ∈ chain.clusters, K = [2] := by
  have hgapBound : ∀ u ∈ chain.gaps, u ≤ 11 := by
    simpa using internalClusterGaps_le hlegal hNe hPos hGap
  have hpair : StrongCriticalPairBounds 11 chain := by
    simpa using strongCriticalPairBounds_of_legal hlegal hNe hPos hGap
  have hmass := clusterMassBounds_of_legal hlegal hlead htrail hNe hPos hGap
  have hpref := prefixPacking_of_chainPacking hpacking (by norm_num) hlead htrail hGap
  have hcount := cluster_count_with_initial_value (by norm_num : 4 ≤ 11)
    (by norm_num : (0 : ℚ) ≤ 36) (by norm_num : (36 : ℚ) ≤ 569 / 15)
    chain hpref hgapBound (noMaxRegularGap_of_strong (by norm_num) hpair)
  have hfirst := hpref.first
  have hreserve := reserve14_degree_two chain hNe hmass hpair
  have hfirstPhi := clusterReserve14_nonnegative
    (hNe _ chain.firstCluster_mem_clusters) (hmass _ chain.firstCluster_mem_clusters)
  have hlastPhi := clusterReserve14_nonnegative
    (hNe _ (lastCluster_mem chain)) (hmass _ (lastCluster_mem chain))
  have hend := endpointZeroBlocks_bound hlegal hNe hPos
  have hend' : lead + trail ≤ 22 := by
    have hex := clusterExceptionCount_le_two lead chain trail
    omega
  have hendQ : (lead : ℚ) + trail ≤ 22 := by exact_mod_cast hend'
  have hidentity := zeroEndedCore_slack_identity (by norm_num : 1 ≤ 11)
    (36 : ℚ) (569 / 15) chain hgapBound (lead := lead) (trail := trail)
  change scalarEnergy 11 36 (569 / 15)
    (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0) = _ at hidentity
  intro K hK
  by_contra hnot
  have hexception := clusterReserve14_exceptional (hmass K hK)
    (cluster_exceptional_mass (hNe K hK) (hmass K hK) hnot) hnot
  have hsum := clusterReserve14_le_sum hNe hmass hK
  norm_num at hcount hfirst hidentity hreserve
  simp only [List.append_assoc] at henergy
  linarith

def regularCutCost14 (u : ℕ) : ℚ :=
  if u ≤ 8 then (1138 / 15) * (10 - u : ℕ) - 144 else 0

def regularCutSum14 (chain : PositiveClusterChain) : ℚ :=
  (chain.gaps.map regularCutCost14).sum

theorem regularCutCost14_nonnegative (u : ℕ) : 0 ≤ regularCutCost14 u := by
  unfold regularCutCost14
  split_ifs with h
  · have hc : (2 : ℚ) ≤ (10 - u : ℕ) := by exact_mod_cast (by omega : 2 ≤ 10 - u)
    linarith
  · rfl

theorem regularCutSum14_nonnegative (chain : PositiveClusterChain) :
    0 ≤ regularCutSum14 chain := by
  unfold regularCutSum14
  apply List.sum_nonneg
  intro x hx
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
  exact regularCutCost14_nonnegative u

theorem regularCutCost14_le_sum {chain : PositiveClusterChain} {u : ℕ}
    (hu : u ∈ chain.gaps) : regularCutCost14 u ≤ regularCutSum14 chain := by
  induction chain with
  | last K => simp [gaps] at hu
  | cons K gap tail ih =>
      have hgap := regularCutCost14_nonnegative gap
      have htail := regularCutSum14_nonnegative tail
      rcases List.mem_cons.mp hu with rfl | hu
      · simp only [regularCutSum14, gaps, List.map_cons, List.sum_cons] at *
        linarith
      · have h := ih hu
        simp only [regularCutSum14, gaps, List.map_cons, List.sum_cons] at *
        linarith

/-- The exact initial-path induction retains the price of every gap <=8.
This is the corrected CP splitting argument; CP is never applied across such a gap. -/
theorem regular_cluster_count14 (chain : PositiveClusterChain)
    (hregular : ∀ K ∈ chain.clusters, K = [2])
    (hpacking : PrefixPacking 11 36 (569 / 15) chain)
    (hgap : ∀ u ∈ chain.gaps, u ≤ 10) :
    4 * (chain.clusters.length : ℚ) - (1138 / 15) * shortGapMass 11 chain +
      regularCutSum14 chain ≤ 4 * firstRegularValue 11 (569 / 15) chain := by
  induction chain with
  | last K =>
      have hK : K = [2] := hregular K (by simp [clusters])
      simp [clusters, shortGapMass, gaps, regularCutSum14,
        firstRegularValue, firstRegularGaps, hK]
  | cons K gap tail ih =>
      have hK : K = [2] := hregular K (by simp [clusters])
      have htailReg : ∀ L ∈ tail.clusters, L = [2] := by
        intro L hL; exact hregular L (by simp [clusters, hL])
      have htailFirst : tail.firstCluster = [2] :=
        htailReg _ tail.firstCluster_mem_clusters
      have htail := ih htailReg hpacking.2 (by
        intro u hu; exact hgap u (by simp [gaps, hu]))
      have htailBound := hpacking.2.first
      have hg := hgap gap (by simp [gaps])
      by_cases h10 : gap = 10
      · have hfirst : firstRegularValue 11 (569 / 15) (.cons K gap tail) =
            1 + firstRegularValue 11 (569 / 15) tail := by
          simp [firstRegularValue, firstRegularGaps, hK, htailFirst, h10]
          ring
        have hcost : regularCutCost14 gap = 0 := by simp [regularCutCost14, h10]
        simp only [clusters, List.length_cons, Nat.cast_add, Nat.cast_one,
          shortGapMass, gaps, List.map_cons, List.sum_cons, regularCutSum14] at *
        rw [hfirst]
        norm_num [h10, hcost] at *
        linarith
      · by_cases h9 : gap = 9
        · have hfirst : firstRegularValue 11 (569 / 15) (.cons K gap tail) =
              1 + firstRegularValue 11 (569 / 15) tail - (569 / 15 : ℚ) / 2 := by
            simp [firstRegularValue, firstRegularGaps, hK, htailFirst, h9]
            ring
          have hcost : regularCutCost14 gap = 0 := by simp [regularCutCost14, h9]
          simp only [clusters, List.length_cons, Nat.cast_add, Nat.cast_one,
            shortGapMass, gaps, List.map_cons, List.sum_cons, regularCutSum14] at *
          rw [hfirst]
          norm_num [h9, hcost] at *
          linarith
        · have hsmall : gap ≤ 8 := by omega
          have hfirst : firstRegularValue 11 (569 / 15) (.cons K gap tail) = 1 := by
            simp [firstRegularValue, firstRegularGaps, hK, htailFirst, h10, h9]
          have hcost : regularCutCost14 gap = (1138 / 15) * (10 - gap : ℕ) - 144 := by
            simp [regularCutCost14, hsmall]
          simp only [clusters, List.length_cons, Nat.cast_add, Nat.cast_one,
            shortGapMass, gaps, List.map_cons, List.sum_cons, regularCutSum14] at *
          rw [hfirst]
          norm_num at *
          linarith

theorem regular_chain14_gap_bound (chain : PositiveClusterChain)
    (hregular : ∀ K ∈ chain.clusters, K = [2])
    (hgap : ∀ u ∈ chain.gaps, u ≤ 11)
    (hmax : NoMaxRegularGap 11 chain) :
    ∀ u ∈ chain.gaps, u ≤ 10 := by
  induction chain with
  | last K => simp [gaps]
  | cons K gap tail ih =>
      have hK := hregular K (by simp [clusters])
      have htailReg : ∀ L ∈ tail.clusters, L = [2] := by
        intro L hL; exact hregular L (by simp [clusters, hL])
      have hfirst := htailReg _ tail.firstCluster_mem_clusters
      have hg := hgap gap (by simp [gaps])
      have hne : gap ≠ 11 := by intro heq; exact hmax.1 heq ⟨hK, hfirst⟩
      have ht := ih htailReg (by
        intro u hu; exact hgap u (by simp [gaps, hu])) hmax.2
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · omega
      · exact ht u hu

theorem regular_chain14_reserves (chain : PositiveClusterChain)
    (hregular : ∀ K ∈ chain.clusters, K = [2]) :
    exceptionalClusterCount chain = 0 ∧ reserveSum 11 36 (569 / 15) chain = 0 := by
  induction chain with
  | last K =>
      have hK := hregular K (by simp [clusters])
      simp [hK, exceptionalClusterCount, reserveSum, clusters]
  | cons K gap tail ih =>
      have hK := hregular K (by simp [clusters])
      have ht := ih (by intro L hL; exact hregular L (by simp [clusters, hL]))
      simp [hK, exceptionalClusterCount, reserveSum, clusters] at *
      exact ht

theorem zeroEndedCore14_endpoint_upper {lead trail : ℕ}
    (chain : PositiveClusterChain)
    (hlegal : IsLegalDeficitSequence 13
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    lead ≤ 11 ∧ trail ≤ 11 := by
  have hrender : chain.render ≠ [] := chain.render_nonempty hNe
  let x := chain.render.head hrender
  have hxhead : x ∈ chain.render := List.head_mem hrender
  have hxhead? : x ∈ chain.render.head? := List.head?_eq_some_head hrender
  have hxpos : 0 < x := chain.render_head_positive hNe hPos x hxhead?
  have hnot : ¬ ∀ y ∈ List.replicate lead 0 ++ chain.render ++
      List.replicate trail 0, y = 0 := by
    intro hall
    have hz := hall x (by simp [hxhead])
    omega
  have hl := legal_zeroInterval_bounds hlegal
    (start := 0) (blockLength := lead) hlead (by simp) (by
      intro j hj
      simp [deficitAt, List.getElem?_append, hj])
  have hr := legal_zeroInterval_bounds hlegal
    (start := lead + chain.render.length) (blockLength := trail)
    htrail (by simp; omega) (by
      intro j hj
      unfold deficitAt
      rw [List.getElem?_append_right (by simp)]
      have hindex : lead + chain.render.length + j -
          (List.replicate lead 0 ++ chain.render).length = j := by simp
      rw [hindex, List.getElem?_eq_getElem (by simpa using hj)]
      simp)
  exact ⟨hl.2 hnot, hr.2 hnot⟩

/-- The remaining scalar slack pays actual shortened gaps and short endpoints. -/
theorem zeroEndedCore14_long_gaps {lead trail : ℕ}
    (chain : PositiveClusterChain)
    (hlegal : IsLegalDeficitSequence 13
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hpacking : ChainPacking 11 36 (569 / 15)
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hGap : ∀ u ∈ chain.gaps, 0 < u)
    (henergy : scalarEnergy 11 36 (569 / 15)
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0) ≤ 1398 / 15) :
    (∀ K ∈ chain.clusters, K = [2]) ∧ 10 ≤ lead ∧ 10 ≤ trail ∧
      (∀ u ∈ chain.gaps, 7 ≤ u) := by
  have hregular := zeroEndedCore14_regular chain hlegal hpacking hlead htrail
    hNe hPos hGap henergy
  have hgapBound : ∀ u ∈ chain.gaps, u ≤ 11 := by
    simpa using internalClusterGaps_le hlegal hNe hPos hGap
  have hpair : StrongCriticalPairBounds 11 chain := by
    simpa using strongCriticalPairBounds_of_legal hlegal hNe hPos hGap
  have hgap10 := regular_chain14_gap_bound chain hregular hgapBound
    (noMaxRegularGap_of_strong (by norm_num) hpair)
  have hpref := prefixPacking_of_chainPacking hpacking (by norm_num) hlead htrail hGap
  have hcount := regular_cluster_count14 chain hregular hpref hgap10
  have hfirst := hpref.first
  have hreserves := regular_chain14_reserves chain hregular
  have hno11 : chain.gaps.count 11 = 0 := by
    apply List.count_eq_zero.mpr
    intro hmem
    have := hgap10 11 hmem
    omega
  have hends := zeroEndedCore14_endpoint_upper chain hlegal hlead htrail hNe hPos
  have hl := hends.1
  have hr := hends.2
  have hlQ : (lead : ℚ) ≤ 11 := by exact_mod_cast hl
  have hrQ : (trail : ℚ) ≤ 11 := by exact_mod_cast hr
  have hidentity := zeroEndedCore_slack_identity (by norm_num : 1 ≤ 11)
    (36 : ℚ) (569 / 15) chain hgapBound (lead := lead) (trail := trail)
  change scalarEnergy 11 36 (569 / 15)
    (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0) = _ at hidentity
  rw [hreserves.1, hreserves.2, hno11] at hidentity
  norm_num at hidentity
  simp only [List.append_assoc] at henergy
  have hpay : regularCutSum14 chain + (1138 / 15 : ℚ) *
      (22 - lead - trail) ≤ 1398 / 15 := by linarith
  have hcuts := regularCutSum14_nonnegative chain
  have hl10 : 10 ≤ lead := by
    by_contra h
    have hl9 : (lead : ℚ) ≤ 9 := by exact_mod_cast (by omega : lead ≤ 9)
    linarith
  have hr10 : 10 ≤ trail := by
    by_contra h
    have hr9 : (trail : ℚ) ≤ 9 := by exact_mod_cast (by omega : trail ≤ 9)
    linarith
  refine ⟨hregular, hl10, hr10, ?_⟩
  intro u hu
  by_contra h
  have hu6 : u ≤ 6 := by omega
  have hcost := regularCutCost14_le_sum hu
  have hshort : (4 : ℚ) ≤ (10 - u : ℕ) := by exact_mod_cast (by omega : 4 ≤ 10 - u)
  simp only [regularCutCost14, if_pos (show u ≤ 8 by omega)] at hcost
  linarith

/-- A literal legal deficit string with full endpoints admits the rigid
decomposition. This is the interface for an actual light segment. -/
theorem deficitString14_rigid {d : List ℕ}
    (hlegal : IsLegalDeficitSequence 13 d)
    (hpacking : ChainPacking 11 36 (569 / 15) d)
    (hhead : d.head? = some 0) (hlast : d.getLast? = some 0)
    (hsum : 0 < d.sum)
    (henergy : scalarEnergy 11 36 (569 / 15) d ≤ 1398 / 15) :
    ∃ dec : PositiveClusterDecomposition d,
      (∀ K ∈ dec.chain.clusters, K = [2]) ∧
        10 ≤ dec.leadingZeros ∧ 10 ≤ dec.trailingZeros ∧
        (∀ u ∈ dec.chain.gaps, 7 ≤ u) := by
  have hpositive : ∃ x ∈ d, 0 < x := by
    by_contra h
    push_neg at h
    have hall : ∀ x ∈ d, x = 0 := by intro x hx; have := h x hx; omega
    have hrep : d = List.replicate d.length 0 :=
      List.eq_replicate_iff.mpr ⟨rfl, hall⟩
    have hz : d.sum = 0 := by rw [hrep]; simp
    omega
  obtain ⟨dec, _⟩ := exists_positiveClusterDecomposition hpositive
  have hrender := dec.chain.render_nonempty dec.cluster_nonempty
  have hlead : 0 < dec.leadingZeros := by
    by_contra h
    have hzero : dec.leadingZeros = 0 := by omega
    have hz : 0 ∈ dec.chain.render.head? := by
      have hh := congrArg List.head? dec.rebuild
      rw [hhead] at hh
      simpa [hzero, hrender] using hh.symm
    exact (Nat.lt_irrefl 0) (dec.chain.render_head_positive
      dec.cluster_nonempty dec.cluster_positive 0 hz)
  have htrail : 0 < dec.trailingZeros := by
    by_contra h
    have hzero : dec.trailingZeros = 0 := by omega
    have hz : 0 ∈ dec.chain.render.getLast? := by
      have hh := congrArg List.getLast? dec.rebuild
      rw [hlast] at hh
      simpa [hzero, List.getLast?_eq_getLast_of_ne_nil hrender] using hh.symm
    exact (Nat.lt_irrefl 0) (render_last_positive dec.chain
      dec.cluster_nonempty dec.cluster_positive 0 hz)
  refine ⟨dec, ?_⟩
  exact zeroEndedCore14_long_gaps dec.chain
    (by rw [← dec.rebuild]; exact hlegal)
    (by rw [← dec.rebuild]; exact hpacking)
    hlead htrail dec.cluster_nonempty dec.cluster_positive dec.gap_positive
    (by rw [← dec.rebuild]; exact henergy)

end SuperpermutationLowerBound.Refinement
