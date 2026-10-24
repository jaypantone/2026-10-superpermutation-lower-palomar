module

public import SuperpermutationLowerBound.Refinement.ChainPackingCounts

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PositiveClusterChain

theorem positive_length_le_sum {K : List ℕ}
    (hpos : ∀ x ∈ K, 0 < x) : K.length ≤ K.sum := by
  induction K with
  | nil => simp
  | cons x K ih =>
      have hx := hpos x (by simp)
      have htail := ih (by intro y hy; exact hpos y (by simp [hy]))
      simp only [List.length_cons, List.sum_cons]
      omega

theorem positive_member_length_le_sum {K : List ℕ} {x : ℕ}
    (hpos : ∀ y ∈ K, 0 < y) (hx : x ∈ K) : x + K.length ≤ K.sum + 1 := by
  induction K with
  | nil => simp at hx
  | cons y K ih =>
      have hy := hpos y (by simp)
      have htailPos : ∀ z ∈ K, 0 < z := by intro z hz; exact hpos z (by simp [hz])
      rcases List.mem_cons.mp hx with rfl | hx
      · have htail := positive_length_le_sum htailPos
        simp only [List.length_cons, List.sum_cons]
        omega
      · have htail := ih htailPos hx
        simp only [List.length_cons, List.sum_cons]
        omega

/-- The strengthened R3 bound includes the lengths of both clusters. -/
def StrongCriticalPairBounds (a : ℕ) : PositiveClusterChain → Prop
  | .last _ => True
  | .cons K gap tail =>
      (gap = a → a + K.length + tail.firstCluster.length ≤ K.sum + tail.firstCluster.sum) ∧
        StrongCriticalPairBounds a tail

private theorem deficitAt_before_cluster_gap {leading gap : ℕ}
    {K rest : List ℕ} (hKne : K ≠ []) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ rest)))
      (leading + K.length - 1) = K.getLast hKne := by
  have hKlen : 0 < K.length := by
    cases K with
    | nil => contradiction
    | cons a tail => simp
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length - 1 - leading = K.length - 1 := by omega
  rw [hindex, ← List.getLast?_eq_getElem?]
  rw [List.getLast?_eq_getLast_of_ne_nil hKne]
  rfl

private theorem deficitAt_after_cluster_gap {leading gap : ℕ}
    {K rest suffix : List ℕ} (hrest : rest ≠ []) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ (rest ++ suffix))))
      (leading + K.length + gap) = rest.head hrest := by
  have hrestLen : 0 < rest.length := by
    cases rest with
    | nil => contradiction
    | cons a tail => simp
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length + gap - leading - K.length - gap = 0 := by omega
  rw [hindex]
  cases rest with
  | nil => contradiction
  | cons a tail => rfl

private theorem deficitAt_inside_cluster_gap {leading gap j : ℕ}
    {K rest : List ℕ} (hj : j < gap) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ rest))) (leading + K.length + j) = 0 := by
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length + j - leading - K.length = j := by omega
  rw [hindex]
  rw [List.getElem?_eq_getElem (by simp; exact hj)]
  simp

private theorem internalClusterGap_isMaximal {n leading trailing gap : ℕ}
    {K : List ℕ} {tail : PositiveClusterChain}
    (hKne : K ≠ []) (hKpos : ∀ x ∈ K, 0 < x)
    (htailNe : ∀ L ∈ tail.clusters, L ≠ [])
    (htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x)
    (hgap : 0 < gap) :
    IsMaximalZeroBlock
      (List.replicate leading 0 ++
        (K ++ (List.replicate gap 0 ++
          (tail.render ++ List.replicate trailing 0))))
      (leading + K.length) gap := by
  have htailRender := tail.render_nonempty htailNe
  have hleftValue := deficitAt_before_cluster_gap
    (leading := leading) (gap := gap) (rest := tail.render ++
      List.replicate trailing 0) hKne
  have hrightValue := deficitAt_after_cluster_gap
    (leading := leading) (gap := gap) (K := K) (rest := tail.render)
      (suffix := List.replicate trailing 0) htailRender
  refine ⟨hgap, ?_, ?_, ?_, ?_⟩
  · simp
    omega
  · intro j hj
    exact deficitAt_inside_cluster_gap (leading := leading) (gap := gap)
      (K := K) (rest := tail.render ++ List.replicate trailing 0) hj
  · right
    refine ⟨by
      have hKlen : 0 < K.length := by
        have hKlen0 : K.length ≠ 0 := by
          intro hzero
          exact hKne (List.eq_nil_of_length_eq_zero hzero)
        omega
      omega, ?_⟩
    rw [hleftValue]
    exact hKpos _ (List.getLast_mem hKne)
  · right
    refine ⟨by
      have htailLen : 0 < tail.render.length := by
        have hne : tail.render.length ≠ 0 := by
          intro hzero
          exact htailRender (List.eq_nil_of_length_eq_zero hzero)
        omega
      simp only [List.length_append, List.length_replicate]
      omega, ?_⟩
    rw [hrightValue]
    exact tail.render_head_positive htailNe htailPos _ (List.head_mem_head? _)

theorem strongCriticalPairBounds_of_legal {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    StrongCriticalPairBounds (n - 2) chain := by
  induction chain generalizing leading with
  | last K => trivial
  | cons K gap tail ih =>
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKpos : ∀ x ∈ K, 0 < x := hclusterPos K
        (by simp [PositiveClusterChain.clusters])
      have hgap : 0 < gap := hgapPos gap (by simp [PositiveClusterChain.gaps])
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL
        exact hclusterNe L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL
        exact hclusterPos L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgapPos u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
      constructor
      · intro hcritical
        have hblock := internalClusterGap_isMaximal
          (n := n) (leading := leading) (trailing := trailing)
          hKne hKpos htailNe htailPos hgap
        have hleft : 0 < leading + K.length := by
          have hKlen : 0 < K.length := by cases K <;> simp_all
          omega
        have hright : leading + K.length + (n - 2) <
            (List.replicate leading 0 ++
              (K ++ (List.replicate (n - 2) 0 ++
                (tail.render ++ List.replicate trailing 0)))).length := by
          have htailRender := tail.render_nonempty htailNe
          have htailLen : 0 < tail.render.length := by
            have hne : tail.render.length ≠ 0 := by
              intro hzero
              exact htailRender (List.eq_nil_of_length_eq_zero hzero)
            omega
          simp only [List.length_append, List.length_replicate]
          omega
        have hlegalCritical : IsLegalDeficitSequence n
            (List.replicate leading 0 ++
              (K ++ (List.replicate (n - 2) 0 ++
                (tail.render ++ List.replicate trailing 0)))) := by
          simpa [PositiveClusterChain.render, hcritical, List.append_assoc] using hlegal
        have hrule := hlegalCritical.rule3 (leading + K.length)
          (by simpa [hcritical] using hblock) hleft hright
        have hleftEq := deficitAt_before_cluster_gap
          (leading := leading) (gap := n - 2)
          (rest := tail.render ++ List.replicate trailing 0) hKne
        have htailRender := tail.render_nonempty htailNe
        have hrightEq := deficitAt_after_cluster_gap
          (leading := leading) (gap := n - 2) (K := K)
          (rest := tail.render) (suffix := List.replicate trailing 0) htailRender
        rw [hleftEq, hrightEq] at hrule
        have hleftLe : K.getLast hKne + K.length ≤ K.sum + 1 :=
          positive_member_length_le_sum hKpos (List.getLast_mem hKne)
        have hfirstNe : tail.firstCluster ≠ [] :=
          htailNe _ tail.firstCluster_mem_clusters
        have hheadEq := tail.render_head_eq_firstCluster_head hfirstNe htailRender
        rw [hheadEq] at hrule
        have hrightLe : tail.firstCluster.head hfirstNe + tail.firstCluster.length ≤
            tail.firstCluster.sum + 1 := positive_member_length_le_sum
              (htailPos _ tail.firstCluster_mem_clusters) (List.head_mem hfirstNe)
        have hn := hlegal.six_le
        omega
      · let suffix := List.replicate gap 0 ++ tail.render ++
            List.replicate trailing 0
        have hlegalAppend : IsLegalDeficitSequence n
            ((List.replicate leading 0 ++ K) ++ suffix) := by
          simpa [suffix, PositiveClusterChain.render, List.append_assoc] using hlegal
        have hsuffixNe : suffix ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp [suffix] at this
          omega
        have hlegalTail := hlegalAppend.suffix_of_append hsuffixNe
        exact ih (leading := gap) (by simpa [suffix] using hlegalTail)
          htailNe htailPos htailGap


theorem singleCluster_mass {n lead trail : ℕ} {K : List ℕ}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate lead 0 ++ K ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hKne : K ≠ []) (hKpos : ∀ x ∈ K, 0 < x) :
    K.length + 1 ≤ K.sum := by
  have h := cluster_length_charge (chain := .last K)
    (by simpa [render] using hlegal)
    (by simpa [clusters] using hKne)
    (by simpa [clusters] using hKpos) (by simp [gaps])
  simpa [clusters, clusterExceptionCount, leftClusterException, rightClusterException,
    Nat.ne_of_gt hlead, Nat.ne_of_gt htrail] using h

theorem clusterMassBounds_of_legal {n lead trail : ℕ} {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hlead : 0 < lead) (htrail : 0 < trail)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hGap : ∀ u ∈ chain.gaps, 0 < u) :
    ∀ K ∈ chain.clusters, K.length + 1 ≤ K.sum := by
  induction chain generalizing lead with
  | last K =>
      intro L hL
      have hLK : L = K := by simpa [clusters] using hL
      subst L
      exact singleCluster_mass (by simpa [render] using hlegal) hlead htrail
        (hNe K (by simp [clusters])) (hPos K (by simp [clusters]))
  | cons K gap tail ih =>
      have hgap := hGap gap (by simp [gaps])
      have hKne := hNe K (by simp [clusters])
      have hKpos := hPos K (by simp [clusters])
      have hfirstLegal : IsLegalDeficitSequence n
          (List.replicate lead 0 ++ K ++ List.replicate gap 0) := by
        apply legal_factor hlegal (before := [])
          (after := tail.render ++ List.replicate trail 0)
        · simp [render, List.append_assoc]
        · simp [hKne]
      have hfirstMass := singleCluster_mass hfirstLegal hlead hgap hKne hKpos
      have htailLegal : IsLegalDeficitSequence n
          (List.replicate gap 0 ++ tail.render ++ List.replicate trail 0) := by
        apply legal_factor hlegal (before := List.replicate lead 0 ++ K) (after := [])
        · simp [render, List.append_assoc]
        · simp [Nat.ne_of_gt hgap]
      have htailMass := ih htailLegal hgap
        (by intro L hL; exact hNe L (by simp [clusters, hL]))
        (by intro L hL; exact hPos L (by simp [clusters, hL]))
        (by intro u hu; exact hGap u (by simp [gaps, hu]))
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hfirstMass
      · exact htailMass L hL

theorem cluster_eq_two_of_sum_two {K : List ℕ}
    (hNe : K ≠ []) (hmass : K.length + 1 ≤ K.sum) (hsum : K.sum = 2) :
    K = [2] := by
  cases K with
  | nil => contradiction
  | cons x tail =>
      have hlen : tail.length = 0 := by simp only [List.length_cons] at hmass; omega
      have hnil : tail = [] := List.eq_nil_of_length_eq_zero hlen
      subst tail
      simpa using hsum

theorem cluster_exceptional_mass {K : List ℕ}
    (hNe : K ≠ []) (hmass : K.length + 1 ≤ K.sum) (hnot : K ≠ [2]) :
    3 ≤ K.sum := by
  have hlen : 0 < K.length := List.length_pos_iff.mpr hNe
  by_contra h
  exact hnot (cluster_eq_two_of_sum_two hNe hmass (by omega))

theorem noMaxRegularGap_of_strong {a : ℕ} (ha : 4 ≤ a)
    {chain : PositiveClusterChain} (h : StrongCriticalPairBounds a chain) :
    NoMaxRegularGap a chain := by
  induction chain with
  | last K => trivial
  | cons K gap tail ih =>
      refine ⟨?_, ih h.2⟩
      intro hgap hboth
      have hb := h.1 hgap
      simp [hboth.1, hboth.2] at hb
      omega

def reserveSum (a : ℕ) (p t : ℚ) (chain : PositiveClusterChain) : ℚ :=
  (chain.clusters.map (clusterReserve a p t)).sum

def lastCluster : PositiveClusterChain → List ℕ
  | .last K => K
  | .cons _ _ tail => lastCluster tail

theorem lastCluster_mem (chain : PositiveClusterChain) : lastCluster chain ∈ chain.clusters := by
  induction chain with
  | last K => simp [lastCluster, clusters]
  | cons K gap tail ih => simp [lastCluster, clusters, ih]

/-- The path incidence estimate keeps both unused endpoint reserves. It is
the degree-two identity with every unselected edge contribution nonnegative. -/
theorem reserve_degree_two_bound {a : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (chain : PositiveClusterChain)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hMass : ∀ K ∈ chain.clusters, K.length + 1 ≤ K.sum)
    (hPair : StrongCriticalPairBounds a chain) :
    4 * t * (chain.gaps.count a : ℚ) + clusterReserve a p t chain.firstCluster +
      clusterReserve a p t (lastCluster chain) ≤ 2 * reserveSum a p t chain := by
  induction chain with
  | last K => simp [gaps, firstCluster, lastCluster, reserveSum, clusters]; ring_nf; rfl
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
      have hKpos := clusterReserve_nonnegative hp ht hmargin hKmass
        (cluster_exceptional_mass hKne hKmass)
      have hLpos := clusterReserve_nonnegative hp ht hmargin hLmass
        (cluster_exceptional_mass hLne hLmass)
      by_cases hgap : gap = a
      · have hpay := clusterReserve_maxZeroGap ha hp ht hmargin
          (List.length_pos_iff.mpr hKne) (List.length_pos_iff.mpr hLne) (hPair.1 hgap)
        simp [gaps, hgap, lastCluster, reserveSum, clusters] at *
        linarith
      · simp [gaps, hgap, lastCluster, reserveSum, clusters] at *
        linarith

end SuperpermutationLowerBound.Refinement
