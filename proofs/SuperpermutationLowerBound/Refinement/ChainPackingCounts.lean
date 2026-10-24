module

public import SuperpermutationLowerBound.Refinement.ChainPacking
public import SuperpermutationLowerBound.Refinement.ScalarAlgebra

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PositiveClusterChain

@[simp] theorem firstCluster_last (K : List ℕ) : (.last K : PositiveClusterChain).firstCluster = K := rfl
@[simp] theorem firstCluster_cons (K : List ℕ) (g : ℕ) (c : PositiveClusterChain) :
    (.cons K g c : PositiveClusterChain).firstCluster = K := rfl

/-- The gaps in the initial path of regular clusters. This is used only
when the first cluster is `[2]`; no numerical property is stored here. -/
def firstRegularGaps (a : ℕ) : PositiveClusterChain → List ℕ
  | .last _ => []
  | .cons _ gap tail =>
      if tail.firstCluster = [2] ∧ (gap = a - 1 ∨ gap = a - 2) then
        gap :: firstRegularGaps a tail else []

def firstRegularValue (a : ℕ) (t : ℚ) (chain : PositiveClusterChain) : ℚ :=
  if chain.firstCluster = [2] then
    ((firstRegularGaps a chain).length : ℚ) + 1 -
      t / 2 * ((firstRegularGaps a chain).count (a - 2) : ℚ)
  else 0

def PrefixPacking (a : ℕ) (p t : ℚ) : PositiveClusterChain → Prop
  | .last K => firstRegularValue a t (.last K) ≤ p
  | .cons K gap tail =>
      firstRegularValue a t (.cons K gap tail) ≤ p ∧ PrefixPacking a p t tail

theorem PrefixPacking.first {a : ℕ} {p t : ℚ} {c : PositiveClusterChain}
    (h : PrefixPacking a p t c) : firstRegularValue a t c ≤ p := by
  cases c with
  | last K => exact h
  | cons K g tail => exact h.1

def exceptionalClusterCount (chain : PositiveClusterChain) : ℕ :=
  (chain.clusters.filter (fun K => K ≠ [2])).length

def shortGapMass (a : ℕ) (chain : PositiveClusterChain) : ℕ :=
  (chain.gaps.map (fun gap => a - 1 - gap)).sum

theorem firstRegularGaps_allowed (a : ℕ) (chain : PositiveClusterChain) :
    ∀ gap ∈ firstRegularGaps a chain, gap = a - 1 ∨ gap = a - 2 := by
  induction chain with
  | last K => simp [firstRegularGaps]
  | cons K gap tail ih =>
      simp only [firstRegularGaps]
      split_ifs with h
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact h.2
        · exact ih u hu
      · simp

theorem firstRegularGaps_prefix {a trail : ℕ} {chain : PositiveClusterChain}
    (hfirst : chain.firstCluster = [2])
    (hgap : ∀ u ∈ chain.gaps, 0 < u) (htrail : 0 < trail) :
    ∃ post : List ℕ, chain.render ++ List.replicate trail 0 =
      regularPath (firstRegularGaps a chain) ++ 0 :: post := by
  induction chain with
  | last K =>
      have hK : K = [2] := hfirst
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : trail ≠ 0)
      exact ⟨List.replicate r 0, by simp [render, hK, firstRegularGaps, regularPath,
        List.replicate_succ]⟩
  | cons K gap tail ih =>
      have hK : K = [2] := hfirst
      have hgapPos := hgap gap (by simp [gaps])
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgap u (by simp [gaps, hu])
      by_cases hjoin : tail.firstCluster = [2] ∧ (gap = a - 1 ∨ gap = a - 2)
      · obtain ⟨post, hp⟩ := ih hjoin.1 htailGap
        refine ⟨post, ?_⟩
        simpa [render, hK, firstRegularGaps, hjoin, regularPath, List.append_assoc]
          using hp
      · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : gap ≠ 0)
        refine ⟨List.replicate r 0 ++ tail.render ++ List.replicate trail 0, ?_⟩
        simp only [firstRegularGaps, if_neg hjoin, regularPath]
        simp [render, hK, hr, List.replicate_succ, List.append_assoc]

theorem firstRegularValue_le_of_chainPacking {a lead trail : ℕ} {p t : ℚ}
    {chain : PositiveClusterChain}
    (hpacking : ChainPacking a p t
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hp : 0 ≤ p) (hlead : 0 < lead) (htrail : 0 < trail)
    (hgap : ∀ u ∈ chain.gaps, 0 < u) :
    firstRegularValue a t chain ≤ p := by
  by_cases hfirst : chain.firstCluster = [2]
  · obtain ⟨post, hpost⟩ := firstRegularGaps_prefix (a := a) hfirst hgap htrail
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : lead ≠ 0)
    have h := hpacking (firstRegularGaps a chain) (firstRegularGaps_allowed a chain)
      (List.replicate r 0) post (by
        rw [List.append_assoc, hpost, hr]
        rw [show List.replicate r.succ 0 = List.replicate r 0 ++ [0] by
          rw [show r.succ = r + 1 from rfl, List.replicate_add]; rfl]
        simp [List.append_assoc])
    simp only [firstRegularValue, if_pos hfirst]
    linarith
  · simpa [firstRegularValue, hfirst] using hp

theorem prefixPacking_of_chainPacking {a lead trail : ℕ} {p t : ℚ}
    {chain : PositiveClusterChain}
    (hpacking : ChainPacking a p t
      (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0))
    (hp : 0 ≤ p) (hlead : 0 < lead) (htrail : 0 < trail)
    (hgap : ∀ u ∈ chain.gaps, 0 < u) :
    PrefixPacking a p t chain := by
  induction chain generalizing lead with
  | last K =>
      exact firstRegularValue_le_of_chainPacking hpacking hp hlead htrail hgap
  | cons K gap tail ih =>
      refine ⟨firstRegularValue_le_of_chainPacking hpacking hp hlead htrail hgap, ?_⟩
      have htailPacking : ChainPacking a p t
          (List.replicate gap 0 ++ tail.render ++ List.replicate trail 0) := by
        apply hpacking.factor (before := List.replicate lead 0 ++ K) (after := [])
        simp [render, List.append_assoc]
      exact ih htailPacking (hgap gap (by simp [gaps])) (by
        intro u hu
        exact hgap u (by simp [gaps, hu]))

def NoMaxRegularGap (a : ℕ) : PositiveClusterChain → Prop
  | .last _ => True
  | .cons K gap tail =>
      (gap = a → ¬ (K = [2] ∧ tail.firstCluster = [2])) ∧ NoMaxRegularGap a tail

/-- Induction with the exact initial regular-path value replaces a separate
graph-component count. A nonregular first cluster has nonpositive energy;
a short cut pays for the next path because `p ≤ t`. -/
theorem cluster_count_with_initial_value {a : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (hpt : p ≤ t)
    (chain : PositiveClusterChain)
    (hpacking : PrefixPacking a p t chain)
    (hgap : ∀ u ∈ chain.gaps, u ≤ a)
    (hmax : NoMaxRegularGap a chain) :
    4 * (chain.clusters.length : ℚ) -
      4 * (p + 1) * exceptionalClusterCount chain - 2 * t * shortGapMass a chain ≤
      4 * firstRegularValue a t chain := by
  have ht : 0 ≤ t := hp.trans hpt
  induction chain with
  | last K =>
      by_cases hK : K = [2]
      · simp [clusters, exceptionalClusterCount, shortGapMass, gaps,
          firstRegularValue, firstCluster_cons, firstCluster_last, firstRegularGaps, hK]
      · simp [clusters, exceptionalClusterCount, shortGapMass, gaps,
          firstRegularValue, firstCluster_cons, firstCluster_last, firstRegularGaps, hK]
        linarith
  | cons K gap tail ih =>
      have htail := ih hpacking.2 (by
        intro u hu
        exact hgap u (by simp [gaps, hu])) hmax.2
      have htailP : firstRegularValue a t tail ≤ p := by
        exact hpacking.2.first
      have hg := hgap gap (by simp [gaps])
      have hshort : 0 ≤ (a - 1 - gap : ℕ) := Nat.zero_le _
      have hshortQ : (0 : ℚ) ≤ (a - 1 - gap : ℕ) := by positivity
      have hshortCost := mul_nonneg ht hshortQ
      by_cases hK : K = [2]
      · by_cases hjoin : tail.firstCluster = [2] ∧ (gap = a - 1 ∨ gap = a - 2)
        · have hfirst : firstRegularValue a t (.cons K gap tail) =
              1 + firstRegularValue a t tail - t / 2 * (a - 1 - gap : ℕ) := by
            rcases hjoin.2 with hgap1 | hgap2
            · have hne : a - 1 ≠ a - 2 := by omega
              simp [firstRegularValue, firstCluster_cons, firstCluster_last, hK, firstRegularGaps, hjoin,
                hjoin.1, hgap1, hne]
              ring
            · have heq : a - 1 - gap = 1 := by omega
              have heq' : a - 1 - (a - 2) = 1 := by omega
              simp [firstRegularValue, firstCluster_cons, firstCluster_last, hK, firstRegularGaps, hjoin,
                hjoin.1, hgap2, heq, heq']
              ring
          simp only [clusters, List.length_cons, exceptionalClusterCount,
            List.filter_cons, hK, ne_eq, not_true_eq_false, decide_false,
            Bool.false_eq_true, ↓reduceIte, shortGapMass, gaps, List.map_cons,
            List.sum_cons, Nat.cast_add, Nat.cast_one] at *
          rw [hfirst]
          linarith
        · have hfirst : firstRegularValue a t (.cons K gap tail) = 1 := by
            simp [firstRegularValue, firstCluster_cons, firstCluster_last, hK, firstRegularGaps, hjoin]
          by_cases htailReg : tail.firstCluster = [2]
          · have hga : gap ≠ a := by
              intro hga
              exact hmax.1 hga ⟨hK, htailReg⟩
            have hsmall : 2 ≤ a - 1 - gap := by
              have hn1 : gap ≠ a - 1 := by intro h; exact hjoin ⟨htailReg, Or.inl h⟩
              have hn2 : gap ≠ a - 2 := by intro h; exact hjoin ⟨htailReg, Or.inr h⟩
              omega
            have hsmallQ : (2 : ℚ) ≤ (a - 1 - gap : ℕ) := by exact_mod_cast hsmall
            have hpay := mul_nonneg ht (sub_nonneg.mpr hsmallQ)
            simp [clusters, exceptionalClusterCount, shortGapMass, gaps, hK,
              hfirst] at *
            nlinarith
          · have hzero : firstRegularValue a t tail = 0 := by
              simp [firstRegularValue, htailReg]
            simp [clusters, exceptionalClusterCount, shortGapMass, gaps, hK,
              hfirst] at *
            nlinarith
      · have hfirst : firstRegularValue a t (.cons K gap tail) = 0 := by
          simp [firstRegularValue, firstCluster_cons, firstCluster_last, hK]
        simp [clusters, exceptionalClusterCount, shortGapMass, gaps, hK,
          hfirst] at *
        nlinarith

end SuperpermutationLowerBound.Refinement
