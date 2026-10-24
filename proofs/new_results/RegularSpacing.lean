module

public import new_results.ScalarRigidity

@[expose] public section

namespace SuperpermutationLowerBound.Refinement
open PositiveClusterChain

/-- A literal zero/two list in which every two has two zero neighbors on each side. -/
def RegularSpacing (d : List ℕ) : Prop :=
  (∀ i, i < d.length → deficitAt d i = 0 ∨ deficitAt d i = 2) ∧
  (∀ i, i < d.length → deficitAt d i = 2 →
    2 ≤ i ∧ i + 2 < d.length ∧
    deficitAt d (i - 1) = 0 ∧ deficitAt d (i - 2) = 0 ∧
    deficitAt d (i + 1) = 0 ∧ deficitAt d (i + 2) = 0)

private theorem deficitAt_zero_prefix (a i : ℕ) (tail : List ℕ) (hi : i < a) :
    deficitAt (List.replicate a 0 ++ tail) i = 0 := by
  simp [deficitAt, List.getElem?_append, hi]

private theorem deficitAt_after_zero_two (a j : ℕ) (tail : List ℕ) :
    deficitAt (List.replicate a 0 ++ 2 :: tail) (a + 1 + j) = deficitAt tail j := by
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rw [show a + 1 + j - a = j + 1 by omega]
  rfl

private theorem spacing_replicate (a : ℕ) : RegularSpacing (List.replicate a 0) := by
  constructor
  · intro i hi
    left
    have hi' : i < a := by simpa using hi
    simp [deficitAt, hi']
  · intro i hi ht
    have hi' : i < a := by simpa using hi
    simp [deficitAt, hi'] at ht

private theorem spacing_prepend (a : ℕ) (tail : List ℕ) (ha : 2 ≤ a)
    (ht : RegularSpacing tail) (hlen : 2 ≤ tail.length)
    (ht0 : deficitAt tail 0 = 0) (ht1 : deficitAt tail 1 = 0) :
    RegularSpacing (List.replicate a 0 ++ 2 :: tail) := by
  let d := List.replicate a 0 ++ 2 :: tail
  have hdlen : d.length = a + 1 + tail.length := by simp [d]; omega
  have hpre : ∀ i, i < a → deficitAt d i = 0 := by
    intro i hi
    exact deficitAt_zero_prefix a i (2 :: tail) hi
  have hat : deficitAt d a = 2 := by simp [d, deficitAt, List.getElem?_append]
  have hpost : ∀ i, a + 1 ≤ i → deficitAt d i = deficitAt tail (i - (a + 1)) := by
    intro i hi
    have he : i = a + 1 + (i - (a + 1)) := by omega
    rw [he]
    simpa using deficitAt_after_zero_two a (i - (a + 1)) tail
  change RegularSpacing d
  constructor
  · intro i hi
    rcases lt_trichotomy i a with hia | rfl | hai
    · exact Or.inl (hpre i hia)
    · exact Or.inr hat
    · have hj : i - (a + 1) < tail.length := by omega
      rw [hpost i (by omega)]
      exact ht.1 _ hj
  · intro i hi htwo
    rcases lt_trichotomy i a with hia | rfl | hai
    · have hz := hpre i hia
      omega
    · refine ⟨ha, by omega, hpre _ (by omega), hpre _ (by omega), ?_, ?_⟩
      · rw [hpost _ (by omega)]
        simpa using ht0
      · rw [hpost _ (by omega)]
        simpa using ht1
    · let j := i - (a + 1)
      have hj : j < tail.length := by dsimp [j]; omega
      have hjtwo : deficitAt tail j = 2 := by
        simpa only [j, hpost i (by omega)] using htwo
      obtain ⟨hj2, hjend, hm1, hm2, hp1, hp2⟩ := ht.2 j hj hjtwo
      refine ⟨by dsimp [j] at hj2; omega, by dsimp [j] at hjend; omega, ?_, ?_, ?_, ?_⟩
      · rw [hpost _ (by dsimp [j] at hj2; omega)]
        have he : i - 1 - (a + 1) = j - 1 := by dsimp [j]; omega
        rw [he]
        exact hm1
      · rw [hpost _ (by dsimp [j] at hj2; omega)]
        have he : i - 2 - (a + 1) = j - 2 := by dsimp [j]; omega
        rw [he]
        exact hm2
      · rw [hpost _ (by omega)]
        have he : i + 1 - (a + 1) = j + 1 := by dsimp [j]; omega
        rw [he]
        exact hp1
      · rw [hpost _ (by omega)]
        have he : i + 2 - (a + 1) = j + 2 := by dsimp [j]; omega
        rw [he]
        exact hp2

/-- Structural induction retains the endpoint zero blocks at every cut. -/
theorem regularSpacing_render (chain : PositiveClusterChain)
    (hregular : ∀ K ∈ chain.clusters, K = [2])
    (hgaps : ∀ u ∈ chain.gaps, 2 ≤ u)
    (lead trail : ℕ) (hlead : 2 ≤ lead) (htrail : 2 ≤ trail) :
    RegularSpacing (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0) := by
  induction chain generalizing lead with
  | last K =>
      have hK := hregular K (by simp [clusters])
      subst K
      have h := spacing_prepend lead (List.replicate trail 0) hlead
        (spacing_replicate trail) (by simpa using htrail)
        (by simp [deficitAt, show 0 < trail by omega])
        (by simp [deficitAt, show 1 < trail by omega])
      simpa [render, List.append_assoc] using h
  | cons K gap tail ih =>
      have hK := hregular K (by simp [clusters])
      subst K
      have hgap : 2 ≤ gap := hgaps gap (by simp [gaps])
      have hr : ∀ J ∈ tail.clusters, J = [2] := by
        intro J hJ
        exact hregular J (by simp [clusters, hJ])
      have hg : ∀ u ∈ tail.gaps, 2 ≤ u := by
        intro u hu
        exact hgaps u (by simp [gaps, hu])
      let rest := List.replicate gap 0 ++ tail.render ++ List.replicate trail 0
      have hrest : RegularSpacing rest := ih hr hg gap hgap
      have hlen : 2 ≤ rest.length := by simp [rest]; omega
      have h0 : deficitAt rest 0 = 0 := by
        simpa only [rest, List.append_assoc] using
          deficitAt_zero_prefix gap 0 (tail.render ++ List.replicate trail 0) (by omega)
      have h1 : deficitAt rest 1 = 0 := by
        simpa only [rest, List.append_assoc] using
          deficitAt_zero_prefix gap 1 (tail.render ++ List.replicate trail 0) (by omega)
      have h := spacing_prepend lead rest hlead hrest hlen h0 h1
      simpa [rest, render, List.append_assoc] using h

/-- The exact index interface consumed by the pivot-rigidity proof. -/
theorem regularSpacing {d : List ℕ} (dec : PositiveClusterDecomposition d)
    (hregular : ∀ K ∈ dec.chain.clusters, K = [2])
    (hlead : 2 ≤ dec.leadingZeros) (htrail : 2 ≤ dec.trailingZeros)
    (hgaps : ∀ u ∈ dec.chain.gaps, 2 ≤ u) :
    (∀ i, i < d.length → deficitAt d i = 0 ∨ deficitAt d i = 2) ∧
    (∀ i, i < d.length → deficitAt d i = 2 →
      2 ≤ i ∧ i + 2 < d.length ∧
      deficitAt d (i - 1) = 0 ∧ deficitAt d (i - 2) = 0 ∧
      deficitAt d (i + 1) = 0 ∧ deficitAt d (i + 2) = 0) := by
  rw [dec.rebuild]
  exact regularSpacing_render dec.chain hregular hgaps
    dec.leadingZeros dec.trailingZeros hlead htrail

end SuperpermutationLowerBound.Refinement
