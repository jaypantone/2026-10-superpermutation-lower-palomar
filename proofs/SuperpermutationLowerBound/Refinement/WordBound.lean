module

public import RefinedLowerChallenge
public import SuperpermutationLowerBound.Refinement.Parameters
public import SuperpermutationLowerBound.Refinement.ScalarSequence
public import SuperpermutationLowerBound.Refinement.ForestAssembly
public import SuperpermutationLowerBound.Section11.MainBound
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! The passage from hereditary geometric chain packing to the exact bound on
arbitrary superpermutation words. The geometric hypothesis is discharged in
the final theorem; this module keeps the scalar and forest interfaces explicit. -/

namespace SuperpermutationLowerBound.Refinement

theorem scalar_affine_of_chainPacking {n : ℕ} (hn : 7 ≤ n) {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hpacking : ChainPacking (n - 2) (period n) (chainAllowance n) d) :
    ListAffineBound (scalarDelta n) (scalarBeta n) d := by
  have hn2 : n - 2 + 2 = n := by omega
  have hcast : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have hlam : chainLambda (n - 2) (effectiveAllowance n) = scalarLambda n := by
    simp [chainLambda, scalarLambda, hcast]
  have hB : chainIntercept (n - 2) (period n) (effectiveAllowance n) =
      scalarInterceptNumerator n := by
    simp only [chainIntercept, scalarInterceptNumerator, hcast]
    ring
  have hmargin : 4 * (period n : ℚ) + 6 ≤
      effectiveAllowance n * (((n - 2 : ℕ) : ℚ) - 2) := by
    simpa only [hcast, sub_sub, show (2:ℚ)+2=4 by norm_num] using effectiveAllowance_margin hn
  intro i j
  have h := deficit_factor_affine_bound (a := n - 2) (by omega)
    (by positivity : (0 : ℚ) ≤ period n) (period_le_effectiveAllowance hn)
    (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 2) (effectiveAllowance_ge_two hn))
    hmargin (by simpa only [hn2] using hlegal)
    (hpacking.mono (chainAllowance_le_effectiveAllowance n)) i j
  simpa only [hlam, hB, scalarDelta, scalarBeta] using h

theorem hereditary_of_chainPacking {k : ℕ} (hk : 8 ≤ k)
    (H : ∀ (p : OverlapPath k) (hp : IsBlockAligned p)
      (s : BlockAlignedLightSegment (by omega : 7 ≤ k) p hp),
      ChainPacking (k - 1 - 2) (period (k - 1)) (chainAllowance (k - 1))
        s.deficitString) :
    HereditarySegmentBound (by omega : 7 ≤ k) (scalarDelta (k - 1))
      (scalarBeta (k - 1)) := by
  intro p hp s
  exact scalar_affine_of_chainPacking (by omega) s.deficitString_legal (H p hp s)

theorem scalar_denominator_pos {n : ℕ} (hn : 7 ≤ n) :
    0 < (n : ℚ) * scalarLambda n - 2 * effectiveAllowance n := by
  have hlam := scalarLambda_pos hn
  have hδ := (scalar_parameters hn).2.1
  have hnq : (7 : ℚ) ≤ n := by exact_mod_cast hn
  have h : 0 < ((n : ℚ) - scalarDelta n) * scalarLambda n :=
    mul_pos (by linarith) hlam
  rw [sub_mul, scalarDelta, div_mul_cancel₀ _ (ne_of_gt hlam)] at h
  exact h

theorem scalar_quotient_eq {n : ℕ} (hn : 7 ≤ n) (T : ℚ) :
    (scalarLambda n * T - scalarInterceptNumerator n) /
      ((n : ℚ) * scalarLambda n - 2 * effectiveAllowance n) =
    (T - scalarBeta n) / ((n : ℚ) - scalarDelta n) := by
  have hlam := ne_of_gt (scalarLambda_pos hn)
  have hden := ne_of_gt (scalar_denominator_pos hn)
  have hδ := (scalar_parameters hn).2.1
  have hnq : (7 : ℚ) ≤ n := by exact_mod_cast hn
  have hα : (n : ℚ) - scalarDelta n ≠ 0 := ne_of_gt (by linarith)
  apply (div_eq_div_iff hden hα).2
  dsimp [scalarDelta, scalarBeta]
  field_simp

/-- The exact rational ceiling is bounded by the actual residual budget. -/
theorem pathForest_refined_threshold {k : ℕ} (hk : 8 ≤ k)
    (H : HereditarySegmentBound (by omega : 7 ≤ k) (scalarDelta (k - 1))
      (scalarBeta (k - 1)))
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    ⌈((scalarLambda (k - 1) * ((k - 1).factorial : ℚ) -
        scalarInterceptNumerator (k - 1)) /
      (((k - 1 : ℕ) : ℚ) * scalarLambda (k - 1) -
        2 * effectiveAllowance (k - 1)))⌉₊ ≤
      pathForestTotalBudget (by omega) P + pathForestV (by omega) P := by
  have hn : 7 ≤ k - 1 := by omega
  obtain ⟨hδ0, hδ, hβ, hβα⟩ := scalar_parameters hn
  have hforest := pathForest_affine_assembly (by omega : 7 ≤ k)
    H hδ0 hδ hβ hβα P hP
  have hnq : (7 : ℚ) ≤ (k - 1 : ℕ) := by exact_mod_cast hn
  apply Nat.ceil_le.mpr
  rw [scalar_quotient_eq hn]
  apply (div_le_iff₀ (by linarith :
    (0 : ℚ) < ((k - 1 : ℕ) : ℚ) - scalarDelta (k - 1))).2
  push_cast
  nlinarith

/-- The final counting implication on the shortest superpermutation length. -/
theorem shortest_bound_of_hereditary {k : ℕ} (hk : 8 ≤ k)
    (H : HereditarySegmentBound (by omega : 7 ≤ k) (scalarDelta (k - 1))
      (scalarBeta (k - 1))) :
    SuperpermutationBounds.RefinedLowerBound k ≤ shortestSuperpermutationLength k := by
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by omega : 3 ≤ k)
  have hthreshold := pathForest_refined_threshold hk H P hP
  have hresidual := pathForest_residual_RV (by omega : 7 ≤ k) P hP
  rw [shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight k
    (by omega : 3 ≤ k)]
  have hweight := hP.1
  dsimp [SuperpermutationBounds.RefinedLowerBound]
  omega

end SuperpermutationLowerBound.Refinement

namespace SuperpermutationBounds

/-- Alphabet transport preserves both coverage and length, so the hereditary
geometric theorem implies the advertised bound for every covering word. -/
theorem word_lower_bound_of_hereditary {K : ℕ} (hK : 8 ≤ K)
    (H : SuperpermutationLowerBound.Refinement.HereditarySegmentBound
      (by omega : 7 ≤ K)
      (SuperpermutationLowerBound.Refinement.scalarDelta (K - 1))
      (SuperpermutationLowerBound.Refinement.scalarBeta (K - 1)))
    (w : List (Fin K)) (hw : Covers w) : RefinedLowerBound K ≤ w.length := by
  classical
  let e : SuperpermutationLowerBound.Alphabet K ≃ Fin K :=
    Fintype.equivFinOfCardEq (by simp [SuperpermutationLowerBound.Alphabet])
  let W : SuperpermutationLowerBound.Word K := w.map e.symm
  have hW : SuperpermutationLowerBound.IsSuperpermutation W := by
    intro p
    have hlength : (p.1.map e).length = K := by
      simpa only [List.length_map] using p.length
    have hnodup : (p.1.map e).Nodup := p.nodup.map e.injective
    obtain ⟨u, v, heq⟩ := hw (p.1.map e) hlength hnodup
    refine ⟨u.map e.symm, v.map e.symm, ?_⟩
    have hmapped := congrArg (List.map e.symm) heq
    simpa [W, List.map_append, List.map_map, Function.comp_def] using hmapped.symm
  have hmain := SuperpermutationLowerBound.Refinement.shortest_bound_of_hereditary hK H
  have hmin := SuperpermutationLowerBound.shortestSuperpermutationLength_le W hW
  have hbound := le_trans hmain hmin
  simpa only [W, List.length_map] using hbound

end SuperpermutationBounds
