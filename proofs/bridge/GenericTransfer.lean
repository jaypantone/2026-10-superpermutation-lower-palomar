module

public import SuperpermutationLowerBound.Refinement.WordBound

@[expose] public section

/-!
The rational chain-to-word transfer used by the frozen chain-return manuscript.
The premise is hereditary packing on actual block-aligned light segments, not
an assumption about the desired word bound. The new geometric argument must
supply this premise separately. The inherited word predicate permits arbitrary
repetitions.
-/

namespace SuperpermutationLowerBound.ChainReturns
open Refinement

/-- Exact parameter domain of the manuscript's chain-to-word proposition. -/
structure Admissible (n : ℕ) (p t : ℚ) : Prop where
  n_ge : 7 ≤ n
  p_nonneg : 0 ≤ p
  p_le_t : p ≤ t
  t_pos : 0 < t
  margin : 4 * p + 6 ≤ t * ((n : ℚ) - 4)

def lam (n : ℕ) (t : ℚ) : ℚ := ((n : ℚ) - 2) * t - 2
def intercept (n : ℕ) (p t : ℚ) : ℚ := 2 * t * ((n : ℚ) - 1) + 4 * p
def delta (n : ℕ) (t : ℚ) : ℚ := 2 * t / lam n t
def beta (n : ℕ) (p t : ℚ) : ℚ := intercept n p t / lam n t

/-- The ceiling in the inherited forest normalization. -/
noncomputable def bound (K : ℕ) (p t : ℚ) : ℕ :=
  let n := K - 1
  K + (K + 1) * n.factorial - 3 +
    ⌈((lam n t * (n.factorial : ℚ) - intercept n p t) /
      ((n : ℚ) * lam n t - 2 * t))⌉₊

/-- All factors of every actual segment must satisfy the chain inequality. -/
def ActualPacking (K : ℕ) (hK : 8 ≤ K) (p t : ℚ) : Prop :=
  ∀ (P : OverlapPath K) (hP : IsBlockAligned P)
    (s : BlockAlignedLightSegment (by omega : 7 ≤ K) P hP),
      ChainPacking (K - 1 - 2) p t s.deficitString

theorem admissible_parameters {n : ℕ} {p t : ℚ} (h : Admissible n p t) :
    0 < lam n t ∧ 0 < delta n t ∧ delta n t < 1 ∧
    1 ≤ beta n p t ∧ beta n p t ≤ (n : ℚ) - delta n t := by
  have hn : (7 : ℚ) ≤ n := by exact_mod_cast h.n_ge
  have hp := h.p_nonneg
  have ht := h.t_pos
  have hm := h.margin
  have hm6 : 6 ≤ t * ((n : ℚ) - 4) := by linarith
  have hlam : 0 < lam n t := by dsimp [lam]; nlinarith
  have hsmall : 2 * t < lam n t := by dsimp [lam]; nlinarith
  have hprod : 0 ≤ ((n : ℚ) - 1) * (t * ((n : ℚ) - 4) - 6) :=
    mul_nonneg (by linarith) (by linarith)
  have hupper : intercept n p t ≤ (n : ℚ) * lam n t - 2 * t := by
    dsimp [intercept, lam]
    nlinarith
  have hbeta : lam n t ≤ intercept n p t := by
    have hnt : 0 ≤ (n : ℚ) * t := mul_nonneg (by positivity) (le_of_lt ht)
    dsimp [lam, intercept]
    nlinarith
  refine ⟨hlam, div_pos (by positivity) hlam,
    (div_lt_one hlam).2 hsmall, (le_div_iff₀ hlam).2 ?_, ?_⟩
  · simpa using hbeta
  · apply (div_le_iff₀ hlam).2
    change intercept n p t ≤ ((n : ℚ) - 2 * t / lam n t) * lam n t
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hlam)]
    exact hupper

theorem scalar_affine {n : ℕ} {p t : ℚ} (h : Admissible n p t)
    {d : List ℕ} (hlegal : IsLegalDeficitSequence n d)
    (hpacking : ChainPacking (n - 2) p t d) :
    ListAffineBound (delta n t) (beta n p t) d := by
  have hn2 : n - 2 + 2 = n := by have := h.n_ge; omega
  have hcast : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
    rw [Nat.cast_sub (by have := h.n_ge; omega : 2 ≤ n), Nat.cast_ofNat]
  have hlam : chainLambda (n - 2) t = lam n t := by simp [chainLambda, lam, hcast]
  have hB : chainIntercept (n - 2) p t = intercept n p t := by
    simp only [chainIntercept, intercept, hcast]; ring
  have hmargin : 4 * p + 6 ≤ t * (((n - 2 : ℕ) : ℚ) - 2) := by
    simpa only [hcast, sub_sub, show (2 : ℚ) + 2 = 4 by norm_num] using h.margin
  intro i j
  have hs := deficit_factor_affine_bound (a := n - 2)
    (by have := h.n_ge; omega) h.p_nonneg h.p_le_t h.t_pos hmargin
    (by simpa only [hn2] using hlegal) hpacking i j
  simpa only [hlam, hB, delta, beta] using hs

theorem hereditary_of_actualPacking {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) (H : ActualPacking K hK p t) :
    HereditarySegmentBound (by omega : 7 ≤ K) (delta (K - 1) t)
      (beta (K - 1) p t) := by
  intro P hP s
  exact scalar_affine h s.deficitString_legal (H P hP s)

theorem denominator_pos {n : ℕ} {p t : ℚ} (h : Admissible n p t) :
    0 < (n : ℚ) * lam n t - 2 * t := by
  obtain ⟨hlam, _, hd, _, _⟩ := admissible_parameters h
  have hn : (7 : ℚ) ≤ n := by exact_mod_cast h.n_ge
  have hh : 0 < ((n : ℚ) - delta n t) * lam n t :=
    mul_pos (by linarith) hlam
  rw [sub_mul, delta, div_mul_cancel₀ _ (ne_of_gt hlam)] at hh
  exact hh

theorem quotient_eq {n : ℕ} {p t : ℚ} (h : Admissible n p t) (T : ℚ) :
    (lam n t * T - intercept n p t) / ((n : ℚ) * lam n t - 2 * t) =
      (T - beta n p t) / ((n : ℚ) - delta n t) := by
  have hlam := ne_of_gt (admissible_parameters h).1
  have hden := ne_of_gt (denominator_pos h)
  have hd := (admissible_parameters h).2.2.1
  have hn : (7 : ℚ) ≤ n := by exact_mod_cast h.n_ge
  have hα : (n : ℚ) - delta n t ≠ 0 := ne_of_gt (by linarith)
  apply (div_eq_div_iff hden hα).2
  dsimp [delta, beta]
  field_simp

/-- Conditional only on the geometric chain estimate for actual segments. -/
theorem shortest_bound_of_actualPacking {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) (H : ActualPacking K hK p t) :
    bound K p t ≤ shortestSuperpermutationLength K := by
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by omega : 3 ≤ K)
  obtain ⟨hlam, hd0, hd, hb, hba⟩ := admissible_parameters h
  have hforest := pathForest_affine_assembly (by omega : 7 ≤ K)
    (hereditary_of_actualPacking hK h H) hd0 hd hb hba P hP
  have hnq : (7 : ℚ) ≤ (K - 1 : ℕ) := by exact_mod_cast h.n_ge
  have hthreshold :
      ⌈((lam (K - 1) t * ((K - 1).factorial : ℚ) - intercept (K - 1) p t) /
        (((K - 1 : ℕ) : ℚ) * lam (K - 1) t - 2 * t))⌉₊ ≤
      pathForestTotalBudget (by omega) P + pathForestV (by omega) P := by
    apply Nat.ceil_le.mpr
    rw [quotient_eq h]
    apply (div_le_iff₀ (by linarith : (0 : ℚ) <
      ((K - 1 : ℕ) : ℚ) - delta (K - 1) t)).2
    push_cast
    nlinarith
  have hresidual := pathForest_residual_RV (by omega : 7 ≤ K) P hP
  rw [shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight K
    (by omega : 3 ≤ K)]
  have hweight := hP.1
  dsimp [bound]
  omega

/-- Transfer to the original contiguous-coverage predicate on arbitrary words. -/
theorem word_bound_of_actualPacking {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) (H : ActualPacking K hK p t)
    (w : List (Fin K)) (hw : SuperpermutationBounds.Covers w) :
    bound K p t ≤ w.length := by
  classical
  let e : Alphabet K ≃ Fin K := Fintype.equivFinOfCardEq (by simp [Alphabet])
  let W : Word K := w.map e.symm
  have hW : IsSuperpermutation W := by
    intro P
    have hlength : (P.1.map e).length = K := by
      simpa only [List.length_map] using P.length
    have hnodup : (P.1.map e).Nodup := P.nodup.map e.injective
    obtain ⟨u, v, heq⟩ := hw (P.1.map e) hlength hnodup
    refine ⟨u.map e.symm, v.map e.symm, ?_⟩
    have hmapped := congrArg (List.map e.symm) heq
    simpa [W, List.map_append, List.map_map, Function.comp_def] using hmapped.symm
  have hmain := shortest_bound_of_actualPacking hK h H
  have hmin := shortestSuperpermutationLength_le W hW
  simpa only [W, List.length_map] using le_trans hmain hmin

end SuperpermutationLowerBound.ChainReturns
