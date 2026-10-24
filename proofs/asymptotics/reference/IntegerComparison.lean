module

public import asymptotics.reference.Comparison

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem referenceCorrectionQ_nonneg {K : ℕ} (hK : 8 ≤ K) :
    0 ≤ referenceCorrectionQ K := by
  have hKR : (8:ℚ) ≤ K := by exact_mod_cast hK
  have hf : ((K-2 : ℕ) : ℚ) ≤ (K-2).factorial :=
    by exact_mod_cast Nat.self_le_factorial (K-2)
  rw [Nat.cast_sub (by omega : 2 ≤ K), Nat.cast_ofNat] at hf
  unfold referenceCorrectionQ
  apply div_nonneg
  · nlinarith
  · nlinarith

theorem reference_bound_difference_limit {N : ℕ → ℕ} {P : ℕ → ℚ × ℚ} {a c : ℝ}
    (hN : Tendsto N atTop atTop) (d : ℕ) (hc : c ≠ 0)
    (hp : Tendsto (fun m => ((P m).1 : ℝ) / (N m : ℝ)^2) atTop (𝓝 a))
    (ht : Tendsto (fun m => ((P m).2 : ℝ) / (N m : ℝ)^d) atTop (𝓝 c))
    (hA : ∀ᶠ m in atTop, Admissible (N m) (P m).1 (P m).2) :
    Tendsto (fun m => ((paperBound (N m+1) (P m).1 (P m).2 : ℝ) -
      (referenceNat (N m+1) : ℝ)) / ((N m-(d+4)).factorial : ℝ))
      atTop (𝓝 (4/c)) := by
  have hgap := reference_gap_limit hN d hc hp ht
  have hreal : Tendsto (fun m => (correctionReal (N m+1) (P m).1 (P m).2 -
      referenceCorrectionReal (N m+1)) / ((N m-(d+4)).factorial : ℝ))
      atTop (𝓝 (4/c)) := by
    apply hgap.congr'
    filter_upwards [hA] with m hm
    have hnR : (7:ℝ) ≤ N m := by exact_mod_cast hm.n_ge
    have htR : (0:ℝ) < (P m).2 := by exact_mod_cast hm.t_pos
    have hk : (N m:ℝ)^2-2*N m-2 ≠ 0 := by nlinarith
    have hdQ := denominator_pos hm
    dsimp [lam] at hdQ
    have hdQ' : 0 < ((N m:ℚ)^2-2*N m-2)*(P m).2-2*N m := by nlinarith
    have hdR : (0:ℝ) < ((N m:ℝ)^2-2*N m-2)*(P m).2-2*N m :=
      by exact_mod_cast hdQ'
    rw [reference_difference_algebra (by have := hm.n_ge; omega) _ _
      (ne_of_gt htR) hk (ne_of_gt hdR)]
  have hf : ∀ᶠ m in atTop, 0 ≤ correctionQ (N m+1) (P m).1 (P m).2 := by
    filter_upwards [hA] with m hm
    exact paper_correction_nonneg (by have := hm.n_ge; omega)
      (by simpa only [Nat.add_sub_cancel] using hm)
  have hg : ∀ᶠ m in atTop, 0 ≤ referenceCorrectionQ (N m+1) := by
    filter_upwards [hA] with m hm
    exact referenceCorrectionQ_nonneg (by have := hm.n_ge; omega)
  have hround := tendsto_rat_natCeil_sub_div hf hg
    ((tendsto_factorial_sub_atTop (d+4)).comp hN)
    (by simpa only [correctionQ_cast, referenceCorrectionQ_cast, Function.comp_apply] using hreal)
  apply hround.congr'
  filter_upwards [] with m
  simp only [paperBound_eq_base_ceil, referenceNat, Nat.cast_add, Function.comp_apply]
  ring

end SuperpermutationBounds.ChainReturns.Asymptotic
