module

public import asymptotics.gains.QuadraticLimits
public import asymptotics.foundation.Rounding

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem admissible_weaken {n : ℕ} {p t p' t' : ℚ}
    (h : Admissible n p t) (hp' : 0 ≤ p') (hpp : p' ≤ p) (htt : t ≤ t') :
    Admissible n p' t' := by
  have hnQ : (7:ℚ) ≤ n := by exact_mod_cast h.n_ge
  refine ⟨h.n_ge, hp', le_trans hpp (le_trans h.p_le_t htt), lt_of_lt_of_le h.t_pos htt, ?_⟩
  have hh := mul_le_mul_of_nonneg_right htt (by linarith : 0 ≤ (n:ℚ)-4)
  linarith [h.margin]

theorem old_mod_zero_admissible (m : ℕ) (hm : 3 ≤ m) :
    Admissible (3*m) (2*m) (4*m-3) := by
  apply admissible_weaken (admissible_modZero m hm 1 (by norm_num))
  · positivity
  · norm_num <;> linarith
  · norm_num <;> linarith

theorem old_mod_one_admissible (m : ℕ) (hm : 3 ≤ m) :
    Admissible (3*m+1) ((m:ℚ)*(2*m+1)) (2*(m:ℚ)^2+2*m-2) := by
  apply admissible_weaken (admissible_modOne m hm 1 (by norm_num))
  · positivity
  · rfl
  · norm_num <;> linarith

theorem oldParameters_admissible {K : ℕ} (hK : 8 ≤ K) :
    Admissible (K-1) (oldParameters K).1 (oldParameters K).2 := by
  by_cases hsmall : K < 13
  · simpa only [oldParameters, if_pos hsmall] using exactParameters_admissible hK
  · have hm : 4 ≤ (K-1)/3 := by omega
    have hmod : (K-1)%3=0 ∨ (K-1)%3=1 ∨ (K-1)%3=2 := by omega
    rcases hmod with hmod | hmod | hmod
    · have hh := old_mod_zero_admissible ((K-1)/3) (by omega)
      convert hh using 1 <;> first | omega | simp [oldParameters, hsmall, oldGeneralParameters, hmod]
    · have hh := old_mod_one_admissible ((K-1)/3) (by omega)
      convert hh using 1 <;> first | omega | simp [oldParameters, hsmall, oldGeneralParameters, hmod]
    · have hh := admissible_modTwo ((K-1)/3) (by omega)
      convert hh using 1 <;> first | omega | simp [oldParameters, hsmall, oldGeneralParameters, hmod]

theorem old_zero_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((oldParameters (3*m+1)).1:ℝ) = zeroOldP (3*m) ∧
    ((oldParameters (3*m+1)).2:ℝ) = zeroOldT (3*m) := by
  have hsmall : ¬3*m+1<13 := by omega
  have he : 3*m+1-1=3*m := by omega
  constructor <;> simp [oldParameters, hsmall, he, oldGeneralParameters, zeroOldP, zeroOldT] <;> ring

theorem old_one_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((oldParameters (3*m+2)).1:ℝ) = oneOldP (3*(m:ℝ)+1) ∧
    ((oldParameters (3*m+2)).2:ℝ) = oneOldT (3*(m:ℝ)+1) := by
  have hsmall : ¬3*m+2<13 := by omega
  have he : 3*m+2-1=3*m+1 := by omega
  have hmod : (3*m+1)%3=1 := by omega
  have hdiv : (3*m+1)/3=m := by omega
  simp [oldParameters, hsmall, he, oldGeneralParameters, hmod, hdiv, oneOldP, oneOldT]
  constructor <;> ring

theorem quadratic_zero_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((quadraticParameters (3*m+1)).1:ℝ) = zeroOldP (3*m)+1/2+1/(3*(m:ℝ))^2 ∧
    ((quadraticParameters (3*m+1)).2:ℝ) = zeroOldT (3*m)-2/(3*(m:ℝ))^2 := by
  have hsmall : ¬3*m+1<13 := by omega
  have he : 3*m+1-1=3*m := by omega
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  simp only [quadraticParameters, if_neg hsmall, he, generalParameters,
    Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega : 0<3)]
  push_cast
  constructor <;> dsimp [zeroOldP, zeroOldT] <;> field_simp <;> ring

theorem quadratic_one_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((quadraticParameters (3*m+2)).1:ℝ) = oneOldP (3*(m:ℝ)+1) ∧
    ((quadraticParameters (3*m+2)).2:ℝ) = oneOldT (3*(m:ℝ)+1)-4/(3*(m:ℝ)+1)^2 := by
  have hsmall : ¬3*m+2<13 := by omega
  have he : 3*m+2-1=3*m+1 := by omega
  have hmod : (3*m+1)%3=1 := by omega
  have hdiv : (3*m+1)/3=m := by omega
  have hm0 : 3*(m:ℝ)+1 ≠ 0 := by positivity
  simp only [quadraticParameters, if_neg hsmall, he, generalParameters, hmod, hdiv]
  push_cast
  constructor <;> dsimp [oneOldP, oneOldT] <;> field_simp <;> ring

theorem quadratic_zero_correction_gain (m : ℕ) (hm : 4 ≤ m) :
    (correctionQ (3*m+1) (quadraticParameters (3*m+1)).1
      (quadraticParameters (3*m+1)).2 : ℝ) -
    (correctionQ (3*m+1) (oldParameters (3*m+1)).1
      (oldParameters (3*m+1)).2 : ℝ) = zeroQuadraticGain (3*m) := by
  have hqa := quadraticParameters_admissible (show 8≤3*m+1 by omega)
  have hoa := oldParameters_admissible (show 8≤3*m+1 by omega)
  have hqt : ((quadraticParameters (3*m+1)).2:ℝ) ≠ 0 := by exact_mod_cast hqa.t_pos.ne'
  have hot : ((oldParameters (3*m+1)).2:ℝ) ≠ 0 := by exact_mod_cast hoa.t_pos.ne'
  rw [correctionQ_cast, correctionQ_cast,
    correctionReal_succ_fraction (3*m) (by omega) _ _ hqt,
    correctionReal_succ_fraction (3*m) (by omega) _ _ hot]
  rw [(quadratic_zero_parameters m hm).1, (quadratic_zero_parameters m hm).2,
    (old_zero_parameters m hm).1, (old_zero_parameters m hm).2]
  simp only [zeroQuadraticGain, factorialA, Nat.cast_mul, Nat.cast_ofNat]

theorem quadratic_one_correction_gain (m : ℕ) (hm : 4 ≤ m) :
    (correctionQ (3*m+2) (quadraticParameters (3*m+2)).1
      (quadraticParameters (3*m+2)).2 : ℝ) -
    (correctionQ (3*m+2) (oldParameters (3*m+2)).1
      (oldParameters (3*m+2)).2 : ℝ) = oneQuadraticGain (3*m+1) := by
  have hqa := quadraticParameters_admissible (show 8≤3*m+2 by omega)
  have hoa := oldParameters_admissible (show 8≤3*m+2 by omega)
  have hqt : ((quadraticParameters (3*m+2)).2:ℝ) ≠ 0 := by exact_mod_cast hqa.t_pos.ne'
  have hot : ((oldParameters (3*m+2)).2:ℝ) ≠ 0 := by exact_mod_cast hoa.t_pos.ne'
  rw [correctionQ_cast, correctionQ_cast,
    show 3*m+2 = (3*m+1)+1 by omega,
    correctionReal_succ_fraction (3*m+1) (by omega) _ _ hqt,
    correctionReal_succ_fraction (3*m+1) (by omega) _ _ hot]
  rw [(quadratic_one_parameters m hm).1, (quadratic_one_parameters m hm).2,
    (old_one_parameters m hm).1, (old_one_parameters m hm).2]
  simp only [oneQuadraticGain, factorialA, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]


theorem gain_residue_tendsto (r : ℕ) : Tendsto (fun m : ℕ => 3*m+r) atTop atTop :=
  tendsto_atTop_mono (fun m => show m ≤ 3*m+r by omega) tendsto_id

theorem quadratic_gain_zero_limit :
    Tendsto (fun m : ℕ => ((quadraticNat (3*m+1):ℝ)-(oldNat (3*m+1):ℝ)) /
      ((3*m+1-9).factorial:ℝ)) atTop (𝓝 (9/2)) := by
  have hf : ∀ᶠ m : ℕ in atTop, 0 ≤ correctionQ (3*m+1)
      (quadraticParameters (3*m+1)).1 (quadraticParameters (3*m+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    exact paper_correction_nonneg (by omega) (quadraticParameters_admissible (by omega))
  have hg : ∀ᶠ m : ℕ in atTop, 0 ≤ correctionQ (3*m+1)
      (oldParameters (3*m+1)).1 (oldParameters (3*m+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    exact paper_correction_nonneg (by omega) (oldParameters_admissible (by omega))
  have hN : Tendsto (fun m : ℕ => 3*m) atTop atTop := by
    simpa only [Nat.add_zero] using gain_residue_tendsto 0
  have hs : Tendsto (fun m : ℕ => ((3*m+1-9).factorial:ℝ)) atTop atTop := by
    simpa only [Function.comp_def, show ∀ m : ℕ, 3*m+1-9=3*m-8 by omega] using
      (tendsto_factorial_sub_atTop 8).comp hN
  have hr : Tendsto (fun m : ℕ =>
      ((correctionQ (3*m+1) (quadraticParameters (3*m+1)).1
        (quadraticParameters (3*m+1)).2 : ℝ) -
       (correctionQ (3*m+1) (oldParameters (3*m+1)).1
        (oldParameters (3*m+1)).2 : ℝ))/((3*m+1-9).factorial:ℝ))
      atTop (𝓝 (9/2)) := by
    apply (zero_quadratic_gain_factorial_limit.comp hN).congr'
    filter_upwards [eventually_ge_atTop 4] with m hm
    rw [quadratic_zero_correction_gain m hm]
    simp only [Function.comp_apply, show 3*m+1-9=3*m-8 by omega]
  have hh := tendsto_rat_natCeil_sub_div hf hg hs hr
  apply hh.congr'
  filter_upwards [] with m
  simp only [quadraticNat, oldNat, paperBound_eq_base_ceil, Nat.cast_add]
  ring

theorem quadratic_gain_one_limit :
    Tendsto (fun m : ℕ => ((quadraticNat (3*m+2):ℝ)-(oldNat (3*m+2):ℝ)) /
      ((3*m+2-11).factorial:ℝ)) atTop (𝓝 324) := by
  have hf : ∀ᶠ m : ℕ in atTop, 0 ≤ correctionQ (3*m+2)
      (quadraticParameters (3*m+2)).1 (quadraticParameters (3*m+2)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    exact paper_correction_nonneg (by omega) (quadraticParameters_admissible (by omega))
  have hg : ∀ᶠ m : ℕ in atTop, 0 ≤ correctionQ (3*m+2)
      (oldParameters (3*m+2)).1 (oldParameters (3*m+2)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    exact paper_correction_nonneg (by omega) (oldParameters_admissible (by omega))
  have hN := gain_residue_tendsto 1
  have hs : Tendsto (fun m : ℕ => ((3*m+2-11).factorial:ℝ)) atTop atTop := by
    simpa only [Function.comp_def, show ∀ m : ℕ, 3*m+2-11=3*m+1-10 by omega] using
      (tendsto_factorial_sub_atTop 10).comp hN
  have hr : Tendsto (fun m : ℕ =>
      ((correctionQ (3*m+2) (quadraticParameters (3*m+2)).1
        (quadraticParameters (3*m+2)).2 : ℝ) -
       (correctionQ (3*m+2) (oldParameters (3*m+2)).1
        (oldParameters (3*m+2)).2 : ℝ))/((3*m+2-11).factorial:ℝ))
      atTop (𝓝 324) := by
    apply (one_quadratic_gain_factorial_limit.comp hN).congr'
    filter_upwards [eventually_ge_atTop 4] with m hm
    rw [quadratic_one_correction_gain m hm]
    simp only [Function.comp_apply, show 3*m+2-11=3*m+1-10 by omega]
  have hh := tendsto_rat_natCeil_sub_div hf hg hs hr
  apply hh.congr'
  filter_upwards [] with m
  simp only [quadraticNat, oldNat, paperBound_eq_base_ceil, Nat.cast_add]
  ring

end SuperpermutationBounds.ChainReturns.Asymptotic
