module

public import asymptotics.Definitions
public import asymptotics.foundation.Rounding
public import asymptotics.reference.Parameters

@[expose] public section

/-! The leading factorial correction, uniformly across all parameter rows. -/
noncomputable section
open Filter Topology
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

/-- The real correction has leading term `2*(K-4)!` for bounded `p/t` and `t≥1`. -/
theorem correction_leading_limit {p t : ℕ → ℝ}
    (hpt : ∀ᶠ K in atTop, 0 ≤ p K / t K ∧ p K / t K ≤ 1)
    (ht : ∀ᶠ K in atTop, 1 ≤ t K) :
    Tendsto (fun K => correctionReal K (p K) (t K) / ((K-4).factorial : ℝ))
      atTop (𝓝 2) := by
  have hinv : ∀ᶠ K in atTop, 0 ≤ 1 / t K ∧ 1 / t K ≤ 1 := by
    filter_upwards [ht] with K hK
    constructor
    · positivity
    · exact (div_le_one (by linarith)).mpr hK
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hi1 := bounded_div_nat_tendsto_zero hinv
  have hi2 := bounded_div_nat_sq_tendsto_zero hinv
  have hd := ((((tendsto_const_nhds (x := (1:ℝ))).sub (hi.const_mul 4)).add
    (hi.pow 2)).sub (hi1.const_mul 2)).add (hi2.const_mul 2)
  simp only [mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hd
  have hden : Tendsto (fun K : ℕ =>
      ((K : ℝ)^2 - 4*K + 1 - 2*((K : ℝ)-1)/t K) / (K : ℝ)^2)
      atTop (𝓝 1) := by
    apply hd.congr'
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    try dsimp
    field_simp
    ring
  have herr : Tendsto (fun K : ℕ =>
      (2*((K : ℝ)-2) + 4*(p K/t K)) / ((K-2).factorial : ℝ)) atTop (𝓝 0) := by
    apply tendsto_div_factorial_sub_of_abs_le tendsto_id 1 2 2
    filter_upwards [hpt, eventually_ge_atTop 2] with K hK hK2
    have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    rw [abs_of_nonneg (by linarith : 0 ≤ 2*((K : ℝ)-2)+4*(p K/t K)), pow_one]
    simp only [id_eq]
    linarith [hK.1, hK.2]
  have hnum := (tendsto_const_nhds (x := (2:ℝ))).sub herr
  simp only [sub_zero] at hnum
  have hratio := ((tendsto_factorial_div_pow_mul_factorial_sub 2).comp
    (tendsto_sub_atTop_nat 2)).mul ((tendsto_nat_sub_div 2).pow 2)
  norm_num only [one_pow, mul_one] at hratio
  have hratio' : Tendsto (fun K : ℕ => ((K-2).factorial : ℝ) /
      ((K : ℝ)^2 * ((K-4).factorial : ℝ))) atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop 3] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    have hN0 : ((K-2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : K-2 ≠ 0)
    have hf : ((K-4).factorial : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply, Nat.sub_sub, show (2:ℕ)+2=4 by rfl]
    field_simp
  have hh := (hnum.div hden (by norm_num)).mul hratio'
  norm_num only [div_one, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with K hK
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hf : ((K-2).factorial : ℝ) ≠ 0 := by positivity
  have hg : ((K-4).factorial : ℝ) ≠ 0 := by positivity
  dsimp [correctionReal]
  field_simp
  ring

/-- The real correction is eventually positive under the same uniform hypotheses. -/
theorem correction_eventually_pos {p t : ℕ → ℝ}
    (hpt : ∀ᶠ K in atTop, 0 ≤ p K / t K ∧ p K / t K ≤ 1)
    (ht : ∀ᶠ K in atTop, 1 ≤ t K) :
    ∀ᶠ K in atTop, 0 < correctionReal K (p K) (t K) := by
  have h := (correction_leading_limit hpt ht).eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<2))
  filter_upwards [h] with K hK
  have hden : (0:ℝ) < ((K-4).factorial:ℝ) := by positivity
  have hh := (lt_div_iff₀ hden).mp hK
  simpa using hh

/-- A real decomposition of the natural bound; subtraction is taken after casting. -/
theorem paperBound_sub_F3Real {K : ℕ} (hK : 3 ≤ K) (p t : ℚ) :
    (paperBound K p t : ℝ) - (F3Nat K : ℝ) =
      ((K : ℝ)-3) + (⌈correctionQ K p t⌉₊ : ℝ) := by
  rw [paperBound_eq_base_ceil, Nat.cast_add,
    Nat.cast_sub (show 3 ≤ F3Nat K + K by omega)]
  push_cast
  ring

/-- Natural rounding and the additive linear term preserve the leading correction. -/
theorem paperBound_leading_limit {p t : ℕ → ℚ}
    (hpt : ∀ᶠ K in atTop, 0 ≤ p K / t K ∧ p K / t K ≤ 1)
    (ht : ∀ᶠ K in atTop, 1 ≤ t K) :
    Tendsto (fun K => ((paperBound K (p K) (t K) : ℝ) - (F3Nat K : ℝ)) /
      ((K-4).factorial : ℝ)) atTop (𝓝 2) := by
  have hptR : ∀ᶠ K in atTop, (0:ℝ) ≤ (p K:ℝ)/(t K:ℝ) ∧ (p K:ℝ)/(t K:ℝ) ≤ 1 := by
    filter_upwards [hpt] with K hK
    exact_mod_cast hK
  have htR : ∀ᶠ K in atTop, (1:ℝ) ≤ (t K:ℝ) := by
    filter_upwards [ht] with K hK
    exact_mod_cast hK
  have hc := correction_leading_limit hptR htR
  have hpos := (correction_eventually_pos hptR htR).mono (fun K hK => hK.le)
  have hr := tendsto_natCeil_div hpos (tendsto_factorial_sub_atTop 4) hc
  have hsmall := (tendsto_pow_div_factorial_sub 1 4).sub
    ((tendsto_pow_div_factorial_sub 0 4).const_mul 3)
  norm_num only [pow_one, pow_zero, mul_zero, sub_zero] at hsmall
  have hh := hsmall.add hr
  norm_num only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 3] with K hK
  rw [paperBound_sub_F3Real hK]
  rw [← correctionQ_cast, natCeil_rat_cast]
  ring

/-- Every general row has `p≥1` once the index is at least twelve. -/
theorem generalParameters_p_ge_one {n : ℕ} (hn : 12 ≤ n)
    {R S : ℚ} (hR : 1 ≤ R) : 1 ≤ (generalParameters n R S).1 := by
  have hm : (4:ℚ) ≤ (n/3:ℕ) := by exact_mod_cast (show 4 ≤ n/3 by omega)
  have hRp : 0 < R := by linarith
  have hr : 0 ≤ (1:ℚ)/(4*R) := by positivity
  have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hmod with h | h | h <;> simp only [generalParameters, h] <;> nlinarith

/-- The scalar bounds used by the exact leading asymptotic. -/
theorem exact_leading_parameters :
    (∀ᶠ K in atTop, (0:ℚ) ≤ (exactParameters K).1 / (exactParameters K).2 ∧
      (exactParameters K).1 / (exactParameters K).2 ≤ 1) ∧
    (∀ᶠ K in atTop, (1:ℚ) ≤ (exactParameters K).2) := by
  constructor
  · filter_upwards [eventually_ge_atTop 13] with K hK
    have h := exactParameters_admissible (by omega : 8 ≤ K)
    exact ⟨div_nonneg h.p_nonneg h.t_pos.le, (div_le_one h.t_pos).mpr h.p_le_t⟩
  · filter_upwards [eventually_ge_atTop 13] with K hK
    have h := exactParameters_admissible (by omega : 8 ≤ K)
    apply le_trans _ h.p_le_t
    rw [exactParameters_large hK]
    apply generalParameters_p_ge_one (by omega)
    exact_mod_cast returnZero_pos (by omega : 2 ≤ K-1)

/-- The same scalar bounds for the quadratic return-order choice. -/
theorem quadratic_leading_parameters :
    (∀ᶠ K in atTop, (0:ℚ) ≤ (quadraticParameters K).1 / (quadraticParameters K).2 ∧
      (quadraticParameters K).1 / (quadraticParameters K).2 ≤ 1) ∧
    (∀ᶠ K in atTop, (1:ℚ) ≤ (quadraticParameters K).2) := by
  constructor
  · filter_upwards [eventually_ge_atTop 13] with K hK
    have h := quadraticParameters_admissible (by omega : 8 ≤ K)
    exact ⟨div_nonneg h.p_nonneg h.t_pos.le, (div_le_one h.t_pos).mpr h.p_le_t⟩
  · filter_upwards [eventually_ge_atTop 13] with K hK
    have h := quadraticParameters_admissible (by omega : 8 ≤ K)
    apply le_trans _ h.p_le_t
    simp only [quadraticParameters, show ¬K<13 by omega, if_false]
    apply generalParameters_p_ge_one (by omega)
    have hN : (12:ℚ) ≤ (K-1:ℕ) := by exact_mod_cast (show 12 ≤ K-1 by omega)
    nlinarith

/-- The exact-return bound has the manuscript's leading factorial correction. -/
theorem exact_leading_limit :
    Tendsto (fun K => (exactReal K - (F3Nat K : ℝ)) / ((K-4).factorial : ℝ))
      atTop (𝓝 2) := by
  exact paperBound_leading_limit exact_leading_parameters.1 exact_leading_parameters.2

/-- The quadratic-return alternative has the same leading factorial correction. -/
theorem quadratic_leading_limit :
    Tendsto (fun K => (quadraticReal K - (F3Nat K : ℝ)) / ((K-4).factorial : ℝ))
      atTop (𝓝 2) := by
  exact paperBound_leading_limit quadratic_leading_parameters.1 quadratic_leading_parameters.2

/-- For every positive epsilon, the leading asymptotic is an eventual lower
bound for every word satisfying the original contiguous-subword predicate. -/
theorem eventually_word_lower_bound_two_sub_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K in atTop, ∀ w : List (Fin K), SuperpermutationBounds.Covers w →
      (F3Nat K : ℝ) + (2-ε) * ((K-4).factorial : ℝ) ≤ (w.length : ℝ) := by
  have hl := exact_leading_limit.eventually
    (eventually_gt_nhds (show 2-ε < (2:ℝ) by linarith))
  filter_upwards [hl, eventually_ge_atTop 8] with K hlim hK w hw
  have hf : (0:ℝ) < ((K-4).factorial : ℝ) := by positivity
  have hmain := (lt_div_iff₀ hf).mp hlim
  have hword : exactReal K ≤ (w.length : ℝ) := by
    unfold exactReal exactNat
    exact_mod_cast (exact_word_bound K hK w hw)
  linarith

/-- Threshold form of the arbitrary-word asymptotic lower bound. -/
theorem word_lower_bound_two_sub_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ w : List (Fin K),
      SuperpermutationBounds.Covers w →
      (F3Nat K : ℝ) + (2-ε) * ((K-4).factorial : ℝ) ≤ (w.length : ℝ) := by
  exact eventually_atTop.mp (eventually_word_lower_bound_two_sub_epsilon ε hε)

end SuperpermutationBounds.ChainReturns.Asymptotic
