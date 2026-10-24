module

public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

def chainLambda (a : ℕ) (t : ℚ) : ℚ := a * t - 2

def chainIntercept (a : ℕ) (p t : ℚ) : ℚ := 2 * t * (a + 1) + 4 * p

def clusterReserve (a : ℕ) (p t : ℚ) (K : List ℕ) : ℚ :=
  chainLambda a t * ((K.sum : ℚ) - 2) - 2 * t * ((K.length : ℚ) - 1) -
    if K = [2] then 0 else 4 * (p + 1)

theorem scalar_margin {a : ℕ} {p t : ℚ}
    (hp : 0 ≤ p) (ht : 0 < t) (hmargin : 4 * p + 6 ≤ t * (a - 2)) :
    0 < chainLambda a t ∧
      4 * (p + 1) ≤ chainLambda a t - 2 * t := by
  dsimp [chainLambda]
  constructor <;> nlinarith

@[simp] theorem clusterReserve_regular (a : ℕ) (p t : ℚ) :
    clusterReserve a p t [2] = 0 := by
  simp [clusterReserve]

theorem clusterReserve_nonnegative {a : ℕ} {p t : ℚ} {K : List ℕ}
    (hp : 0 ≤ p) (ht : 0 < t) (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (hmass : K.length + 1 ≤ K.sum)
    (hexceptional : K ≠ [2] → 3 ≤ K.sum) :
    0 ≤ clusterReserve a p t K := by
  by_cases hregular : K = [2]
  · simp [hregular]
  · have hmassQ : (K.length : ℚ) + 1 ≤ K.sum := by exact_mod_cast hmass
    have hthreeQ : (3 : ℚ) ≤ K.sum := by exact_mod_cast hexceptional hregular
    have hc := (scalar_margin hp ht hmargin).2
    have hcost : 0 ≤ 4 * (p + 1) := by positivity
    have hmul := mul_nonneg (show 0 ≤ chainLambda a t - 2 * t by linarith)
      (show 0 ≤ (K.sum : ℚ) - 3 by linarith)
    have hlength := mul_nonneg (show 0 ≤ 2 * t by positivity)
      (show 0 ≤ (K.sum : ℚ) - (K.length : ℚ) - 1 by linarith)
    simp only [clusterReserve, if_neg hregular]
    nlinarith

/-- The maximal-gap payment retains the positive entries already counted
in the two cluster lengths. -/
theorem clusterReserve_maxZeroGap {a : ℕ} {p t : ℚ} {K L : List ℕ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (hK : 1 ≤ K.length) (hL : 1 ≤ L.length)
    (hboundary : a + K.length + L.length ≤ K.sum + L.sum) :
    4 * t ≤ clusterReserve a p t K + clusterReserve a p t L := by
  have hlambda := (scalar_margin hp ht hmargin).1
  have hc := (scalar_margin hp ht hmargin).2
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hmQ : (2 : ℚ) ≤ (K.length : ℚ) + L.length := by exact_mod_cast (by omega : 2 ≤ K.length + L.length)
  have hbQ : (a : ℚ) + K.length + L.length ≤ (K.sum : ℚ) + L.sum := by
    exact_mod_cast hboundary
  have hmass := mul_nonneg (le_of_lt hlambda)
    (show 0 ≤ (K.sum : ℚ) + L.sum - a - K.length - L.length by linarith)
  have hlen := mul_nonneg (show 0 ≤ chainLambda a t - 2 * t by linarith)
    (show 0 ≤ (K.length : ℚ) + L.length - 2 by linarith)
  have hdim := mul_nonneg (le_of_lt hlambda) (show 0 ≤ (a : ℚ) - 4 by linarith)
  unfold clusterReserve
  split_ifs <;> nlinarith

theorem clusterReserve_terminal {a : ℕ} {p t : ℚ} {K : List ℕ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (hK : 1 ≤ K.length) (hboundary : a + K.length ≤ K.sum) :
    4 * t ≤ clusterReserve a p t K := by
  have hlambda := (scalar_margin hp ht hmargin).1
  have hc := (scalar_margin hp ht hmargin).2
  have haQ : (4 : ℚ) ≤ a := by exact_mod_cast ha
  have hmQ : (1 : ℚ) ≤ K.length := by exact_mod_cast hK
  have hbQ : (a : ℚ) + K.length ≤ (K.sum : ℚ) := by exact_mod_cast hboundary
  have hmass := mul_nonneg (le_of_lt hlambda)
    (show 0 ≤ (K.sum : ℚ) - a - K.length by linarith)
  have hlen := mul_nonneg (show 0 ≤ chainLambda a t - 2 * t by linarith)
    (show 0 ≤ (K.length : ℚ) - 1 by linarith)
  have hdim := mul_nonneg (le_of_lt hlambda) (show 0 ≤ (a : ℚ) - 4 by linarith)
  have hlambdat : 2 * t ≤ chainLambda a t := by linarith
  unfold clusterReserve
  split_ifs <;> nlinarith

/-- The exact chain count is sufficient to pay the exceptional clusters. -/
theorem chainPacking_cluster_count {p t s b H h₁ h₂ u : ℚ}
    (hp : 0 ≤ p) (hpt : p ≤ t) (hh₂ : 0 ≤ h₂)
    (hpaths : u ≤ b + 1 + h₂)
    (hshort : h₁ + 2 * h₂ ≤ H)
    (hpacking : s - b ≤ p * u + t / 2 * h₁) :
    4 * s ≤ 4 * p + 4 * (p + 1) * b + 2 * t * H := by
  have ht : 0 ≤ t := hp.trans hpt
  have h₁ := mul_nonneg hp (sub_nonneg.mpr hpaths)
  have h₂ := mul_nonneg ht (sub_nonneg.mpr hshort)
  have h₃ := mul_nonneg (sub_nonneg.mpr hpt) hh₂
  nlinarith

end SuperpermutationLowerBound.Refinement
