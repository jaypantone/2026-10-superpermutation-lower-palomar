module

public import asymptotics.foundation.Factorial
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-! Natural ceilings do not change a limit after division by a diverging scale. -/
noncomputable section
open Filter Topology
namespace SuperpermutationLowerBound.ChainReturns.Asymptotics

/-- Natural ceiling commutes with the embedding of rationals into reals. -/
@[simp] theorem natCeil_rat_cast (q : ℚ) : ⌈(q : ℝ)⌉₊ = ⌈q⌉₊ := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast (Nat.le_ceil q)
  · apply Nat.ceil_le.mpr
    exact_mod_cast (Nat.le_ceil (q : ℝ))

/-- A ceiling's bounded nonnegative rounding error vanishes on a diverging scale. -/
theorem tendsto_natCeil_error_div {α : Type*} {l : Filter α} {f s : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hs : Tendsto s l atTop) :
    Tendsto (fun x => ((⌈f x⌉₊ : ℝ) - f x) / s x) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hs)
  · filter_upwards [hs.eventually (eventually_gt_atTop 0)] with x hx
    exact div_nonneg (sub_nonneg.mpr (Nat.le_ceil (f x))) hx.le
  · filter_upwards [hf, hs.eventually (eventually_gt_atTop 0)] with x hx hsx
    apply div_le_div_of_nonneg_right _ hsx.le
    have h := Nat.ceil_lt_add_one hx
    linarith

/-- A difference of ceiling errors vanishes on a diverging scale. -/
theorem tendsto_natCeil_sub_error_div {α : Type*} {l : Filter α} {f g s : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hs : Tendsto s l atTop) :
    Tendsto (fun x => (((⌈f x⌉₊ : ℝ) - (⌈g x⌉₊ : ℝ)) - (f x - g x)) / s x)
      l (𝓝 0) := by
  have h := (tendsto_natCeil_error_div hf hs).sub (tendsto_natCeil_error_div hg hs)
  simp only [sub_zero] at h
  convert h using 1
  ext x
  ring

/-- A normalized real limit is preserved by a natural ceiling. -/
theorem tendsto_natCeil_div {α : Type*} {l : Filter α} {f s : α → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hs : Tendsto s l atTop)
    (h : Tendsto (fun x => f x / s x) l (𝓝 L)) :
    Tendsto (fun x => (⌈f x⌉₊ : ℝ) / s x) l (𝓝 L) := by
  have ht := h.add (tendsto_natCeil_error_div hf hs)
  simp only [add_zero] at ht
  convert ht using 1
  ext x
  ring

/-- A normalized difference limit is preserved by taking natural ceilings separately. -/
theorem tendsto_natCeil_sub_div {α : Type*} {l : Filter α} {f g s : α → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hs : Tendsto s l atTop) (h : Tendsto (fun x => (f x - g x) / s x) l (𝓝 L)) :
    Tendsto (fun x => ((⌈f x⌉₊ : ℝ) - (⌈g x⌉₊ : ℝ)) / s x) l (𝓝 L) := by
  have ht := h.add (tendsto_natCeil_sub_error_div hf hg hs)
  simp only [add_zero] at ht
  convert ht using 1
  ext x
  ring

/-- The same transfer for the rational formulas defining the bounds. -/
theorem tendsto_rat_natCeil_sub_div {α : Type*} {l : Filter α}
    {f g : α → ℚ} {s : α → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hs : Tendsto s l atTop)
    (h : Tendsto (fun x => ((f x : ℝ) - (g x : ℝ)) / s x) l (𝓝 L)) :
    Tendsto (fun x => ((⌈f x⌉₊ : ℝ) - (⌈g x⌉₊ : ℝ)) / s x) l (𝓝 L) := by
  have hf' : ∀ᶠ x in l, (0 : ℝ) ≤ f x := hf.mono (fun x hx => by exact_mod_cast hx)
  have hg' : ∀ᶠ x in l, (0 : ℝ) ≤ g x := hg.mono (fun x hx => by exact_mod_cast hx)
  simpa using tendsto_natCeil_sub_div hf' hg' hs h

end SuperpermutationLowerBound.ChainReturns.Asymptotics
