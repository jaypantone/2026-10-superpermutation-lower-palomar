module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open scoped BigOperators

/-- An injective finite incidence map counts each occupied endpoint once. -/
theorem sum_over_injective_incidence {E V : Type*} [Fintype E] [Fintype V]
    [DecidableEq V]
    (f : E → V) (hf : Function.Injective f) (w : V → ℚ) :
    (∑ v, if ∃ e, f e = v then w v else 0) = ∑ e, w (f e) := by
  classical
  have hr : (Finset.univ.filter (fun v => ∃ e, f e = v)) = Finset.univ.image f := by
    ext v
    simp
  rw [← Finset.sum_filter, hr, Finset.sum_image hf.injOn]

/-- Local endpoint charges and nonnegative edge margins leave exactly the
intercepts at vertices with no incoming edge.  Self-loops need no exception. -/
theorem finite_incidence_assembly {E V : Type*} [Fintype E] [Fintype V]
    [DecidableEq V]
    (source target : E → V) (hs : Function.Injective source)
    (ht : Function.Injective target) (s c a b : V → ℚ)
    (hlocal : ∀ v, s v + (if ∃ e, target e = v then a v else 0) +
      (if ∃ e, source e = v then b v else 0) ≤ c v)
    (hedge : ∀ e, c (target e) ≤ b (source e) + a (target e)) :
    (∑ v, s v) ≤ ∑ v, if ¬∃ e, target e = v then c v else 0 := by
  classical
  have hl := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  simp only [Finset.sum_add_distrib] at hl
  rw [sum_over_injective_incidence target ht,
    sum_over_injective_incidence source hs] at hl
  have he := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedge e)
  simp only [Finset.sum_add_distrib] at he
  have hc : (∑ v, c v) = (∑ e, c (target e)) +
      ∑ v, if ¬∃ e, target e = v then c v else 0 := by
    rw [← sum_over_injective_incidence target ht, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : ∃ e, target e = v <;> simp [h]
  linarith

end SuperpermutationLowerBound.Refinement
