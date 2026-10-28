import AlmanacDefs
import Submissions.Solution

/-! Linking proofs for the lower batch, using the Almanac's word predicate.
The original general bounds and asymptotic comparisons remain in the library.
The correction of order (n-4)! is not a positive coefficient of (n-3)!. -/

namespace AlmanacAdapter
open SuperpermutationPalomar

theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

def ExactWordBound : Prop :=
  ∀ n : Nat, 8 ≤ n → ∀ w : Almanac.Word n,
    Almanac.IsSuperpermutation n w →
      GeneralLower.paperBound n (GeneralLower.exactParameters n).1
        (GeneralLower.exactParameters n).2 ≤ w.length

def QuadraticWordBound : Prop :=
  ∀ n : Nat, 8 ≤ n → ∀ w : Almanac.Word n,
    Almanac.IsSuperpermutation n w →
      GeneralLower.paperBound n (GeneralLower.quadraticParameters n).1
        (GeneralLower.quadraticParameters n).2 ≤ w.length

theorem exact_word_bound : ExactWordBound := by
  intro n hn w hw
  exact GeneralLower.exact_word_bound n hn w ((covers_iff w).mpr hw)

theorem quadratic_word_bound : QuadraticWordBound := by
  intro n hn w hw
  exact GeneralLower.quadratic_word_bound n hn w ((covers_iff w).mpr hw)

theorem lower10 : Almanac.LowerBoundAt 10 4033379 := by
  intro w hw
  exact Lower10.word_lower_bound w ((covers_iff w).mpr hw)

theorem lower12 : Almanac.LowerBoundAt 12 522622380 := by
  intro w hw
  have h := exact_word_bound 12 (by decide) w hw
  have hceil : ⌈((1415227652 : ℚ) / 18827)⌉₊ = 75171 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [GeneralLower.paperBound, GeneralLower.exactParameters, Nat.factorial, hceil] at h
  exact h

theorem lower14 : Almanac.LowerBoundAt 14 93891141150 := by
  intro w hw
  exact Lower14.word_lower_bound w ((covers_iff w).mpr hw)

@[simp] theorem fact_eq (n : Nat) : Almanac.fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Almanac.fact, Nat.factorial_succ, ih]

/-- Transfer the real-epsilon word bound to the site's rational-epsilon
fourth-factorial template, preserving the quantification over all words. -/
theorem asymptotic_lower_four : Almanac.AsymptoticLowerAt 4 2 := by
  intro ε hε
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨N, hN⟩ := LowerAsymptotics.word_lower_bound_two_sub_epsilon (ε : ℝ) hεR
  refine ⟨N, ?_⟩
  intro n hn w hw
  have h := hN n hn w ((covers_iff w).mpr hw)
  have hR :
      (n.factorial : ℝ) + ((n - 1).factorial : ℝ) + ((n - 2).factorial : ℝ) +
        (2 - (ε : ℝ)) * ((n - 4).factorial : ℝ) ≤ (w.length : ℝ) := by
    simpa [F3Nat, Nat.cast_add] using h
  simp only [Almanac.asymptoticFormAt, fact_eq]
  exact_mod_cast hR

end AlmanacAdapter
