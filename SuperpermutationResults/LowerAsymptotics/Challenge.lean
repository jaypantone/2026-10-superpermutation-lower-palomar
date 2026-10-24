module

public import SuperpermutationResults.GeneralLower.Challenge
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
The leading correction and comparisons of explicit integer formulas.
All differences are formed after casting to the reals, so natural subtraction
cannot truncate them. These limits compare proved formulas; they do not
assert an asymptotic equality for the optimal superpermutation length.

The reference is the Fritsch–Halfar all-size formula, not Halfar's separate
finite search bounds. `oldNat` is our preceding general formula. The final
two claims are eventual lower estimates, not limits.
-/
namespace SuperpermutationResults.LowerAsymptotics
open GeneralLower
open Filter Topology
noncomputable section

def exactNat (K : ℕ) : ℕ :=
  paperBound K (exactParameters K).1 (exactParameters K).2

def quadraticNat (K : ℕ) : ℕ :=
  paperBound K (quadraticParameters K).1 (quadraticParameters K).2

def oldGeneralParameters (n : ℕ) : ℚ × ℚ :=
  let m : ℚ := (n / 3 : ℕ)
  match n % 3 with
  | 0 => (2*m, 4*m-3)
  | 1 => (m*(2*m+1), 2*m^2+2*m-2)
  | _ => ((m+1)*(2*m+1), 4*m^2+5*m-5/2)

/-- The initial rows are retained; they do not affect the limits. -/
def oldParameters (K : ℕ) : ℚ × ℚ :=
  if K < 13 then exactParameters K else oldGeneralParameters (K-1)

def oldNat (K : ℕ) : ℕ :=
  paperBound K (oldParameters K).1 (oldParameters K).2

def referenceCorrectionQ (K : ℕ) : ℚ :=
  2 * (((K-2).factorial : ℚ) - ((K : ℚ)-2)) /
    ((K : ℚ)^2 - 4*K + 1)

/-- The explicit all-size reference formula; no proof is imported here. -/
def referenceNat (K : ℕ) : ℕ :=
  F3Nat K + K - 3 + ⌈referenceCorrectionQ K⌉₊

def exactReal (K : ℕ) : ℝ := exactNat K
def quadraticReal (K : ℕ) : ℝ := quadraticNat K

def ExactLeadingLimit : Prop :=
   Tendsto (fun K => (exactReal K - (F3Nat K : ℝ)) / ((K-4).factorial : ℝ))
      atTop (𝓝 2)

def QuadraticLeadingLimit : Prop :=
   Tendsto (fun K => (quadraticReal K - (F3Nat K : ℝ)) / ((K-4).factorial : ℝ))
      atTop (𝓝 2)

def WordLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    ∀ w : List (Fin K), Covers w →
      (F3Nat K : ℝ) + (2-ε) * ((K-4).factorial : ℝ) ≤ (w.length : ℝ)

def ExactReferenceZero : Prop :=
   Tendsto (fun m : ℕ => ((exactNat (3*m+1) : ℝ) - (referenceNat (3*m+1) : ℝ)) /
      ((3*m+1-6).factorial : ℝ)) atTop (𝓝 3)

def ExactReferenceOne : Prop :=
   Tendsto (fun m : ℕ => ((exactNat (3*m+2) : ℝ) - (referenceNat (3*m+2) : ℝ)) /
      ((3*m+2-7).factorial : ℝ)) atTop (𝓝 18)

def ExactReferenceTwo : Prop :=
   Tendsto (fun m : ℕ => ((exactNat (3*m+3) : ℝ) - (referenceNat (3*m+3) : ℝ)) /
      ((3*m+3-7).factorial : ℝ)) atTop (𝓝 9)

def QuadraticReferenceZero : Prop :=
   Tendsto (fun m : ℕ => ((quadraticNat (3*m+1) : ℝ) - (referenceNat (3*m+1) : ℝ)) /
      ((3*m+1-6).factorial : ℝ)) atTop (𝓝 3)

def QuadraticReferenceOne : Prop :=
   Tendsto (fun m : ℕ => ((quadraticNat (3*m+2) : ℝ) - (referenceNat (3*m+2) : ℝ)) /
      ((3*m+2-7).factorial : ℝ)) atTop (𝓝 18)

def QuadraticReferenceTwo : Prop :=
   Tendsto (fun m : ℕ => ((quadraticNat (3*m+3) : ℝ) - (referenceNat (3*m+3) : ℝ)) /
      ((3*m+3-7).factorial : ℝ)) atTop (𝓝 9)

def QuadraticGainZero : Prop :=
   Tendsto (fun m : ℕ => ((quadraticNat (3*m+1):ℝ)-(oldNat (3*m+1):ℝ)) /
      ((3*m+1-9).factorial:ℝ)) atTop (𝓝 (9/2))

def QuadraticGainOne : Prop :=
   Tendsto (fun m : ℕ => ((quadraticNat (3*m+2):ℝ)-(oldNat (3*m+2):ℝ)) /
      ((3*m+2-11).factorial:ℝ)) atTop (𝓝 324)

def ExactGainZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (9/2:ℝ)-ε ≤
    ((exactNat (3*m+1):ℝ)-(oldNat (3*m+1):ℝ))/((3*m+1-9).factorial:ℝ)

def ExactGainOne : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (324:ℝ)-ε ≤
    ((exactNat (3*m+2):ℝ)-(oldNat (3*m+2):ℝ))/((3*m+2-11).factorial:ℝ)

end
end SuperpermutationResults.LowerAsymptotics
