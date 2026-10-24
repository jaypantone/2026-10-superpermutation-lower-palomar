module

public import bridge.FrozenBounds
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Sequences in the frozen asymptotic statements. Differences below are
taken after casting to the reals, so natural subtraction cannot truncate them.
The old and reference expressions are comparison formulas, not assumptions
about optimal superpermutation lengths. -/
namespace SuperpermutationBounds.ChainReturns.Asymptotic

noncomputable section

def F3Nat (K : ℕ) : ℕ := K.factorial + (K-1).factorial + (K-2).factorial

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

/-- Below the general-table range the frozen initial rows are retained.
These finitely many values have no effect on any limit. -/
def oldParameters (K : ℕ) : ℚ × ℚ :=
  if K < 13 then exactParameters K else oldGeneralParameters (K-1)

def oldNat (K : ℕ) : ℕ := paperBound K (oldParameters K).1 (oldParameters K).2

def correctionQ (K : ℕ) (p t : ℚ) : ℚ :=
  (2 * ((K-2).factorial : ℚ) - 2*((K : ℚ)-2) - 4*p/t) /
    ((K : ℚ)^2 - 4*K + 1 - 2*((K : ℚ)-1)/t)

def correctionReal (K : ℕ) (p t : ℝ) : ℝ :=
  (2 * ((K-2).factorial : ℝ) - 2*((K : ℝ)-2) - 4*p/t) /
    ((K : ℝ)^2 - 4*K + 1 - 2*((K : ℝ)-1)/t)

def referenceCorrectionQ (K : ℕ) : ℚ :=
  2 * (((K-2).factorial : ℚ) - ((K : ℚ)-2)) /
    ((K : ℚ)^2 - 4*K + 1)

def referenceCorrectionReal (K : ℕ) : ℝ :=
  2 * (((K-2).factorial : ℝ) - ((K : ℝ)-2)) /
    ((K : ℝ)^2 - 4*K + 1)

/-- The explicit all-size Fritsch--Halfar reference formula. This definition
does not assert an independent verification of Halfar's proof package. -/
def referenceNat (K : ℕ) : ℕ :=
  F3Nat K + K - 3 + ⌈referenceCorrectionQ K⌉₊

def exactReal (K : ℕ) : ℝ := exactNat K
def quadraticReal (K : ℕ) : ℝ := quadraticNat K
def oldReal (K : ℕ) : ℝ := oldNat K
def referenceReal (K : ℕ) : ℝ := referenceNat K

@[simp] theorem correctionQ_cast (K : ℕ) (p t : ℚ) :
    (correctionQ K p t : ℝ) = correctionReal K (p : ℝ) (t : ℝ) := by
  simp [correctionQ, correctionReal]

@[simp] theorem referenceCorrectionQ_cast (K : ℕ) :
    (referenceCorrectionQ K : ℝ) = referenceCorrectionReal K := by
  simp [referenceCorrectionQ, referenceCorrectionReal]

theorem paperBound_eq_base_ceil (K : ℕ) (p t : ℚ) :
    paperBound K p t = F3Nat K + K - 3 + ⌈correctionQ K p t⌉₊ := rfl

end
end SuperpermutationBounds.ChainReturns.Asymptotic
