module

public import SquareEntry
public import pairs.TwoClassification

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- Cancellation of the chart shared by the two full-run entries. -/
theorem pair_chart_quotient {G : Type*} [Group G] (g r : G) (m b c j : ℕ)
    (hb : g ^ b = g⁻¹) (hc : c = m+2+j) :
    (g^m * r * g^b * r * g^c * r * g^b) * (g^j * r * g^b)⁻¹ =
      g^m * r * g⁻¹ * r * g^(m+2) := by
  calc
    _ = g^m * r * g^b * r * (g^c * (g^j)⁻¹) := by group
    _ = g^m * r * g^b * r * g^(m+2) := by
      rw [hc, pow_add]
      group
    _ = _ := by rw [hb]

theorem square_chart_quotient (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2) :
    let g := cellG (3*m+2) hn
    let r := cellRho (3*m+2) hn
    let b := _root_.ChainReturns.twoMax m
    let c := _root_.ChainReturns.twoThreshold m - 2
    let j := _root_.ChainReturns.twoThreshold m - m - 4
    (g^m * r * g^b * r * g^c * r * g^b) * (g^j * r * g^b)⁻¹ =
      g^m * r * g⁻¹ * r * g^(m+2) := by
  dsimp only
  apply pair_chart_quotient
  · have hperiod := cellG_return_residue2 m hn
    have hp : _root_.ChainReturns.twoMax m + 1 = (m+1)*(2*m+1) := by
      unfold _root_.ChainReturns.twoMax
      ring
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, hp]
    exact hperiod
  · unfold _root_.ChainReturns.twoThreshold
    have hv : m+4 ≤ 2*m*(m+1) := by nlinarith
    omega

/-- Put the canonical collision into the two prefix charts used by an
actual occurrence. The first chart is A inverse and the second B inverse. -/
theorem square_entries_of_quotient (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2)
    (A B : Equiv.Perm (Fin (3*m+2+1)))
    (hquot : B * A⁻¹ = cellG (3*m+2) hn ^ m * cellRho (3*m+2) hn *
      (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn * cellG (3*m+2) hn ^ (m+2))
    (e : Fin (3*m+2+1) ≃ Alphabet (3*m+2+1)) :
    fullRunMapPower (by omega) (3*m+2-4)
      (fullEntry (3*m+2) hn (A.symm.trans e)) =
      runMapPower (by omega) (3*m+2-2)
        (fullEntry (3*m+2) hn (B.symm.trans e)) := by
  have he : (cellG (3*m+2) hn ^ m * cellRho (3*m+2) hn *
      (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn * cellG (3*m+2) hn ^ (m+2)).trans
      (B.symm.trans e) = A.symm.trans e := by
    apply Equiv.ext
    intro i
    simp only [Equiv.trans_apply]
    rw [← hquot, Equiv.Perm.mul_apply]
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.Perm.inv_def]
  have hh := square_full_entry m hm hn (B.symm.trans e)
  rw [he] at hh
  exact hh

end SuperpermutationLowerBound.Refinement
