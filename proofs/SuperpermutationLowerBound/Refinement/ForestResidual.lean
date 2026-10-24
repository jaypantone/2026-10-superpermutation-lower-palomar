module

public import SuperpermutationLowerBound.Section09.ResidualInequality

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

variable {k : ℕ}

/-- The initial vertex is the first visited vertex of its rotation class. -/
theorem pathTail_mem_firstVisited (hk : 1 ≤ k) (P : HamiltonianPath k) :
    P.tail ∈ firstVisitedVertices hk P := by
  apply (mem_firstVisitedVertices_iff hk P P.tail).mpr
  intro u _
  rw [P.vertexIndex_tail]
  exact Nat.zero_le _

/-- The apparent entrance exception cannot occur for the actual selected edge. -/
theorem pathForestMZero_empty (hk : 7 ≤ k) (P : HamiltonianPath k) :
    pathForestMZero hk P = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  rcases (mem_pathForestMZero hk P C).mp hC with ⟨hU, hweight, hdoor⟩
  have hnot := pathForest_doorEntry_entranceDoor_not_firstVisited hk P C
    ((mem_pathForestU hk P C).mp hU) hweight
  rw [hdoor] at hnot
  exact hnot (pathTail_mem_firstVisited (by omega) P)

/-- With the empty class retained, the three residual sums pay every
unabsorbed cheap component, without subtracting an exceptional unit. -/
theorem pathForestV_le_residualSums (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    pathForestV hk P ≤
      pathForestSigmaOne hk P + pathForestSigmaTwo hk P +
        pathForestSigmaThree hk P := by
  have hcard := pathForest_classes_card_identity hk P hP
  rw [pathForestMZero_empty hk P, Finset.card_empty] at hcard
  have h1 := pathForestSigmaOne_ge_MOne hk P
  have h2 := pathForestSigmaTwo_ge_MTwo hk P
  have h3 := pathForest_headUnion hk P hP
  have h3' := (Nat.le_max_right
    (max 0 (pathForestTerminalFullCount hk P - 1))
    (pathForestMThree hk P).card).trans (h3.2.trans h3.1)
  unfold pathForestV
  omega

/-- Natural residual excess, after paying the unabsorbed cheap components. -/
noncomputable def forestResidualExcess (hk : 7 ≤ k) (P : HamiltonianPath k) : ℕ :=
  forestHeadIndicator P (residualVertices (by omega) P) +
    pathForestSigmaOne hk P + pathForestSigmaTwo hk P + pathForestSigmaThree hk P -
      pathForestV hk P

/-- Exact residual equality on the actual reduced minimum path. -/
theorem pathForest_residual_exact (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    P.weight = (k + 1) * (k - 1).factorial - 3 +
      pathForestTotalBudget (by omega) P + pathForestV hk P +
        forestResidualExcess hk P := by
  have hid := pathForest_residualIdentity hk P hP
  have hpaid := pathForestV_le_residualSums hk P hP
  unfold forestResidualExcess
  omega

theorem pathForest_residual_RV (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    (k + 1) * (k - 1).factorial - 3 +
      pathForestTotalBudget (by omega) P + pathForestV hk P ≤ P.weight := by
  rw [pathForest_residual_exact hk P hP]
  omega

end SuperpermutationLowerBound.Refinement
