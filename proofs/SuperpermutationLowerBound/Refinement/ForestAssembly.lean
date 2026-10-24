module

public import SuperpermutationLowerBound.Refinement.ForestCapacity
public import SuperpermutationLowerBound.Refinement.ForestResidual
public import SuperpermutationLowerBound.Refinement.ForestIncidence
public import SuperpermutationLowerBound.Section10.Assembly

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open scoped BigOperators

variable {k : ℕ}

abbrev ForestVertex (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  WeakComponent (pathForest (by omega) P)

abbrev ForestEdge (hk : 7 ≤ k) (P : HamiltonianPath k) :=
  {e : ForestVertex hk P × ForestVertex hk P // (pathForestAbsorptionGraph hk P).Adj e.1 e.2}

def forestCheap (hk : 7 ≤ k) (P : HamiltonianPath k) (C : ForestVertex hk P) : Prop :=
  ∃ p : PathForestNonrootComponent hk P, p.1 = C ∧ p ∈ pathForestU hk P

def forestSpecial (hk : 7 ≤ k) (P : HamiltonianPath k) (C : ForestVertex hk P) : Prop :=
  (pathForestAbsorptionGraph hk P).Adj C C ∧ PathForestAbsorptionEdgeTypeI hk P C C

theorem forestCheap_nonroot (hk : 7 ≤ k) (P : HamiltonianPath k) {C : ForestVertex hk P}
    (h : forestCheap hk P C) : C ≠ pathForestRootComponent (by omega) P := by
  rcases h with ⟨p, rfl, hp⟩
  exact p.2

theorem forestCheap_iff (hk : 7 ≤ k) (P : HamiltonianPath k)
    (p : PathForestNonrootComponent hk P) : forestCheap hk P p.1 ↔ p ∈ pathForestU hk P := by
  constructor
  · rintro ⟨q, he, hq⟩
    have : q = p := Subtype.ext he
    simpa [this] using hq
  · exact fun h => ⟨p, rfl, h⟩

theorem forestSpecial_cheap (hk : 7 ≤ k) (P : HamiltonianPath k)
    {C : ForestVertex hk P} (h : forestSpecial hk P C) : forestCheap hk P C := by
  have ht := pathForestAbsorption_target_data hk P h.1
  exact ⟨⟨C, ht.1⟩, rfl, ht.2⟩

noncomputable def forestIntercept (hk : 7 ≤ k) (P : HamiltonianPath k)
    (δ β : ℚ) (C : ForestVertex hk P) : ℚ := by
  classical
  exact if C = pathForestRootComponent (by omega) P then β
    else if forestCheap hk P C then β - 1 else β - (((k - 1 : ℕ) : ℚ) - δ)

noncomputable def forestInCharge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (δ β : ℚ) (C : ForestVertex hk P) : ℚ := by
  classical
  exact if forestCheap hk P C then
    min (endpointCharge δ (pathForestComponentFirstDeficit hk P C - 1)) (β - 1) else 0

/-- The exceptional one-run loop reallocates its exact local slack to the
outgoing charge; the ordinary root/cheap/expensive intercepts are unchanged. -/
noncomputable def forestOutCharge (hk : 7 ≤ k) (P : HamiltonianPath k)
    (δ β : ℚ) (C : ForestVertex hk P) : ℚ := by
  classical
  exact if forestSpecial hk P C then β - δ
    else endpointCharge δ (pathForestComponentLastDeficit hk P C)

theorem forestInCharge_nonneg (hk : 7 ≤ k) (P : HamiltonianPath k)
    {δ β : ℚ} (hβ : 1 ≤ β) (C : ForestVertex hk P) : 0 ≤ forestInCharge hk P δ β C := by
  classical
  unfold forestInCharge
  split
  · exact le_min (endpointCharge_nonneg _ _) (by linarith)
  · rfl

theorem forestOutCharge_nonneg (hk : 7 ≤ k) (P : HamiltonianPath k)
    {δ β : ℚ} (hδ : δ < 1) (hβ : 1 ≤ β) (C : ForestVertex hk P) :
    0 ≤ forestOutCharge hk P δ β C := by
  classical
  unfold forestOutCharge
  split
  · linarith
  · exact endpointCharge_nonneg _ _

theorem forest_full_local_bound (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hδ0 : 0 < δ) (hδ : δ < 1)
    (hβ : 1 ≤ β) (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (P : HamiltonianPath k) (C : ForestVertex hk P) :
    rationalComponentSurplus hk P δ C + forestInCharge hk P δ β C +
      forestOutCharge hk P δ β C ≤ forestIntercept hk P δ β C := by
  classical
  by_cases hs : forestSpecial hk P C
  · have hcheap := forestSpecial_cheap hk P hs
    have hnr := forestCheap_nonroot hk P hcheap
    have hd := hs.2
    have hblocks : (pathForestComponentBlockCount (by omega) P C : ℚ) =
        ((k - 1 : ℕ) : ℚ) - 1 := by
      rw [hd.2.1]
      have hn : k - 2 + 1 = k - 1 := by omega
      have hnq : ((k - 2 : ℕ) : ℚ) + 1 = ((k - 1 : ℕ) : ℚ) := by exact_mod_cast hn
      linarith
    simp only [rationalComponentSurplus, hd.2.2.1, Nat.cast_one, mul_one,
      forestInCharge, forestOutCharge, forestIntercept, hcheap, hs, hnr,
      ite_true, ite_false, hd.2.2.2.1, Nat.sub_self, endpointCharge, Nat.cast_zero,
      zero_sub, max_eq_left (by linarith : -δ ≤ 0),
      min_eq_left (by linarith : (0 : ℚ) ≤ β - 1), hblocks]
    linarith
  · rw [forestOutCharge, if_neg hs]
    by_cases hr : C = pathForestRootComponent (by omega) P
    · subst C
      have hcheap : ¬forestCheap hk P (pathForestRootComponent (by omega) P) := by
        intro hc
        exact forestCheap_nonroot hk P hc rfl
      simp only [forestInCharge, hcheap, ite_false, add_zero,
        forestIntercept, ite_true]
      exact root_affine_capacity hk H (by linarith) hβα P
    · by_cases hc : forestCheap hk P C
      · rcases hc with ⟨p, rfl, hp⟩
        have hc := (forestCheap_iff hk P p).2 hp
        simp only [forestInCharge, forestIntercept, hc, hr, ite_true, ite_false]
        exact cheap_affine_capacity_clipped hk H hδ hβ hβα P p hp
      · let p : PathForestNonrootComponent hk P := ⟨C, hr⟩
        have hp : p ∉ pathForestU hk P := by
          intro hp
          exact hc ((forestCheap_iff hk P p).2 hp)
        simp only [forestInCharge, forestIntercept, hc, hr, ite_false, add_zero]
        exact expensive_affine_capacity hk H (by linarith) hβα P p hp

theorem forest_edge_bound (hk : 7 ≤ k) {δ β : ℚ}
    (hδ0 : 0 < δ) (hδ : δ < 1) (hβ : 1 ≤ β)
    (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P)
    {q C : ForestVertex hk P} (he : (pathForestAbsorptionGraph hk P).Adj q C) :
    forestIntercept hk P δ β C ≤ forestOutCharge hk P δ β q + forestInCharge hk P δ β C := by
  classical
  have ht := pathForestAbsorption_target_data hk P he
  have hc : forestCheap hk P C := ⟨⟨C, ht.1⟩, rfl, ht.2⟩
  simp only [forestIntercept, ht.1, hc, ite_false, ite_true, forestInCharge]
  rcases pathForestAbsorption_edgeTypes hk P hP he with hI | hII
  · have hq : q = C := hI.1.1.1.symm
    subst q
    have hs : forestSpecial hk P C := ⟨he, hI.1⟩
    rw [forestOutCharge, if_pos hs, hI.1.2.2.2.1]
    simp only [Nat.sub_self, endpointCharge, Nat.cast_zero, zero_sub,
      max_eq_left (by linarith : -δ ≤ 0), min_eq_left (by linarith : (0 : ℚ) ≤ β - 1)]
    linarith
  · have hs : ¬forestSpecial hk P q := by
      intro hs
      have hqC := pathForestAbsorptionGraph_out_unique hk P hs.1 he
      subst C
      exact hII.2 hs.2
    rw [forestOutCharge, if_neg hs]
    have hf := hII.1.2.1
    have hl := hII.1.2.2.1
    have hsum := hII.1.2.2.2.1
    have hfq : 2 ≤ (pathForestComponentFirstDeficit hk P C : ℚ) := by exact_mod_cast hf
    have hlq : 2 ≤ (pathForestComponentLastDeficit hk P q : ℚ) := by exact_mod_cast hl
    have hsumq : (k : ℚ) ≤ (pathForestComponentFirstDeficit hk P C : ℚ) +
        (pathForestComponentLastDeficit hk P q : ℚ) := by exact_mod_cast hsum
    have hkq : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hA : endpointCharge δ (pathForestComponentFirstDeficit hk P C - 1) =
        (pathForestComponentFirstDeficit hk P C : ℚ) - 1 - δ := by
      rw [endpointCharge, Nat.cast_sub (by omega : 1 ≤ pathForestComponentFirstDeficit hk P C),
        Nat.cast_one, max_eq_right (by linarith)]
    have hB : endpointCharge δ (pathForestComponentLastDeficit hk P q) =
        (pathForestComponentLastDeficit hk P q : ℚ) - δ := by
      rw [endpointCharge, max_eq_right (by linarith)]
    rw [hA, hB]
    by_cases ha : (pathForestComponentFirstDeficit hk P C : ℚ) - 1 - δ ≤ β - 1
    · rw [min_eq_left ha]
      rw [hkq] at hβα
      linarith
    · rw [min_eq_right (le_of_not_ge ha)]
      linarith

open Classical in
theorem forest_head_intercept_sum (hk : 7 ≤ k) {δ β : ℚ}
    (hβ : 1 ≤ β) (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ) (P : HamiltonianPath k) :
    (∑ C : ForestVertex hk P,
      if ¬∃ q, (pathForestAbsorptionGraph hk P).Adj q C then forestIntercept hk P δ β C else 0) ≤
      β + (((k - 1 : ℕ) : ℚ) - δ) * (pathForestV hk P : ℚ) := by
  classical
  let U := (pathForestUnabsorbedU hk P).image (fun p => p.1)
  let α : ℚ := ((k - 1 : ℕ) : ℚ) - δ
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hUcard : U.card = pathForestV hk P := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      pathForestUnabsorbedU_card]
  have hp (C : ForestVertex hk P) :
      (if ¬∃ q, (pathForestAbsorptionGraph hk P).Adj q C then forestIntercept hk P δ β C else 0) ≤
        (if C = pathForestRootComponent (by omega) P then β else 0) +
        (if C ∈ U then α else 0) := by
    by_cases hin : ∃ q, (pathForestAbsorptionGraph hk P).Adj q C
    · simp only [hin, not_true_eq_false, ite_false]
      have hroot : 0 ≤ (if C = pathForestRootComponent (by omega) P then β else 0) := by
        split <;> linarith
      have hcheap : 0 ≤ (if C ∈ U then α else 0) := by split <;> linarith
      linarith
    · simp only [hin, not_false_eq_true, ite_true]
      by_cases hr : C = pathForestRootComponent (by omega) P
      · simp only [forestIntercept, hr, ite_true]
        split <;> linarith
      · by_cases hc : forestCheap hk P C
        · have hU : C ∈ U := by
            rcases hc with ⟨p, hpC, hp⟩
            apply Finset.mem_image.mpr
            refine ⟨p, ?_, hpC⟩
            apply (mem_pathForestUnabsorbedU hk P p).mpr
            exact ⟨hp, by simpa [hpC] using hin⟩
          simp only [forestIntercept, hr, hc, hU, ite_false, ite_true, zero_add]
          dsimp [α]
          linarith
        · simp only [forestIntercept, hr, hc, ite_false, zero_add]
          have : 0 ≤ (if C ∈ U then α else 0) := by split <;> linarith
          linarith
  have hsum := Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) => hp C)
  rw [Finset.sum_add_distrib] at hsum
  have hroot : (∑ C : ForestVertex hk P,
      if C = pathForestRootComponent (by omega) P then β else 0) = β := by simp
  have hfilter : Finset.univ.filter (fun C => C ∈ U) = U := by ext C; simp
  have hU : (∑ C : ForestVertex hk P, if C ∈ U then α else 0) = α * (pathForestV hk P : ℚ) := by
    rw [← Finset.sum_filter, hfilter]
    simp [hUcard, mul_comm]
  rw [hroot, hU] at hsum
  exact hsum

/-- The clipped incidence theorem on the literal absorption graph, with the
actual component partition and exact number of unabsorbed cheap components. -/
theorem pathForest_affine_assembly (hk : 7 ≤ k) {δ β : ℚ}
    (H : HereditarySegmentBound hk δ β) (hδ0 : 0 < δ) (hδ : δ < 1)
    (hβ : 1 ≤ β) (hβα : β ≤ ((k - 1 : ℕ) : ℚ) - δ)
    (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    ((k - 1).factorial : ℚ) ≤ (((k - 1 : ℕ) : ℚ) - δ) *
      ((pathForestTotalBudget (by omega) P : ℚ) + (pathForestV hk P : ℚ)) + β := by
  classical
  let E := ForestEdge hk P
  letI : Fintype E := Fintype.ofFinite E
  let source : E → ForestVertex hk P := fun e => e.1.1
  let target : E → ForestVertex hk P := fun e => e.1.2
  have hs : Function.Injective source := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext hef
    exact pathForestAbsorptionGraph_out_unique hk P e.2 (by
      have h : e.1.1 = f.1.1 := hef
      rw [h]
      exact f.2)
  have ht : Function.Injective target := by
    intro e f hef
    apply Subtype.ext
    apply Prod.ext _ hef
    exact pathForestAbsorptionGraph_in_unique hk P e.2 (by
      have h : e.1.2 = f.1.2 := hef
      rw [h]
      exact f.2)
  have hlocal (C : ForestVertex hk P) : rationalComponentSurplus hk P δ C +
      (if ∃ e, target e = C then forestInCharge hk P δ β C else 0) +
      (if ∃ e, source e = C then forestOutCharge hk P δ β C else 0) ≤ forestIntercept hk P δ β C := by
    have hfull := forest_full_local_bound hk H hδ0 hδ hβ hβα P C
    have ha := forestInCharge_nonneg hk P (δ := δ) hβ C
    have hb := forestOutCharge_nonneg hk P hδ hβ C
    split <;> split <;> linarith
  have hedge (e : E) : forestIntercept hk P δ β (target e) ≤
      forestOutCharge hk P δ β (source e) + forestInCharge hk P δ β (target e) :=
    forest_edge_bound hk hδ0 hδ hβ hβα P hP e.2
  have hsum := finite_incidence_assembly source target hs ht
    (rationalComponentSurplus hk P δ) (forestIntercept hk P δ β)
    (forestInCharge hk P δ β) (forestOutCharge hk P δ β) hlocal hedge
  have hin (C : ForestVertex hk P) : (∃ e, target e = C) ↔
      ∃ q, (pathForestAbsorptionGraph hk P).Adj q C := by
    constructor
    · rintro ⟨e, he⟩
      exact ⟨source e, by simpa [← he, source, target] using e.2⟩
    · rintro ⟨q, hq⟩
      exact ⟨⟨(q, C), hq⟩, rfl⟩
  simp only [hin] at hsum
  have hhead := forest_head_intercept_sum hk hβ hβα P
  have hfinal := hsum.trans hhead
  rw [rationalComponentSurplus_sum hk P δ] at hfinal
  nlinarith

end SuperpermutationLowerBound.Refinement
