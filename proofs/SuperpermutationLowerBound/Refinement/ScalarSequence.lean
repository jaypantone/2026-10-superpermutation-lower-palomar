module

public import SuperpermutationLowerBound.Refinement.ScalarCore

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PositiveClusterChain

def scalarEnergy (a : ℕ) (p t : ℚ) (d : List ℕ) : ℚ :=
  chainLambda a t * d.sum - 2 * t * d.length + chainIntercept a p t

theorem exists_init_last {d : List ℕ} (hne : d ≠ []) :
    ∃ init : List ℕ, ∃ last : ℕ, d = init ++ [last] := by
  induction d with
  | nil => contradiction
  | cons x xs ih =>
      by_cases hxs : xs = []
      · exact ⟨[], x, by simp [hxs]⟩
      · obtain ⟨init, last, h⟩ := ih hxs
        exact ⟨x :: init, last, by simp [h]⟩

theorem render_last_positive (chain : PositiveClusterChain)
    (hNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    ∀ x ∈ chain.render.getLast?, 0 < x := by
  induction chain with
  | last K =>
      intro x hx
      exact hPos K (by simp [clusters]) x (List.mem_of_mem_getLast? hx)
  | cons K gap tail ih =>
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL; exact hNe L (by simp [clusters, hL])
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL; exact hPos L (by simp [clusters, hL])
      have htailRender := tail.render_nonempty htailNe
      intro x hx
      apply ih htailNe htailPos x
      simpa [render, List.getLast?_eq_getLast_of_ne_nil htailRender] using hx

theorem positive_entry_energy {a x : ℕ} {p t : ℚ}
    (hp : 0 ≤ p) (ht : 0 < t) (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (hx : 0 < x) : 0 ≤ chainLambda a t * (x : ℚ) - 2 * t := by
  have hlambda := (scalar_margin hp ht hmargin).1
  have hc := (scalar_margin hp ht hmargin).2
  have hxQ : (1 : ℚ) ≤ x := by exact_mod_cast hx
  have hmul := mul_nonneg (le_of_lt hlambda) (sub_nonneg.mpr hxQ)
  nlinarith

/-- The legal-sequence theorem includes the empty list. Legality itself is
required exactly for nonempty lists, retaining the accepted definition. -/
theorem scalarEnergy_nonnegative {a : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (hpt : p ≤ t) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    (d : List ℕ) (hlegal : d ≠ [] → IsLegalDeficitSequence (a + 2) d)
    (hpacking : ChainPacking a p t d) : 0 ≤ scalarEnergy a p t d := by
  have hB : 0 ≤ chainIntercept a p t := by unfold chainIntercept; positivity
  have main : ∀ m : ℕ, ∀ d : List ℕ, d.length = m →
      (d ≠ [] → IsLegalDeficitSequence (a + 2) d) →
      ChainPacking a p t d → 0 ≤ scalarEnergy a p t d := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro d hlen hlegal hpacking
      by_cases hnil : d = []
      · simpa [scalarEnergy, hnil] using hB
      have hlegal' := hlegal hnil
      by_cases hall : ∀ x ∈ d, x = 0
      · have hr : d.length ≤ a + 1 := by
          have h := hlegal'.rule1
          rw [if_pos hall] at h
          simpa using h
        have hrep : d = List.replicate d.length 0 := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
        have hsum : d.sum = 0 := by rw [hrep]; simp
        have hrQ : (d.length : ℚ) ≤ a + 1 := by exact_mod_cast hr
        have hpay := mul_nonneg (show 0 ≤ 2 * t by positivity) (sub_nonneg.mpr hrQ)
        simp only [scalarEnergy, hsum, Nat.cast_zero, mul_zero, zero_sub, chainIntercept]
        nlinarith
      have hpositive : ∃ x ∈ d, 0 < x := by
        push_neg at hall
        obtain ⟨x, hx, hxne⟩ := hall
        exact ⟨x, hx, by omega⟩
      obtain ⟨init, last, hlast⟩ := exists_init_last hnil
      by_cases hlastPos : 0 < last
      · have hshort : init.length < m := by simp [hlast] at hlen; omega
        have hinitLegal : init ≠ [] → IsLegalDeficitSequence (a + 2) init := by
          intro hne
          exact legal_factor hlegal' (before := []) (after := [last]) (by simpa using hlast) hne
        have hinitPacking := hpacking.factor (before := []) (after := [last]) (by simpa using hlast)
        have hi := ih init.length hshort init rfl hinitLegal hinitPacking
        have hpaye := positive_entry_energy hp ht hmargin hlastPos
        simp only [scalarEnergy, hlast, List.sum_append, List.sum_singleton,
          List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at *
        nlinarith
      have hlastZero : last = 0 := by omega
      cases d with
      | nil => contradiction
      | cons x xs =>
        by_cases hx : 0 < x
        · have hshort : xs.length < m := by simp at hlen; omega
          have hxsLegal : xs ≠ [] → IsLegalDeficitSequence (a + 2) xs := by
            intro hne
            exact legal_factor hlegal' (before := [x]) (after := []) (by simp) hne
          have hxsPacking : ChainPacking a p t xs :=
            hpacking.factor (before := [x]) (after := []) (by simp)
          have hi := ih xs.length hshort xs rfl hxsLegal hxsPacking
          have hpaye := positive_entry_energy hp ht hmargin hx
          simp only [scalarEnergy, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
          nlinarith
        · have hxZero : x = 0 := by omega
          subst x
          obtain ⟨dec, _⟩ := exists_positiveClusterDecomposition hpositive
          have hrender := dec.chain.render_nonempty dec.cluster_nonempty
          have hlead : 0 < dec.leadingZeros := by
            by_contra h
            have hzero : dec.leadingZeros = 0 := by omega
            have hz : 0 ∈ dec.chain.render.head? := by
              have hh := congrArg List.head? dec.rebuild
              simpa [hzero, hrender] using hh.symm
            exact (Nat.lt_irrefl 0) (dec.chain.render_head_positive
              dec.cluster_nonempty dec.cluster_positive 0 hz)
          have htrail : 0 < dec.trailingZeros := by
            by_contra h
            have hzero : dec.trailingZeros = 0 := by omega
            have hz : 0 ∈ dec.chain.render.getLast? := by
              have hh := congrArg List.getLast? dec.rebuild
              have hdlast : (0 :: xs).getLast? = some 0 := by simp [hlast, hlastZero]
              rw [hdlast] at hh
              simpa [hzero, List.getLast?_eq_getLast_of_ne_nil hrender] using hh.symm
            exact (Nat.lt_irrefl 0) (render_last_positive dec.chain
              dec.cluster_nonempty dec.cluster_positive 0 hz)
          have hcore := zeroEndedCore_bound ha hp hpt ht hmargin dec.chain
            (by simpa only [dec.rebuild] using hlegal')
            (by simpa only [dec.rebuild] using hpacking)
            hlead htrail dec.cluster_nonempty dec.cluster_positive dec.gap_positive
          simpa only [scalarEnergy, dec.rebuild] using hcore
  exact main d.length d rfl hlegal hpacking

theorem deficit_lower_bound_of_chainPacking {a : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (hpt : p ≤ t) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    {d : List ℕ} (hlegal : IsLegalDeficitSequence (a + 2) d)
    (hpacking : ChainPacking a p t d) :
    0 ≤ ((a : ℚ) * t - 2) * (d.sum : ℚ) - 2 * t * (d.length : ℚ) +
      2 * t * (a + 1) + 4 * p := by
  have h := scalarEnergy_nonnegative ha hp hpt ht hmargin d (fun _ => hlegal) hpacking
  simpa [scalarEnergy, chainLambda, chainIntercept, add_assoc] using h

/-- The rational affine form, for every contiguous factor including the
empty factor. This is the interface used by the endpoint and forest proof. -/
theorem deficit_factor_affine_bound {a : ℕ} {p t : ℚ}
    (ha : 4 ≤ a) (hp : 0 ≤ p) (hpt : p ≤ t) (ht : 0 < t)
    (hmargin : 4 * p + 6 ≤ t * (a - 2))
    {d : List ℕ} (hlegal : IsLegalDeficitSequence (a + 2) d)
    (hpacking : ChainPacking a p t d) (i j : ℕ) :
    (2 * t / chainLambda a t) * (((d.drop i).take j).length : ℚ) -
      chainIntercept a p t / chainLambda a t ≤ (((d.drop i).take j).sum : ℚ) := by
  have h := scalarEnergy_nonnegative ha hp hpt ht hmargin ((d.drop i).take j)
    (legal_drop_take hlegal i j) (hpacking.drop_take i j)
  have hlambda := (scalar_margin hp ht hmargin).1
  rw [show (2 * t / chainLambda a t) * (((d.drop i).take j).length : ℚ) -
      chainIntercept a p t / chainLambda a t =
      (2 * t * (((d.drop i).take j).length : ℚ) - chainIntercept a p t) /
        chainLambda a t by ring]
  apply (div_le_iff₀ hlambda).2
  dsimp [scalarEnergy] at h
  nlinarith

end SuperpermutationLowerBound.Refinement
