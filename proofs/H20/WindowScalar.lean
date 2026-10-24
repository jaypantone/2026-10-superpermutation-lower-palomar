module

public import H20.ActualSegments
public import SuperpermutationLowerBound.Refinement.EndpointBounds
public import Mathlib.Tactic

@[expose] public section

/-!
A direct window-to-hereditary conversion, retaining actual run factors.
-/
namespace H20
open SuperpermutationLowerBound
open SuperpermutationLowerBound.Refinement
open SuperpermLowerBounds

/-- The natural-number zero-run and deficit-one hypotheses used by the
published list-capacity lemma. -/
structure RunConditions (k : ℕ) (D : List ℕ) : Prop where
  run : ∀ L1 R L2 : List ℕ, D = L1 ++ R ++ L2 →
    (∀ u ∈ R, u = 0) → R.length ≤ k - 2
  runR : ∀ (L1 R : List ℕ) (z : ℕ) (L2 : List ℕ), D = L1 ++ R ++ z :: L2 →
    (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3
  runL : ∀ (L1 : List ℕ) (z : ℕ) (R L2 : List ℕ), D = L1 ++ z :: R ++ L2 →
    (∀ u ∈ R, u = 0) → 0 < z → R.length ≤ k - 3
  unit : ChainC.UnitRule D

theorem runConditions_of_legal {k : ℕ} (hk : 7 ≤ k) {D : List ℕ}
    (H : IsLegalDeficitSequence (k - 1) D) : RunConditions k D := by
  constructor
  · intro L1 R L2 he hz
    by_cases hR : R = []
    · simp [hR]
    have hlegal := legal_factor H he hR
    have hb := hlegal.rule1
    rw [if_pos hz] at hb
    omega
  · intro L1 R z L2 he hz hzp
    by_cases hR : R = []
    · simp [hR]
    have hlegal : IsLegalDeficitSequence (k - 1) (R ++ [z]) :=
      legal_factor H (before := L1) (after := L2) (by simpa [List.append_assoc] using he)
        (by simp)
    have hzero : ∀ j, j < R.length → deficitAt (R ++ [z]) (0 + j) = 0 := by
      intro j hj
      have hh := hz R[j] (List.getElem_mem hj)
      simpa [deficitAt, List.getElem?_append, hj] using hh
    have hb := legal_zeroInterval_bounds hlegal
      (start := 0) (blockLength := R.length) (List.length_pos_iff.mpr hR)
      (by simp) hzero
    have hn : ¬∀ x ∈ R ++ [z], x = 0 := by
      intro hall
      have hh := hall z (by simp)
      omega
    have := hb.2 hn
    omega
  · intro L1 z R L2 he hz hzp
    by_cases hR : R = []
    · simp [hR]
    have hlegal : IsLegalDeficitSequence (k - 1) (z :: R) :=
      legal_factor H (before := L1) (after := L2) (by simpa [List.append_assoc] using he)
        (by simp)
    have hzero : ∀ j, j < R.length → deficitAt (z :: R) (1 + j) = 0 := by
      intro j hj
      have hh := hz R[j] (List.getElem_mem hj)
      simpa [deficitAt, Nat.add_comm, hj] using hh
    have hb := legal_zeroInterval_bounds hlegal
      (start := 1) (blockLength := R.length) (List.length_pos_iff.mpr hR)
      (by simp only [List.length_cons]; omega) hzero
    have hn : ¬∀ x ∈ z :: R, x = 0 := by
      intro hall
      have hh := hall z (by simp)
      omega
    have := hb.2 hn
    omega
  · intro L1 L2 z he
    by_contra hz
    have h := H.rule2 L1.length (by simp [he])
    apply h
    simp [deficitAt, he, List.getElem?_append]
    omega

/-- The uniformly bounded endpoint prices give the whole-list affine
inequality. The hypotheses quantify over all window factors of this list. -/
theorem affine_of_windows {k cn bn q : ℕ} (hk : 7 ≤ k)
    (hc : cn ≤ q * (k - 5))
    (hA : 0 < (q : ℚ) * ((k : ℚ) - 3) - cn)
    {D : List ℕ} (H : IsLegalDeficitSequence (k - 1) D)
    (hW : ∀ L1 W L2 : List ℕ, D = L1 ++ W ++ L2 →
      ChainC.IsWindow W → ChainC.WindowBound k cn bn q W) :
    (2 * q / ((q : ℚ) * ((k : ℚ) - 3) - cn)) * D.length -
      (2 * (q : ℚ) * ((k : ℚ) - 2) + bn) /
        ((q : ℚ) * ((k : ℚ) - 3) - cn) ≤ D.sum := by
  have hR := runConditions_of_legal hk H
  let x := D.head H.nonempty
  let y := D.getLast H.nonempty
  have hx : ∃ t, D = x :: t := ⟨D.tail, (List.cons_head_tail H.nonempty).symm⟩
  have hy : ∃ t, D = t ++ [y] := ⟨D.dropLast, (List.dropLast_append_getLast H.nonempty).symm⟩
  have hcap := ChainC.chain_capacity_list (k := k) (cn := cn) (bn := bn) (q := q)
    (by omega) hc hx hy hR.run hR.runR hR.runL hR.unit hW
  have hxprice := ChainC.priceC_le (k := k) (cn := cn) (bn := bn) (q := q)
    (by omega) hc x D.length
  have hyprice := ChainC.priceC_le (k := k) (cn := cn) (bn := bn) (q := q)
    (by omega) hc y D.length
  have hcap' : 2 * (q : ℤ) * D.length ≤
      ((q : ℤ) * ((k : ℤ) - 3) - cn) * (D.sum : ℤ) +
        (2 * (q : ℤ) * ((k : ℤ) - 2) + bn) := by linarith
  have hcapQ : 2 * (q : ℚ) * D.length ≤
      ((q : ℚ) * ((k : ℚ) - 3) - cn) * (D.sum : ℚ) +
        (2 * (q : ℚ) * ((k : ℚ) - 2) + bn) := by
    have cast_capacity (Q K C B L T : ℕ)
        (h : 2 * (Q : ℤ) * L ≤ ((Q : ℤ) * ((K : ℤ) - 3) - C) * (T : ℤ) +
          (2 * (Q : ℤ) * ((K : ℤ) - 2) + B)) :
        2 * (Q : ℚ) * L ≤ ((Q : ℚ) * ((K : ℚ) - 3) - C) * (T : ℚ) +
          (2 * (Q : ℚ) * ((K : ℚ) - 2) + B) := by
      exact_mod_cast h
    exact cast_capacity q k cn bn D.length D.sum hcap' 
  rw [div_mul_eq_mul_div, ← sub_div]
  apply (div_le_iff₀ hA).2
  nlinarith

/-- Any certified window statement supplies our actual hereditary forest
interface, with the stated rational parameters and no duplicated end payment. -/
theorem hereditary_of_wstatement {k cn bn q : ℕ} (hk : 7 ≤ k)
    (hc : cn ≤ q * (k - 5))
    (hA : 0 < (q : ℚ) * ((k : ℚ) - 3) - cn)
    (HW : S.WStatement k cn bn q) :
    HereditarySegmentBound hk
      (2 * q / ((q : ℚ) * ((k : ℚ) - 3) - cn))
      ((2 * (q : ℚ) * ((k : ℚ) - 2) + bn) /
        ((q : ℚ) * ((k : ℚ) - 3) - cn)) := by
  intro p hp s i j
  let D := (s.deficitString.drop i).take j
  by_cases hD : D = []
  · have hb : 0 ≤ (2 * (q : ℚ) * ((k : ℚ) - 2) + bn) /
        ((q : ℚ) * ((k : ℚ) - 3) - cn) := by
      apply div_nonneg
      · have hkQ : (7 : ℚ) ≤ k := by exact_mod_cast hk
        exact add_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
      · exact le_of_lt hA
    simpa [D, hD] using neg_nonpos.mpr hb
  · have hl := legal_drop_take s.deficitString_legal i j hD
    apply affine_of_windows hk hc hA hl
    intro L1 W L2 he hw
    have hwhole : s.deficitString =
        (s.deficitString.take i ++ L1) ++ W ++
          (L2 ++ (s.deficitString.drop i).drop j) := by
      calc
        s.deficitString = s.deficitString.take i ++
            ((s.deficitString.drop i).take j ++ (s.deficitString.drop i).drop j) := by simp
        _ = _ := by rw [show (s.deficitString.drop i).take j = L1 ++ W ++ L2 from he]; simp [List.append_assoc]
    have hslice : (s.deficitString.drop (s.deficitString.take i ++ L1).length).take W.length = W := by
      calc
        (s.deficitString.drop (s.deficitString.take i ++ L1).length).take W.length =
            (((s.deficitString.take i ++ L1) ++ W ++
              (L2 ++ (s.deficitString.drop i).drop j)).drop
                (s.deficitString.take i ++ L1).length).take W.length :=
          congrArg (fun D => (D.drop (s.deficitString.take i ++ L1).length).take W.length) hwhole
        _ = W := by
          rw [List.append_assoc (s.deficitString.take i ++ L1) W
            (L2 ++ (s.deficitString.drop i).drop j), List.drop_left, List.take_left]
    have hh := actualSegment_factor_window hk HW p hp s
      (s.deficitString.take i ++ L1).length W.length (hslice.symm ▸ hw)
    simpa only [hslice] using hh

end H20
