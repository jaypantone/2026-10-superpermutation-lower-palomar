module

public import SuperpermutationLowerBound.Section06.Charging

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- The literal deficit list of singleton-two clusters separated by the
specified positive zero gaps. -/
def regularPath : List ℕ → List ℕ
  | [] => [2]
  | gap :: gaps => 2 :: (List.replicate gap 0 ++ regularPath gaps)

/-- Hereditary chain packing, stated on literal contiguous factors.
The gaps `a-1` stay in a chain and the gaps `a-2` link successive chains.
The bounding zeros ensure that all singleton twos are whole positive clusters. -/
def ChainPacking (a : ℕ) (p t : ℚ) (d : List ℕ) : Prop :=
  ∀ gaps : List ℕ,
    (∀ gap ∈ gaps, gap = a - 1 ∨ gap = a - 2) →
    ∀ before after : List ℕ,
      d = before ++ (0 :: (regularPath gaps ++ [0])) ++ after →
      2 * ((gaps.length : ℚ) + 1) ≤
        2 * p + t * (gaps.count (a - 2) : ℚ)

theorem ChainPacking.factor {a : ℕ} {p t : ℚ} {d factor before after : List ℕ}
    (h : ChainPacking a p t d) (heq : d = before ++ factor ++ after) :
    ChainPacking a p t factor := by
  intro gaps hg pre post hfactor
  apply h gaps hg (before ++ pre) (post ++ after)
  simp only [heq, hfactor, List.append_assoc]

theorem ChainPacking.drop_take {a : ℕ} {p t : ℚ} {d : List ℕ}
    (h : ChainPacking a p t d) (i j : ℕ) :
    ChainPacking a p t ((d.drop i).take j) := by
  apply h.factor (before := d.take i) (after := (d.drop i).drop j)
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem ChainPacking.mono {a : ℕ} {p t t' : ℚ} {d : List ℕ}
    (h : ChainPacking a p t d) (htt' : t ≤ t') :
    ChainPacking a p t' d := by
  intro gaps hg before after heq
  exact (h gaps hg before after heq).trans (by
    gcongr)

theorem legal_drop_take {n : ℕ} {d : List ℕ}
    (h : IsLegalDeficitSequence n d) (i j : ℕ)
    (hne : (d.drop i).take j ≠ []) :
    IsLegalDeficitSequence n ((d.drop i).take j) := by
  have hlen : 0 < ((d.drop i).take j).length := List.length_pos_iff.mpr hne
  have hi : i < d.length := by
    simp only [List.length_take, List.length_drop] at hlen
    omega
  have hs := h.slice (start := i) (sliceLength := min j (d.length - i))
    (by simp only [List.length_take, List.length_drop] at hlen; omega) (by omega)
  have heq : ((d.drop i).take j) = (d.drop i).take (min j (d.length - i)) := by
    simpa only [List.length_drop] using
      (List.take_eq_take_min (l := d.drop i) (i := j))
  rw [heq]
  exact hs

theorem legal_factor {n : ℕ} {d factor before after : List ℕ}
    (h : IsLegalDeficitSequence n d) (heq : d = before ++ factor ++ after)
    (hne : factor ≠ []) : IsLegalDeficitSequence n factor := by
  have hf : (d.drop before.length).take factor.length = factor := by
    simp [heq, List.append_assoc]
  have hs := legal_drop_take h before.length factor.length (by simpa [hf] using hne)
  simpa only [hf] using hs

end SuperpermutationLowerBound.Refinement
