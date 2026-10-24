module

public import SuperpermutationLowerBound.Foundation.Graph
public import Mathlib.Data.List.Permutation
public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound

/-! Frozen Section 1 overlap results (Lemmas 1.2 and 1.3). -/

open PermutationVertex

variable {k : ℕ}

private theorem noShorterOverlap_of_cut {u v : PermutationVertex k} {t : ℕ}
    (htk : t < k) (hword : v.1 = u.1.drop t ++ (v.1.drop (k - t))) :
    ∀ s, 1 ≤ s → s < t → ¬ OverlapsAt u v s := by
  intro s _hs hst hov
  have hslt : s < u.1.length := by simpa [u.length] using (lt_trans hst htk)
  have htlt : t < u.1.length := by simpa [u.length] using htk
  have hks : k - s ≠ 0 := by omega
  have hheadv : v.1.head? = u.1[t]? := by
    rw [hword, List.head?_append, List.head?_drop,
      List.getElem?_eq_getElem htlt]
    simp
  have hhead := congrArg List.head? hov
  rw [List.head?_drop, List.head?_take, if_neg hks, hheadv,
    List.getElem?_eq_getElem hslt, List.getElem?_eq_getElem htlt] at hhead
  have helem : u.1[s] = u.1[t] := Option.some.inj hhead
  have : s = t := (u.nodup.getElem_inj_iff).mp helem
  omega

private theorem noShorterOverlap_of_append {u v : PermutationVertex k} {t : ℕ}
    (htk : t < k) {suffix : Word k} (hword : v.1 = u.1.drop t ++ suffix) :
    ∀ s, 1 ≤ s → s < t → ¬ OverlapsAt u v s := by
  have hlen : suffix.length = t := by
    have hvlen := v.length
    rw [hword, List.length_append, List.length_drop, u.length] at hvlen
    omega
  have hsuffix : suffix = v.1.drop (k - t) := by
    calc
      suffix = (u.1.drop t ++ suffix).drop (u.1.drop t).length := by simp
      _ = v.1.drop (u.1.drop t).length := by rw [← hword]
      _ = v.1.drop (k - t) := by simp [u.length]
  apply noShorterOverlap_of_cut htk
  simpa [hsuffix] using hword

/-- Frozen Lemma 1.2, general form: a weight-`t` target is the retained suffix followed by
an arrangement of the cut prefix, and all smaller positive overlaps are excluded. -/
theorem overlapWeight_eq_iff_drop_append_arrangement
    (u v : PermutationVertex k) (t : ℕ) (_hk : 3 ≤ k) (_hne : u ≠ v)
    (ht : 1 ≤ t) (_htk : t ≤ k) :
    overlapWeight u v = t ↔
      ∃ suffix : Word k,
        suffix.Perm (u.1.take t) ∧
        v.1 = u.1.drop t ++ suffix ∧
        ∀ s, 1 ≤ s → s < t → ¬ OverlapsAt u v s := by
  rw [overlapWeight_eq_iff_overlap_no_shorter u v ht]
  constructor
  · rintro ⟨hov, hshort⟩
    let suffix := v.1.drop (k - t)
    have hword : v.1 = u.1.drop t ++ suffix := by
      calc
        v.1 = v.1.take (k - t) ++ v.1.drop (k - t) :=
          (v.1.take_append_drop (k - t)).symm
        _ = u.1.drop t ++ suffix := by rw [← hov]
    have hvperm : v.1.Perm (u.1.drop t ++ u.1.take t) := by
      calc
        v.1.Perm u.1 := v.perm u
        u.1.Perm (u.1.take t ++ u.1.drop t) :=
          List.Perm.of_eq (u.1.take_append_drop t).symm
        (u.1.take t ++ u.1.drop t).Perm (u.1.drop t ++ u.1.take t) :=
          List.perm_append_comm
    rw [hword] at hvperm
    have hsuffix : suffix.Perm (u.1.take t) :=
      (List.perm_append_left_iff (u.1.drop t)).mp hvperm
    exact ⟨suffix, hsuffix, hword, hshort⟩
  · rintro ⟨suffix, hsuffix, hword, hshort⟩
    refine ⟨?_, hshort⟩
    unfold OverlapsAt
    rw [hword, List.take_append_of_le_length]
    · simp [u.length]
    · simp [u.length]

/-- Frozen Lemma 1.2(i): the unique weight-one successor is the rotation. -/
theorem unique_weight_one_successor (u v : PermutationVertex k) (hk : 3 ≤ k)
    (hne : u ≠ v) :
    overlapWeight u v = 1 ↔ v = rotation u := by
  rw [overlapWeight_eq_iff_drop_append_arrangement u v 1 hk hne (by omega) (by omega)]
  constructor
  · rintro ⟨suffix, hsuffix, hword, _hshort⟩
    obtain ⟨a, rest, hu⟩ := List.exists_cons_of_length_pos
      (l := u.1) (by simpa [u.length] using (show 0 < k by omega))
    have hsuffix' : suffix = [a] := by
      simpa [hu] using hsuffix
    apply PermutationVertex.ext
    simpa [hu, hsuffix'] using hword
  · rintro rfl
    exact ⟨u.1.take 1, .refl _, rfl, fun s hs hlt _hov => by omega⟩

/-- Frozen Lemma 1.2(i): the unique weight-one predecessor is the inverse rotation. -/
theorem unique_weight_one_predecessor (u v : PermutationVertex k) (hk : 3 ≤ k)
    (hne : v ≠ u) :
    overlapWeight v u = 1 ↔ v = inverseRotation u := by
  rw [unique_weight_one_successor v u hk hne]
  constructor
  · intro h
    calc
      v = inverseRotation (rotation v) := (inverseRotation_rotation (by omega) v).symm
      _ = inverseRotation u := congrArg inverseRotation h.symm
  · rintro rfl
    exact (rotation_inverseRotation (by omega) u).symm

theorem rotation_has_weight_one (u : PermutationVertex k) (hk : 3 ≤ k) :
    overlapWeight u (rotation u) = 1 :=
  (unique_weight_one_successor u (rotation u) hk (rotation_ne_self (by omega) u).symm).mpr rfl

theorem inverseRotation_has_weight_one (u : PermutationVertex k) (hk : 3 ≤ k) :
    overlapWeight (inverseRotation u) u = 1 := by
  have hne : inverseRotation u ≠ u := by
    intro h
    have hrot := congrArg rotation h
    have heq : u = rotation u := by
      exact (rotation_inverseRotation (by omega) u).symm.trans hrot
    exact rotation_ne_self (by omega) u heq.symm
  exact (unique_weight_one_predecessor u (inverseRotation u) hk hne).mpr rfl

/-- Frozen Lemma 1.2(ii): the weight-two successors are exactly the double rotation and
the Section 1 door map. -/
theorem weight_two_successors (u v : PermutationVertex k) (hk : 3 ≤ k)
    (hne : u ≠ v) :
    overlapWeight u v = 2 ↔ v = doubleRotation u ∨ v = door u := by
  rw [overlapWeight_eq_iff_drop_append_arrangement u v 2 hk hne (by omega) (by omega)]
  constructor
  · rintro ⟨suffix, hsuffix, hword, _hshort⟩
    obtain ⟨a, tail, hu₁⟩ := List.exists_cons_of_length_pos
      (l := u.1) (by simpa [u.length] using (show 0 < k by omega))
    have htail : 0 < tail.length := by
      have hul := u.length
      rw [hu₁] at hul
      simp only [List.length_cons] at hul
      omega
    obtain ⟨b, rest, hu₂⟩ := List.exists_cons_of_length_pos htail
    have hu : u.1 = a :: b :: rest := hu₁.trans (congrArg (List.cons a) hu₂)
    have hpair : suffix = [a, b] ∨ suffix = [b, a] := by
      rw [hu] at hsuffix
      simpa using (List.perm_pair.mp hsuffix)
    rcases hpair with hpair | hpair
    · left
      apply PermutationVertex.ext
      simpa [hu, hpair] using hword
    · right
      apply PermutationVertex.ext
      simpa [hu, hpair] using hword
  · rintro (rfl | rfl)
    · exact ⟨u.1.take 2, .refl _, rfl,
        noShorterOverlap_of_append (u := u) (v := doubleRotation u) (by omega) rfl⟩
    · exact ⟨(u.1.take 2).reverse, List.reverse_perm _, rfl,
        noShorterOverlap_of_append (u := u) (v := door u) (by omega) rfl⟩

theorem doubleRotation_has_weight_two (u : PermutationVertex k) (hk : 3 ≤ k) :
    overlapWeight u (doubleRotation u) = 2 :=
  (weight_two_successors u (doubleRotation u) hk
    (doubleRotation_ne_self hk u).symm).mpr (Or.inl rfl)

theorem door_has_weight_two (u : PermutationVertex k) (hk : 3 ≤ k) :
    overlapWeight u (door u) = 2 :=
  (weight_two_successors u (door u) hk (door_ne_self hk u).symm).mpr (Or.inr rfl)

/-- The first-three-symbol permutation list contains exactly six arrangements. -/
theorem first_three_arrangements_count (u : PermutationVertex k) (hk : 3 ≤ k) :
    (u.1.take 3).permutations.length = 6 := by
  rw [List.length_permutations]
  have htake : (u.1.take 3).length = 3 := by simp [u.length, Nat.min_eq_left hk]
  rw [htake]
  norm_num

/-- The six entries counted above are pairwise distinct arrangements. -/
theorem first_three_arrangements_exactly_six (u : PermutationVertex k) (hk : 3 ≤ k) :
    (u.1.take 3).permutations.length = 6 ∧ (u.1.take 3).permutations.Nodup := by
  refine ⟨first_three_arrangements_count u hk, ?_⟩
  exact List.nodup_permutations _ ((List.take_sublist 3 u.1).nodup u.nodup)

/-- Frozen Lemma 1.2(iii): for `k ≥ 4`, the weight-three successors are precisely the six
arrangements of the first three symbols appended after `u.drop 3`. -/
theorem weight_three_successors (u v : PermutationVertex k) (hk : 4 ≤ k)
    (hne : u ≠ v) :
    overlapWeight u v = 3 ↔
      ∃ suffix ∈ (u.1.take 3).permutations, v.1 = u.1.drop 3 ++ suffix := by
  rw [overlapWeight_eq_iff_drop_append_arrangement u v 3 (by omega) hne
    (by omega) (by omega)]
  constructor
  · rintro ⟨suffix, hsuffix, hword, _hshort⟩
    exact ⟨suffix, List.mem_permutations.mpr hsuffix, hword⟩
  · rintro ⟨suffix, hsuffix, hword⟩
    have hperm : suffix.Perm (u.1.take 3) := List.mem_permutations.mp hsuffix
    exact ⟨suffix, hperm, hword,
      noShorterOverlap_of_append (u := u) (v := v) (by omega) hword⟩

private theorem overlapsAt_add (u v x : PermutationVertex k) {s t : ℕ}
    (hst : s + t ≤ k) (huv : OverlapsAt u v s) (hvx : OverlapsAt v x t) :
    OverlapsAt u x (s + t) := by
  unfold OverlapsAt at huv hvx ⊢
  calc
    u.1.drop (s + t) = (u.1.drop s).drop t := by rw [List.drop_drop]
    _ = (v.1.take (k - s)).drop t := congrArg (fun word => word.drop t) huv
    _ = (v.1.drop t).take ((k - s) - t) := List.drop_take
    _ = (x.1.take (k - t)).take ((k - s) - t) :=
      congrArg (fun word => word.take ((k - s) - t)) hvx
    _ = x.1.take (k - (s + t)) := by
      rw [List.take_take]
      congr 1
      omega

/-- Frozen Lemma 1.3: overlap weights satisfy the directed triangle inequality. -/
theorem directed_triangle_inequality (u v x : PermutationVertex k) (hk : 2 ≤ k)
    (_huv : u ≠ v) (_hvx : v ≠ x) (_hux : u ≠ x) :
    overlapWeight u x ≤ overlapWeight u v + overlapWeight v x := by
  let s := overlapWeight u v
  let t := overlapWeight v x
  by_cases hlarge : k ≤ s + t
  · exact (overlapWeight_le_length (by omega) u x).trans hlarge
  · have hst : s + t ≤ k := by omega
    apply overlapWeight_min u x
    · have hs := (overlapWeight_spec u v).1
      have ht := (overlapWeight_spec v x).1
      omega
    · exact overlapsAt_add u v x hst (overlapWeight_spec u v).2
        (overlapWeight_spec v x).2

end SuperpermutationLowerBound
