module

public import SuperpermutationLowerBound.Refinement.ReturnGeometry

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

open PermutationVertex

section ActualHistory

variable {k : ℕ} {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}

/-- An occupied class witnessed by a block slot of an actual earlier local
run. This retains the shared surrounding path and its global disjointness. -/
def OccupiedBefore (segment : BlockAlignedLightSegment hk p hp) (cut : ℕ)
    (v : PermutationVertex k) : Prop :=
  ∃ i : Fin segment.length, i.val < cut ∧ ∃ slot : ℕ,
    slot < (segment.actualRun i).length ∧
      rotationClass (runMapPower (by omega) slot (segment.actualRun i).entry) = rotationClass v

theorem OccupiedBefore.mono {segment : BlockAlignedLightSegment hk p hp}
    {cut cut' : ℕ} {v : PermutationVertex k}
    (h : OccupiedBefore segment cut v) (hcut : cut ≤ cut') :
    OccupiedBefore segment cut' v := by
  obtain ⟨i, hi, slot, hs, heq⟩ := h
  exact ⟨i, by omega, slot, hs, heq⟩

theorem OccupiedBefore.of_class_eq {segment : BlockAlignedLightSegment hk p hp}
    {cut : ℕ} {u v : PermutationVertex k}
    (h : OccupiedBefore segment cut u) (heq : rotationClass u = rotationClass v) :
    OccupiedBefore segment cut v := by
  obtain ⟨i, hi, slot, hs, hc⟩ := h
  exact ⟨i, hi, slot, hs, hc.trans heq⟩

theorem occupiedBefore_of_slot (segment : BlockAlignedLightSegment hk p hp)
    (i : Fin segment.length) (cut slot : ℕ) (hcut : i.val < cut)
    (hslot : slot < (segment.actualRun i).length) :
    OccupiedBefore segment cut
      (runMapPower (by omega) slot (segment.actualRun i).entry) :=
  ⟨i, hcut, slot, hslot, rfl⟩

theorem not_occupiedBefore_slot (segment : BlockAlignedLightSegment hk p hp)
    (i : Fin segment.length) (slot : ℕ) (hslot : slot < (segment.actualRun i).length) :
    ¬ OccupiedBefore segment i.val
      (runMapPower (by omega) slot (segment.actualRun i).entry) := by
  rintro ⟨j, hji, oldslot, holdslot, hclass⟩
  have hjglobal := blockAlignedLightSegment_globalStart_bounds hk p hp segment
  have hne := actualRuns_rotationClasses_ne hk p hp
    (segment.globalStart + j.val) (segment.globalStart + i.val)
    (by omega) (by omega) (by omega)
    (List.get_mem (segment.actualRun j).blocks ⟨oldslot, holdslot⟩)
    (List.get_mem (segment.actualRun i).blocks ⟨slot, hslot⟩)
  rw [blockAlignedRun_entrySequence hk p hp (segment.actualRun j) oldslot holdslot,
    blockAlignedRun_entrySequence hk p hp (segment.actualRun i) slot hslot] at hne
  exact hne hclass

/-- The C branch is a rotation of the last slot in the rotated target's
insertion block. This identity holds in every satellite chart. -/
theorem target_C_eq_rotation_lastRot {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.target .C = rotationPower 1 (runMapPower (by omega) (k - 2) (R.target .rot)) := by
  apply PermutationVertex.ext
  rw [rotationPower_word (by omega), runMapPower_word (by omega), R.target_word]
  have hword : (R.target .rot).1 = (R.tail ++ [R.c2, R.c1]) ++ [R.satellite] := by
    rw [R.target_word]
    simp [SatelliteContext.targetSuffix, List.append_assoc]
  have hsat : entrySatellite (by omega) (R.target .rot) = R.satellite := by
    have hlast : (R.target .rot).1.getLast? = some R.satellite := by rw [hword]; simp
    simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast
  rw [hword, List.dropLast_concat, hsat]
  have hlength : (R.tail ++ [R.c2]).length = k - 2 := by
    simp only [List.length_append, List.length_singleton, R.tail_length]
    omega
  have hrot : (R.tail ++ [R.c2, R.c1]).rotate (k - 2) = [R.c1] ++ R.tail ++ [R.c2] := by
    rw [← hlength]
    simpa [List.append_assoc] using List.rotate_append_length_eq (R.tail ++ [R.c2]) [R.c1]
  rw [hrot]
  simp [SatelliteContext.targetSuffix, List.rotate_cons_succ, List.append_assoc]

end ActualHistory

def terminalAIndex (n i : ℕ) : ℕ :=
  if i < n - 2 then i else if i = n - 2 then n - 1 else if i = n - 1 then n else n - 2

theorem terminalAIndex_lt (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n + 1) :
    terminalAIndex n i < n + 1 := by
  unfold terminalAIndex
  split_ifs <;> omega

/-- The A branch only cycles the last three positions of the rotated target. -/
theorem target_A_get {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (i : ℕ) (hi : i < n + 1) :
    (R.target .A).1[i]'(by simp [PermutationVertex.length]; omega) =
      (R.target .rot).1[terminalAIndex n i]'(by
        simpa [PermutationVertex.length] using terminalAIndex_lt n hn i hi) := by
  have htail : R.tail.length = n - 2 := by simpa using R.tail_length
  by_cases hicore : i < n - 2
  · have hidx : terminalAIndex n i = i := by simp [terminalAIndex, hicore]
    simp only [R.target_word, SatelliteContext.targetSuffix, hidx]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  · have hc : i = n - 2 ∨ i = n - 1 ∨ i = n := by omega
    rcases hc with heq | heq | heq
    all_goals subst i
    all_goals simp only [terminalAIndex]
    all_goals split_ifs <;> try (first | contradiction | omega)
    all_goals simp only [R.target_word, SatelliteContext.targetSuffix]
    all_goals rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    all_goals simp only [htail, show n - 2 - (n - 2) = 0 by omega,
      show n - 1 - (n - 2) = 1 by omega, show n - (n - 2) = 2 by omega]
    all_goals rfl

private theorem add_mod_once {n s i : ℕ} (hs : s ≤ n) (hi : i < n) :
    (s + i) % n = if s + i < n then s + i else s + i - n := by
  by_cases h : s + i < n
  · simp [h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem terminalA_rotated_core_value (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n) :
    cellUValue n (terminalAIndex n ((1 + i) % n)) = (3 + i) % (n + 1) := by
  rw [add_mod_once (by omega : 1 ≤ n) hi,
    add_mod_once (by omega : 3 ≤ n + 1) (by omega : i < n + 1)]
  split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [terminalAIndex]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellUValue]
  all_goals split_ifs <;> (first | contradiction | omega)

theorem terminalA_rotated_last_value (n : ℕ) (hn : 7 ≤ n) :
    cellUValue n (terminalAIndex n n) = (3 + n) % (n + 1) := by
  have hmod : (3 + n) % (n + 1) = 2 := by
    rw [show 3 + n = (n + 1) + 2 by omega]
    simp [Nat.mod_eq_of_lt (show 2 < n + 1 by omega)]
  rw [hmod]
  unfold terminalAIndex
  split_ifs <;> simp only [cellUValue] <;> split_ifs <;> omega

/-- Slot one of the A branch is the identity class in the normalized chart. -/
theorem target_A_collision_of_rot_normalized {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hrot : R.target .rot = fullEntry n hn e) :
    runMapPower (by omega) 1 (R.target .A) = rotationPower 3 (coordinateVertex e) := by
  have hgetA (i : ℕ) (hi : i < n + 1) :
      (R.target .A).1[i]'(by simp [PermutationVertex.length]; omega) =
        e (cellU n hn ⟨terminalAIndex n i, terminalAIndex_lt n hn i hi⟩) := by
    rw [target_A_get hn R i hi]
    have h := congrArg (fun v : PermutationVertex (n + 1) =>
      v.1[terminalAIndex n i]'(by simpa [v.length] using terminalAIndex_lt n hn i hi)) hrot
    simpa only [fullEntry_word, List.getElem_ofFn] using h
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n
    · have hget := runMapPower_get_core (by omega : 2 ≤ n + 1) (R.target .A) 1 i (by omega)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget, hgetA ((1 + i) % n) (by have := Nat.mod_lt (1 + i) (by omega : 0 < n); omega)]
      simp only [rotationPower_word (show 1 ≤ n + 1 by omega), coordinateVertex_word,
        List.getElem_rotate, List.length_ofFn, List.getElem_ofFn]
      apply congrArg e
      apply Fin.ext
      simpa [Nat.add_comm] using terminalA_rotated_core_value n hn i hicore
    · have hin : i = n := by omega
      subst i
      have hget := runMapPower_get_last (by omega : 2 ≤ n + 1) (R.target .A) 1
      simp only [Nat.add_sub_cancel] at hget
      rw [hget, hgetA n (by omega)]
      simp only [rotationPower_word (show 1 ≤ n + 1 by omega), coordinateVertex_word,
        List.getElem_rotate, List.length_ofFn, List.getElem_ofFn]
      apply congrArg e
      apply Fin.ext
      simpa [Nat.add_comm] using terminalA_rotated_last_value n hn

theorem runMapPower_comp {k : ℕ} (hk : 1 ≤ k) (s t : ℕ) (u : PermutationVertex k) :
    runMapPower hk s (runMapPower hk t u) = runMapPower hk (s + t) u := by
  simp only [runMapPower, Function.iterate_add_apply]

theorem FullPrefix.not_occupiedBefore_slot {k : ℕ} {hk : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment}
    (C : FullPrefix R) (j : Fin C.count) (slot : ℕ)
    (hslot : slot < (C.run j).length) :
    ¬ OccupiedBefore segment (R.localIndex.val + 1 + j.val)
      (runMapPower (by omega) slot (C.run j).entry) := by
  let i : Fin segment.length := ⟨R.localIndex.val + 1 + j.val, by
    have := C.inBounds
    omega⟩
  have heq : segment.actualRun i = C.run j := rfl
  have h := SuperpermutationLowerBound.Refinement.not_occupiedBefore_slot
    segment i slot (by simpa [heq] using hslot)
  simpa only [i, heq] using h

/-- The three surviving branches of an actual following full run all collide
with the stated actual history. Only the full-run consequence is asserted. -/
theorem terminal_full_run_collision {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (C : FullPrefix R)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hdeficit : R.deficit = 2) (hentry : R.entry = shortEntry n hn e)
    (shift : ℕ) (hshiftLow : 2 ≤ shift) (hshiftHigh : shift ≤ n - 2)
    (hprior : ∀ slot : ℕ, slot < n - 2 →
      OccupiedBefore segment (R.localIndex.val + 1)
        (runMapPower (by omega) slot (runMapPower (by omega) shift (fullEntry n hn e))))
    (hidentity : OccupiedBefore segment (R.localIndex.val + 1) (coordinateVertex e)) : False := by
  have hrot := deficitTwo_target_rot_normalized hn R e hdeficit hentry
  have hfull : C.first.length = n := by
    exact C.run_isFull ⟨0, C.positive⟩
  have hno (slot : ℕ) (hs : slot < n) :
      ¬ OccupiedBefore segment (R.localIndex.val + 1)
        (runMapPower (by omega) slot C.first.entry) := by
    have h := C.not_occupiedBefore_slot ⟨0, C.positive⟩ slot (by
      change slot < C.first.length
      rw [hfull]
      exact hs)
    simpa only [Nat.add_zero, FullPrefix.first] using h
  rcases C.first_classification with hrotBranch | hABranch | hCBranch
  · have h := hprior 0 (by omega)
    have hoccupied : OccupiedBefore segment (R.localIndex.val + 1)
        (runMapPower (by omega) shift C.first.entry) := by
      rw [hrotBranch, hrot]
      simpa [runMapPower] using h
    exact hno shift (by omega) hoccupied
  · apply hno 1 (by omega)
    apply hidentity.of_class_eq
    rw [hABranch, target_A_collision_of_rot_normalized hn R e hrot,
      rotationClass_rotationPower (by omega)]
  · have hslot : n - 1 - shift < n - 2 := by omega
    have h := hprior (n - 1 - shift) hslot
    have hsum : n - 1 - shift + shift = n - 1 := by omega
    rw [runMapPower_comp, hsum] at h
    apply hno 0 (by omega)
    apply h.of_class_eq
    change rotationClass (runMapPower (by omega) (n - 1) (fullEntry n hn e)) =
      rotationClass C.first.entry
    rw [hCBranch, target_C_eq_rotation_lastRot R, hrot,
      rotationClass_rotationPower (by omega)]
    simp only [show n + 1 - 2 = n - 1 by omega]

/-- An earlier actual short run supplies the transported row hypothesis of
the terminal collision theorem; no abstract footprint is assumed. -/
theorem terminal_full_run_collision_of_earlier_run {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (C : FullPrefix R)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hdeficit : R.deficit = 2) (hentry : R.entry = shortEntry n hn e)
    (shift : ℕ) (hshiftLow : 2 ≤ shift) (hshiftHigh : shift ≤ n - 2)
    (old : Fin segment.length) (hold : old.val < R.localIndex.val + 1)
    (holdLength : (segment.actualRun old).length = n - 2)
    (holdEntry : (segment.actualRun old).entry = runMapPower (by omega) shift (fullEntry n hn e))
    (hidentity : OccupiedBefore segment (R.localIndex.val + 1) (coordinateVertex e)) : False := by
  apply terminal_full_run_collision hn R C e hdeficit hentry shift hshiftLow hshiftHigh
    (hidentity := hidentity)
  intro slot hs
  have h := occupiedBefore_of_slot segment old (R.localIndex.val + 1) slot hold (by
    rw [holdLength]
    exact hs)
  simpa only [holdEntry] using h

/-- The full run immediately preceding the canonical short entry has its
last block in the identity rotation class. -/
theorem incoming_full_identity_value (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n + 1) :
    cellYValue n (prefixRotateIndex (n + 1) (n - 1) (n - 2)
      (prefixRotateIndex (n + 1) n (n - 1) i)) = (1 + i) % (n + 1) := by
  by_cases hicore : i < n
  · have hinner : prefixRotateIndex (n + 1) n (n - 1) i = (n - 1 + i) % n := by
      simp only [prefixRotateIndex, if_pos hicore]
    rw [hinner, add_mod_once (by omega : n - 1 ≤ n) hicore]
    split_ifs with hwrap
    · have hi0 : i = 0 := by omega
      subst i
      simp only [Nat.add_zero]
      simp only [prefixRotateIndex, lt_self_iff_false, if_false, cellYValue]
      rw [Nat.mod_eq_of_lt (by omega)]
      split_ifs <;> omega
    · have hj : n - 1 + i - n < n - 1 := by omega
      rw [prefixRotateIndex, if_pos hj,
        add_mod_once (by omega : n - 2 ≤ n - 1) hj]
      rw [Nat.mod_eq_of_lt (by omega : 1 + i < n + 1)]
      split_ifs <;> simp only [cellYValue] <;> split_ifs <;>
        (first | contradiction | omega)
  · have hin : i = n := by omega
    subst i
    simp only [prefixRotateIndex, lt_self_iff_false, if_false]
    rw [if_neg (by omega : ¬ n < n - 1)]
    rw [show 1 + n = n + 1 by omega, Nat.mod_self]
    simp only [cellYValue]
    split_ifs <;> omega

theorem incoming_full_identity_word (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    runMapPower (by omega) (n - 1)
      (fullRunMapPower (by omega) (n - 2) (shortEntry n hn e)) =
        rotationPower 1 (coordinateVertex e) := by
  have hcoords : vertexCoordinates
      (runMapPower (by omega) (n - 1)
        (fullRunMapPower (by omega) (n - 2) (shortEntry n hn e))) =
      vertexCoordinates (rotationPower 1 (coordinateVertex e)) := by
    apply Equiv.ext
    intro i
    rw [runMapPower_coordinates (by omega), fullRunMapPower_coordinates (by omega),
      rotationPower_coordinates (by omega)]
    simp only [shortEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
    apply congrArg e
    apply Fin.ext
    change cellYValue n (prefixRotateIndex (n + 1) (n + 1 - 2) (n - 2)
      (prefixRotateIndex (n + 1) (n + 1 - 1) (n - 1) i.val)) =
        (1 + i.val) % (n + 1)
    simpa only [Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega] using
      incoming_full_identity_value n hn i.val i.isLt
  have h := congrArg coordinateVertex hcoords
  simpa only [coordinateVertex_vertexCoordinates] using h

/-- Invert one full-run transition using its proved exact period. -/
theorem incoming_full_entry_eq {n : ℕ} (hn : 7 ≤ n)
    (u v : PermutationVertex (n + 1))
    (hnext : fullRunMap (by omega) u = v) :
    u = fullRunMapPower (by omega) (n - 2) v := by
  have hperiod := (fullRunMap_order_exact (by omega : 3 ≤ n + 1) u).1
  have hstep : fullRunMapPower (by omega) (n - 2) (fullRunMap (by omega) u) =
      fullRunMapPower (by omega) (n - 1) u := by
    rw [show n - 1 = (n - 2) + 1 by omega]
    simp only [fullRunMapPower, Function.iterate_succ_apply]
  rw [hnext] at hstep
  simpa only [show n + 1 - 2 = n - 1 by omega] using hperiod.symm.trans hstep.symm

/-- Actual incoming full-run history supplies the identity premise of the
terminal collision theorem, at every later cutoff. -/
theorem incoming_full_identity_occupied {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp)
    (old : Fin segment.length) (cut : ℕ) (hold : old.val < cut)
    (hfull : (segment.actualRun old).length = n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hnext : fullRunMap (by omega) (segment.actualRun old).entry = shortEntry n hn e) :
    OccupiedBefore segment cut (coordinateVertex e) := by
  have hentry := incoming_full_entry_eq hn _ _ hnext
  have h := occupiedBefore_of_slot segment old cut (n - 1) hold (by rw [hfull]; omega)
  apply h.of_class_eq
  rw [hentry, incoming_full_identity_word, rotationClass_rotationPower (by omega)]

end SuperpermutationLowerBound.Refinement
