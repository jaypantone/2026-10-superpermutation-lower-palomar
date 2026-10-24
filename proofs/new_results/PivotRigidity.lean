module

public import new_results.ScalarRigidity
public import new_results.RegularSpacing
public import SuperpermutationLowerBound.Refinement.GeometryIntervals
public import SuperpermutationLowerBound.Refinement.ReflectionPath

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex PositiveClusterChain

variable {k : ℕ}

theorem fullRunMapPower_satellite (hk : 3 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    entrySatellite (by omega) (fullRunMapPower hk i u) = entrySatellite (by omega) u := by
  have hdrop : u.1.drop (k - 2) ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp [PermutationVertex.length] at hl
    omega
  have hune : u.1 ≠ [] := by
    intro h
    have hl := u.length
    rw [h] at hl
    simp at hl
    omega
  have hlast : (fullRunMapPower hk i u).1.getLast? = u.1.getLast? := by
    rw [fullRunMapPower_word]
    simp [List.getLast?_eq_getLast_of_ne_nil hdrop,
      List.getLast?_eq_getLast_of_ne_nil hune]
  have hlast' : (fullRunMapPower hk i u).1.getLast? =
      some (entrySatellite (by omega) u) := by
    rw [hlast]
    simp [entrySatellite, List.getLast?_eq_getLast_of_ne_nil hune]
  simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast'

theorem reflectEntry_satellite (hk : 1 ≤ k) (u : PermutationVertex k) :
    entrySatellite hk (reflectEntry u) = entrySatellite hk u := by
  have hu := entry_dropLast_append_satellite hk u
  have hlen : u.1.dropLast.length = k - 1 := by simp [PermutationVertex.length]
  have hexit : (blockExit u).1 = [entrySatellite hk u] ++ u.1.dropLast := by
    change u.1.drop (k - 1) ++ u.1.take (k - 1) = _
    calc
      u.1.drop (k - 1) ++ u.1.take (k - 1) =
          (u.1.dropLast ++ [entrySatellite hk u]).drop (k - 1) ++
          (u.1.dropLast ++ [entrySatellite hk u]).take (k - 1) := by rw [hu]
      _ = _ := by rw [← hlen]; simp
  have hlast : (reflectEntry u).1.getLast? = some (entrySatellite hk u) := by
    simp [reflectEntry, reverseVertex_word, hexit]
  simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast

noncomputable def segmentSatellite {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : Fin s.length) : Alphabet k := entrySatellite (by omega) (s.actualRun i).entry

theorem actualRun_last_satellite {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : Fin s.length) :
    entrySatellite (by omega) (s.actualRun i).lastEntry = segmentSatellite s i := by
  rw [blockAlignedRun_lastEntry_eq_runMapPower hk p hp (s.actualRun i)]
  exact runMapPower_satellite (by omega) _ _

theorem segmentSatellite_full_next {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : ℕ) (hi : i + 1 < s.length)
    (hleft : deficitAt s.deficitString i = 0)
    (hright : deficitAt s.deficitString (i + 1) = 0) :
    segmentSatellite s ⟨i + 1, hi⟩ = segmentSatellite s ⟨i, by omega⟩ := by
  have hleftFull : (s.actualRun ⟨i, by omega⟩).IsFull := by
    have hz := (s.deficitString_get_eq_zero_iff ⟨i, by omega⟩).mp (by
      rw [← s.deficitAt_deficitString_eq i (by omega)]; exact hleft)
    change (s.actualRun ⟨i, by omega⟩).blocks.length = k - 1
    rw [s.actualRun_blocks]
    exact hz
  have hrightFull : (s.actualRun ⟨i + 1, hi⟩).length = k - 1 := by
    change (s.actualRun ⟨i + 1, hi⟩).blocks.length = k - 1
    rw [s.actualRun_blocks]
    exact (s.deficitString_get_eq_zero_iff ⟨i + 1, hi⟩).mp (by
      rw [← s.deficitAt_deficitString_eq (i + 1) hi]; exact hright)
  have hlight := blockAlignedLightSegment_runAt_light hk p hp s i hi
  have hlight' : IsLightRunBoundary
      (s.actualRun ⟨i, by omega⟩).blocks (s.actualRun ⟨i + 1, hi⟩).blocks := by
    simpa only [s.actualRun_blocks] using hlight
  have he := blockAlignedChartForcing hk p hp (s.globalStart + i)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp s; omega)
    hleftFull (by simpa [BlockAlignedLightSegment.actualRun, Nat.add_assoc] using hlight')
    (by simpa [BlockAlignedLightSegment.actualRun, Nat.add_assoc] using
      (show k - 2 ≤ (s.actualRun ⟨i + 1, hi⟩).length by omega))
  change entrySatellite (by omega) (s.actualRun ⟨i + 1, hi⟩).entry = _
  have he' : (s.actualRun ⟨i + 1, hi⟩).entry =
      fullRunMap (by omega) (s.actualRun ⟨i, by omega⟩).entry := by
    simpa [BlockAlignedLightSegment.actualRun, Nat.add_assoc] using he
  rw [he']
  simpa [fullRunMapPower, Function.iterate_one, segmentSatellite] using
    fullRunMapPower_satellite (by omega) 1 (s.actualRun ⟨i, by omega⟩).entry

theorem segmentSatellite_two_next {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : ℕ) (hi : i + 2 < s.length)
    (htwo : deficitAt s.deficitString i = 2)
    (hzero1 : deficitAt s.deficitString (i + 1) = 0)
    (hzero2 : deficitAt s.deficitString (i + 2) = 0) :
    segmentSatellite s ⟨i + 1, by omega⟩ = segmentSatellite s ⟨i, by omega⟩ := by
  have hpos : 0 < s.deficitString.get ⟨i, by simp; omega⟩ := by
    rw [← s.deficitAt_deficitString_eq i (by omega), htwo]
    norm_num
  let R := s.satelliteContextAt ⟨i, by omega⟩ hpos
  have hRdef : R.deficit = 2 := by
    rw [s.satelliteContextAt_deficit]
    rw [← s.deficitAt_deficitString_eq i (by omega)]
    exact htwo
  let C : FullPrefix R := {
    count := 2
    positive := by norm_num
    inBounds := by simp [R, BlockAlignedLightSegment.satelliteContextAt]; omega
    full := by
      intro j hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · change (s.runAt ⟨i + 1, by omega⟩).length = k - 1
        apply (s.deficitString_get_eq_zero_iff ⟨i + 1, by omega⟩).mp
        rw [← s.deficitAt_deficitString_eq (i + 1) (by omega)]
        exact hzero1
      · change (s.runAt ⟨i + 2, by omega⟩).length = k - 1
        apply (s.deficitString_get_eq_zero_iff ⟨i + 2, by omega⟩).mp
        rw [← s.deficitAt_deficitString_eq (i + 2) (by omega)]
        exact hzero2 }
  have he := C.first_eq_rot (by simpa [C, hRdef])
  have hsat : entrySatellite (by omega) (R.target .rot) = R.satellite :=
    R.sixTargetTable.2.2.2.1
  change entrySatellite (by omega) C.first.entry = R.satellite
  rw [he]
  exact hsat

@[simp] theorem reflectedSegment_length {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp) :
    (reflectedSegment hk p hp s).length = s.length := by
  simp [BlockAlignedLightSegment.length, reflectedSegment]

theorem reflectedSegment_runAt_mirror {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : Fin s.length) :
    (reflectedSegment hk p hp s).runAt
      ⟨s.length - 1 - i.1, by simp; omega⟩ = reflectList reflectEntry (s.runAt i) := by
  have hindex : s.runs.length - 1 - (s.length - 1 - i.1) = i.1 := by
    change s.length - 1 - (s.length - 1 - i.1) = i.1
    omega
  simp only [BlockAlignedLightSegment.runAt, reflectedSegment, reflectList,
    List.get_eq_getElem, List.getElem_map, List.getElem_reverse, hindex]

theorem segmentSatellite_reflected {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : Fin s.length) :
    segmentSatellite (reflectedSegment hk p hp s)
      ⟨s.length - 1 - i.1, by simp; omega⟩ = segmentSatellite s i := by
  let r := s.actualRun i
  let sr := reflectedSegment hk p hp s
  let j : Fin sr.length := ⟨s.length - 1 - i.1, by simp [sr]; omega⟩
  have hblocks : (sr.actualRun j).blocks = reflectList reflectEntry r.blocks := by
    rw [sr.actualRun_blocks, s.actualRun_blocks]
    exact reflectedSegment_runAt_mirror s i
  have he : (sr.actualRun j).entry = reflectEntry r.lastEntry := by
    change (sr.actualRun j).blocks.head _ = reflectEntry (r.blocks.getLast _)
    simp only [hblocks, reflectList_head]
  change entrySatellite (by omega) (sr.actualRun j).entry = segmentSatellite s i
  rw [he, reflectEntry_satellite]
  exact actualRun_last_satellite s i

theorem deficitAt_reverse_mirror (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    deficitAt d.reverse (d.length - 1 - i) = deficitAt d i := by
  unfold deficitAt
  rw [List.getElem?_reverse (by omega)]
  congr 2
  omega

theorem segmentSatellite_two_prev {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (i : ℕ) (hi : i < s.length) (hi2 : 2 ≤ i)
    (htwo : deficitAt s.deficitString i = 2)
    (hzero1 : deficitAt s.deficitString (i - 1) = 0)
    (hzero2 : deficitAt s.deficitString (i - 2) = 0) :
    segmentSatellite s ⟨i - 1, by omega⟩ = segmentSatellite s ⟨i, hi⟩ := by
  let sr := reflectedSegment hk p hp s
  let j := s.length - 1 - i
  have hj : j + 2 < sr.length := by simp [sr, j]; omega
  have hd (a : ℕ) (ha : a < s.length) :
      deficitAt sr.deficitString (s.length - 1 - a) = deficitAt s.deficitString a := by
    rw [show sr.deficitString = s.deficitString.reverse from
      reflectedSegment_deficitString hk p hp s]
    simpa using deficitAt_reverse_mirror s.deficitString a (by simpa using ha)
  have ht : deficitAt sr.deficitString j = 2 := by
    simpa [j] using (hd i hi).trans htwo
  have hz1 : deficitAt sr.deficitString (j + 1) = 0 := by
    have heq : j + 1 = s.length - 1 - (i - 1) := by dsimp [j]; omega
    rw [heq, hd (i - 1) (by omega)]
    exact hzero1
  have hz2 : deficitAt sr.deficitString (j + 2) = 0 := by
    have heq : j + 2 = s.length - 1 - (i - 2) := by dsimp [j]; omega
    rw [heq, hd (i - 2) (by omega)]
    exact hzero2
  have h := segmentSatellite_two_next sr j hj ht hz1 hz2
  have h0 := segmentSatellite_reflected s ⟨i, hi⟩
  have h1 := segmentSatellite_reflected s ⟨i - 1, by omega⟩
  have heq : j + 1 = s.length - 1 - (i - 1) := by dsimp [j]; omega
  simpa only [sr, j, heq, h0, h1] using h

/-- Only the local zero/two pattern is needed after the scalar argument. -/
theorem segment_satellite_constant_of_buffered {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (hvalues : ∀ i, i < s.deficitString.length →
      deficitAt s.deficitString i = 0 ∨ deficitAt s.deficitString i = 2)
    (hbuffer : ∀ i, i < s.deficitString.length → deficitAt s.deficitString i = 2 →
      2 ≤ i ∧ i + 2 < s.deficitString.length ∧
      deficitAt s.deficitString (i - 1) = 0 ∧
      deficitAt s.deficitString (i - 2) = 0 ∧
      deficitAt s.deficitString (i + 1) = 0 ∧
      deficitAt s.deficitString (i + 2) = 0) :
    ∀ i j : Fin s.length, segmentSatellite s i = segmentSatellite s j := by
  have hadj (i : ℕ) (hi : i + 1 < s.length) :
      segmentSatellite s ⟨i + 1, hi⟩ = segmentSatellite s ⟨i, by omega⟩ := by
    rcases hvalues i (by simpa using (show i < s.length by omega)) with hz | ht
    · rcases hvalues (i + 1) (by simpa using hi) with hz' | ht'
      · exact segmentSatellite_full_next s i hi hz hz'
      · have hb := hbuffer (i + 1) (by simpa using hi) ht'
        have h := segmentSatellite_two_prev s (i + 1) hi hb.1 ht' hb.2.2.1 hb.2.2.2.1
        simpa using h.symm
    · have hb := hbuffer i (by simpa using (show i < s.length by omega)) ht
      exact segmentSatellite_two_next s i (by simpa using hb.2.1) ht
        hb.2.2.2.2.1 hb.2.2.2.2.2
  have hlen : 0 < s.length := blockAlignedLightSegment_length_pos hk p hp s
  have hbase : ∀ i, ∀ hi : i < s.length,
      segmentSatellite s ⟨i, hi⟩ = segmentSatellite s ⟨0, hlen⟩ := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
        intro hi
        exact (hadj i hi).trans (ih (by omega))
  intro i j
  exact (hbase i i.2).trans (hbase j j.2).symm

/-- Scalar rigidity on a genuine light segment forces one common satellite. -/
theorem segment_satellite_constant_of_rigid {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment hk p hp)
    (dec : PositiveClusterDecomposition s.deficitString)
    (hregular : ∀ K ∈ dec.chain.clusters, K = [2])
    (hlead : 2 ≤ dec.leadingZeros) (htrail : 2 ≤ dec.trailingZeros)
    (hgaps : ∀ u ∈ dec.chain.gaps, 2 ≤ u) :
    ∀ i j : Fin s.length, segmentSatellite s i = segmentSatellite s j := by
  have h := regularSpacing dec hregular hlead htrail hgaps
  exact segment_satellite_constant_of_buffered s h.1 h.2

theorem segment_satellite_constant14 {p : OverlapPath 14}
    {hp : IsBlockAligned p} (s : BlockAlignedLightSegment (by omega) p hp)
    (hpacking : ChainPacking 11 36 (569 / 15) s.deficitString)
    (hhead : s.deficitString.head? = some 0)
    (hlast : s.deficitString.getLast? = some 0)
    (hsum : 0 < s.deficitString.sum)
    (henergy : scalarEnergy 11 36 (569 / 15) s.deficitString ≤ 1398 / 15) :
    ∀ i j : Fin s.length, segmentSatellite s i = segmentSatellite s j := by
  obtain ⟨dec, hreg, hl, hr, hg⟩ := deficitString14_rigid
    s.deficitString_legal hpacking hhead hlast hsum henergy
  exact segment_satellite_constant_of_rigid s dec hreg (by omega) (by omega)
    (by intro u hu; have := hg u hu; omega)

end SuperpermutationLowerBound.Refinement
