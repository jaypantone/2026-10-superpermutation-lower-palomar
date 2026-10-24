module

public import SuperpermutationLowerBound.Section05.FullRunChart

@[expose] public section

namespace SuperpermutationLowerBound

/-! The frozen satellite calculus of Section 5, from a genuine nonfull run
inside a genuine maximal light segment through the local gap rule.  All run
indices are transported through the local-to-global run interface.
-/

open PermutationVertex

variable {k : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The six names in Table `tab:six`, in its exact order. -/
inductive SatelliteTargetName where
  | skip | rot | A | B | C | D
  deriving DecidableEq, Fintype, Repr

namespace SatelliteTargetName

/-- The exact table order `skip, rot, A, B, C, D`. -/
def all : List SatelliteTargetName := [.skip, .rot, .A, .B, .C, .D]

@[simp] theorem all_length : all.length = 6 := rfl

theorem all_nodup : all.Nodup := by decide

end SatelliteTargetName

/-- An actual nonfull run `R₀` at an exact local position of a generic
maximal light segment.  Nonfull means `ℓ₀ ≤ n-1 = k-2`. -/
structure SatelliteContext (hk : 7 ≤ k) (p : OverlapPath k)
    (hp : IsBlockAligned p) (segment : BlockAlignedLightSegment hk p hp) where
  localIndex : Fin segment.length
  nonfull : (segment.runAt localIndex).length ≤ k - 2

namespace SatelliteContext

/-- The globally indexed actual run represented by the context. -/
noncomputable def run {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + R.localIndex, by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩

/-- The exact run length `ℓ₀`. -/
noncomputable def length {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : ℕ := R.run.length

/-- The exact deficit `d₀=n-ℓ₀`. -/
noncomputable def deficit {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : ℕ := R.run.deficit

/-- The entry `u` of `R₀`. -/
noncomputable def entry {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : PermutationVertex k := R.run.entry

/-- The cyclic core `γ₀`. -/
noncomputable def core {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : CyclicCore k := entryCore R.entry

/-- The satellite `s`. -/
noncomputable def satellite {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Alphabet k :=
  entrySatellite (by omega) R.entry

/-- The core linearization beginning at `c₁=u_{ℓ₀}`. -/
noncomputable def rotatedCore {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Word k :=
  R.entry.1.dropLast.rotate (R.length - 1)

/-- The cyclicly indexed letter `c₁=u_{ℓ₀}`. -/
noncomputable def c1 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Alphabet k :=
  R.rotatedCore.get ⟨0, by
    simp [rotatedCore, PermutationVertex.length]
    omega⟩

/-- The cyclicly indexed letter `c₂=u_{ℓ₀+1}`. -/
noncomputable def c2 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Alphabet k :=
  R.rotatedCore.get ⟨1, by
    simp [rotatedCore, PermutationVertex.length]
    omega⟩

/-- The retained word `t=(u_{ℓ₀+2},…,u_{ℓ₀-1})`; it is allowed to be
empty by the definition, although the standing range makes its length at
least four. -/
noncomputable def tail {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Word k := R.rotatedCore.drop 2

/-- The occupied slot set `J₀`, expressed without choosing a new cyclic
origin: slots `0,…,ℓ₀-1` of the entry core. -/
noncomputable def occupiedSlots {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Finset (Alphabet k) := by
  classical
  exact Finset.univ.image fun i : Fin R.length =>
    coreSlotLetter (by omega) R.entry
      ⟨i, i.2.trans_le (blockAlignedRun_length_le hk p hp R.run)⟩

/-- The final entry of `R₀`. -/
noncomputable def finalEntry {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : PermutationVertex k := R.run.lastEntry

/-- The exit of the final block of `R₀`. -/
noncomputable def exit {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : PermutationVertex k :=
  blockExit R.finalEntry

/-- The six suffix arrangements from `(s,c₁,c₂)`. -/
noncomputable def targetSuffix {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : SatelliteTargetName → Word k
  | .skip => [R.c1, R.c2, R.satellite]
  | .rot => [R.c2, R.c1, R.satellite]
  | .A => [R.c1, R.satellite, R.c2]
  | .B => [R.satellite, R.c1, R.c2]
  | .C => [R.c2, R.satellite, R.c1]
  | .D => [R.satellite, R.c2, R.c1]

/-- A named actual target word from Table `tab:six`. -/
noncomputable def target {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (name : SatelliteTargetName) :
    PermutationVertex k := chartTargetOfSuffix R.exit (R.targetSuffix name)

/-- The six named actual targets, in the exact table order. -/
noncomputable def targetList {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : List (PermutationVertex k) :=
  SatelliteTargetName.all.map R.target

/-- The transposed core in the `rot` row. -/
noncomputable def rotCore {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : CyclicCore k :=
  (R.tail ++ [R.c2, R.c1] : Cycle (Alphabet k))

/-- The core obtained from `γ₀` by replacing `c₂` by `s`, in row `A`. -/
noncomputable def aCore {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : CyclicCore k :=
  (R.tail ++ [R.c1, R.satellite] : Cycle (Alphabet k))

/-- The core in row `C`: delete `c₁` and put `s` after `c₂`. -/
noncomputable def cCore {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : CyclicCore k :=
  (R.tail ++ [R.c2, R.satellite] : Cycle (Alphabet k))

/-- The core in row `D`: delete `c₁` and put `s` before `c₂`. -/
noncomputable def dCore {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : CyclicCore k :=
  (R.tail ++ [R.satellite, R.c2] : Cycle (Alphabet k))

/-- The local run list and the globally indexed run agree exactly. -/
theorem run_blocks {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.run.blocks = segment.runAt R.localIndex := by
  simpa [run] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment R.localIndex).symm

/-- Exact nonfull length bounds, including `ℓ₀=1` and `ℓ₀=n-1`. -/
theorem length_bounds {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    1 ≤ R.length ∧ R.length ≤ k - 2 := by
  constructor
  · exact blockAlignedRun_length_pos hk p hp R.run
  · change R.run.blocks.length ≤ k - 2
    rw [R.run_blocks]
    exact R.nonfull

/-- Exact deficit identity; natural subtraction is not being used outside
its justified range. -/
theorem length_add_deficit {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.length + R.deficit = k - 1 := by
  have hle := blockAlignedRun_length_le hk p hp R.run
  simp only [length, deficit, BlockAlignedRun.deficit]
  omega

/-- A represented nonfull run has positive deficit. -/
theorem deficit_pos {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : 1 ≤ R.deficit := by
  have h := R.length_add_deficit
  have hnonfull := R.length_bounds.2
  omega

/-- The cyclic split is exactly `[c₁,c₂] ++ t`, including wraparound. -/
theorem rotatedCore_eq {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.rotatedCore = [R.c1, R.c2] ++ R.tail := by
  have hlen : R.rotatedCore.length = k - 1 := by
    simp [rotatedCore, PermutationVertex.length]
  cases hcore : R.rotatedCore with
  | nil =>
      exfalso
      simp [hcore] at hlen
      omega
  | cons a rest =>
      cases hrest : rest with
      | nil =>
          exfalso
          simp [hcore, hrest] at hlen
          omega
      | cons b t =>
          simp [c1, c2, tail, hcore, hrest]

/-- Consequently `t` has the exact `n-2=k-3` letters. -/
theorem tail_length {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : R.tail.length = k - 3 := by
  have hlen : R.rotatedCore.length = k - 1 := by
    simp [rotatedCore, PermutationVertex.length]
  rw [R.rotatedCore_eq] at hlen
  simp at hlen
  omega

/-- The cyclic predecessor `u_{ℓ₀-1}` of `c₁`; this is well-defined even
at wraparound. -/
noncomputable def c0 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Alphabet k :=
  R.tail.getLast (by
    have := R.tail_length
    intro h
    simp [h] at this
    omega)

/-- The retained endgame prefix obtained by removing `c₀` from `t`. -/
noncomputable def endTail {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Word k := R.tail.dropLast

/-- Exact split `t=t'c₀` used in the endgame, with no linear-index
assumption. -/
theorem tail_eq_endTail_append_c0 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.tail = R.endTail ++ [R.c0] := by
  exact (List.dropLast_append_getLast (by
    have := R.tail_length
    intro h
    simp [h] at this
    omega)).symm

/-- The endgame prefix has `n-3=k-4` letters. -/
theorem endTail_length {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.endTail.length = k - 4 := by
  simp [endTail, R.tail_length]
  omega

/-- The actual last entry is `τ₂^(ℓ₀-1)(u)`. -/
theorem finalEntry_eq {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.finalEntry = runMapPower (by omega) (R.length - 1) R.entry := by
  exact blockAlignedRun_lastEntry_eq_runMapPower hk p hp R.run

/-- Exact final-entry word `c₁ c₂ t s`. -/
theorem finalEntry_word {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.finalEntry.1 = [R.c1, R.c2] ++ R.tail ++ [R.satellite] := by
  rw [R.finalEntry_eq, runMapPower_word (by omega)]
  change R.rotatedCore ++ [R.satellite] = _
  rw [R.rotatedCore_eq]

/-- Exact exit word `s c₁ c₂ t`. -/
theorem exit_word {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.exit.1 = [R.satellite, R.c1, R.c2] ++ R.tail := by
  rw [exit, blockExit, inverseRotation_word, R.finalEntry_word]
  have hlen : ([R.c1, R.c2] ++ R.tail).length = k - 1 := by
    simp [R.tail_length]
    omega
  rw [show k - 1 = ([R.c1, R.c2] ++ R.tail).length by omega]
  simp

/-- The actual occupied classes and the explicit slot set `J₀`. -/
theorem occupied_classes_and_slots {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.run.occupiedClasses =
        (Finset.range R.length).image
          (fun i => rotationClass (runMapPower (by omega) i R.entry)) ∧
      R.occupiedSlots = Finset.univ.image (fun i : Fin R.length =>
        coreSlotLetter (by omega) R.entry
          ⟨i, i.2.trans_le (blockAlignedRun_length_le hk p hp R.run)⟩) := by
  exact ⟨blockAlignedRun_occupiedClasses_eq_slots hk p hp R.run, rfl⟩

private theorem targetSuffix_perm {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (name : SatelliteTargetName) :
    (R.targetSuffix name).Perm (R.exit.1.take 3) := by
  have hexit : R.exit.1.take 3 = [R.satellite, R.c1, R.c2] := by
    rw [R.exit_word]
    simp
  rw [hexit]
  cases name
  · simpa [targetSuffix] using
      (List.perm_append_comm :
        ([R.c1, R.c2] ++ [R.satellite]).Perm
          ([R.satellite] ++ [R.c1, R.c2]))
  · exact (List.Perm.swap R.c1 R.c2 [R.satellite]).trans (by
      simpa [targetSuffix] using
        (List.perm_append_comm :
          ([R.c1, R.c2] ++ [R.satellite]).Perm
            ([R.satellite] ++ [R.c1, R.c2])))
  · exact List.Perm.swap R.satellite R.c1 [R.c2]
  · exact .refl _
  · simpa [targetSuffix] using
      (List.perm_append_comm :
        ([R.c2] ++ [R.satellite, R.c1]).Perm
          ([R.satellite, R.c1] ++ [R.c2]))
  · exact (List.Perm.swap R.c1 R.c2 []).cons R.satellite

/-- Exact word of each named target in Table `tab:six`. -/
theorem target_word {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (name : SatelliteTargetName) :
    (R.target name).1 = R.tail ++ R.targetSuffix name := by
  have hperm := targetSuffix_perm R name
  have hdrop : R.exit.1.drop 3 = R.tail := by
    rw [R.exit_word]
    simp
  unfold target chartTargetOfSuffix
  rw [dif_pos hperm]
  change R.exit.1.drop 3 ++ R.targetSuffix name = _
  rw [hdrop]

private theorem target_eq_cutAppend {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (name : SatelliteTargetName) :
    R.target name = PermutationVertex.cutAppend R.exit 3
      (R.targetSuffix name) (targetSuffix_perm R name) := by
  simp [target, chartTargetOfSuffix, targetSuffix_perm]

/-- Every named target is an actual weight-three successor. -/
theorem target_weight_three {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (name : SatelliteTargetName) :
    overlapWeight R.exit (R.target name) = 3 := by
  rw [weightThreeTargetList_iff (by omega)]
  rw [target_eq_cutAppend R name]
  unfold weightThreeTargetList
  apply List.mem_map.mpr
  let suffix : {s // s ∈ (R.exit.1.take 3).permutations} :=
    ⟨R.targetSuffix name,
      List.mem_permutations.mpr (targetSuffix_perm R name)⟩
  exact ⟨suffix, List.mem_attach _ _, rfl⟩

private theorem target_letters_distinct {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.c1 ≠ R.c2 ∧ R.c1 ≠ R.satellite ∧ R.c2 ≠ R.satellite := by
  have hcoreNodup : R.rotatedCore.Nodup := by
    exact (List.rotate_perm R.entry.1.dropLast (R.length - 1)).nodup_iff.mpr
      ((List.dropLast_sublist R.entry.1).nodup R.entry.nodup)
  have hc1c2 : R.c1 ≠ R.c2 := by
    intro heq
    have hfin := hcoreNodup.get_inj_iff.mp heq
    have := congrArg Fin.val hfin
    simp at this
  have hentryNodup :
      (R.entry.1.dropLast ++ [R.satellite]).Nodup := by
    change (R.entry.1.dropLast ++
      [entrySatellite (by omega : 1 ≤ k) R.entry]).Nodup
    rw [entry_dropLast_append_satellite (by omega : 1 ≤ k)]
    exact R.entry.nodup
  have hsatNot : R.satellite ∉ R.entry.1.dropLast := by
    have hdisjoint := (List.nodup_append.mp hentryNodup).2.2
    intro hmem
    exact (hdisjoint _ hmem _ (by simp)) rfl
  have hrotPerm : R.rotatedCore.Perm R.entry.1.dropLast :=
    List.rotate_perm _ _
  have hc1Mem : R.c1 ∈ R.entry.1.dropLast :=
    hrotPerm.mem_iff.mp (by rw [R.rotatedCore_eq]; simp)
  have hc2Mem : R.c2 ∈ R.entry.1.dropLast :=
    hrotPerm.mem_iff.mp (by rw [R.rotatedCore_eq]; simp)
  exact ⟨hc1c2, fun h => hsatNot (h ▸ hc1Mem),
    fun h => hsatNot (h ▸ hc2Mem)⟩

private theorem targetSuffix_injective {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Function.Injective R.targetSuffix := by
  intro a b hab
  obtain ⟨h12, h1s, h2s⟩ := target_letters_distinct R
  cases a <;> cases b <;> simp_all [targetSuffix]

private theorem target_injective {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) : Function.Injective R.target := by
  intro a b hab
  apply targetSuffix_injective R
  have hword := congrArg Subtype.val hab
  rw [R.target_word a, R.target_word b] at hword
  exact List.append_right_injective R.tail hword

/-- The six targets are distinct and the list has length six. -/
theorem targetList_exactly_six {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.targetList.length = 6 ∧ R.targetList.Nodup := by
  constructor
  · simp [targetList, SatelliteTargetName.all]
  · exact SatelliteTargetName.all_nodup.map (target_injective R)

/-- **The six targets.**  All and only the six distinct named words are the
actual weight-three successors of the actual exit of `R₀`. -/
theorem sixTargets {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (v : PermutationVertex k) :
    overlapWeight R.exit v = 3 ↔ v ∈ R.targetList := by
  rw [weightThreeTargetList_iff (by omega)]
  have hsub : R.targetList ⊆ weightThreeTargetList R.exit := by
    intro x hx
    unfold targetList at hx
    obtain ⟨name, _hname, rfl⟩ := List.mem_map.mp hx
    exact (weightThreeTargetList_iff (by omega) R.exit (R.target name)).mp
      (R.target_weight_three name)
  have hsubperm := List.subperm_of_subset R.targetList_exactly_six.2 hsub
  have hperm : R.targetList.Perm (weightThreeTargetList R.exit) := by
    apply hsubperm.perm_of_length_le
    rw [R.targetList_exactly_six.1,
      (weightThreeTargetList_exactly_six (by omega) R.exit).1]
  exact hperm.mem_iff.symm

private theorem entrySatellite_of_append {hk : 1 ≤ k}
    (v : PermutationVertex k) (pre : Word k) (x : Alphabet k)
    (hword : v.1 = pre ++ [x]) : entrySatellite hk v = x := by
  have hlast : v.1.getLast? = some x := by rw [hword]; simp
  simpa [entrySatellite] using List.getLast_of_getLast?_eq_some hlast

private theorem entryCore_of_append
    (v : PermutationVertex k) (pre : Word k) (x : Alphabet k)
    (hword : v.1 = pre ++ [x]) : entryCore v = (pre : Cycle (Alphabet k)) := by
  rw [entryCore, hword, List.dropLast_concat]

/-- The `skip` target is exactly `τ₂^(ℓ₀+1)(u)`, including the wraparound
case `ℓ₀=n-1`. -/
theorem target_skip_eq_runMapPower {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.target .skip = runMapPower (by omega) (R.length + 1) R.entry := by
  apply PermutationVertex.ext
  rw [R.target_word, runMapPower_word (by omega)]
  change R.tail ++ [R.c1, R.c2, R.satellite] =
    R.entry.1.dropLast.rotate (R.length + 1) ++ [R.satellite]
  have hcoreLength : R.entry.1.dropLast.length = k - 1 := by
    simp [PermutationVertex.length]
  have hlen : R.length - 1 + 2 = R.length + 1 := by
    have := R.length_bounds.1
    omega
  have hrotate : R.entry.1.dropLast.rotate (R.length + 1) =
      R.tail ++ [R.c1, R.c2] := by
    calc
      R.entry.1.dropLast.rotate (R.length + 1) =
          R.entry.1.dropLast.rotate ((R.length - 1) + 2) := by rw [hlen]
      _ = R.rotatedCore.rotate 2 := by
        simp [rotatedCore, List.rotate_rotate]
      _ = R.tail ++ [R.c1, R.c2] := by
        rw [R.rotatedCore_eq]
        simp [List.rotate_eq_drop_append_take]
  rw [hrotate]
  simp [List.append_assoc]

/-- The `B` target is literally a rotation of the final entry, hence is
the last occupied block class of `R₀`. -/
theorem target_B_eq_rotationPower_finalEntry {hk : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.target .B = rotationPower 2 R.finalEntry := by
  apply PermutationVertex.ext
  rw [R.target_word, rotationPower_word (by omega), R.finalEntry_word]
  simp [targetSuffix]

private theorem prev_concat_eq_getLast {α : Type*} [BEq α] [LawfulBEq α]
    [DecidableEq α] (l : List α) (s : α) (hl : l ≠ []) (hs : s ∉ l) :
    (l ++ [s]).prev s (by simp) = l.getLast hl := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a rest ih =>
      cases rest with
      | nil =>
          have hsa : s ≠ a := by
            intro h
            apply hs
            simp [h]
          simp [List.prev, hsa]
      | cons b rest =>
          have hsa : s ≠ a := by
            intro h
            apply hs
            simp [h]
          have hsb : s ≠ b := by
            intro h
            apply hs
            simp [h]
          have hsTail : s ∉ b :: rest := by
            intro h
            exact hs (by simp [h])
          have hrec := ih (by simp) hsTail
          simpa [List.prev, hsa, hsb] using hrec

/-- On a nonempty noduplicated word, the final letters of its rotations
distinguish rotation indices in the fundamental range. -/
private theorem rotate_getLast_injective_on_range {α : Type*}
    [DecidableEq α] (l : List α) (hnodup : l.Nodup) (hne : l ≠ [])
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length)
    (heq : (l.rotate i).getLast (by simpa using hne) =
      (l.rotate j).getLast (by simpa using hne)) : i = j := by
  have hri : l.rotate i ≠ [] := by simpa using hne
  have hrj : l.rotate j ≠ [] := by simpa using hne
  have heq' : (l.rotate i).getLast hri = (l.rotate j).getLast hrj := by
    simpa only using heq
  rw [List.getLast_eq_getElem hri, List.getLast_eq_getElem hrj,
    List.getElem_rotate, List.getElem_rotate] at heq'
  have hindex := hnodup.getElem_inj_iff.mp heq'
  simp only [List.length_rotate] at hindex
  have hmod : i % l.length = j % l.length :=
    Nat.ModEq.add_left_cancel' (l.length - 1) hindex
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

private theorem rotationClassSlot_of_append
    (v : PermutationVertex k) (pre : Word k) (x : Alphabet k)
    (hpre : pre ≠ []) (hword : v.1 = pre ++ [x]) :
    rotationClassSlot v x = pre.getLast hpre := by
  have hx : x ∉ pre := by
    intro hxpre
    have hnodup : (pre ++ [x]).Nodup := by
      rw [← hword]
      exact v.nodup
    have hdisjoint := (List.nodup_append.mp hnodup).2.2
    exact (hdisjoint _ hxpre _ (by simp)) rfl
  simpa [rotationClassSlot, hword] using
    (prev_concat_eq_getLast pre x hpre hx)

/-- The entire exact class/core/satellite/slot table `tab:six`. -/
theorem sixTargetTable {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    entrySatellite (by omega) (R.target .skip) = R.satellite ∧
      entryCore (R.target .skip) = R.core ∧
      rotationClassSlot (R.target .skip) R.satellite = R.c2 ∧
    entrySatellite (by omega) (R.target .rot) = R.satellite ∧
      entryCore (R.target .rot) = R.rotCore ∧
    entrySatellite (by omega) (R.target .A) = R.c2 ∧
      entryCore (R.target .A) = R.aCore ∧
    rotationClass (R.target .B) = rotationClass R.finalEntry ∧
      deleteSatellite (R.target .B) R.satellite = R.core ∧
      rotationClassSlot (R.target .B) R.satellite =
        coreSlotLetter (by omega) R.entry
          ⟨R.length - 1, by have := R.length_bounds; omega⟩ ∧
    entrySatellite (by omega) (R.target .C) = R.c1 ∧
      entryCore (R.target .C) = R.cCore ∧
    entrySatellite (by omega) (R.target .D) = R.c1 ∧
      entryCore (R.target .D) = R.dCore := by
  have hskipWord : (R.target .skip).1 =
      (R.tail ++ [R.c1, R.c2]) ++ [R.satellite] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hrotWord : (R.target .rot).1 =
      (R.tail ++ [R.c2, R.c1]) ++ [R.satellite] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hAWord : (R.target .A).1 =
      (R.tail ++ [R.c1, R.satellite]) ++ [R.c2] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hCWord : (R.target .C).1 =
      (R.tail ++ [R.c2, R.satellite]) ++ [R.c1] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hDWord : (R.target .D).1 =
      (R.tail ++ [R.satellite, R.c2]) ++ [R.c1] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hskipSat : entrySatellite (by omega) (R.target .skip) =
      R.satellite :=
    entrySatellite_of_append (R.target .skip)
      (R.tail ++ [R.c1, R.c2]) R.satellite hskipWord
  have hskipCore : entryCore (R.target .skip) = R.core := by
    rw [R.target_skip_eq_runMapPower]
    exact runMapPower_core (by omega) (R.length + 1) R.entry
  have hskipSlot : rotationClassSlot (R.target .skip) R.satellite =
      R.c2 := by
    have hpre : R.tail ++ [R.c1, R.c2] ≠ [] := by simp
    calc
      rotationClassSlot (R.target .skip) R.satellite =
          (R.tail ++ [R.c1, R.c2]).getLast hpre :=
        rotationClassSlot_of_append (R.target .skip)
          (R.tail ++ [R.c1, R.c2]) R.satellite hpre hskipWord
      _ = R.c2 := by simp
  have hrotSat : entrySatellite (by omega) (R.target .rot) =
      R.satellite :=
    entrySatellite_of_append (R.target .rot)
      (R.tail ++ [R.c2, R.c1]) R.satellite hrotWord
  have hrotCore : entryCore (R.target .rot) = R.rotCore := by
    exact entryCore_of_append (R.target .rot)
      (R.tail ++ [R.c2, R.c1]) R.satellite hrotWord
  have hASat : entrySatellite (by omega) (R.target .A) = R.c2 :=
    entrySatellite_of_append (R.target .A)
      (R.tail ++ [R.c1, R.satellite]) R.c2 hAWord
  have hACore : entryCore (R.target .A) = R.aCore := by
    exact entryCore_of_append (R.target .A)
      (R.tail ++ [R.c1, R.satellite]) R.c2 hAWord
  have hBClass : rotationClass (R.target .B) =
      rotationClass R.finalEntry := by
    rw [R.target_B_eq_rotationPower_finalEntry]
    exact rotationClass_rotationPower (by omega) 2 R.finalEntry
  have hfinalSat : entrySatellite (by omega) R.finalEntry =
      R.satellite := by
    rw [R.finalEntry_eq]
    exact runMapPower_satellite (by omega) (R.length - 1) R.entry
  have hfinalCore : entryCore R.finalEntry = R.core := by
    rw [R.finalEntry_eq]
    exact runMapPower_core (by omega) (R.length - 1) R.entry
  have hBDelete : deleteSatellite (R.target .B) R.satellite =
      R.core := by
    calc
      deleteSatellite (R.target .B) R.satellite =
          deleteSatellite R.finalEntry R.satellite :=
        deleteSatellite_eq_of_same_class (by omega) hBClass R.satellite
      _ = entryCore R.finalEntry := by
        rw [← hfinalSat]
        exact deleteSatellite_entrySatellite (by omega) R.finalEntry
      _ = R.core := hfinalCore
  have hBSlot : rotationClassSlot (R.target .B) R.satellite =
      coreSlotLetter (by omega) R.entry
        ⟨R.length - 1, by have := R.length_bounds; omega⟩ := by
    calc
      rotationClassSlot (R.target .B) R.satellite =
          rotationClassSlot R.finalEntry R.satellite :=
        rotationClassSlot_eq_of_same_class (by omega) hBClass R.satellite
      _ = rotationClassSlot
          (runMapPower (by omega) (R.length - 1) R.entry) R.satellite := by
        rw [R.finalEntry_eq]
      _ = coreSlotLetter (by omega) R.entry
          ⟨R.length - 1, by have := R.length_bounds; omega⟩ := by
        exact runMapPower_slot (by omega) R.entry
          ⟨R.length - 1, by have := R.length_bounds; omega⟩
  have hCSat : entrySatellite (by omega) (R.target .C) = R.c1 :=
    entrySatellite_of_append (R.target .C)
      (R.tail ++ [R.c2, R.satellite]) R.c1 hCWord
  have hCCore : entryCore (R.target .C) = R.cCore := by
    exact entryCore_of_append (R.target .C)
      (R.tail ++ [R.c2, R.satellite]) R.c1 hCWord
  have hDSat : entrySatellite (by omega) (R.target .D) = R.c1 :=
    entrySatellite_of_append (R.target .D)
      (R.tail ++ [R.satellite, R.c2]) R.c1 hDWord
  have hDCore : entryCore (R.target .D) = R.dCore := by
    exact entryCore_of_append (R.target .D)
      (R.tail ++ [R.satellite, R.c2]) R.c1 hDWord
  exact ⟨hskipSat, hskipCore, hskipSlot, hrotSat, hrotCore,
    hASat, hACore, hBClass, hBDelete, hBSlot, hCSat, hCCore,
    hDSat, hDCore⟩

/-! ## Immediate fates -/

/-- The actual run immediately following `R₀` in its light segment. -/
noncomputable def nextRun {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length) :
    BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩

/-- The next actual global run is the next exact local run. -/
theorem nextRun_blocks {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length) :
    (R.nextRun hnext).blocks =
      segment.runAt ⟨R.localIndex.1 + 1, hnext⟩ := by
  simpa [nextRun] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
      ⟨R.localIndex.1 + 1, hnext⟩).symm

private theorem runBoundaryWeight_of_nonempty
    (left right : List (PermutationVertex k))
    (hleft : left ≠ []) (hright : right ≠ []) :
    runBoundaryWeight left right =
      overlapWeight (blockExit (left.getLast hleft)) (right.head hright) := by
  simp [runBoundaryWeight, List.getLast?_eq_some_getLast hleft,
    List.head?_eq_some_head hright]

/-- The actual next entry is reached from the actual final exit by weight
three. -/
theorem nextRun_entry_weight_three {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length) :
    overlapWeight R.exit (R.nextRun hnext).entry = 3 := by
  have hlight := blockAlignedLightSegment_runAt_light hk p hp segment
    R.localIndex.1 hnext
  rw [← R.run_blocks, ← R.nextRun_blocks hnext] at hlight
  have hleft : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hright : (R.nextRun hnext).blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp (R.nextRun hnext)
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  unfold IsLightRunBoundary at hlight
  rw [runBoundaryWeight_of_nonempty R.run.blocks
    (R.nextRun hnext).blocks hleft hright] at hlight
  simpa [exit, finalEntry, BlockAlignedRun.lastEntry,
    BlockAlignedRun.entry] using hlight

private theorem blockEntries_nodup (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedBlockEntries hk p hp).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact (blockAlignedBlockEntries_pairwiseDistinct hk p hp).imp (by
    intro u v hclasses huv
    exact hclasses (congrArg rotationClass huv))

private theorem rotationClasses_ne_of_entries_mem (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    {u v : PermutationVertex k}
    (hu : u ∈ blockAlignedBlockEntries hk p hp)
    (hv : v ∈ blockAlignedBlockEntries hk p hp)
    (huv : u ≠ v) : rotationClass u ≠ rotationClass v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have hpair := blockAlignedBlockEntries_pairwiseDistinct hk p hp
  by_cases hij : i.1 < j.1
  · have hrel := List.pairwise_iff_getElem.mp hpair i.1 j.1 i.2 j.2 hij
    change rotationClass ((blockAlignedBlockEntries hk p hp).get i) ≠
      rotationClass ((blockAlignedBlockEntries hk p hp).get j) at hrel
    rw [hi, hj] at hrel
    exact hrel
  · by_cases hji : j.1 < i.1
    · have hrel := List.pairwise_iff_getElem.mp hpair j.1 i.1 j.2 i.2 hji
      change rotationClass ((blockAlignedBlockEntries hk p hp).get j) ≠
        rotationClass ((blockAlignedBlockEntries hk p hp).get i) at hrel
      rw [hj, hi] at hrel
      exact fun hclasses => hrel hclasses.symm
    · have hindex : i = j := Fin.ext (by omega)
      subst j
      exact (huv (hi.symm.trans hj)).elim

private theorem runAt_rotationClasses_ne_of_lt (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i j : ℕ) (hi : i < (blockAlignedRuns hk p hp).length)
    (hj : j < (blockAlignedRuns hk p hp).length) (hij : i < j)
    {u v : PermutationVertex k}
    (hu : u ∈ (blockAlignedRunAt hk p hp ⟨i, hi⟩).blocks)
    (hv : v ∈ (blockAlignedRunAt hk p hp ⟨j, hj⟩).blocks) :
    rotationClass u ≠ rotationClass v := by
  let runs := blockAlignedRuns hk p hp
  have hflat : runs.flatten = blockAlignedBlockEntries hk p hp :=
    (blockAlignedRuns_spec hk p hp).1
  have hnodup : runs.flatten.Nodup := by
    rw [hflat]
    exact blockEntries_nodup hk p hp
  have hpair : runs.Pairwise List.Disjoint := (List.nodup_flatten.mp hnodup).2
  have hdisjoint := hpair.rel_get_of_lt
    (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (Fin.mk_lt_mk.mpr hij)
  have huv : u ≠ v := by
    intro heq
    exact List.disjoint_left.mp hdisjoint hu (heq ▸ hv)
  have huEntries : u ∈ blockAlignedBlockEntries hk p hp := by
    rw [← hflat]
    exact List.mem_flatten.mpr
      ⟨(blockAlignedRuns hk p hp).get ⟨i, hi⟩,
        List.get_mem _ _, hu⟩
  have hvEntries : v ∈ blockAlignedBlockEntries hk p hp := by
    rw [← hflat]
    exact List.mem_flatten.mpr
      ⟨(blockAlignedRuns hk p hp).get ⟨j, hj⟩,
        List.get_mem _ _, hv⟩
  exact rotationClasses_ne_of_entries_mem hk p hp huEntries hvEntries huv

private theorem runMapPower_runMapPower_eq_of_add (hk : 7 ≤ k)
    (u : PermutationVertex k) (a b : ℕ) (hab : a + b = k - 1) :
    runMapPower (by omega) b (runMapPower (by omega) a u) = u := by
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), runMapPower_word (by omega)]
  simp only [List.dropLast_concat]
  rw [runMapPower_satellite (by omega)]
  rw [List.rotate_rotate, hab]
  have hcoreLength : u.1.dropLast.length = k - 1 := by
    simp [PermutationVertex.length]
  rw [← hcoreLength, List.rotate_length]
  exact entry_dropLast_append_satellite (by omega) u

/-- The delayed collision of the `skip` row is the entry class of `R₀`. -/
theorem target_skip_delayed_collision {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    runMapPower (by omega) (k - 2 - R.length) (R.target .skip) =
      R.entry := by
  rw [R.target_skip_eq_runMapPower]
  apply runMapPower_runMapPower_eq_of_add hk
  have := R.length_bounds
  omega

private theorem rotate_append_left_length (left right : List α) :
    (left ++ right).rotate left.length = right ++ left := by
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp

/-- The delayed `D` class is the already occupied `B` class. -/
theorem target_B_eq_rotation_D_delayed {hk : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.target .B =
      rotation (runMapPower (by omega) (k - 2) (R.target .D)) := by
  have hDWord : (R.target .D).1 =
      (R.tail ++ [R.satellite, R.c2]) ++ [R.c1] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hDSat := R.sixTargetTable.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply PermutationVertex.ext
  rw [rotation_word_eq_rotate (by omega), runMapPower_word (by omega),
    hDWord, hDSat]
  simp only [List.dropLast_concat]
  have hindex : k - 2 = (R.tail ++ [R.satellite]).length := by
    simp [R.tail_length]
    omega
  rw [hindex]
  rw [show R.tail ++ [R.satellite, R.c2] =
    (R.tail ++ [R.satellite]) ++ [R.c2] by simp [List.append_assoc]]
  rw [rotate_append_left_length]
  rw [R.target_word]
  simp [targetSuffix, List.rotate_cons_succ, List.append_assoc]

/-- Immediate fate of `B`: its class is the last occupied block class, so
the following actual run cannot start there. -/
theorem immediateFate_B {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length) :
    (R.nextRun hnext).entry ≠ R.target .B := by
  intro hentry
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hnextNonempty : (R.nextRun hnext).blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp (R.nextRun hnext)
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hclasses : rotationClass R.finalEntry =
      rotationClass (R.nextRun hnext).entry := by
    calc
      rotationClass R.finalEntry = rotationClass (R.target .B) :=
        R.sixTargetTable.2.2.2.2.2.2.2.1.symm
      _ = rotationClass (R.nextRun hnext).entry :=
        congrArg rotationClass hentry.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by omega) (List.getLast_mem hRNonempty)
    (List.head_mem hnextNonempty)) hclasses

/-- Immediate fate of `D`: an actual run entered there has at most `n-1`
blocks. -/
theorem immediateFate_D {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length)
    (hentry : (R.nextRun hnext).entry = R.target .D) :
    (R.nextRun hnext).length ≤ k - 2 := by
  by_contra hnot
  have hlong : k - 2 < (R.nextRun hnext).length := by omega
  let y := (R.nextRun hnext).blocks.get ⟨k - 2, hlong⟩
  have hy : y = runMapPower (by omega) (k - 2) (R.target .D) := by
    calc
      y = runMapPower (by omega) (k - 2) (R.nextRun hnext).entry :=
        blockAlignedRun_entrySequence hk p hp (R.nextRun hnext)
          (k - 2) hlong
      _ = _ := congrArg _ hentry
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hclasses : rotationClass R.finalEntry = rotationClass y := by
    calc
      rotationClass R.finalEntry = rotationClass (R.target .B) :=
        R.sixTargetTable.2.2.2.2.2.2.2.1.symm
      _ = rotationClass
          (rotation (runMapPower (by omega) (k - 2) (R.target .D))) :=
        congrArg rotationClass R.target_B_eq_rotation_D_delayed
      _ = rotationClass
          (runMapPower (by omega) (k - 2) (R.target .D)) := by
        simpa [rotationPower, Function.iterate_one] using
          rotationClass_rotationPower (by omega) 1 _
      _ = rotationClass y := congrArg rotationClass hy.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by omega) (List.getLast_mem hRNonempty) (List.get_mem _ _)) hclasses

/-- Immediate fate of `skip`: an actual run entered there has at most
`n-1-ℓ₀` blocks, with truncated subtraction justified by nonfullness. -/
theorem immediateFate_skip {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length)
    (hentry : (R.nextRun hnext).entry = R.target .skip) :
    (R.nextRun hnext).length ≤ k - 2 - R.length := by
  by_contra hnot
  have hdelay : k - 2 - R.length < (R.nextRun hnext).length := by omega
  let y := (R.nextRun hnext).blocks.get
    ⟨k - 2 - R.length, hdelay⟩
  have hy : y = R.entry := by
    calc
      y = runMapPower (by omega) (k - 2 - R.length)
          (R.nextRun hnext).entry :=
        blockAlignedRun_entrySequence hk p hp (R.nextRun hnext)
          (k - 2 - R.length) hdelay
      _ = runMapPower (by omega) (k - 2 - R.length)
          (R.target .skip) := congrArg _ hentry
      _ = R.entry := R.target_skip_delayed_collision
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hclasses : rotationClass R.entry = rotationClass y :=
    congrArg rotationClass hy.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by omega) (List.head_mem hRNonempty) (List.get_mem _ _)) hclasses

/-- **Immediate fates.**  The following actual entry is one of the six
targets; `B`, `D`, and `skip` have the exact three stated fates, and a full
following run can begin only at `rot`, `A`, or `C`. -/
theorem immediateFates {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hnext : R.localIndex.1 + 1 < segment.length) :
    (R.nextRun hnext).entry ∈ R.targetList ∧
      (R.nextRun hnext).entry ≠ R.target .B ∧
      ((R.nextRun hnext).entry = R.target .D →
        (R.nextRun hnext).length ≤ k - 2) ∧
      ((R.nextRun hnext).entry = R.target .skip →
        (R.nextRun hnext).length ≤ k - 2 - R.length) ∧
      ((R.nextRun hnext).IsFull →
        (R.nextRun hnext).entry = R.target .rot ∨
        (R.nextRun hnext).entry = R.target .A ∨
        (R.nextRun hnext).entry = R.target .C) := by
  have hmem := (R.sixTargets (R.nextRun hnext).entry).mp
    (R.nextRun_entry_weight_three hnext)
  refine ⟨hmem, R.immediateFate_B hnext,
    R.immediateFate_D hnext, R.immediateFate_skip hnext, ?_⟩
  intro hfull
  unfold targetList at hmem
  simp only [SatelliteTargetName.all, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hskip | hrot | hA | hB | hC | hD
  · have hbound := R.immediateFate_skip hnext hskip
    have hlength : (R.nextRun hnext).length = k - 1 := hfull
    have := R.length_bounds.1
    omega
  · exact Or.inl hrot
  · exact Or.inr (Or.inl hA)
  · exact (R.immediateFate_B hnext hB).elim
  · exact Or.inr (Or.inr hC)
  · have hbound := R.immediateFate_D hnext hD
    have hlength : (R.nextRun hnext).length = k - 1 := hfull
    omega

/-! ## Maximal full chains following the nonfull run -/

/-- The `rot` chain closes after its `n-2=k-3` possible full runs at the
first as-yet unoccupied slot of the original two-loop. -/
theorem fullRunMapPower_rot_closes {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    fullRunMapPower (by omega) (k - 3) (R.target .rot) =
      runMapPower (by omega) R.length R.entry := by
  apply PermutationVertex.ext
  rw [fullRunMapPower_word, R.target_word,
    runMapPower_word (by omega)]
  have htail : R.tail.length = k - 3 := R.tail_length
  have hword : R.tail ++ [R.c2, R.c1, R.satellite] =
      (R.tail ++ [R.c2]) ++ [R.c1, R.satellite] := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have htake :
      (R.tail ++ [R.c2, R.c1, R.satellite]).take (k - 2) =
        R.tail ++ [R.c2] := by
    calc
      (R.tail ++ [R.c2, R.c1, R.satellite]).take (k - 2) =
          ((R.tail ++ [R.c2]) ++ [R.c1, R.satellite]).take (k - 2) :=
        congrArg (fun w => w.take (k - 2)) hword
      _ = R.tail ++ [R.c2] := by
        rw [show k - 2 = (R.tail ++ [R.c2]).length by
          simp [htail]; omega]
        exact List.take_left
  have hdrop :
      (R.tail ++ [R.c2, R.c1, R.satellite]).drop (k - 2) =
        [R.c1, R.satellite] := by
    calc
      (R.tail ++ [R.c2, R.c1, R.satellite]).drop (k - 2) =
          ((R.tail ++ [R.c2]) ++ [R.c1, R.satellite]).drop (k - 2) :=
        congrArg (fun w => w.drop (k - 2)) hword
      _ = [R.c1, R.satellite] := by
        rw [show k - 2 = (R.tail ++ [R.c2]).length by
          simp [htail]; omega]
        exact List.drop_left
  simp only [targetSuffix] at *
  rw [htake, hdrop]
  have hprefixRotate :
      (R.tail ++ [R.c2]).rotate (k - 3) = [R.c2] ++ R.tail := by
    rw [show k - 3 = R.tail.length by omega]
    simp [List.rotate_eq_drop_append_take]
  rw [hprefixRotate]
  have hlen : R.length - 1 + 1 = R.length := by
    have := R.length_bounds.1
    omega
  have hcoreRotate : R.entry.1.dropLast.rotate R.length =
      [R.c2] ++ R.tail ++ [R.c1] := by
    calc
      R.entry.1.dropLast.rotate R.length =
          R.entry.1.dropLast.rotate ((R.length - 1) + 1) := by rw [hlen]
      _ = R.rotatedCore.rotate 1 := by
        simp [rotatedCore, List.rotate_rotate]
      _ = [R.c2] ++ R.tail ++ [R.c1] := by
        rw [R.rotatedCore_eq]
        simp [List.rotate_eq_drop_append_take]
  rw [hcoreRotate]
  simp [satellite, List.append_assoc]

private theorem entry_word_at_chain_cut {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    R.entry.1 =
      R.tail.drop (k - 2 - R.length) ++ [R.c1, R.c2] ++
        R.tail.take (k - 2 - R.length) ++ [R.satellite] := by
  let q := k - 2 - R.length
  let x := R.tail.take q
  let z := R.tail.drop q
  have hq : q ≤ R.tail.length := by
    dsimp [q]
    rw [R.tail_length]
    have := R.length_bounds.1
    omega
  have hxlen : x.length = q := by simp [x, hq]
  have hzlen : z.length = R.length - 1 := by
    simp [z, q, R.tail_length]
    have := R.length_bounds
    omega
  have htail : R.tail = x ++ z := by
    exact (R.tail.take_append_drop q).symm
  have hsum : (R.length - 1) + (q + 2) = k - 1 := by
    dsimp [q]
    have := R.length_bounds
    omega
  have hcoreLength : R.entry.1.dropLast.length = k - 1 := by
    simp [PermutationVertex.length]
  have hundo : R.entry.1.dropLast = R.rotatedCore.rotate (q + 2) := by
    calc
      R.entry.1.dropLast =
          R.entry.1.dropLast.rotate (k - 1) := by
        rw [← hcoreLength, List.rotate_length]
      _ = R.entry.1.dropLast.rotate ((R.length - 1) + (q + 2)) := by
        rw [hsum]
      _ = (R.entry.1.dropLast.rotate (R.length - 1)).rotate (q + 2) := by
        rw [List.rotate_rotate]
      _ = R.rotatedCore.rotate (q + 2) := by rfl
  have hrotated : R.rotatedCore = ([R.c1, R.c2] ++ x) ++ z := by
    rw [R.rotatedCore_eq, htail]
    simp
  have hqprefix : ([R.c1, R.c2] ++ x).length = q + 2 := by
    simp [hxlen]
  have hcoreWord : R.entry.1.dropLast = z ++ [R.c1, R.c2] ++ x := by
    rw [hundo, hrotated, ← hqprefix, rotate_append_left_length]
    simp [List.append_assoc]
  rw [← entry_dropLast_append_satellite (by omega) R.entry,
    hcoreWord]
  change z ++ [R.c1, R.c2] ++ x ++ [R.satellite] = _
  rfl

/-- At the first forbidden `A`-chain index, block `ℓ₀` is already in
the entry class of `R₀`. -/
theorem fullRunMapPower_A_collision {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    runMapPower (by omega) R.length
        (fullRunMapPower (by omega) (k - 2 - R.length) (R.target .A)) =
      rotationPower (R.length + 1) R.entry := by
  let q := k - 2 - R.length
  let x := R.tail.take q
  let z := R.tail.drop q
  have hq : q ≤ R.tail.length := by
    dsimp [q]
    rw [R.tail_length]
    have := R.length_bounds.1
    omega
  have hxlen : x.length = q := by simp [x, hq]
  have hzlen : z.length = R.length - 1 := by
    simp [z, q, R.tail_length]
    have := R.length_bounds
    omega
  have htail : R.tail = x ++ z :=
    (R.tail.take_append_drop q).symm
  have htargetWord : (R.target .A).1 =
      (R.tail ++ [R.c1]) ++ [R.satellite, R.c2] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hprefixLength : (R.tail ++ [R.c1]).length = k - 2 := by
    simp [R.tail_length]
    omega
  have hfullWord :
      (fullRunMapPower (by omega) q (R.target .A)).1 =
        z ++ [R.c1] ++ x ++ [R.satellite, R.c2] := by
    rw [fullRunMapPower_word, htargetWord]
    rw [show ((R.tail ++ [R.c1]) ++ [R.satellite, R.c2]).take (k - 2) =
      R.tail ++ [R.c1] by
        rw [← hprefixLength]
        exact List.take_left]
    rw [show ((R.tail ++ [R.c1]) ++ [R.satellite, R.c2]).drop (k - 2) =
      [R.satellite, R.c2] by
        rw [← hprefixLength]
        exact List.drop_left]
    rw [htail]
    have hpref : (x ++ z) ++ [R.c1] = x ++ (z ++ [R.c1]) := by
      simp [List.append_assoc]
    rw [hpref, ← hxlen, rotate_append_left_length]
  have hfullSat : entrySatellite (by omega)
      (fullRunMapPower (by omega) q (R.target .A)) = R.c2 := by
    apply entrySatellite_of_append
      (fullRunMapPower (by omega) q (R.target .A))
      (z ++ [R.c1] ++ x ++ [R.satellite]) R.c2
    rw [hfullWord]
    simp [List.append_assoc]
  have hfullCore :
      (fullRunMapPower (by omega) q (R.target .A)).1.dropLast =
        z ++ [R.c1] ++ x ++ [R.satellite] := by
    rw [hfullWord]
    rw [show z ++ [R.c1] ++ x ++ [R.satellite, R.c2] =
      (z ++ [R.c1] ++ x ++ [R.satellite]) ++ [R.c2] by
        simp [List.append_assoc]]
    exact List.dropLast_concat
  have hrunRotate :
      (z ++ [R.c1] ++ x ++ [R.satellite]).rotate R.length =
        x ++ [R.satellite] ++ z ++ [R.c1] := by
    have hleftLength : (z ++ [R.c1]).length = R.length := by
      simp [hzlen]
      have := R.length_bounds.1
      omega
    rw [show z ++ [R.c1] ++ x ++ [R.satellite] =
      (z ++ [R.c1]) ++ (x ++ [R.satellite]) by
        simp [List.append_assoc]]
    rw [← hleftLength, rotate_append_left_length]
    simp only [List.append_assoc]
  have hentryWord := entry_word_at_chain_cut R
  change R.entry.1 = z ++ [R.c1, R.c2] ++ x ++ [R.satellite] at hentryWord
  have hentryRotate : R.entry.1.rotate (R.length + 1) =
      x ++ [R.satellite] ++ z ++ [R.c1, R.c2] := by
    rw [hentryWord]
    have hleftLength : (z ++ [R.c1, R.c2]).length = R.length + 1 := by
      simp [hzlen]
      have := R.length_bounds.1
      omega
    rw [show z ++ [R.c1, R.c2] ++ x ++ [R.satellite] =
      (z ++ [R.c1, R.c2]) ++ (x ++ [R.satellite]) by
        simp [List.append_assoc]]
    rw [← hleftLength, rotate_append_left_length]
    simp only [List.append_assoc]
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), rotationPower_word (by omega),
    hfullCore, hfullSat, hrunRotate, hentryRotate]
  simp

/-- At the first forbidden `C`-chain index, block `ℓ₀-1` is already in
the entry class of `R₀`. -/
theorem fullRunMapPower_C_collision {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    runMapPower (by omega) (R.length - 1)
        (fullRunMapPower (by omega) (k - 2 - R.length) (R.target .C)) =
      rotationPower R.length R.entry := by
  let q := k - 2 - R.length
  let x := R.tail.take q
  let z := R.tail.drop q
  have hq : q ≤ R.tail.length := by
    dsimp [q]
    rw [R.tail_length]
    have := R.length_bounds.1
    omega
  have hxlen : x.length = q := by simp [x, hq]
  have hzlen : z.length = R.length - 1 := by
    simp [z, q, R.tail_length]
    have := R.length_bounds
    omega
  have htail : R.tail = x ++ z :=
    (R.tail.take_append_drop q).symm
  have htargetWord : (R.target .C).1 =
      (R.tail ++ [R.c2]) ++ [R.satellite, R.c1] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hprefixLength : (R.tail ++ [R.c2]).length = k - 2 := by
    simp [R.tail_length]
    omega
  have hfullWord :
      (fullRunMapPower (by omega) q (R.target .C)).1 =
        z ++ [R.c2] ++ x ++ [R.satellite, R.c1] := by
    rw [fullRunMapPower_word, htargetWord]
    rw [show ((R.tail ++ [R.c2]) ++ [R.satellite, R.c1]).take (k - 2) =
      R.tail ++ [R.c2] by
        rw [← hprefixLength]
        exact List.take_left]
    rw [show ((R.tail ++ [R.c2]) ++ [R.satellite, R.c1]).drop (k - 2) =
      [R.satellite, R.c1] by
        rw [← hprefixLength]
        exact List.drop_left]
    rw [htail]
    have hpref : (x ++ z) ++ [R.c2] = x ++ (z ++ [R.c2]) := by
      simp [List.append_assoc]
    rw [hpref, ← hxlen, rotate_append_left_length]
  have hfullSat : entrySatellite (by omega)
      (fullRunMapPower (by omega) q (R.target .C)) = R.c1 := by
    apply entrySatellite_of_append
      (fullRunMapPower (by omega) q (R.target .C))
      (z ++ [R.c2] ++ x ++ [R.satellite]) R.c1
    rw [hfullWord]
    simp [List.append_assoc]
  have hfullCore :
      (fullRunMapPower (by omega) q (R.target .C)).1.dropLast =
        z ++ [R.c2] ++ x ++ [R.satellite] := by
    rw [hfullWord]
    rw [show z ++ [R.c2] ++ x ++ [R.satellite, R.c1] =
      (z ++ [R.c2] ++ x ++ [R.satellite]) ++ [R.c1] by
        simp [List.append_assoc]]
    exact List.dropLast_concat
  have hrunRotate :
      (z ++ [R.c2] ++ x ++ [R.satellite]).rotate (R.length - 1) =
        [R.c2] ++ x ++ [R.satellite] ++ z := by
    rw [show z ++ [R.c2] ++ x ++ [R.satellite] =
      z ++ ([R.c2] ++ x ++ [R.satellite]) by
        simp [List.append_assoc]]
    rw [← hzlen, rotate_append_left_length]
  have hentryWord := entry_word_at_chain_cut R
  change R.entry.1 = z ++ [R.c1, R.c2] ++ x ++ [R.satellite] at hentryWord
  have hentryRotate : R.entry.1.rotate R.length =
      [R.c2] ++ x ++ [R.satellite] ++ z ++ [R.c1] := by
    rw [hentryWord]
    have hleftLength : (z ++ [R.c1]).length = R.length := by
      simp [hzlen]
      have := R.length_bounds.1
      omega
    rw [show z ++ [R.c1, R.c2] ++ x ++ [R.satellite] =
      (z ++ [R.c1]) ++ ([R.c2] ++ x ++ [R.satellite]) by
        simp [List.append_assoc]]
    rw [← hleftLength, rotate_append_left_length]
    simp only [List.append_assoc]
  apply PermutationVertex.ext
  rw [runMapPower_word (by omega), rotationPower_word (by omega),
    hfullCore, hfullSat, hrunRotate, hentryRotate]

/-- A nonempty maximal chain of consecutive full runs beginning immediately
after `R₀` and remaining inside the same actual light segment.  Maximality is
forward maximality at the exact local endpoint. -/
structure FullRunChain {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) where
  runCount : ℕ
  positive : 0 < runCount
  inBounds : R.localIndex.1 + 1 + runCount ≤ segment.length
  full : ∀ j, ∀ hj : j < runCount,
    (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1
  maximal : ∀ hnext : R.localIndex.1 + 1 + runCount < segment.length,
    (segment.runAt ⟨R.localIndex.1 + 1 + runCount, hnext⟩).length ≠ k - 1

namespace FullRunChain

/-- The `j`th actual run in the following chain, at its transported global
index. -/
noncomputable def run {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : Fin chain.runCount) : BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1 + j.1), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      have := chain.inBounds
      omega⟩

/-- The transported chain run is exactly the corresponding local run. -/
theorem run_blocks {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : Fin chain.runCount) :
    (chain.run j).blocks =
      segment.runAt ⟨R.localIndex.1 + 1 + j.1, by
        have := chain.inBounds
        omega⟩ := by
  simpa [run] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
      ⟨R.localIndex.1 + 1 + j.1, by
        have := chain.inBounds
        omega⟩).symm

/-- The actual first run of the chain. -/
noncomputable def firstRun {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain) :
    BlockAlignedRun hk p hp := chain.run ⟨0, chain.positive⟩

/-- The following chain as the accepted E1 global full-light interval. -/
noncomputable def globalChain {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain) :
    BlockAlignedFullLightChain hk p hp :=
  segment.fullIntervalChain hk p hp (R.localIndex.1 + 1) chain.runCount
    chain.inBounds chain.full

/-- Exact E1 `τ₃` entry formula for every actual run in the chain. -/
theorem entry_formula {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : ℕ) (hj : j < chain.runCount) :
    (chain.run ⟨j, hj⟩).entry =
      fullRunMapPower (by omega) j chain.firstRun.entry := by
  have hformula := blockAlignedFullLightChain_entry_formula hk p hp
    chain.globalChain j hj
  simpa [globalChain, run, firstRun, Nat.add_assoc] using hformula

/-- Every represented chain run is actually full. -/
theorem run_isFull {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : ℕ) (hj : j < chain.runCount) :
    (chain.run ⟨j, hj⟩).IsFull := by
  have hblocks := chain.run_blocks ⟨j, hj⟩
  have hlength := congrArg List.length hblocks
  simpa [BlockAlignedRun.IsFull, BlockAlignedRun.length] using
    hlength.trans (chain.full j hj)

/-- The first actual following run is the immediate successor `nextRun`. -/
theorem firstRun_eq_nextRun {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain) :
    chain.firstRun = R.nextRun (by
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_right chain.positive) chain.inBounds) := by
  rfl

/-- Immediate-fate classification of the first full run of an actual
following chain. -/
theorem first_entry_classification {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain) :
    chain.firstRun.entry = R.target .rot ∨
      chain.firstRun.entry = R.target .A ∨
      chain.firstRun.entry = R.target .C := by
  let hnext : R.localIndex.1 + 1 < segment.length := by
    have := chain.inBounds
    have := chain.positive
    omega
  have hfullLocal := chain.full 0 chain.positive
  have hfull : (R.nextRun hnext).IsFull := by
    have hblocks := R.nextRun_blocks hnext
    have hlength := congrArg List.length hblocks
    simpa [BlockAlignedRun.IsFull, BlockAlignedRun.length] using
      hlength.trans hfullLocal
  have hclass := (R.immediateFates hnext).2.2.2.2 hfull
  simpa [chain.firstRun_eq_nextRun] using hclass

/-- Any later actual run entered at `τ₂^ℓ₀(u)` lays at most the exact gap
`d₀=n-ℓ₀`, including `ℓ₀=1` and `ℓ₀=n-1`. -/
theorem gap_entry_length_le {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : ℕ) (hj : j < chain.runCount)
    (hentry : (chain.run ⟨j, hj⟩).entry =
      runMapPower (by omega) R.length R.entry) :
    (chain.run ⟨j, hj⟩).length ≤ R.deficit := by
  by_contra hnot
  have hdelay : R.deficit < (chain.run ⟨j, hj⟩).length := by omega
  let y := (chain.run ⟨j, hj⟩).blocks.get ⟨R.deficit, hdelay⟩
  have hy : y = R.entry := by
    calc
      y = runMapPower (by omega) R.deficit
          (chain.run ⟨j, hj⟩).entry :=
        blockAlignedRun_entrySequence hk p hp (chain.run ⟨j, hj⟩)
          R.deficit hdelay
      _ = runMapPower (by omega) R.deficit
          (runMapPower (by omega) R.length R.entry) := congrArg _ hentry
      _ = R.entry := runMapPower_runMapPower_eq_of_add hk R.entry
        R.length R.deficit R.length_add_deficit
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hclasses : rotationClass R.entry = rotationClass y :=
    congrArg rotationClass hy.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1 + j))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        have := chain.inBounds
        omega)
    (by omega) (List.head_mem hRNonempty) (List.get_mem _ _)) hclasses

private theorem no_entry_class_collision {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (j : ℕ) (hj : j < chain.runCount) (i : ℕ)
    (hi : i < (chain.run ⟨j, hj⟩).blocks.length)
    (hclass : rotationClass
      ((chain.run ⟨j, hj⟩).blocks.get ⟨i, hi⟩) =
        rotationClass R.entry) : False := by
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1 + j))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        have := chain.inBounds
        omega)
    (by omega) (List.head_mem hRNonempty) (List.get_mem _ _)) hclass.symm

/-- A `rot`-entered maximal chain has at most `n-2=k-3` full runs. -/
theorem rot_runCount_le {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hfirst : chain.firstRun.entry = R.target .rot) :
    chain.runCount ≤ k - 3 := by
  by_contra hnot
  have hj : k - 3 < chain.runCount := by omega
  have hentry : (chain.run ⟨k - 3, hj⟩).entry =
      runMapPower (by omega) R.length R.entry := by
    calc
      (chain.run ⟨k - 3, hj⟩).entry =
          fullRunMapPower (by omega) (k - 3) chain.firstRun.entry :=
        chain.entry_formula (k - 3) hj
      _ = fullRunMapPower (by omega) (k - 3) (R.target .rot) :=
        congrArg _ hfirst
      _ = runMapPower (by omega) R.length R.entry :=
        R.fullRunMapPower_rot_closes
  have hgap := chain.gap_entry_length_le (k - 3) hj hentry
  have hfull : (chain.run ⟨k - 3, hj⟩).length = k - 1 :=
    chain.run_isFull (k - 3) hj
  have hdeficit := R.length_add_deficit
  have hlengthPos := R.length_bounds.1
  omega

/-- An `A`-entered maximal chain has at most `n-1-ℓ₀`. -/
theorem A_runCount_le {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hfirst : chain.firstRun.entry = R.target .A) :
    chain.runCount ≤ k - 2 - R.length := by
  by_contra hnot
  let q := k - 2 - R.length
  have hj : q < chain.runCount := by dsimp [q]; omega
  have hrunFull := chain.run_isFull q hj
  have hi : R.length < (chain.run ⟨q, hj⟩).blocks.length := by
    have hfull : (chain.run ⟨q, hj⟩).blocks.length = k - 1 := hrunFull
    have := R.length_bounds.2
    omega
  let y := (chain.run ⟨q, hj⟩).blocks.get ⟨R.length, hi⟩
  have hy : y = rotationPower (R.length + 1) R.entry := by
    calc
      y = runMapPower (by omega) R.length
          (chain.run ⟨q, hj⟩).entry :=
        blockAlignedRun_entrySequence hk p hp (chain.run ⟨q, hj⟩)
          R.length hi
      _ = runMapPower (by omega) R.length
          (fullRunMapPower (by omega) q chain.firstRun.entry) := by
        congr 1
        exact chain.entry_formula q hj
      _ = runMapPower (by omega) R.length
          (fullRunMapPower (by omega) q (R.target .A)) :=
        congrArg _ (congrArg _ hfirst)
      _ = rotationPower (R.length + 1) R.entry := by
        simpa [q] using R.fullRunMapPower_A_collision
  apply no_entry_class_collision chain q hj R.length hi
  change rotationClass y = rotationClass R.entry
  rw [hy]
  exact rotationClass_rotationPower (by omega) (R.length + 1) R.entry

/-- A `C`-entered maximal chain has at most `n-1-ℓ₀`. -/
theorem C_runCount_le {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hfirst : chain.firstRun.entry = R.target .C) :
    chain.runCount ≤ k - 2 - R.length := by
  by_contra hnot
  let q := k - 2 - R.length
  have hj : q < chain.runCount := by dsimp [q]; omega
  have hrunFull := chain.run_isFull q hj
  have hi : R.length - 1 < (chain.run ⟨q, hj⟩).blocks.length := by
    have hfull : (chain.run ⟨q, hj⟩).blocks.length = k - 1 := hrunFull
    have := R.length_bounds
    omega
  let y := (chain.run ⟨q, hj⟩).blocks.get ⟨R.length - 1, hi⟩
  have hy : y = rotationPower R.length R.entry := by
    calc
      y = runMapPower (by omega) (R.length - 1)
          (chain.run ⟨q, hj⟩).entry :=
        blockAlignedRun_entrySequence hk p hp (chain.run ⟨q, hj⟩)
          (R.length - 1) hi
      _ = runMapPower (by omega) (R.length - 1)
          (fullRunMapPower (by omega) q chain.firstRun.entry) := by
        congr 1
        exact chain.entry_formula q hj
      _ = runMapPower (by omega) (R.length - 1)
          (fullRunMapPower (by omega) q (R.target .C)) :=
        congrArg _ (congrArg _ hfirst)
      _ = rotationPower R.length R.entry := by
        simpa [q] using R.fullRunMapPower_C_collision
  apply no_entry_class_collision chain q hj (R.length - 1) hi
  change rotationClass y = rotationClass R.entry
  rw [hy]
  exact rotationClass_rotationPower (by omega) R.length R.entry

/-! ## The endgame of an extremal `rot` chain -/

/-- A class already occupied either by `R₀` or by one of the actual full
runs in the following chain. -/
def OccupiedBeforeEnd {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (v : PermutationVertex k) : Prop :=
  (∃ y ∈ R.run.blocks, rotationClass v = rotationClass y) ∨
    ∃ j, ∃ hj : j < chain.runCount,
      ∃ y ∈ (chain.run ⟨j, hj⟩).blocks,
        rotationClass v = rotationClass y

/-- The last actual run when an extremal `rot` chain has exactly
`n-2=k-3` runs. -/
noncomputable def endRun {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3) : BlockAlignedRun hk p hp :=
  chain.run ⟨k - 4, by omega⟩

/-- Exact word of the entry of the last full run in an extremal `rot`
chain. -/
theorem endRun_entry_word {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot) :
    (chain.endRun hcount).entry.1 =
      R.c0 :: ([R.c2] ++ R.endTail) ++ [R.c1, R.satellite] := by
  have hj : k - 4 < chain.runCount := by omega
  have hentry := chain.entry_formula (k - 4) hj
  have htail := R.tail_eq_endTail_append_c0
  have htarget : (R.target .rot).1 =
      (R.tail ++ [R.c2]) ++ [R.c1, R.satellite] := by
    rw [R.target_word]
    simp [targetSuffix, List.append_assoc]
  have hprefixLength : (R.tail ++ [R.c2]).length = k - 2 := by
    simp [R.tail_length]
    omega
  have hrotate : (R.tail ++ [R.c2]).rotate (k - 4) =
      [R.c0, R.c2] ++ R.endTail := by
    rw [htail]
    rw [show R.endTail ++ [R.c0] ++ [R.c2] =
      R.endTail ++ [R.c0, R.c2] by simp [List.append_assoc]]
    rw [show k - 4 = R.endTail.length by rw [R.endTail_length]]
    exact rotate_append_left_length R.endTail [R.c0, R.c2]
  rw [endRun, hentry, hrot, fullRunMapPower_word, htarget]
  rw [show ((R.tail ++ [R.c2]) ++ [R.c1, R.satellite]).take (k - 2) =
    R.tail ++ [R.c2] by
      rw [← hprefixLength]
      exact List.take_left]
  rw [show ((R.tail ++ [R.c2]) ++ [R.c1, R.satellite]).drop (k - 2) =
    [R.c1, R.satellite] by
      rw [← hprefixLength]
      exact List.drop_left]
  rw [hrotate]
  simp

/-- Exact six chart words at the final exit, in the frozen E1 order. -/
theorem endRun_target_words {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot) :
    let w := (chain.endRun hcount).entry
    (fullRunChartTarget1 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.c0, R.c1, R.satellite] ∧
    (fullRunChartTarget2 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.c0, R.satellite, R.c1] ∧
    (fullRunChartTarget3 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.c1, R.c0, R.satellite] ∧
    (fullRunChartTarget4 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.c1, R.satellite, R.c0] ∧
    (fullRunChartTarget5 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.satellite, R.c0, R.c1] ∧
    (fullRunChartTarget6 hk w).1 =
        ([R.c2] ++ R.endTail) ++ [R.satellite, R.c1, R.c0] := by
  dsimp only
  apply fullRunChart_target_words_of_split hk
    (chain.endRun hcount).entry R.c0 R.c1 R.satellite
    ([R.c2] ++ R.endTail)
  · simp [R.endTail_length]
    omega
  · simpa [List.append_assoc] using chain.endRun_entry_word hcount hrot

/-- The sole forward chart target is exactly the gap entry
`τ₂^ℓ₀(u)`. -/
theorem endRun_target1_eq_gap {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot) :
    fullRunChartTarget1 hk (chain.endRun hcount).entry =
      runMapPower (by omega) R.length R.entry := by
  have hj : k - 4 < chain.runCount := by omega
  have hentry := chain.entry_formula (k - 4) hj
  rw [fullRunChart_target1_eq_fullRunMap, endRun, hentry]
  have hsucc : k - 4 + 1 = k - 3 := by omega
  rw [hrot]
  calc
    fullRunMap (by omega)
        (fullRunMapPower (by omega) (k - 4) (R.target .rot)) =
        fullRunMapPower (by omega) (k - 4 + 1) (R.target .rot) := by
      simp [fullRunMapPower, Function.iterate_succ_apply']
    _ = fullRunMapPower (by omega) (k - 3) (R.target .rot) := by
      rw [hsucc]
    _ = runMapPower (by omega) R.length R.entry :=
      R.fullRunMapPower_rot_closes

/-- The second endgame target is a rotation of the last occupied class of
`R₀`. -/
theorem endRun_target2_eq_rotation_B {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot) :
    fullRunChartTarget2 hk (chain.endRun hcount).entry =
      rotationPower (k - 1) (R.target .B) := by
  apply PermutationVertex.ext
  rw [(chain.endRun_target_words hcount hrot).2.1,
    rotationPower_word (by omega), R.target_word,
    R.tail_eq_endTail_append_c0]
  have hleftLength :
      (R.endTail ++ [R.c0, R.satellite, R.c1]).length = k - 1 := by
    simp [R.endTail_length]
    omega
  rw [show R.endTail ++ [R.c0] ++
      R.targetSuffix SatelliteTargetName.B =
      (R.endTail ++ [R.c0, R.satellite, R.c1]) ++ [R.c2] by
        simp [targetSuffix, List.append_assoc]]
  rw [← hleftLength, rotate_append_left_length]
  simp

private theorem previous_R0_entry_word {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) (hlength : 2 ≤ R.length) :
    (runMapPower (by omega) (R.length - 2) R.entry).1 =
      [R.c0, R.c1, R.c2] ++ R.endTail ++ [R.satellite] := by
  have hcoreLength : R.entry.1.dropLast.length = k - 1 := by
    simp [PermutationVertex.length]
  have hrotated : R.rotatedCore =
      ([R.c1, R.c2] ++ R.endTail) ++ [R.c0] := by
    rw [R.rotatedCore_eq, R.tail_eq_endTail_append_c0]
    simp
  have hprefixLength : ([R.c1, R.c2] ++ R.endTail).length = k - 2 := by
    simp [R.endTail_length]
    omega
  have hprev : R.entry.1.dropLast.rotate (R.length - 2) =
      R.rotatedCore.rotate (k - 2) := by
    have harith : (R.length - 2) + (k - 1) =
        (R.length - 1) + (k - 2) := by
      have hell : R.length - 2 + 2 = R.length := by omega
      have hk' : k - 2 + 2 = k := by omega
      omega
    calc
      R.entry.1.dropLast.rotate (R.length - 2) =
          (R.entry.1.dropLast.rotate (R.length - 2)).rotate (k - 1) := by
        symm
        rw [show k - 1 =
          (R.entry.1.dropLast.rotate (R.length - 2)).length by
            simp [hcoreLength]]
        exact List.rotate_length _
      _ = R.entry.1.dropLast.rotate ((R.length - 2) + (k - 1)) := by
        rw [List.rotate_rotate]
      _ = R.entry.1.dropLast.rotate ((R.length - 1) + (k - 2)) := by
        rw [harith]
      _ = (R.entry.1.dropLast.rotate (R.length - 1)).rotate (k - 2) := by
        rw [List.rotate_rotate]
      _ = R.rotatedCore.rotate (k - 2) := by rfl
  rw [runMapPower_word (by omega), hprev, hrotated]
  rw [← hprefixLength, rotate_append_left_length]
  simp [satellite]

/-- Under the exact hypothesis `ℓ₀≥2`, the fifth endgame target is a
rotation of block `ℓ₀-2` of `R₀`. -/
theorem endRun_target5_eq_previous_R0 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot)
    (hlength : 2 ≤ R.length) :
    fullRunChartTarget5 hk (chain.endRun hcount).entry =
      rotationPower 2
        (runMapPower (by omega) (R.length - 2) R.entry) := by
  apply PermutationVertex.ext
  rw [(chain.endRun_target_words hcount hrot).2.2.2.2.1,
    rotationPower_word (by omega), previous_R0_entry_word R hlength]
  rw [show [R.c0, R.c1, R.c2] ++ R.endTail ++ [R.satellite] =
    [R.c0, R.c1] ++ ([R.c2] ++ R.endTail ++ [R.satellite]) by
      simp]
  symm
  rw [show 2 = ([R.c0, R.c1] : Word k).length by simp,
    rotate_append_left_length]
  simp [List.append_assoc]

/-- The actual run immediately after a maximal following full chain, when
that local endpoint still lies in the light segment. -/
noncomputable def afterRun {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hnext : R.localIndex.1 + 1 + chain.runCount < segment.length) :
    BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1 + chain.runCount), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩

/-- Exact local/global identity for the run after the chain. -/
theorem afterRun_blocks {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hnext : R.localIndex.1 + 1 + chain.runCount < segment.length) :
    (chain.afterRun hnext).blocks =
      segment.runAt
        ⟨R.localIndex.1 + 1 + chain.runCount, hnext⟩ := by
  simpa [afterRun] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
      ⟨R.localIndex.1 + 1 + chain.runCount, hnext⟩).symm

/-- From the gap entry after the chain, at most `d₀` blocks can actually be
laid. -/
theorem afterRun_gap_length_le {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hnext : R.localIndex.1 + 1 + chain.runCount < segment.length)
    (hentry : (chain.afterRun hnext).entry =
      runMapPower (by omega) R.length R.entry) :
    (chain.afterRun hnext).length ≤ R.deficit := by
  by_contra hnot
  have hdelay : R.deficit < (chain.afterRun hnext).length := by omega
  let y := (chain.afterRun hnext).blocks.get ⟨R.deficit, hdelay⟩
  have hy : y = R.entry := by
    calc
      y = runMapPower (by omega) R.deficit
          (chain.afterRun hnext).entry :=
        blockAlignedRun_entrySequence hk p hp (chain.afterRun hnext)
          R.deficit hdelay
      _ = runMapPower (by omega) R.deficit
          (runMapPower (by omega) R.length R.entry) := congrArg _ hentry
      _ = R.entry := runMapPower_runMapPower_eq_of_add hk R.entry
        R.length R.deficit R.length_add_deficit
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hclasses : rotationClass R.entry = rotationClass y :=
    congrArg rotationClass hy.symm
  exact (runAt_rotationClasses_ne_of_lt hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1 + chain.runCount))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        omega)
    (by omega) (List.head_mem hRNonempty) (List.get_mem _ _)) hclasses

/-- **The three chains.**  Exact bounds for all three possible first
entries.  In the extremal `rot` case the formal next `τ₃` entry is the
gap class, and an actual post-chain run which is that `τ₃` continuation
has at most the exact gap `d₀`.  Unlike the former clause, this quantifies
the actual run after an exact chain, not an already-full member of it. -/
theorem threeChains {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain) :
    (chain.firstRun.entry = R.target .rot →
      chain.runCount ≤ k - 3 ∧
      fullRunMapPower (by omega) (k - 3) chain.firstRun.entry =
        runMapPower (by omega) R.length R.entry ∧
      (chain.runCount = k - 3 →
        ∀ hnext : R.localIndex.1 + 1 + chain.runCount < segment.length,
          (chain.afterRun hnext).entry =
              fullRunMapPower (by omega) (k - 3) chain.firstRun.entry →
            (chain.afterRun hnext).entry =
                runMapPower (by omega) R.length R.entry ∧
              (chain.afterRun hnext).length ≤ R.deficit)) ∧
    (chain.firstRun.entry = R.target .A →
      chain.runCount ≤ k - 2 - R.length) ∧
    (chain.firstRun.entry = R.target .C →
      chain.runCount ≤ k - 2 - R.length) := by
  constructor
  · intro hrot
    refine ⟨chain.rot_runCount_le hrot, ?_, ?_⟩
    · rw [hrot]
      exact R.fullRunMapPower_rot_closes
    · intro _hcount hnext hentry
      have hgap : (chain.afterRun hnext).entry =
          runMapPower (by omega) R.length R.entry := by
        calc
          (chain.afterRun hnext).entry =
              fullRunMapPower (by omega) (k - 3)
                chain.firstRun.entry := hentry
          _ = fullRunMapPower (by omega) (k - 3)
              (R.target .rot) := congrArg _ hrot
          _ = runMapPower (by omega) R.length R.entry :=
            R.fullRunMapPower_rot_closes
      exact ⟨hgap, chain.afterRun_gap_length_le hnext hgap⟩
  constructor
  · exact chain.A_runCount_le
  · exact chain.C_runCount_le

/-- The boundary from the last full chain run to its actual following run
has exact weight three. -/
theorem afterRun_entry_weight_three {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hnext : R.localIndex.1 + 1 + chain.runCount < segment.length) :
    overlapWeight
      (blockExit (chain.run ⟨chain.runCount - 1, by
        have := chain.positive
        omega⟩).lastEntry)
      (chain.afterRun hnext).entry = 3 := by
  have hlastLocal : R.localIndex.1 + 1 + (chain.runCount - 1) + 1 <
      segment.length := by
    have := chain.positive
    omega
  have hlight := blockAlignedLightSegment_runAt_light hk p hp segment
    (R.localIndex.1 + 1 + (chain.runCount - 1)) hlastLocal
  have hlastBlocks := chain.run_blocks
    ⟨chain.runCount - 1, by have := chain.positive; omega⟩
  have hafterBlocks := chain.afterRun_blocks hnext
  have hafterBlocks' : (chain.afterRun hnext).blocks =
      segment.runAt
        ⟨R.localIndex.1 + 1 + (chain.runCount - 1) + 1,
          hlastLocal⟩ := by
    have hindex : R.localIndex.1 + 1 + (chain.runCount - 1) + 1 =
        R.localIndex.1 + 1 + chain.runCount := by
      have := chain.positive
      omega
    simpa only [hindex] using hafterBlocks
  rw [← hlastBlocks, ← hafterBlocks'] at hlight
  have hlastNonempty :
      (chain.run ⟨chain.runCount - 1, by
        have := chain.positive
        omega⟩).blocks ≠ [] := by
    exact List.ne_nil_of_mem_splitBy
      (chain.run ⟨chain.runCount - 1, by
        have := chain.positive
        omega⟩).isRun
  have hafterNonempty : (chain.afterRun hnext).blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy (chain.afterRun hnext).isRun
  unfold IsLightRunBoundary at hlight
  rw [runBoundaryWeight_of_nonempty _ _ hlastNonempty hafterNonempty] at hlight
  simpa [BlockAlignedRun.lastEntry, BlockAlignedRun.entry] using hlight

/-- An actual run after the chain cannot enter any class already occupied
by `R₀` or the chain. -/
theorem afterRun_not_occupied {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hnext : R.localIndex.1 + 1 + chain.runCount < segment.length) :
    ¬chain.OccupiedBeforeEnd (chain.afterRun hnext).entry := by
  intro hoccupied
  have hafterNonempty : (chain.afterRun hnext).blocks ≠ [] :=
    List.ne_nil_of_mem_splitBy (chain.afterRun hnext).isRun
  rcases hoccupied with hR | hchain
  · obtain ⟨y, hy, hclass⟩ := hR
    exact (runAt_rotationClasses_ne_of_lt hk p hp
      (segment.globalStart + R.localIndex.1)
      (segment.globalStart + (R.localIndex.1 + 1 + chain.runCount))
      (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
          omega)
      (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
          omega)
      (by omega) hy (List.head_mem hafterNonempty)) hclass.symm
  · obtain ⟨j, hj, y, hy, hclass⟩ := hchain
    exact (runAt_rotationClasses_ne_of_lt hk p hp
      (segment.globalStart + (R.localIndex.1 + 1 + j))
      (segment.globalStart + (R.localIndex.1 + 1 + chain.runCount))
      (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
          have := chain.inBounds
          omega)
      (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
          omega)
      (by omega) hy (List.head_mem hafterNonempty)) hclass.symm

/-- In an extremal formal `rot` orbit, the gap class at the next
`τ₃` entry is not among the classes of any earlier full run.  This is
the unconditional cyclic-core separation used by the endgame, independent
of whether an actual following run exists. -/
private theorem rot_gap_class_ne_formal_chain_block
    {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (j i : ℕ) (hj : j < k - 3) (_hi : i < k - 1) :
    rotationClass (runMapPower (by omega) R.length R.entry) ≠
      rotationClass
        (runMapPower (by omega) i
          (fullRunMapPower (by omega) j (R.target .rot))) := by
  let pre : Word k := R.tail ++ [R.c2]
  have hprefixLength : pre.length = k - 2 := by
    simp [pre, R.tail_length]
    omega
  have htargetWord : (R.target .rot).1 =
      pre ++ [R.c1, R.satellite] := by
    rw [R.target_word]
    simp [pre, targetSuffix, List.append_assoc]
  have htargetNodup : (pre ++ [R.c1, R.satellite]).Nodup := by
    rw [← htargetWord]
    exact (R.target .rot).nodup
  have hprefixNodup : pre.Nodup :=
    (List.nodup_append.mp htargetNodup).1
  have hc1not : R.c1 ∉ pre := by
    have hdisjoint := (List.nodup_append.mp htargetNodup).2.2
    intro hc1
    exact hdisjoint R.c1 hc1 R.c1 (by simp) rfl
  have hprefixNonempty : pre ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [hprefixLength] at hlen
    simp at hlen
    omega
  have hfullWord (q : ℕ) :
      (fullRunMapPower (by omega) q (R.target .rot)).1 =
        pre.rotate q ++ [R.c1, R.satellite] := by
    rw [fullRunMapPower_word, htargetWord]
    have htake : (pre ++ [R.c1, R.satellite]).take (k - 2) =
        pre := by
      rw [← hprefixLength]
      exact List.take_left
    have hdrop : (pre ++ [R.c1, R.satellite]).drop (k - 2) =
        [R.c1, R.satellite] := by
      rw [← hprefixLength]
      exact List.drop_left
    rw [htake, hdrop]
  have hgapWord :
      (runMapPower (by omega) R.length R.entry).1 =
        pre.rotate (k - 3) ++ [R.c1, R.satellite] := by
    rw [← R.fullRunMapPower_rot_closes]
    exact hfullWord (k - 3)
  have hchainWord :
      (fullRunMapPower (by omega) j (R.target .rot)).1 =
        (pre.rotate j ++ [R.c1]) ++ [R.satellite] := by
    simpa [List.append_assoc] using hfullWord j
  have hgapWord' :
      (runMapPower (by omega) R.length R.entry).1 =
        (pre.rotate (k - 3) ++ [R.c1]) ++ [R.satellite] := by
    simpa [List.append_assoc] using hgapWord
  have hgapSat :
      entrySatellite (by omega)
        (runMapPower (by omega) R.length R.entry) = R.satellite := by
    simpa [SatelliteContext.satellite] using
      runMapPower_satellite (by omega) R.length R.entry
  have hchainSat :
      entrySatellite (by omega)
        (fullRunMapPower (by omega) j (R.target .rot)) = R.satellite :=
    entrySatellite_of_append
      (fullRunMapPower (by omega) j (R.target .rot))
      (pre.rotate j ++ [R.c1]) R.satellite hchainWord
  have hblockSat :
      entrySatellite (by omega)
        (runMapPower (by omega) i
          (fullRunMapPower (by omega) j (R.target .rot))) =
        R.satellite := by
    exact (runMapPower_satellite (by omega) i
      (fullRunMapPower (by omega) j (R.target .rot))).trans hchainSat
  intro hclass
  have hdelete := deleteSatellite_eq_of_same_class
    (by omega) hclass R.satellite
  have hcoreEq :
      entryCore (runMapPower (by omega) R.length R.entry) =
        entryCore (fullRunMapPower (by omega) j (R.target .rot)) := by
    calc
      entryCore (runMapPower (by omega) R.length R.entry) =
          deleteSatellite (runMapPower (by omega) R.length R.entry)
            R.satellite := by
        rw [← hgapSat]
        exact (deleteSatellite_entrySatellite (by omega) _).symm
      _ = deleteSatellite
          (runMapPower (by omega) i
            (fullRunMapPower (by omega) j (R.target .rot)))
          R.satellite := hdelete
      _ = entryCore
          (runMapPower (by omega) i
            (fullRunMapPower (by omega) j (R.target .rot))) := by
        rw [← hblockSat]
        exact deleteSatellite_entrySatellite (by omega) _
      _ = entryCore
          (fullRunMapPower (by omega) j (R.target .rot)) :=
        runMapPower_core (by omega) i _
  have hcycle :
      ((pre.rotate (k - 3) ++ [R.c1]) : Cycle (Alphabet k)) =
        (pre.rotate j ++ [R.c1] : Cycle (Alphabet k)) := by
    calc
      ((pre.rotate (k - 3) ++ [R.c1]) : Cycle (Alphabet k)) =
          entryCore (runMapPower (by omega) R.length R.entry) :=
        (entryCore_of_append
          (runMapPower (by omega) R.length R.entry)
          (pre.rotate (k - 3) ++ [R.c1]) R.satellite
          hgapWord').symm
      _ = entryCore
          (fullRunMapPower (by omega) j (R.target .rot)) := hcoreEq
      _ = (pre.rotate j ++ [R.c1] : Cycle (Alphabet k)) :=
        entryCore_of_append
          (fullRunMapPower (by omega) j (R.target .rot))
          (pre.rotate j ++ [R.c1]) R.satellite hchainWord
  have hrotated :
      pre.rotate (k - 3) ++ [R.c1] ~r
        pre.rotate j ++ [R.c1] :=
    Cycle.coe_eq_coe.mp hcycle
  have hc1notLeft : R.c1 ∉ pre.rotate (k - 3) := by
    simpa using hc1not
  have hc1notRight : R.c1 ∉ pre.rotate j := by
    simpa using hc1not
  have hleftNodup :
      (pre.rotate (k - 3) ++ [R.c1]).Nodup := by
    have hrotateNodup : (pre.rotate (k - 3)).Nodup :=
      List.nodup_rotate.mpr hprefixNodup
    rw [← List.concat_eq_append]
    exact hrotateNodup.concat hc1notLeft
  have hc1mem : R.c1 ∈ pre.rotate (k - 3) ++ [R.c1] := by simp
  have hprev := List.isRotated_prev_eq hrotated hleftNodup hc1mem
  have hleftNonempty : pre.rotate (k - 3) ≠ [] := by
    simpa using hprefixNonempty
  have hrightNonempty : pre.rotate j ≠ [] := by
    simpa using hprefixNonempty
  have hlast :
      (pre.rotate (k - 3)).getLast hleftNonempty =
        (pre.rotate j).getLast hrightNonempty := by
    calc
      (pre.rotate (k - 3)).getLast hleftNonempty =
          (pre.rotate (k - 3) ++ [R.c1]).prev R.c1 (by simp) :=
        (prev_concat_eq_getLast (pre.rotate (k - 3)) R.c1
          hleftNonempty hc1notLeft).symm
      _ = (pre.rotate j ++ [R.c1]).prev R.c1 (by simp) := hprev
      _ = (pre.rotate j).getLast hrightNonempty :=
        prev_concat_eq_getLast (pre.rotate j) R.c1
          hrightNonempty hc1notRight
  have hindex := rotate_getLast_injective_on_range
    pre hprefixNodup hprefixNonempty (k - 3) j
    (by rw [hprefixLength]; omega)
    (by rw [hprefixLength]; omega) hlast
  omega

/-- Exactly the five named non-gap endgame targets lie in classes already
occupied by `R₀` or by the actual full chain: target 1 is unoccupied
unconditionally, even when no following run exists, while targets 2--6 are
occupied. -/
theorem endRun_five_occupied {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot)
    (hlength : 2 ≤ R.length) :
    ¬chain.OccupiedBeforeEnd
        (fullRunChartTarget1 hk (chain.endRun hcount).entry) ∧
    chain.OccupiedBeforeEnd
        (fullRunChartTarget2 hk (chain.endRun hcount).entry) ∧
    chain.OccupiedBeforeEnd
        (fullRunChartTarget3 hk (chain.endRun hcount).entry) ∧
    chain.OccupiedBeforeEnd
        (fullRunChartTarget4 hk (chain.endRun hcount).entry) ∧
    chain.OccupiedBeforeEnd
        (fullRunChartTarget5 hk (chain.endRun hcount).entry) ∧
    chain.OccupiedBeforeEnd
        (fullRunChartTarget6 hk (chain.endRun hcount).entry) := by
  let j := k - 4
  have hj : j < chain.runCount := by dsimp [j]; omega
  let last := chain.run ⟨j, hj⟩
  have hlastEq : last = chain.endRun hcount := by rfl
  have hlastFull : last.IsFull := chain.run_isFull j hj
  have hlastLength : last.blocks.length = k - 1 := hlastFull
  have hlastNonempty : last.blocks ≠ [] := by
    intro h
    rw [h] at hlastLength
    simp at hlastLength
    omega
  have hRNonempty : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hnotTarget1 :
      ¬chain.OccupiedBeforeEnd
        (fullRunChartTarget1 hk (chain.endRun hcount).entry) := by
    intro hoccupied
    rcases hoccupied with hR | hchain
    · obtain ⟨y, hy, hclass⟩ := hR
      obtain ⟨fi, hget⟩ := List.mem_iff_get.mp hy
      have hiLength : fi.1 < R.length := by
        simp [SatelliteContext.length, BlockAlignedRun.length]
      have hyPower :
          y = runMapPower (by omega) fi.1 R.entry := by
        calc
          y = R.run.blocks.get fi := hget.symm
          _ = runMapPower (by omega) fi.1 R.run.entry :=
            blockAlignedRun_entrySequence hk p hp R.run fi.1
              (by simp [BlockAlignedRun.length])
          _ = runMapPower (by omega) fi.1 R.entry := rfl
      have hlengthIndex : R.length < k - 1 := by
        have := R.length_bounds.2
        omega
      have hiIndex : fi.1 < k - 1 := hiLength.trans hlengthIndex
      have hclasses :
          rotationClass (runMapPower (by omega) R.length R.entry) =
            rotationClass (runMapPower (by omega) fi.1 R.entry) := by
        calc
          rotationClass (runMapPower (by omega) R.length R.entry) =
              rotationClass
                (fullRunChartTarget1 hk (chain.endRun hcount).entry) :=
            congrArg rotationClass
              (chain.endRun_target1_eq_gap hcount hrot).symm
          _ = rotationClass y := hclass
          _ = rotationClass (runMapPower (by omega) fi.1 R.entry) :=
            congrArg rotationClass hyPower
      have hindexEq := runMap_rotationClasses_injective (by omega) R.entry
        hlengthIndex hiIndex hclasses
      omega
    · obtain ⟨q, hq, y, hy, hclass⟩ := hchain
      obtain ⟨fi, hget⟩ := List.mem_iff_get.mp hy
      have hrunLength :
          (chain.run ⟨q, hq⟩).blocks.length = k - 1 :=
        chain.run_isFull q hq
      have hiIndex : fi.1 < k - 1 := by omega
      have hyFormal :
          y = runMapPower (by omega) fi.1
            (fullRunMapPower (by omega) q (R.target .rot)) := by
        calc
          y = (chain.run ⟨q, hq⟩).blocks.get fi := hget.symm
          _ = runMapPower (by omega) fi.1
              (chain.run ⟨q, hq⟩).entry :=
            blockAlignedRun_entrySequence hk p hp
              (chain.run ⟨q, hq⟩) fi.1
              (by simp [BlockAlignedRun.length])
          _ = runMapPower (by omega) fi.1
              (fullRunMapPower (by omega) q chain.firstRun.entry) := by
            congr 1
            exact chain.entry_formula q hq
          _ = runMapPower (by omega) fi.1
              (fullRunMapPower (by omega) q (R.target .rot)) := by
            rw [hrot]
      have hclasses :
          rotationClass (runMapPower (by omega) R.length R.entry) =
            rotationClass
              (runMapPower (by omega) fi.1
                (fullRunMapPower (by omega) q (R.target .rot))) := by
        calc
          rotationClass (runMapPower (by omega) R.length R.entry) =
              rotationClass
                (fullRunChartTarget1 hk (chain.endRun hcount).entry) :=
            congrArg rotationClass
              (chain.endRun_target1_eq_gap hcount hrot).symm
          _ = rotationClass y := hclass
          _ = rotationClass
              (runMapPower (by omega) fi.1
                (fullRunMapPower (by omega) q (R.target .rot))) :=
            congrArg rotationClass hyFormal
      have hqBound : q < k - 3 := by omega
      exact rot_gap_class_ne_formal_chain_block R q fi.1
        hqBound hiIndex hclasses
  constructor
  · exact hnotTarget1
  constructor
  · refine Or.inl ⟨R.finalEntry, ?_, ?_⟩
    · exact List.getLast_mem hRNonempty
    · calc
        rotationClass (fullRunChartTarget2 hk
            (chain.endRun hcount).entry) =
            rotationClass (rotationPower (k - 1) (R.target .B)) :=
          congrArg rotationClass (chain.endRun_target2_eq_rotation_B
            hcount hrot)
        _ = rotationClass (R.target .B) :=
          rotationClass_rotationPower (by omega) (k - 1) (R.target .B)
        _ = rotationClass R.finalEntry :=
          R.sixTargetTable.2.2.2.2.2.2.2.1
  constructor
  · have hi1 : 1 < last.blocks.length := by omega
    refine Or.inr ⟨j, hj, last.blocks.get ⟨1, hi1⟩,
      List.get_mem _ _, ?_⟩
    have hy := blockAlignedRun_entrySequence hk p hp last 1 (by
      simpa [BlockAlignedRun.length] using hi1)
    calc
      rotationClass (fullRunChartTarget3 hk
          (chain.endRun hcount).entry) =
          rotationClass (runMap (by omega) last.entry) := by
        rw [← hlastEq, fullRunChart_target3_eq_runMap]
      _ = rotationClass (last.blocks.get ⟨1, hi1⟩) := by
        rw [hy]
        simp [runMapPower]
  constructor
  · have hi0 : 0 < last.blocks.length := by omega
    refine Or.inr ⟨j, hj, last.blocks.get ⟨0, hi0⟩,
      List.get_mem _ _, ?_⟩
    have hy := blockAlignedRun_entrySequence hk p hp last 0 (by
      simpa [BlockAlignedRun.length] using hi0)
    calc
      rotationClass (fullRunChartTarget4 hk
          (chain.endRun hcount).entry) =
          rotationClass (rotation last.entry) := by
        rw [← hlastEq, fullRunChart_target4_eq_rotation]
      _ = rotationClass last.entry :=
        rotationClass_rotationPower (by omega) 1 last.entry
      _ = rotationClass (last.blocks.get ⟨0, hi0⟩) := by
        rw [hy]
        simp [runMapPower]
  constructor
  · have hi : R.length - 2 < R.run.blocks.length := by
      change R.length - 2 < R.length
      omega
    let y := R.run.blocks.get ⟨R.length - 2, hi⟩
    refine Or.inl ⟨y, List.get_mem _ _, ?_⟩
    have hy := blockAlignedRun_entrySequence hk p hp R.run
      (R.length - 2) hi
    calc
      rotationClass (fullRunChartTarget5 hk
          (chain.endRun hcount).entry) =
          rotationClass (rotationPower 2
            (runMapPower (by omega) (R.length - 2) R.entry)) :=
        congrArg rotationClass
          (chain.endRun_target5_eq_previous_R0 hcount hrot hlength)
      _ = rotationClass
          (runMapPower (by omega) (R.length - 2) R.entry) :=
        rotationClass_rotationPower (by omega) 2 _
      _ = rotationClass y := congrArg rotationClass hy.symm
  · refine Or.inr ⟨j, hj, last.lastEntry,
      List.getLast_mem hlastNonempty, ?_⟩
    have hchartLast := fullRunChart_lastEntry hk p hp last hlastFull
    calc
      rotationClass (fullRunChartTarget6 hk
          (chain.endRun hcount).entry) =
          rotationClass
            (rotationPower 2
              (fullRunChartLastEntry hk last.entry)) := by
        rw [← hlastEq, fullRunChart_target6_eq_rotationPower_lastEntry]
      _ = rotationClass (fullRunChartLastEntry hk last.entry) :=
        rotationClass_rotationPower (by omega) 2 _
      _ = rotationClass last.lastEntry :=
        congrArg rotationClass hchartLast.symm

/-- **The endgame of the chart chain.**  For `ℓ₀≥2` and exactly
`n-2=k-3` actual `rot`-chain full runs, the actual final exit has exactly
the six named weight-three successors.  Five named classes are already
occupied, target 1 is unconditionally unoccupied and is
`τ₂^ℓ₀(u)`, and every actual further run is forced to that entry and lays
at most `d₀` blocks. -/
theorem endgame {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : chain.runCount = k - 3)
    (hrot : chain.firstRun.entry = R.target .rot)
    (hlength : 2 ≤ R.length) :
    let w := (chain.endRun hcount).entry
    (∀ v : PermutationVertex k,
      overlapWeight (blockExit (chain.endRun hcount).lastEntry) v = 3 ↔
        v ∈ fullRunChartTargets hk w) ∧
    (fullRunChartTargets hk w).length = 6 ∧
    (fullRunChartTargets hk w).Nodup ∧
    fullRunChartTarget1 hk w =
      runMapPower (by omega) R.length R.entry ∧
    ¬chain.OccupiedBeforeEnd (fullRunChartTarget1 hk w) ∧
    chain.OccupiedBeforeEnd (fullRunChartTarget2 hk w) ∧
    chain.OccupiedBeforeEnd (fullRunChartTarget3 hk w) ∧
    chain.OccupiedBeforeEnd (fullRunChartTarget4 hk w) ∧
    chain.OccupiedBeforeEnd (fullRunChartTarget5 hk w) ∧
    chain.OccupiedBeforeEnd (fullRunChartTarget6 hk w) ∧
    ∀ hnext : R.localIndex.1 + 1 + chain.runCount < segment.length,
      (chain.afterRun hnext).entry =
          runMapPower (by omega) R.length R.entry ∧
        (chain.afterRun hnext).length ≤ R.deficit := by
  dsimp only
  have hj : k - 4 < chain.runCount := by omega
  have hendFull : (chain.endRun hcount).IsFull := by
    exact chain.run_isFull (k - 4) hj
  have hchartLast := fullRunChart_lastEntry hk p hp
    (chain.endRun hcount) hendFull
  have htargets : ∀ v : PermutationVertex k,
      overlapWeight (blockExit (chain.endRun hcount).lastEntry) v = 3 ↔
        v ∈ fullRunChartTargets hk (chain.endRun hcount).entry := by
    intro v
    rw [hchartLast]
    exact fullRunChart_weightThree_successors hk
      (chain.endRun hcount).entry v
  have hexact := fullRunChartTargets_exactly_six hk
    (chain.endRun hcount).entry
  have hfive := chain.endRun_five_occupied hcount hrot hlength
  refine ⟨htargets, hexact.1, hexact.2,
    chain.endRun_target1_eq_gap hcount hrot,
    hfive.1, hfive.2.1, hfive.2.2.1, hfive.2.2.2.1,
    hfive.2.2.2.2.1, hfive.2.2.2.2.2, ?_⟩
  intro hnext
  have hweight := chain.afterRun_entry_weight_three hnext
  have hmember : (chain.afterRun hnext).entry ∈
      fullRunChartTargets hk (chain.endRun hcount).entry := by
    apply (htargets (chain.afterRun hnext).entry).mp
    have hlastIndex : chain.runCount - 1 = k - 4 := by omega
    simpa [endRun, hlastIndex] using hweight
  rw [fullRunChartTargets_eq_named] at hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  have hnot := chain.afterRun_not_occupied hnext
  have hentry : (chain.afterRun hnext).entry =
      fullRunChartTarget1 hk (chain.endRun hcount).entry := by
    rcases hmember with h1 | h2 | h3 | h4 | h5 | h6
    · exact h1
    · exact (hnot (h2 ▸ hfive.2.1)).elim
    · exact (hnot (h3 ▸ hfive.2.2.1)).elim
    · exact (hnot (h4 ▸ hfive.2.2.2.1)).elim
    · exact (hnot (h5 ▸ hfive.2.2.2.2.1)).elim
    · exact (hnot (h6 ▸ hfive.2.2.2.2.2)).elim
  have hgap : (chain.afterRun hnext).entry =
      runMapPower (by omega) R.length R.entry :=
    hentry.trans (chain.endRun_target1_eq_gap hcount hrot)
  exact ⟨hgap, chain.afterRun_gap_length_le hnext hgap⟩

end FullRunChain

/-! ## Proposition L3 in exact light-segment indices -/

/-- **L3(i), no long full streak.**  A positive-deficit actual run cannot
be followed in its light segment by `n-1=k-2` consecutive full runs. -/
theorem noLongFullStreak {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hin : R.localIndex.1 + 1 + (k - 2) ≤ segment.length)
    (hfull : ∀ j, ∀ hj : j < k - 2,
      (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1) :
    False := by
  let chain : R.FullRunChain :=
    { runCount := k - 2
      positive := by omega
      inBounds := hin
      full := hfull
      maximal := by
        intro hnext
        exfalso
        exact (blockAlignedLightSegment_fullInterval_no_successor hk p hp
          segment (R.localIndex.1 + 1) hin hfull) hnext }
  rcases chain.first_entry_classification with hrot | hA | hC
  · have := chain.rot_runCount_le hrot
    dsimp [chain] at this
    omega
  · have hbound := chain.A_runCount_le hA
    have hpos := R.length_bounds.1
    dsimp [chain] at hbound
    omega
  · have hbound := chain.C_runCount_le hC
    have hpos := R.length_bounds.1
    dsimp [chain] at hbound
    omega

/-- **L3(ii), the gap rule.**  After exactly `n-2=k-3` full runs and a
further actual run `R₁`, its exact local length is at most `d₀`; the stated
deficit inequality is proved equivalent with all truncated subtractions
inside their justified range. -/
theorem gapRule {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (hR1 : R.localIndex.1 + 1 + (k - 3) < segment.length)
    (hfull : ∀ j, ∀ hj : j < k - 3,
      (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1) :
    let ℓ1 := (segment.runAt
      ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length
    ℓ1 ≤ R.deficit ∧
      k - 1 - R.deficit ≤ k - 1 - ℓ1 ∧
      (ℓ1 ≤ R.deficit ↔
        k - 1 - R.deficit ≤ k - 1 - ℓ1) := by
  dsimp only
  have hinLong : R.localIndex.1 + 1 + (k - 2) ≤ segment.length := by
    omega
  have hR1NotFull :
      (segment.runAt
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length ≠ k - 1 := by
    intro hR1Full
    have hfullLong : ∀ j, ∀ hj : j < k - 2,
        (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length =
          k - 1 := by
      intro j hj
      by_cases hshort : j < k - 3
      · exact hfull j hshort
      · have heq : j = k - 3 := by omega
        subst j
        exact hR1Full
    exact R.noLongFullStreak hinLong hfullLong
  let chain : R.FullRunChain :=
    { runCount := k - 3
      positive := by omega
      inBounds := by omega
      full := hfull
      maximal := by
        intro hnext
        simpa using hR1NotFull }
  let hnext : R.localIndex.1 + 1 + chain.runCount < segment.length := by
    simpa [chain] using hR1
  have hactual : (chain.afterRun hnext).length ≤ R.deficit := by
    by_cases hone : R.length = 1
    · have hdeficit : R.deficit = k - 2 := by
        have := R.length_add_deficit
        omega
      have hle := blockAlignedRun_length_le hk p hp (chain.afterRun hnext)
      have hnot : (chain.afterRun hnext).length ≠ k - 1 := by
        have hblocks := chain.afterRun_blocks hnext
        have hlength := congrArg List.length hblocks
        intro hfullActual
        apply hR1NotFull
        have hindex : R.localIndex.1 + 1 + chain.runCount =
            R.localIndex.1 + 1 + (k - 3) := by simp [chain]
        simpa [BlockAlignedRun.length, hindex] using
          hlength.symm.trans hfullActual
      omega
    · have hlength : 2 ≤ R.length := by
        have := R.length_bounds.1
        omega
      rcases chain.first_entry_classification with hrot | hA | hC
      · rcases chain.endgame (by rfl) hrot hlength with
          ⟨_htargets, _hlen, _hnodup, _hgap,
            _hnot1, _h2, _h3, _h4, _h5, _h6, hafter⟩
        exact (hafter hnext).2
      · have hbound := chain.A_runCount_le hA
        have hchainCount : chain.runCount = k - 3 := rfl
        have := R.length_bounds.1
        omega
      · have hbound := chain.C_runCount_le hC
        have hchainCount : chain.runCount = k - 3 := rfl
        have := R.length_bounds.1
        omega
  have hblocks := chain.afterRun_blocks hnext
  have hlocal :
      (segment.runAt
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length ≤ R.deficit := by
    have hindex : R.localIndex.1 + 1 + chain.runCount =
        R.localIndex.1 + 1 + (k - 3) := by simp [chain]
    have hlength := congrArg List.length hblocks
    simpa [BlockAlignedRun.length, hindex] using hlength ▸ hactual
  have hdle : R.deficit ≤ k - 1 := by
    have := R.length_add_deficit
    omega
  let hrunGlobal := blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1 + (k - 3)), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩
  have hrunBlocks : hrunGlobal.blocks =
      segment.runAt ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩ := by
    simpa [hrunGlobal] using
      (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).symm
  have hℓle :
      (segment.runAt
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length ≤ k - 1 := by
    have := blockAlignedRun_length_le hk p hp hrunGlobal
    have hlength := congrArg List.length hrunBlocks
    simpa [BlockAlignedRun.length] using hlength ▸ this
  constructor
  · exact hlocal
  constructor
  · omega
  · omega

/-- **Proposition L3.**  The two exact locally indexed conclusions packaged
together for every represented positive-deficit run in a generic light
segment. -/
theorem L3 {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) :
    (∀ (hin : R.localIndex.1 + 1 + (k - 2) ≤ segment.length)
      (_hfull : ∀ j, ∀ hj : j < k - 2,
        (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1),
      False) ∧
    ∀ (hR1 : R.localIndex.1 + 1 + (k - 3) < segment.length)
      (_hfull : ∀ j, ∀ hj : j < k - 3,
        (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1),
      let ℓ1 := (segment.runAt
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length
      ℓ1 ≤ R.deficit ∧
        k - 1 - R.deficit ≤ k - 1 - ℓ1 := by
  constructor
  · exact R.noLongFullStreak
  · intro hR1 hfull
    exact ⟨(R.gapRule hR1 hfull).1, (R.gapRule hR1 hfull).2.1⟩

end SatelliteContext

end SuperpermutationLowerBound
