module

public import SuperpermutationLowerBound.Refinement.GeometryBasic

@[expose] public section

/-! Global coverage forbids a partition of each n-class insertion loop into
rows of sizes n or n-2 when n>4. This is a finite-set argument, independent
of the order of the rows. The path-level application must establish all
partition hypotheses explicitly. -/
namespace SuperpermutationLowerBound
namespace NewResults

open Finset

/-- A partition into rows occupying more than half of their containing loop
must occupy each such loop in full. -/
theorem dense_rows_fill_loops {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (U : Finset α) (row loop : ι → Finset α) (n : ℕ)
    (hcover : ∀ x ∈ U, ∃ i ∈ I, x ∈ row i)
    (hinside : ∀ i ∈ I, row i ⊆ loop i)
    (hglobal : ∀ i ∈ I, loop i ⊆ U)
    (hsize : ∀ i ∈ I, (loop i).card = n)
    (hdense : ∀ i ∈ I, n < 2 * (row i).card)
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (row i) (row j))
    (hloops : ∀ i ∈ I, ∀ j ∈ I, loop i = loop j ∨ Disjoint (loop i) (loop j)) :
    ∀ i ∈ I, row i = loop i := by
  intro i hi
  apply Finset.Subset.antisymm (hinside i hi)
  intro x hx
  obtain ⟨j, hj, hxj⟩ := hcover x (hglobal i hi hx)
  by_cases hij : i = j
  · simpa [hij] using hxj
  have heq : loop i = loop j := by
    rcases hloops i hi j hj with heq | hsep
    · exact heq
    · exact (Finset.disjoint_left.mp hsep hx (hinside j hj hxj)).elim
  have hsub : row i ∪ row j ⊆ loop i := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hinside i hi hy
    · rw [heq]
      exact hinside j hj hy
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (hdisjoint i hi j hj hij), hsize i hi] at hc
  have hdi := hdense i hi
  have hdj := hdense j hj
  omega

/-- In particular, full and deficit-two rows cannot tile a loop containing
any deficit-two row. -/
theorem full_or_two_rows_are_full {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (U : Finset α) (row loop : ι → Finset α) (n : ℕ) (hn : 4 < n)
    (hcover : ∀ x ∈ U, ∃ i ∈ I, x ∈ row i)
    (hinside : ∀ i ∈ I, row i ⊆ loop i)
    (hglobal : ∀ i ∈ I, loop i ⊆ U)
    (hsize : ∀ i ∈ I, (loop i).card = n)
    (hrow : ∀ i ∈ I, (row i).card = n ∨ (row i).card = n - 2)
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (row i) (row j))
    (hloops : ∀ i ∈ I, ∀ j ∈ I, loop i = loop j ∨ Disjoint (loop i) (loop j)) :
    ∀ i ∈ I, (row i).card = n := by
  have hdense : ∀ i ∈ I, n < 2 * (row i).card := by
    intro i hi
    rcases hrow i hi with h | h <;> omega
  intro i hi
  rw [dense_rows_fill_loops I U row loop n hcover hinside hglobal hsize
    hdense hdisjoint hloops i hi, hsize i hi]

/-- Loops with one common satellite partition the rotation classes, even
when the cyclic cores differ. -/
theorem commonSatellite_twoLoops_eq_or_disjoint {k : ℕ} (hk : 1 ≤ k)
    (s : Alphabet k) (γ η : CyclicCore k) :
    twoLoop hk s γ = twoLoop hk s η ∨ Disjoint (twoLoop hk s γ) (twoLoop hk s η) := by
  classical
  by_cases heq : γ = η
  · exact Or.inl (by rw [heq])
  right
  apply Finset.disjoint_left.mpr
  intro B hB hB'
  obtain ⟨_, u, hu, hsu, hcu⟩ := (mem_twoLoop hk s γ B).mp hB
  obtain ⟨_, v, hv, hsv, hcv⟩ := (mem_twoLoop hk s η B).mp hB'
  have hd := deleteSatellite_eq_of_same_class hk (hu.trans hv.symm) s
  have hdu : deleteSatellite u s = entryCore u := by
    rw [← hsu]
    exact deleteSatellite_entrySatellite hk u
  have hdv : deleteSatellite v s = entryCore v := by
    rw [← hsv]
    exact deleteSatellite_entrySatellite hk v
  rw [hdu, hdv, hcu, hcv] at hd
  exact heq hd


/-- Every rotation class of a block-aligned Hamiltonian path is occupied by
some actual maximal weight-two run. -/
theorem aligned_hamiltonian_run_cover {k : ℕ} (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hp : IsBlockAligned P.toOverlapPath)
    (B : Finset (PermutationVertex k)) (hB : B ∈ rotationBlocks k) :
    ∃ i : Fin (blockAlignedRuns hk P.toOverlapPath hp).length,
      B ∈ (blockAlignedRunAt hk P.toOverlapPath hp i).occupiedClasses := by
  classical
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp (P.complete u)
  let p := P.toOverlapPath
  have hai : a.val < p.length := a.isLt
  have hb : a.val / k < pathBlockCount p := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    rw [Nat.mul_comm]
    rw [← blockAligned_length_eq hp]
    exact hai
  let entry := (blockAlignedBlockEntries hk p hp).get ⟨a.val / k, by simpa using hb⟩
  have he : entry ∈ blockAlignedBlockEntries hk p hp := List.get_mem _ _
  have heq : rotationClass entry = rotationClass u := by
    have hf := exitless_vertex_formula hp.1 (by omega) a.val hai
    have hu : p.vertex ⟨a.val, hai⟩ = u := ha
    rw [hu] at hf
    rw [hf, rotationClass_rotationPower (by omega)]
    exact congrArg rotationClass (blockAlignedBlockEntry_eq_vertex hk p hp _ hb)
  rw [← (blockAlignedRuns_spec hk p hp).1] at he
  obtain ⟨r, hr, her⟩ := List.mem_flatten.mp he
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
  refine ⟨i, ?_⟩
  change rotationClass u ∈ ((blockAlignedRuns hk p hp).get i).toFinset.image rotationClass
  rw [hi]
  exact Finset.mem_image.mpr ⟨entry, List.mem_toFinset.mpr her, heq⟩

/-- The finite occupied-class cardinality is the actual run length. -/
theorem actual_run_class_card {k : ℕ} (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) (r : BlockAlignedRun hk p hp) :
    r.occupiedClasses.card = r.length := by
  classical
  rw [blockAlignedRun_occupiedClasses_eq_slots hk p hp r, Finset.card_image_iff.mpr]
  · exact Finset.card_range _
  · intro i hi j hj hij
    apply runMap_rotationClasses_injective (by omega) r.entry _ _ hij
    · exact (Finset.mem_range.mp hi).trans_le (blockAlignedRun_length_le hk p hp r)
    · exact (Finset.mem_range.mp hj).trans_le (blockAlignedRun_length_le hk p hp r)

/-- Global coverage plus one common satellite excludes deficit-two rows
when all actual rows have deficit zero or two. -/
theorem common_satellite_zero_two_full {k : ℕ} (hk : 7 ≤ k)
    (P : HamiltonianPath k) (hp : IsBlockAligned P.toOverlapPath)
    (s : Alphabet k)
    (hs : ∀ i : Fin (blockAlignedRuns hk P.toOverlapPath hp).length,
      entrySatellite (by omega) (blockAlignedRunAt hk P.toOverlapPath hp i).entry = s)
    (hd : ∀ i : Fin (blockAlignedRuns hk P.toOverlapPath hp).length,
      (blockAlignedRunAt hk P.toOverlapPath hp i).deficit = 0 ∨
      (blockAlignedRunAt hk P.toOverlapPath hp i).deficit = 2) :
    ∀ i : Fin (blockAlignedRuns hk P.toOverlapPath hp).length,
      (blockAlignedRunAt hk P.toOverlapPath hp i).IsFull := by
  classical
  let p := P.toOverlapPath
  let r := fun i : Fin (blockAlignedRuns hk p hp).length => blockAlignedRunAt hk p hp i
  let row := fun i => (r i).occupiedClasses
  let loop := fun i => twoLoop (by omega : 1 ≤ k) s (entryCore (r i).entry)
  have hcard : ∀ i, (row i).card = (r i).length := fun i => actual_run_class_card hk p hp (r i)
  have hcover : ∀ B ∈ rotationBlocks k, ∃ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), B ∈ row i := by
    intro B hB
    obtain ⟨i, hi⟩ := aligned_hamiltonian_run_cover hk P hp B hB
    exact ⟨i, Finset.mem_univ _, hi⟩
  have hinside : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), row i ⊆ loop i := by
    intro i _
    simpa only [row, loop, ← hs i] using blockAlignedRun_occupiedClasses_subset_twoLoop hk p hp (r i)
  have hglobal : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), loop i ⊆ rotationBlocks k := by
    intro i _ B hB
    exact ((mem_twoLoop (by omega) s (entryCore (r i).entry) B).mp hB).1
  have hsize : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), (loop i).card = k - 1 := by
    intro i _
    simpa only [loop, ← hs i] using twoLoop_card (by omega) (r i).entry
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), (row i).card = k - 1 ∨ (row i).card = (k - 1) - 2 := by
    intro i _
    rw [hcard]
    have hb := blockAlignedRun_length_le hk p hp (r i)
    have hdi := hd i
    change (k - 1) - (r i).length = 0 ∨ (k - 1) - (r i).length = 2 at hdi
    omega
  have hdisjoint : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), ∀ j ∈ Finset.univ, i ≠ j → Disjoint (row i) (row j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro B hi hj
    obtain ⟨u, hu, hub⟩ := Finset.mem_image.mp hi
    obtain ⟨v, hv, hvb⟩ := Finset.mem_image.mp hj
    have hc : rotationClass u = rotationClass v := hub.trans hvb.symm
    rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with hlt | hgt
    · exact Refinement.actualRuns_rotationClasses_ne hk p hp _ _ i.isLt j.isLt hlt
        (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv) hc
    · exact Refinement.actualRuns_rotationClasses_ne hk p hp _ _ j.isLt i.isLt hgt
        (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hu) hc.symm
  have hloops : ∀ i ∈ (Finset.univ : Finset (Fin (blockAlignedRuns hk p hp).length)), ∀ j ∈ Finset.univ, loop i = loop j ∨ Disjoint (loop i) (loop j) := by
    intro i _ j _
    exact commonSatellite_twoLoops_eq_or_disjoint (by omega) s _ _
  intro i
  have hc := full_or_two_rows_are_full Finset.univ (rotationBlocks k) row loop
    (k - 1) (by omega) hcover hinside hglobal hsize hrow hdisjoint hloops i (Finset.mem_univ _)
  simpa only [BlockAlignedRun.IsFull, hcard] using hc

/-- The same conclusion stated directly for a complete overlap path, as
needed for a root component of the forest surgery. -/
theorem complete_aligned_zero_two_full {k : ℕ} (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hc : ∀ u : PermutationVertex k, u ∈ p.vertices)
    (s : Alphabet k)
    (hs : ∀ i : Fin (blockAlignedRuns hk p hp).length,
      entrySatellite (by omega) (blockAlignedRunAt hk p hp i).entry = s)
    (hd : ∀ i : Fin (blockAlignedRuns hk p hp).length,
      (blockAlignedRunAt hk p hp i).deficit = 0 ∨
      (blockAlignedRunAt hk p hp i).deficit = 2) :
    ∀ i : Fin (blockAlignedRuns hk p hp).length,
      (blockAlignedRunAt hk p hp i).IsFull := by
  let P : HamiltonianPath k := ⟨p.vertices, p.nodup, hc⟩
  exact common_satellite_zero_two_full hk P hp s hs hd

end NewResults
end SuperpermutationLowerBound
