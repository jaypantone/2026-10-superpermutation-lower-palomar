module

public import LowerBounds.SSound
public import SuperpermutationLowerBound.Refinement.ChainPacking

@[expose] public section

/-!
The actual-segment bridge for the H20 finite certificates.
The map only erases the subtype proof on the existing one-based alphabet.
There is no model-realization assumption and no CP-to-window implication.
-/
namespace H20
open SuperpermutationLowerBound
open SuperpermutationLowerBound.PermutationVertex
open SuperpermutationLowerBound.Refinement
open SuperpermLowerBounds

/-- Erase alphabet membership proofs, preserving the literal letters. -/
def wordOfVertex {k : ℕ} (v : PermutationVertex k) : List ℕ :=
  v.1.map Subtype.val

def chainOfRuns {k : ℕ} (L : List (List (PermutationVertex k))) : List (List (List ℕ)) :=
  L.map (List.map wordOfVertex)

theorem wordOfVertex_perm {k : ℕ} (v : PermutationVertex k) :
    S.PermW k (wordOfVertex v) := by
  refine ⟨v.nodup.map Subtype.val_injective, ?_, ?_⟩
  · simpa [wordOfVertex] using v.length
  · intro a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_Icc.mp x.2
    · intro ha
      let x : Alphabet k := ⟨a, Finset.mem_Icc.mpr ha⟩
      have hx : x ∈ v.1 := v.2.mem_iff.mpr (by simp [alphabetWord])
      exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem wordOfVertex_link {k d : ℕ} (u v : PermutationVertex k)
    (h : overlapWeight (blockExit u) v = d) :
    S.WLink k d (wordOfVertex u) (wordOfVertex v) := by
  have hov := (overlapWeight_spec (blockExit u) v).2
  rw [h] at hov
  have hm := congrArg (List.map (Subtype.val : Alphabet k → ℕ)) hov
  simpa only [S.WLink, wordOfVertex, OverlapsAt, blockExit,
    inverseRotation_word_eq_rotate, List.map_drop, List.map_take, List.map_rotate] using hm

theorem rotationClass_eq_of_erased_rotation {k : ℕ} (hk : 1 ≤ k)
    (u v : PermutationVertex k) (h : wordOfVertex u ~r wordOfVertex v) :
    rotationClass u = rotationClass v := by
  obtain ⟨i, hi⟩ := h
  have he : (rotationPower i u).1 = v.1 := by
    apply List.map_injective_iff.mpr Subtype.val_injective
    simpa only [rotationPower_word hk, List.map_rotate, wordOfVertex] using hi
  have hv : rotationPower i u = v := PermutationVertex.ext he
  rw [← hv, rotationClass_rotationPower hk]

/-- Every actual light segment, including all its occupied classes, is a
chain in Halfar's word model. -/
theorem actualSegment_isWChain {k : ℕ} (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    S.IsWChain k (chainOfRuns s.runs) := by
  have hs := blockAlignedLightSegment_infix_runs hk p hp s
  have hspec := blockAlignedRuns_spec hk p hp
  have hmem : ∀ R ∈ s.runs, R ∈ blockAlignedRuns hk p hp :=
    fun R hR => hs.subset hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP w hw
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hP
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact wordOfVertex_perm v
  · intro P hP
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hP
    intro he
    exact hspec.2.1 ((List.map_eq_nil_iff.mp he) ▸ hmem R hR)
  · intro P hP
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hP
    simpa only [List.length_map, BlockAlignedRun.length] using
      blockAlignedRun_length_le hk p hp ⟨R, hmem R hR⟩
  · intro P hP
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hP
    rw [List.isChain_map]
    exact (hspec.2.2.1 R (hmem R hR)).imp (fun u v huv => wordOfVertex_link u v huv)
  · unfold chainOfRuns
    rw [List.isChain_map]
    apply (blockAlignedLightSegment_isChain hk p hp s).imp
    intro R T hRT hR hT
    have hR' : R ≠ [] := fun e => hR (by simp [e])
    have hT' : T ≠ [] := fun e => hT (by simp [e])
    rw [List.getLast_map, List.head_map]
    apply wordOfVertex_link
    simpa only [IsLightRunBoundary, runBoundaryWeight,
      List.getLast?_eq_some_getLast hR', List.head?_eq_some_head hT'] using hRT
  · unfold chainOfRuns
    rw [← List.map_flatten, List.pairwise_map]
    have hclasses := blockAlignedBlockEntries_pairwiseDistinct hk p hp
    rw [← hspec.1] at hclasses
    exact (hclasses.sublist (List.Sublist.flatten hs.sublist)).imp
      (fun {u v} huv hrot => huv (rotationClass_eq_of_erased_rotation (by omega) u v hrot))

@[simp] theorem wdef_chainOfRuns {k : ℕ} (L : List (List (PermutationVertex k))) :
    S.wdef k (chainOfRuns L) = L.map (fun R => k - 1 - R.length) := by
  simp [S.wdef, chainOfRuns, List.map_map, Function.comp_def]

/-- The checked window inequality holds on every literal run factor of
an actual light segment. Free endpoints are retained. -/
theorem actualSegment_factor_window {k cn bn q : ℕ} (hk : 7 ≤ k)
    (H : S.WStatement k cn bn q)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) (i j : ℕ)
    (hw : ChainC.IsWindow ((s.deficitString.drop i).take j)) :
    ChainC.WindowBound k cn bn q ((s.deficitString.drop i).take j) := by
  let L := chainOfRuns s.runs
  have hL : S.IsWChain k L := actualSegment_isWChain hk p hp s
  have hin : ((L.drop i).take j) <:+: L := by
    refine ⟨L.take i, (L.drop i).drop j, ?_⟩
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have he : S.wdef k ((L.drop i).take j) = ((s.deficitString.drop i).take j) := by
    simp [L, S.wdef, chainOfRuns, BlockAlignedLightSegment.deficitString,
      List.map_map, Function.comp_def]
  have hh := H _ (hL.infix hin) (he.symm ▸ hw)
  simpa only [he] using hh

end H20
