module

public import SuperpermutationLowerBound.Refinement.GeometryBasic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
Coordinates for literal permutation words. The accepted alphabet is one-based;
the return calculations use zero-based labels. An equivalence from `Fin k` to
the accepted alphabet connects the two without changing either convention.
-/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

/-- A literal word obtained by listing an arbitrary coordinate equivalence. -/
noncomputable def coordinateVertex (e : Fin k ≃ Alphabet k) : PermutationVertex k :=
  ⟨List.ofFn e, by
    classical
    apply (List.perm_ext_iff_of_nodup ?_ (Finset.nodup_toList _)).2
    · intro x
      simp only [List.mem_ofFn, alphabetWord, Finset.mem_toList, Finset.mem_univ,
        iff_true]
      exact e.surjective x
    · exact List.nodup_ofFn.mpr e.injective⟩

@[simp] theorem coordinateVertex_word (e : Fin k ≃ Alphabet k) :
    (coordinateVertex e).1 = List.ofFn e := rfl

@[simp] theorem coordinateVertex_get (e : Fin k ≃ Alphabet k) (i : Fin k) :
    (coordinateVertex e).1[i.1]'(by simp) = e i := by
  simp

/-- The coordinates determined by any actual literal entry word. -/
noncomputable def vertexCoordinates (u : PermutationVertex k) : Fin k ≃ Alphabet k :=
  Equiv.ofBijective (fun i => u.1[i.1]'(by simpa [u.length] using i.2)) (by
    constructor
    · intro i j hij
      exact Fin.ext (u.nodup.getElem_inj_iff.mp hij)
    · intro x
      have hx : x ∈ u.1 := u.perm_alphabet.mem_iff.mpr (by simp [alphabetWord])
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
      exact ⟨⟨i.1, by simpa [u.length] using i.2⟩, hi⟩)

@[simp] theorem vertexCoordinates_apply (u : PermutationVertex k) (i : Fin k) :
    vertexCoordinates u i = u.1[i.1]'(by simpa [u.length] using i.2) := rfl

@[simp] theorem coordinateVertex_vertexCoordinates (u : PermutationVertex k) :
    coordinateVertex (vertexCoordinates u) = u := by
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [u.length]
  · intro i hi hj
    simp

@[simp] theorem vertexCoordinates_coordinateVertex (e : Fin k ≃ Alphabet k) :
    vertexCoordinates (coordinateVertex e) = e := by
  ext i
  simp

theorem coordinateVertex_injective : Function.Injective
    (coordinateVertex : (Fin k ≃ Alphabet k) → PermutationVertex k) := by
  intro e f hef
  have := congrArg vertexCoordinates hef
  simpa using this

/-- Relabel a literal word by a permutation of the actual alphabet. -/
noncomputable def relabelVertex (σ : Equiv.Perm (Alphabet k))
    (u : PermutationVertex k) : PermutationVertex k :=
  coordinateVertex ((vertexCoordinates u).trans σ)

@[simp] theorem relabelVertex_word (σ : Equiv.Perm (Alphabet k))
    (u : PermutationVertex k) :
    (relabelVertex σ u).1 = u.1.map σ := by
  rw [relabelVertex, coordinateVertex_word]
  have h : List.ofFn (vertexCoordinates u) = u.1 :=
    congrArg Subtype.val (coordinateVertex_vertexCoordinates u)
  change List.ofFn (fun i => σ (vertexCoordinates u i)) = u.1.map σ
  exact (List.map_ofFn (g := σ) (f := vertexCoordinates u)).symm.trans
    (congrArg (List.map σ) h)

@[simp] theorem relabelVertex_one (u : PermutationVertex k) :
    relabelVertex 1 u = u := by
  apply PermutationVertex.ext
  simp

theorem relabelVertex_mul (σ τ : Equiv.Perm (Alphabet k)) (u : PermutationVertex k) :
    relabelVertex (σ * τ) u = relabelVertex σ (relabelVertex τ u) := by
  apply PermutationVertex.ext
  simp [List.map_map]

theorem relabelVertex_injective (σ : Equiv.Perm (Alphabet k)) :
    Function.Injective (relabelVertex σ) := by
  intro u v h
  have := congrArg (relabelVertex σ⁻¹) h
  simpa [← relabelVertex_mul] using this

theorem relabelVertex_rotationPower (hk : 1 ≤ k)
    (σ : Equiv.Perm (Alphabet k)) (i : ℕ) (u : PermutationVertex k) :
    relabelVertex σ (rotationPower i u) = rotationPower i (relabelVertex σ u) := by
  apply PermutationVertex.ext
  simp only [relabelVertex_word, rotationPower_word hk, List.map_rotate]

@[simp] theorem relabelVertex_satellite (hk : 1 ≤ k)
    (σ : Equiv.Perm (Alphabet k)) (u : PermutationVertex k) :
    entrySatellite hk (relabelVertex σ u) = σ (entrySatellite hk u) := by
  unfold entrySatellite
  simp only [relabelVertex_word, List.getLast_map]

theorem relabelVertex_runMapPower (hk : 2 ≤ k)
    (σ : Equiv.Perm (Alphabet k)) (i : ℕ) (u : PermutationVertex k) :
    relabelVertex σ (runMapPower (by omega) i u) =
      runMapPower (by omega) i (relabelVertex σ u) := by
  apply PermutationVertex.ext
  simp only [relabelVertex_word, runMapPower_word hk, List.map_append,
    List.map_rotate, List.map_dropLast, List.map_cons, List.map_nil,
    relabelVertex_satellite]

theorem relabelVertex_fullRunMapPower (hk : 3 ≤ k)
    (σ : Equiv.Perm (Alphabet k)) (i : ℕ) (u : PermutationVertex k) :
    relabelVertex σ (fullRunMapPower hk i u) =
      fullRunMapPower hk i (relabelVertex σ u) := by
  apply PermutationVertex.ext
  simp only [relabelVertex_word, fullRunMapPower_word hk, List.map_append,
    List.map_rotate, List.map_take, List.map_drop]

/-- Relabeling preserves equality of rotation classes in both directions. -/
theorem relabelVertex_rotationClass_eq_iff (hk : 1 ≤ k)
    (σ : Equiv.Perm (Alphabet k)) (u v : PermutationVertex k) :
    rotationClass (relabelVertex σ u) = rotationClass (relabelVertex σ v) ↔
      rotationClass u = rotationClass v := by
  simp only [rotationClass_eq_iff_mem hk, mem_rotationClass_iff]
  constructor
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, relabelVertex_injective σ ?_⟩
    rw [relabelVertex_rotationPower hk]
    exact heq
  · rintro ⟨i, hi, heq⟩
    refine ⟨i, hi, ?_⟩
    rw [← relabelVertex_rotationPower hk, heq]

end SuperpermutationLowerBound.Refinement
