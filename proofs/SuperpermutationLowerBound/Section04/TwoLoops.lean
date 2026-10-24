module

public import SuperpermutationLowerBound.Section03.ReducedPaths
public import Mathlib.Data.List.Cycle

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 4 through Lemma `twoloop`: the run map and the cyclic
satellite/core geometry.  A core is represented by Mathlib's genuine cyclic
quotient `List.Cycle`, never by a preferred linear representative. -/

open PermutationVertex

variable {k : ℕ}

/-- A cyclic word over the original alphabet.  Section 4 cores have length
`k - 1` and omit their satellite. -/
abbrev CyclicCore (k : ℕ) := Cycle (Alphabet k)

private theorem vertex_word_nonempty (hk : 1 ≤ k) (u : PermutationVertex k) :
    u.1 ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [u.length] at hlength
  omega

/-- The last letter singled out by a block entry. -/
def entrySatellite (hk : 1 ≤ k) (u : PermutationVertex k) : Alphabet k :=
  u.1.getLast (vertex_word_nonempty hk u)

/-- The genuinely cyclic core obtained by deleting the last (satellite)
letter of a block entry. -/
def entryCore (u : PermutationVertex k) : CyclicCore k :=
  (u.1.dropLast : Cycle (Alphabet k))

/-- Delete a specified satellite from a representative and forget the choice
of linear start point.  Invariance on rotation classes is proved below. -/
def deleteSatellite (u : PermutationVertex k) (s : Alphabet k) : CyclicCore k :=
  (u.1.erase s : Cycle (Alphabet k))

private theorem alphabet_mem_vertex (u : PermutationVertex k) (s : Alphabet k) :
    s ∈ u.1 := by
  have hs : s ∈ alphabetWord k := by
    simp [alphabetWord]
  exact (u.perm_alphabet.mem_iff).mpr hs

private theorem satellite_not_mem_dropLast (hk : 1 ≤ k)
    (u : PermutationVertex k) : entrySatellite hk u ∉ u.1.dropLast := by
  intro hmem
  have hlast : entrySatellite hk u ∈ [entrySatellite hk u] := by simp
  have hnodup := u.nodup
  rw [← List.dropLast_append_getLast (vertex_word_nonempty hk u)] at hnodup
  have hdisjoint := (List.nodup_append.mp hnodup).2.2
  exact (hdisjoint _ hmem _ (by simpa [entrySatellite] using hlast)) rfl

/-- The entry word is its linearized core followed by its satellite. -/
theorem entry_dropLast_append_satellite (hk : 1 ≤ k)
    (u : PermutationVertex k) :
    u.1.dropLast ++ [entrySatellite hk u] = u.1 := by
  exact List.dropLast_append_getLast
    (vertex_word_nonempty hk u)

/-- Deleting the distinguished last letter realizes the cyclic core. -/
theorem deleteSatellite_entrySatellite (hk : 1 ≤ k)
    (u : PermutationVertex k) :
    deleteSatellite u (entrySatellite hk u) = entryCore u := by
  rw [deleteSatellite, entryCore, ← entry_dropLast_append_satellite hk u]
  rw [List.erase_append_right _ (satellite_not_mem_dropLast hk u)]
  simp

private theorem erase_rotation_one_cycle {α : Type*} [BEq α] [LawfulBEq α]
    (l : List α) (s : α) (hnodup : l.Nodup) :
    ((l.rotate 1).erase s : Cycle α) = (l.erase s : Cycle α) := by
  rcases l with _ | ⟨a, rest⟩
  · simp
  · have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have haNotRest : a ∉ rest := (List.nodup_cons.mp hnodup).1
    by_cases hsa : s = a
    · subst s
      rw [List.erase_cons_head]
      simp only [List.rotate_cons_succ, List.rotate_zero]
      rw [List.erase_append_right _ haNotRest]
      simp
    · simp only [List.rotate_cons_succ, List.rotate_zero]
      by_cases hsrest : s ∈ rest
      · rw [List.erase_cons_tail (by simpa using Ne.symm hsa)]
        rw [List.erase_append_left [a] hsrest]
        exact (Cycle.coe_cons_eq_coe_append (rest.erase s) a).symm
      · have hsall : s ∉ a :: rest := by simp [hsa, hsrest]
        have hsrot : s ∉ rest ++ [a] := by simp [hsa, hsrest]
        rw [List.erase_of_not_mem hsall, List.erase_of_not_mem hsrot]
        exact (Cycle.coe_cons_eq_coe_append rest a).symm

/-- Deleting a specified satellite is invariant under changing the linear
representative by a rotation. -/
theorem deleteSatellite_rotationPower (hk : 1 ≤ k) (i : ℕ)
    (u : PermutationVertex k) (s : Alphabet k) :
    deleteSatellite (rotationPower i u) s = deleteSatellite u s := by
  induction i generalizing u with
  | zero => rfl
  | succ i ih =>
      rw [show i + 1 = Nat.succ i by omega, rotationPower_succ]
      calc
        deleteSatellite (rotationPower i (rotation u)) s =
            deleteSatellite (rotation u) s := ih (rotation u)
        _ = deleteSatellite u s := by
          rw [deleteSatellite, deleteSatellite, rotation_word_eq_rotate hk]
          exact erase_rotation_one_cycle u.1 s u.nodup

/-- Consequently, deletion is well-defined on rotation classes. -/
theorem deleteSatellite_eq_of_same_class (hk : 1 ≤ k)
    {u v : PermutationVertex k} (hclass : rotationClass u = rotationClass v)
    (s : Alphabet k) :
    deleteSatellite u s = deleteSatellite v s := by
  have hv : v ∈ rotationClass u :=
    (rotationClass_eq_iff_mem hk u v).mp hclass
  obtain ⟨i, _hi, hpow⟩ := (mem_rotationClass_iff u v).mp hv
  rw [← hpow, deleteSatellite_rotationPower hk]

/-- The slot of a specified satellite in a rotation class: the cyclic
predecessor of the satellite. -/
def rotationClassSlot (u : PermutationVertex k) (s : Alphabet k) : Alphabet k :=
  u.1.prev s (alphabet_mem_vertex u s)

/-- Slot orientation is invariant under rotating a representative. -/
theorem rotationClassSlot_rotationPower (hk : 1 ≤ k) (i : ℕ)
    (u : PermutationVertex k) (s : Alphabet k) :
    rotationClassSlot (rotationPower i u) s = rotationClassSlot u s := by
  have hrot : u.1 ~r (rotationPower i u).1 := by
    refine ⟨i, ?_⟩
    exact (rotationPower_word hk i u).symm
  symm
  exact List.isRotated_prev_eq hrot u.nodup (alphabet_mem_vertex u s)

/-- The slot accessor is therefore well-defined on a rotation class. -/
theorem rotationClassSlot_eq_of_same_class (hk : 1 ≤ k)
    {u v : PermutationVertex k} (hclass : rotationClass u = rotationClass v)
    (s : Alphabet k) :
    rotationClassSlot u s = rotationClassSlot v s := by
  have hv : v ∈ rotationClass u :=
    (rotationClass_eq_iff_mem hk u v).mp hclass
  obtain ⟨i, _hi, hpow⟩ := (mem_rotationClass_iff u v).mp hv
  rw [← hpow, rotationClassSlot_rotationPower hk]

/-- The run map `τ₂`: rotate the first `k-1` letters left once and fix the
last letter. -/
def runMap (hk : 1 ≤ k) (u : PermutationVertex k) : PermutationVertex k :=
  ⟨u.1.dropLast.rotate 1 ++ [entrySatellite hk u], by
    exact ((List.rotate_perm _ _).append_right _).trans
      ((List.Perm.of_eq (entry_dropLast_append_satellite hk u)).trans u.2)⟩

/-- The inverse run map: rotate the first `k-1` letters right once and fix the
last letter. -/
def runMapInverse (hk : 2 ≤ k) (u : PermutationVertex k) : PermutationVertex k :=
  ⟨u.1.dropLast.rotate (k - 2) ++ [entrySatellite (by omega) u], by
    exact ((List.rotate_perm _ _).append_right _).trans
      ((List.Perm.of_eq
        (entry_dropLast_append_satellite (by omega) u)).trans u.2)⟩

/-- The literal frozen word formula
`x₁⋯xₙs ↦ x₂⋯xₙx₁s`. -/
@[simp]
theorem runMap_word (hk : 1 ≤ k) (u : PermutationVertex k) :
    (runMap hk u).1 = u.1.dropLast.rotate 1 ++ [entrySatellite hk u] := rfl

/-- The literal inverse word formula
`x₁⋯xₙs ↦ xₙx₁⋯xₙ₋₁s`. -/
@[simp]
theorem runMapInverse_word (hk : 2 ≤ k) (u : PermutationVertex k) :
    (runMapInverse hk u).1 =
      u.1.dropLast.rotate (k - 2) ++ [entrySatellite (by omega) u] := rfl

/-- Iterated notation for `τ₂`. -/
def runMapPower (hk : 1 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    PermutationVertex k :=
  ((runMap hk)^[i]) u

/-- The explicit frozen iterate formula: `τ₂^i` rotates the core by `i` and
leaves the satellite fixed. -/
theorem runMapPower_word (hk : 2 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    (runMapPower (by omega) i u).1 =
      u.1.dropLast.rotate i ++ [entrySatellite (by omega) u] := by
  induction i with
  | zero =>
      simpa [runMapPower] using (entry_dropLast_append_satellite (by omega) u).symm
  | succ i ih =>
      rw [runMapPower, Function.iterate_succ_apply']
      change (runMap (by omega) (runMapPower (by omega) i u)).1 = _
      rw [runMap_word, ih]
      have hsatellite :
          entrySatellite (by omega) (runMapPower (by omega) i u) =
            entrySatellite (by omega) u := by
        have hlast : (runMapPower (by omega) i u).1.getLast? =
            some (entrySatellite (by omega) u) := by
          calc
            (runMapPower (by omega) i u).1.getLast? =
                (u.1.dropLast.rotate i ++
                  [entrySatellite (by omega) u]).getLast? :=
              congrArg List.getLast? ih
            _ = some (entrySatellite (by omega) u) := by simp
        simpa [entrySatellite] using
          (List.getLast_of_getLast?_eq_some hlast)
      rw [hsatellite]
      simpa [List.rotate_rotate, Nat.succ_eq_add_one]

/-- `τ₂^i` fixes the satellite. -/
theorem runMapPower_satellite (hk : 2 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    entrySatellite (by omega) (runMapPower (by omega) i u) =
      entrySatellite (by omega) u := by
  have hlast : (runMapPower (by omega) i u).1.getLast? =
      some (entrySatellite (by omega) u) := by
    calc
      (runMapPower (by omega) i u).1.getLast? =
          (u.1.dropLast.rotate i ++
            [entrySatellite (by omega) u]).getLast? :=
        congrArg List.getLast? (runMapPower_word hk i u)
      _ = some (entrySatellite (by omega) u) := by simp
  simpa [entrySatellite] using (List.getLast_of_getLast?_eq_some hlast)

/-- One application of `τ₂` fixes the satellite. -/
@[simp]
theorem runMap_satellite (hk : 2 ≤ k) (u : PermutationVertex k) :
    entrySatellite (by omega) (runMap (by omega) u) =
      entrySatellite (by omega) u := by
  simpa [runMapPower, Function.iterate_one] using runMapPower_satellite hk 1 u

/-- `τ₂^i` preserves the cyclic core. -/
theorem runMapPower_core (hk : 2 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    entryCore (runMapPower (by omega) i u) = entryCore u := by
  rw [entryCore, entryCore, runMapPower_word hk]
  simp only [List.dropLast_concat]
  rw [Cycle.coe_eq_coe]
  exact List.IsRotated.forall _ _

/-- The two displayed maps are mutual inverses in the standing range. -/
@[simp]
theorem runMapInverse_runMap (hk : 2 ≤ k) (u : PermutationVertex k) :
    runMapInverse hk (runMap (by omega) u) = u := by
  apply PermutationVertex.ext
  rw [runMapInverse_word, runMap_word]
  simp only [List.dropLast_concat]
  rw [runMap_satellite hk]
  rw [List.rotate_rotate]
  have hcoreLength : u.1.dropLast.length = k - 1 := by
    simp [u.length]
  calc
    u.1.dropLast.rotate (1 + (k - 2)) ++ [entrySatellite (by omega) u] =
        u.1.dropLast.rotate (k - 1) ++ [entrySatellite (by omega) u] := by
      congr 3 <;> omega
    _ = u.1.dropLast ++ [entrySatellite (by omega) u] := by
      rw [← hcoreLength, List.rotate_length]
    _ = u.1 := entry_dropLast_append_satellite (by omega) u

/-- The two displayed maps are mutual inverses in the standing range. -/
@[simp]
theorem runMap_runMapInverse (hk : 2 ≤ k) (u : PermutationVertex k) :
    runMap (by omega) (runMapInverse hk u) = u := by
  apply PermutationVertex.ext
  rw [runMap_word, runMapInverse_word]
  simp only [List.dropLast_concat]
  change (u.1.dropLast.rotate (k - 2)).rotate 1 ++
      [entrySatellite (by omega) (runMapInverse hk u)] = u.1
  have hsatellite : entrySatellite (by omega) (runMapInverse hk u) =
      entrySatellite (by omega) u := by
    have hlast := congrArg List.getLast? (runMapInverse_word hk u)
    simpa [entrySatellite] using hlast
  rw [hsatellite]
  rw [List.rotate_rotate]
  have hcoreLength : u.1.dropLast.length = k - 1 := by
    simp [u.length]
  calc
    u.1.dropLast.rotate ((k - 2) + 1) ++ [entrySatellite (by omega) u] =
        u.1.dropLast.rotate (k - 1) ++ [entrySatellite (by omega) u] := by
      congr 3 <;> omega
    _ = u.1.dropLast ++ [entrySatellite (by omega) u] := by
      rw [← hcoreLength, List.rotate_length]
    _ = u.1 := entry_dropLast_append_satellite (by omega) u

/-- The double-rotation successor of a block exit is the ordinary rotation of
the block entry. -/
theorem doubleRotation_blockExit (hk : 3 ≤ k) (u : PermutationVertex k) :
    doubleRotation (blockExit u) = rotation u := by
  change doubleRotation (inverseRotation u) = rotation u
  apply PermutationVertex.ext
  rw [doubleRotation_word_eq_rotate (by omega), inverseRotation_word_eq_rotate,
    rotation_word_eq_rotate (by omega), List.rotate_rotate]
  have hlength : u.1.length = k := u.length
  have hrotateLength : u.1.rotate k = u.1 := by
    calc
      u.1.rotate k = u.1.rotate u.1.length := congrArg u.1.rotate hlength.symm
      _ = u.1 := List.rotate_length _
  calc
    u.1.rotate ((k - 1) + 2) = u.1.rotate (k + 1) := by
      rw [show (k - 1) + 2 = k + 1 by omega]
    _ = (u.1.rotate k).rotate 1 := by rw [List.rotate_rotate]
    _ = u.1.rotate 1 := by rw [hrotateLength]

/-- The other weight-two successor of a block exit is exactly `τ₂`. -/
theorem door_blockExit (hk : 3 ≤ k) (u : PermutationVertex k) :
    door (blockExit u) = runMap (by omega) u := by
  let core := u.1.dropLast
  let s := entrySatellite (by omega : 1 ≤ k) u
  have hcoreLength : core.length = k - 1 := by simp [core, u.length]
  have hcore : core ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [hcoreLength] at this
    omega
  obtain ⟨x, rest, hcoreEq⟩ := List.exists_cons_of_ne_nil hcore
  have hu : u.1 = core ++ [s] := (entry_dropLast_append_satellite (by omega) u).symm
  have hblock : (blockExit u).1 = s :: core := by
    change u.1.drop (k - 1) ++ u.1.take (k - 1) = s :: core
    rw [hu, ← hcoreLength]
    simp
  apply PermutationVertex.ext
  rw [door_word, hblock, runMap_word]
  change (s :: core).drop 2 ++ ((s :: core).take 2).reverse =
    core.rotate 1 ++ [s]
  rw [hcoreEq]
  simp

/-- Frozen Lemma `tau2`, successor classification: among genuine successors,
the exit of a block has exactly the ordinary rotation and `τ₂` at weight two. -/
theorem blockExit_weight_two_successors (hk : 3 ≤ k)
    (u v : PermutationVertex k) (hne : blockExit u ≠ v) :
    overlapWeight (blockExit u) v = 2 ↔
      v = rotation u ∨ v = runMap (by omega) u := by
  rw [weight_two_successors (blockExit u) v hk hne,
    doubleRotation_blockExit hk, door_blockExit hk]

/-- The ordinary-rotation successor remains in the entry block. -/
theorem rotation_mem_entryClass (hk : 1 ≤ k) (u : PermutationVertex k) :
    rotation u ∈ rotationClass u := by
  simpa [rotationPower, Function.iterate_one] using
    rotationPower_mem_rotationClass hk 1 u

/-- `τ₂` has exact order `k-1` on every block entry, not merely an
`(k-1)`st-iterate identity. -/
theorem runMap_order_exact (hk : 3 ≤ k) (u : PermutationVertex k) :
    runMapPower (by omega) (k - 1) u = u ∧
      ∀ i, 0 < i → i < k - 1 → runMapPower (by omega) i u ≠ u := by
  have hcoreLength : u.1.dropLast.length = k - 1 := by simp [u.length]
  have hcoreNonempty : u.1.dropLast ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    rw [hcoreLength] at this
    simp at this
    omega
  constructor
  · apply PermutationVertex.ext
    rw [runMapPower_word (by omega)]
    rw [← hcoreLength, List.rotate_length]
    exact entry_dropLast_append_satellite (by omega) u
  · intro i hi hilt heq
    have hword := congrArg Subtype.val heq
    rw [runMapPower_word (by omega)] at hword
    have hcoreEq : u.1.dropLast.rotate i = u.1.dropLast := by
      have := congrArg (fun l => l.dropLast) hword
      simpa using this
    have hcoreNodup : u.1.dropLast.Nodup := by
      have hnodup := u.nodup
      rw [← entry_dropLast_append_satellite (by omega) u] at hnodup
      exact (List.nodup_append.mp hnodup).1
    have hmod := (hcoreNodup.rotate_eq_self_iff).mp hcoreEq
    rcases hmod with hmod | hnil
    · rw [hcoreLength, Nat.mod_eq_of_lt hilt] at hmod
      omega
    · exact hcoreNonempty hnil

private theorem eq_of_isRotated_of_head?_eq {α : Type*}
    {l m : List α} (hnodup : l.Nodup) (hl : l ≠ [])
    (hrot : l ~r m) (hhead : l.head? = m.head?) : l = m := by
  obtain ⟨r, hr⟩ := hrot
  let q := r % l.length
  have hlengthPos : 0 < l.length := List.length_pos_of_ne_nil hl
  have hq : q < l.length := Nat.mod_lt _ hlengthPos
  have hrq : l.rotate q = m := by
    calc
      l.rotate q = l.rotate r := by
        exact List.rotate_mod l r
      _ = m := hr
  have hheadq : l.head? = (l.rotate q).head? :=
    hhead.trans (congrArg List.head? hrq).symm
  have hleft : l.head? = some l[0] := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlengthPos]
  have hright : (l.rotate q).head? = some l[q] := by
    rw [List.head?_rotate hq, List.getElem?_eq_getElem hq]
  rw [hleft, hright] at hheadq
  have helem : l[0] = l[q] := Option.some.inj hheadq
  have hqzero : q = 0 := by
    symm
    exact hnodup.getElem_inj_iff.mp helem
  calc
    l = l.rotate 0 := (List.rotate_zero l).symm
    _ = l.rotate q := by rw [hqzero]
    _ = m := hrq

private theorem eq_of_same_class_same_satellite (hk : 1 ≤ k)
    {u v : PermutationVertex k}
    (hclass : rotationClass u = rotationClass v)
    (hsatellite : entrySatellite hk u = entrySatellite hk v) : u = v := by
  have hv : v ∈ rotationClass u :=
    (rotationClass_eq_iff_mem hk u v).mp hclass
  obtain ⟨i, _hi, hpow⟩ := (mem_rotationClass_iff u v).mp hv
  have hrot : u.1 ~r v.1 := by
    refine ⟨i, ?_⟩
    calc
      u.1.rotate i = (rotationPower i u).1 :=
        (rotationPower_word hk i u).symm
      _ = v.1 := congrArg Subtype.val hpow
  have hlast : u.1.getLast? = v.1.getLast? := by
    rw [List.getLast?_eq_some_getLast (vertex_word_nonempty hk u),
      List.getLast?_eq_some_getLast (vertex_word_nonempty hk v)]
    exact congrArg some hsatellite
  have hreverse : u.1.reverse = v.1.reverse := by
    apply eq_of_isRotated_of_head?_eq
      (List.nodup_reverse.mpr u.nodup)
      (by simpa using vertex_word_nonempty hk u)
      hrot.reverse
    simpa using hlast
  exact PermutationVertex.ext (List.reverse_injective hreverse)

/-- The `k-1` rotation classes in one run-map orbit are pairwise distinct. -/
theorem runMap_rotationClasses_injective (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    Set.InjOn
      (fun i : ℕ => rotationClass (runMapPower (by omega) i u))
      (Set.Iio (k - 1)) := by
  intro i hi j hj hclass
  have hsatellite :
      entrySatellite (by omega) (runMapPower (by omega) i u) =
        entrySatellite (by omega) (runMapPower (by omega) j u) :=
    (runMapPower_satellite (by omega) i u).trans
      (runMapPower_satellite (by omega) j u).symm
  have hentries : runMapPower (by omega) i u =
      runMapPower (by omega) j u :=
    eq_of_same_class_same_satellite (by omega) hclass hsatellite
  have hword := congrArg Subtype.val hentries
  rw [runMapPower_word (by omega), runMapPower_word (by omega)] at hword
  have hcoreEq : u.1.dropLast.rotate i = u.1.dropLast.rotate j := by
    have := congrArg List.dropLast hword
    simpa using this
  have hcoreNodup : u.1.dropLast.Nodup := by
    have hnodup := u.nodup
    rw [← entry_dropLast_append_satellite (by omega) u] at hnodup
    exact (List.nodup_append.mp hnodup).1
  have hcoreNonempty : u.1.dropLast ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp [u.length] at hlength
    omega
  have hmod := hcoreNodup.rotate_congr hcoreNonempty i j hcoreEq
  have hcoreLength : u.1.dropLast.length = k - 1 := by simp [u.length]
  rw [hcoreLength, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

/-- The run-map successor leaves the entry rotation class. -/
theorem runMap_not_mem_entryClass (hk : 3 ≤ k) (u : PermutationVertex k) :
    runMap (by omega) u ∉ rotationClass u := by
  intro hmem
  have hclasses : rotationClass (runMap (by omega) u) = rotationClass u :=
    rotationClass_eq_of_mem (by omega) hmem
  have hinj := runMap_rotationClasses_injective hk u
  have hone : (1 : ℕ) < k - 1 := by omega
  have hzero : (0 : ℕ) < k - 1 := by omega
  have hbad : (1 : ℕ) = 0 := hinj hone hzero (by
    simpa [runMapPower, Function.iterate_one] using hclasses)
  omega

/-- The two classified genuine weight-two successors of a block exit are
different.  Thus the disjunction in `blockExit_weight_two_successors` really
lists two successors, rather than one successor twice. -/
theorem blockExit_weight_two_successors_distinct (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    rotation u ≠ runMap (by omega) u := by
  intro hsame
  apply runMap_not_mem_entryClass hk u
  rw [← hsame]
  exact rotation_mem_entryClass (by omega) u

/-- The semantic two-loop `L(s, γ)`: rotation classes whose unique
representative ending in `s` has cyclic core `γ`. -/
noncomputable def twoLoop (hk : 1 ≤ k) (s : Alphabet k) (γ : CyclicCore k) :
    Finset (Finset (PermutationVertex k)) := by
  classical
  exact (rotationBlocks k).filter fun B =>
    ∃ u : PermutationVertex k,
      rotationClass u = B ∧ entrySatellite hk u = s ∧ entryCore u = γ

/-- Membership in a two-loop is exactly the frozen satellite/core condition. -/
theorem mem_twoLoop (hk : 1 ≤ k) (s : Alphabet k) (γ : CyclicCore k)
    (B : Finset (PermutationVertex k)) :
    B ∈ twoLoop hk s γ ↔
      B ∈ rotationBlocks k ∧
        ∃ u : PermutationVertex k,
          rotationClass u = B ∧ entrySatellite hk u = s ∧ entryCore u = γ := by
  classical
  simp [twoLoop]

/-- The finite set of rotation classes in one `τ₂` orbit. -/
noncomputable def runMapOrbitClasses (hk : 1 ≤ k) (u : PermutationVertex k) :
    Finset (Finset (PermutationVertex k)) := by
  classical
  exact (Finset.range (k - 1)).image fun i =>
    rotationClass (runMapPower hk i u)

/-- Concrete membership in the displayed `τ₂` orbit. -/
theorem mem_runMapOrbitClasses (hk : 1 ≤ k) (u : PermutationVertex k)
    (B : Finset (PermutationVertex k)) :
    B ∈ runMapOrbitClasses hk u ↔
      ∃ i < k - 1, rotationClass (runMapPower hk i u) = B := by
  classical
  simp [runMapOrbitClasses]

/-- Frozen Lemma `twoloop`, exact set equality: the satellite/core two-loop
is the full `τ₂` orbit, not merely a superset of it. -/
theorem twoLoop_eq_runMapOrbitClasses (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    twoLoop (by omega) (entrySatellite (by omega) u) (entryCore u) =
      runMapOrbitClasses (by omega) u := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨_hBlock, v, hvB, hsatellite, hcore⟩ :=
      (mem_twoLoop (by omega) (entrySatellite (by omega) u)
        (entryCore u) B).mp hB
    have hcycle :
        (u.1.dropLast : Cycle (Alphabet k)) =
          (v.1.dropLast : Cycle (Alphabet k)) := hcore.symm
    obtain ⟨r, hr⟩ := (Cycle.coe_eq_coe.mp hcycle)
    let i := r % (k - 1)
    have hi : i < k - 1 := Nat.mod_lt _ (by omega)
    have hcoreLength : u.1.dropLast.length = k - 1 := by simp [u.length]
    have hrotate : u.1.dropLast.rotate i = v.1.dropLast := by
      dsimp [i]
      calc
        u.1.dropLast.rotate (r % (k - 1)) =
            u.1.dropLast.rotate (r % u.1.dropLast.length) := by
          rw [hcoreLength]
        _ = u.1.dropLast.rotate r := List.rotate_mod u.1.dropLast r
        _ = v.1.dropLast := hr
    have hentry : runMapPower (by omega) i u = v := by
      apply PermutationVertex.ext
      rw [runMapPower_word (by omega)]
      calc
        u.1.dropLast.rotate i ++ [entrySatellite (by omega) u] =
            v.1.dropLast ++ [entrySatellite (by omega) v] := by
          rw [hrotate, hsatellite]
        _ = v.1 := entry_dropLast_append_satellite (by omega) v
    apply (mem_runMapOrbitClasses (by omega) u B).mpr
    exact ⟨i, hi, by rw [hentry, hvB]⟩
  · intro hB
    obtain ⟨i, hi, hclass⟩ :=
      (mem_runMapOrbitClasses (by omega) u B).mp hB
    apply (mem_twoLoop (by omega) (entrySatellite (by omega) u)
      (entryCore u) B).mpr
    refine ⟨?_, runMapPower (by omega) i u, hclass, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨runMapPower (by omega) i u, Finset.mem_univ _, hclass⟩
    · exact runMapPower_satellite (by omega) i u
    · exact runMapPower_core (by omega) i u

/-- The run-map orbit contains exactly `k-1` rotation classes. -/
theorem runMapOrbitClasses_card (hk : 3 ≤ k) (u : PermutationVertex k) :
    (runMapOrbitClasses (by omega) u).card = k - 1 := by
  classical
  unfold runMapOrbitClasses
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_range (k - 1)
  · intro i hi j hj hij
    exact runMap_rotationClasses_injective hk u
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- A two-loop contains exactly `n = k-1` rotation classes. -/
theorem twoLoop_card (hk : 3 ≤ k) (u : PermutationVertex k) :
    (twoLoop (by omega) (entrySatellite (by omega) u) (entryCore u)).card =
      k - 1 := by
  rw [twoLoop_eq_runMapOrbitClasses hk, runMapOrbitClasses_card hk]

private theorem entry_core_nonempty (hk : 2 ≤ k) (u : PermutationVertex k) :
    u.1.dropLast ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [u.length] at hlength
  omega

private theorem prev_concat_eq_getLast {α : Type*} [BEq α] [LawfulBEq α]
    [DecidableEq α]
    (l : List α) (s : α) (hl : l ≠ []) (hs : s ∉ l) :
    (l ++ [s]).prev s (by simp) = l.getLast hl := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a tail ih =>
      cases tail with
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

/-- The predecessor label of slot `i`.  By definition slot `0` is after the
last core letter (`x₀ = xₙ`), while positive slot `i` is after `xᵢ`. -/
def coreSlotLetter (hk : 2 ≤ k) (u : PermutationVertex k)
    (i : Fin (k - 1)) : Alphabet k :=
  (u.1.dropLast.rotate i.1).getLast (by
    simpa using entry_core_nonempty hk u)

/-- The frozen convention `x₀ = xₙ`. -/
@[simp]
theorem coreSlotLetter_zero (hk : 2 ≤ k) (u : PermutationVertex k) :
    coreSlotLetter hk u ⟨0, by omega⟩ =
      u.1.dropLast.getLast (entry_core_nonempty hk u) := by
  simp [coreSlotLetter]

/-- For positive indices the frozen slot convention is literally the slot
after the correspondingly numbered core letter: slot `i+1` is after the
zero-based word entry `u[i]`. -/
theorem coreSlotLetter_succ (hk : 3 ≤ k) (u : PermutationVertex k)
    (i : ℕ) (hi : i + 1 < k - 1) :
    coreSlotLetter (by omega) u ⟨i + 1, hi⟩ =
      u.1.get ⟨i, by rw [u.length]; omega⟩ := by
  let core := u.1.dropLast
  have hcoreLength : core.length = k - 1 := by
    simp [core, u.length]
  have hlast : core.rotate (i + 1) ≠ [] := by
    simpa [core] using entry_core_nonempty (by omega) u
  rw [coreSlotLetter, List.getLast_eq_getElem hlast]
  rw [List.getElem_rotate]
  have hmod : (core.length - 1 + (i + 1)) % core.length = i := by
    rw [hcoreLength]
    have hkpos : 0 < k - 1 := by omega
    have hi' : i < k - 1 := by omega
    have hadd : k - 1 - 1 + (i + 1) = (k - 1) + i := by omega
    rw [hadd, Nat.add_mod_left, Nat.mod_eq_of_lt hi']
  simp only [List.length_rotate]
  have hcoreBound : i < core.length := by
    rw [hcoreLength]
    omega
  trans core.get ⟨i, hcoreBound⟩
  · apply congrArg core.get
    exact Fin.ext hmod
  · simpa [core] using
      (List.getElem_dropLast (xs := u.1) (i := i)
        hcoreBound)

private def coreSlotIndex (_hk : 2 ≤ k) (i : Fin (k - 1)) : ℕ :=
  if i.1 = 0 then k - 2 else i.1 - 1

private theorem coreSlotIndex_lt (hk : 2 ≤ k) (i : Fin (k - 1)) :
    coreSlotIndex hk i < k := by
  unfold coreSlotIndex
  split <;> omega

private theorem coreSlotIndex_injective (hk : 2 ≤ k) :
    Function.Injective (coreSlotIndex (k := k) hk) := by
  intro i j hij
  apply Fin.ext
  by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = 0
  · omega
  · simp [coreSlotIndex, hi, hj] at hij
    omega
  · simp [coreSlotIndex, hi, hj] at hij
    omega
  · simp [coreSlotIndex, hi, hj] at hij
    omega

private theorem coreSlotLetter_eq_get (hk : 3 ≤ k)
    (u : PermutationVertex k) (i : Fin (k - 1)) :
    coreSlotLetter (by omega) u i =
      u.1.get ⟨coreSlotIndex (by omega) i, by
        rw [u.length]
        exact coreSlotIndex_lt (by omega) i⟩ := by
  by_cases hi : i.1 = 0
  · have hiFin : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hiFin]
    rw [coreSlotLetter_zero]
    let core := u.1.dropLast
    have hcoreLength : core.length = k - 1 := by
      simp [core, u.length]
    have hcoreNonempty : core ≠ [] := entry_core_nonempty (by omega) u
    have hcoreLastBound : k - 2 < core.length := by
      rw [hcoreLength]
      omega
    calc
      core.getLast hcoreNonempty =
          core.get ⟨k - 2, by rw [hcoreLength]; omega⟩ := by
        rw [List.getLast_eq_getElem hcoreNonempty]
        congr 1
        rw [hcoreLength]
        omega
      _ = u.1.get ⟨k - 2, by rw [u.length]; omega⟩ := by
        simpa [core] using
          (List.getElem_dropLast (xs := u.1) (i := k - 2) hcoreLastBound)
      _ = u.1.get ⟨coreSlotIndex (by omega)
            (⟨0, by omega⟩ : Fin (k - 1)), by
          rw [u.length]
          exact coreSlotIndex_lt (by omega)
            (⟨0, by omega⟩ : Fin (k - 1))⟩ := by
        congr 1
  · let j := i.1 - 1
    have hjSucc : j + 1 = i.1 := by
      dsimp [j]
      omega
    have hjBound : j + 1 < k - 1 := by
      rw [hjSucc]
      exact i.2
    have hFin : (⟨j + 1, hjBound⟩ : Fin (k - 1)) = i :=
      Fin.ext hjSucc
    calc
      coreSlotLetter (by omega) u i =
          coreSlotLetter (by omega) u ⟨j + 1, hjBound⟩ := by rw [hFin]
      _ = u.1.get ⟨j, by rw [u.length]; omega⟩ :=
        coreSlotLetter_succ hk u j hjBound
      _ = u.1.get ⟨coreSlotIndex (by omega) i, by
          rw [u.length]
          exact coreSlotIndex_lt (by omega) i⟩ := by
        congr 1
        apply Fin.ext
        simp [coreSlotIndex, hi, j]

/-- The cyclic predecessor labels distinguish all `k-1` slots of a
two-loop. -/
theorem coreSlotLetter_injective (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    Function.Injective (coreSlotLetter (by omega) u) := by
  intro i j hij
  have hget : u.1.get ⟨coreSlotIndex (by omega) i, by
        rw [u.length]
        exact coreSlotIndex_lt (by omega) i⟩ =
      u.1.get ⟨coreSlotIndex (by omega) j, by
        rw [u.length]
        exact coreSlotIndex_lt (by omega) j⟩ := by
    rw [← coreSlotLetter_eq_get hk u i,
      ← coreSlotLetter_eq_get hk u j]
    exact hij
  have hfinIndex :
      (⟨coreSlotIndex (by omega) i, by
        rw [u.length]
        exact coreSlotIndex_lt (by omega) i⟩ : Fin u.1.length) =
      ⟨coreSlotIndex (by omega) j, by
        rw [u.length]
        exact coreSlotIndex_lt (by omega) j⟩ :=
    u.nodup.get_inj_iff.mp hget
  have hindex : coreSlotIndex (by omega) i = coreSlotIndex (by omega) j :=
    congrArg Fin.val hfinIndex
  exact coreSlotIndex_injective (by omega) hindex

/-- Frozen slot correspondence: `[τ₂^i(u)]` sits in the slot after the
`i`th cyclic core label, with slot zero using `x₀ = xₙ`. -/
theorem runMapPower_slot (hk : 3 ≤ k) (u : PermutationVertex k)
    (i : Fin (k - 1)) :
    rotationClassSlot (runMapPower (by omega) i.1 u)
        (entrySatellite (by omega) u) =
      coreSlotLetter (by omega) u i := by
  let core := u.1.dropLast
  let s := entrySatellite (by omega : 1 ≤ k) u
  have hcore : core.rotate i.1 ≠ [] := by
    simpa [core] using entry_core_nonempty (by omega) u
  have hs : s ∉ core.rotate i.1 := by
    have hs0 := satellite_not_mem_dropLast (by omega) u
    simpa [core, s] using hs0
  have hprev := prev_concat_eq_getLast (core.rotate i.1) s hcore hs
  have hword := runMapPower_word (by omega : 2 ≤ k) i.1 u
  simpa [rotationClassSlot, coreSlotLetter, core, s,
    hword] using hprev

/-- Along the canonical enumeration of a two-loop, the predecessor slot
determines the orbit index. -/
theorem runMapPower_slots_injective (hk : 3 ≤ k)
    (u : PermutationVertex k) :
    Function.Injective (fun i : Fin (k - 1) =>
      rotationClassSlot (runMapPower (by omega) i.1 u)
        (entrySatellite (by omega) u)) := by
  intro i j hij
  change rotationClassSlot (runMapPower (by omega) i.1 u)
      (entrySatellite (by omega) u) =
    rotationClassSlot (runMapPower (by omega) j.1 u)
      (entrySatellite (by omega) u) at hij
  rw [runMapPower_slot hk u i, runMapPower_slot hk u j] at hij
  exact coreSlotLetter_injective hk u hij

/-- Exact class/slot equivalence in the displayed `τ₂` enumeration of a
two-loop. -/
theorem runMapPower_rotationClass_eq_iff_slot_eq (hk : 3 ≤ k)
    (u : PermutationVertex k) (i j : Fin (k - 1)) :
    rotationClass (runMapPower (by omega) i.1 u) =
        rotationClass (runMapPower (by omega) j.1 u) ↔
      rotationClassSlot (runMapPower (by omega) i.1 u)
          (entrySatellite (by omega) u) =
        rotationClassSlot (runMapPower (by omega) j.1 u)
          (entrySatellite (by omega) u) := by
  constructor
  · intro hclass
    exact rotationClassSlot_eq_of_same_class (by omega) hclass _
  · intro hslot
    have hij := runMapPower_slots_injective hk u hslot
    rw [hij]

/-- Semantic class-determination direction: two classes in the same
two-loop having the same predecessor slot are equal. -/
theorem twoLoop_class_eq_of_slot_eq (hk : 3 ≤ k)
    (u a b : PermutationVertex k)
    (ha : rotationClass a ∈
      twoLoop (by omega) (entrySatellite (by omega) u) (entryCore u))
    (hb : rotationClass b ∈
      twoLoop (by omega) (entrySatellite (by omega) u) (entryCore u))
    (hslot : rotationClassSlot a (entrySatellite (by omega) u) =
      rotationClassSlot b (entrySatellite (by omega) u)) :
    rotationClass a = rotationClass b := by
  rw [twoLoop_eq_runMapOrbitClasses hk] at ha hb
  obtain ⟨i, hi, hia⟩ :=
    (mem_runMapOrbitClasses (by omega) u (rotationClass a)).mp ha
  obtain ⟨j, hj, hjb⟩ :=
    (mem_runMapOrbitClasses (by omega) u (rotationClass b)).mp hb
  let fi : Fin (k - 1) := ⟨i, hi⟩
  let fj : Fin (k - 1) := ⟨j, hj⟩
  have hslotOrbit :
      rotationClassSlot (runMapPower (by omega) fi.1 u)
          (entrySatellite (by omega) u) =
        rotationClassSlot (runMapPower (by omega) fj.1 u)
          (entrySatellite (by omega) u) := by
    calc
      rotationClassSlot (runMapPower (by omega) fi.1 u)
          (entrySatellite (by omega) u) =
          rotationClassSlot a (entrySatellite (by omega) u) :=
        rotationClassSlot_eq_of_same_class (by omega) (by simpa [fi] using hia) _
      _ = rotationClassSlot b (entrySatellite (by omega) u) := hslot
      _ = rotationClassSlot (runMapPower (by omega) fj.1 u)
          (entrySatellite (by omega) u) :=
        (rotationClassSlot_eq_of_same_class (by omega)
          (by simpa [fj] using hjb) _).symm
  have hfi : fi = fj := runMapPower_slots_injective hk u hslotOrbit
  calc
    rotationClass a = rotationClass (runMapPower (by omega) fi.1 u) := by
      simpa [fi] using hia.symm
    _ = rotationClass (runMapPower (by omega) fj.1 u) := by rw [hfi]
    _ = rotationClass b := by simpa [fj] using hjb

end SuperpermutationLowerBound
