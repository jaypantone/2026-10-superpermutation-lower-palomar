module

public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.Rotate
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace SuperpermutationLowerBound

/-! Words and permutation vertices over the literal one-based alphabet `{1, ..., k}`. -/

/-- A symbol in the one-based alphabet `{1, ..., k}`. -/
abbrev Alphabet (k : ℕ) := {a : ℕ // a ∈ Finset.Icc 1 k}

/-- A finite word over the one-based alphabet `{1, ..., k}`. -/
abbrev Word (k : ℕ) := List (Alphabet k)

/-- A duplicate-free complete listing of the one-based alphabet. -/
noncomputable def alphabetWord (k : ℕ) : Word k :=
  (Finset.univ : Finset (Alphabet k)).toList

/-- A permutation vertex is a word containing every one-based symbol exactly once. -/
def PermutationVertex (k : ℕ) := {w : Word k // w.Perm (alphabetWord k)}

/-- A finite enumeration of all permutation vertices. -/
noncomputable def allVertices (k : ℕ) : List (PermutationVertex k) :=
  (alphabetWord k).permutations.attach.map fun w =>
    ⟨w.1, List.mem_permutations.mp w.2⟩

noncomputable instance (k : ℕ) : Fintype (PermutationVertex k) := by
  classical
  apply Fintype.ofList (allVertices k)
  intro v
  unfold allVertices
  apply List.mem_map.mpr
  let w : {word // word ∈ (alphabetWord k).permutations} :=
    ⟨v.1, List.mem_permutations.mpr v.2⟩
  exact ⟨w, List.mem_attach _ _, Subtype.ext rfl⟩

namespace PermutationVertex

variable {k : ℕ}

instance : Coe (PermutationVertex k) (Word k) := ⟨Subtype.val⟩

@[ext]
theorem ext {u v : PermutationVertex k} (h : u.1 = v.1) : u = v := Subtype.ext h

theorem perm_alphabet (u : PermutationVertex k) : u.1.Perm (alphabetWord k) := u.2

theorem perm (u v : PermutationVertex k) : u.1.Perm v.1 := u.2.trans v.2.symm

theorem nodup (u : PermutationVertex k) : u.1.Nodup := by
  exact u.2.nodup_iff.mpr (Finset.nodup_toList _)

theorem length (u : PermutationVertex k) : u.1.length = k := by
  rw [u.2.length_eq]
  simp [alphabetWord, Alphabet]

/-- Cut after dropping `t` initial symbols and append an arrangement of that prefix. -/
def cutAppend (u : PermutationVertex k) (t : ℕ) (suffix : Word k)
    (hsuffix : suffix.Perm (u.1.take t)) : PermutationVertex k :=
  ⟨u.1.drop t ++ suffix, by
    calc
      (u.1.drop t ++ suffix).Perm (u.1.drop t ++ u.1.take t) := hsuffix.append_left _
      (u.1.drop t ++ u.1.take t).Perm (u.1.take t ++ u.1.drop t) :=
        List.perm_append_comm
      (u.1.take t ++ u.1.drop t).Perm u.1 := by rw [u.1.take_append_drop]
      u.1.Perm (alphabetWord k) := u.2⟩

/-- Left rotation `u₂ ... uₖ u₁`. -/
def rotation (u : PermutationVertex k) : PermutationVertex k :=
  cutAppend u 1 (u.1.take 1) (.refl _)

/-- Right rotation `uₖ u₁ ... uₖ₋₁`. -/
def inverseRotation (u : PermutationVertex k) : PermutationVertex k :=
  cutAppend u (k - 1) (u.1.take (k - 1)) (.refl _)

/-- Double left rotation `u₃ ... uₖ u₁ u₂`. -/
def doubleRotation (u : PermutationVertex k) : PermutationVertex k :=
  cutAppend u 2 (u.1.take 2) (.refl _)

/-- The Section 1 door map `u₃ ... uₖ u₂ u₁`. -/
def door (u : PermutationVertex k) : PermutationVertex k :=
  cutAppend u 2 (u.1.take 2).reverse (List.reverse_perm _)

@[simp] theorem rotation_word (u : PermutationVertex k) :
    (rotation u).1 = u.1.drop 1 ++ u.1.take 1 := rfl

@[simp] theorem inverseRotation_word (u : PermutationVertex k) :
    (inverseRotation u).1 = u.1.drop (k - 1) ++ u.1.take (k - 1) := rfl

@[simp] theorem doubleRotation_word (u : PermutationVertex k) :
    (doubleRotation u).1 = u.1.drop 2 ++ u.1.take 2 := rfl

@[simp] theorem door_word (u : PermutationVertex k) :
    (door u).1 = u.1.drop 2 ++ (u.1.take 2).reverse := rfl

theorem rotation_word_eq_rotate (hk : 1 ≤ k) (u : PermutationVertex k) :
    (rotation u).1 = u.1.rotate 1 := by
  symm
  apply List.rotate_eq_drop_append_take
  simpa [length] using hk

theorem inverseRotation_word_eq_rotate (u : PermutationVertex k) :
    (inverseRotation u).1 = u.1.rotate (k - 1) := by
  symm
  apply List.rotate_eq_drop_append_take
  rw [length]
  exact Nat.sub_le k 1

theorem doubleRotation_word_eq_rotate (hk : 2 ≤ k) (u : PermutationVertex k) :
    (doubleRotation u).1 = u.1.rotate 2 := by
  symm
  apply List.rotate_eq_drop_append_take
  simpa [length] using hk

@[simp]
theorem rotation_inverseRotation (hk : 1 ≤ k) (u : PermutationVertex k) :
    rotation (inverseRotation u) = u := by
  apply ext
  calc
    (rotation (inverseRotation u)).1 = (inverseRotation u).1.rotate 1 :=
      rotation_word_eq_rotate hk _
    _ = (u.1.rotate (k - 1)).rotate 1 := by rw [inverseRotation_word_eq_rotate]
    _ = u.1.rotate ((k - 1) + 1) := List.rotate_rotate _ _ _
    _ = u.1.rotate k := by
      congr 1
      omega
    _ = u.1.rotate u.1.length := congrArg u.1.rotate u.length.symm
    _ = u.1 := List.rotate_length _

@[simp]
theorem inverseRotation_rotation (hk : 1 ≤ k) (u : PermutationVertex k) :
    inverseRotation (rotation u) = u := by
  apply ext
  calc
    (inverseRotation (rotation u)).1 = (rotation u).1.rotate (k - 1) :=
      inverseRotation_word_eq_rotate _
    _ = (u.1.rotate 1).rotate (k - 1) := by rw [rotation_word_eq_rotate hk]
    _ = u.1.rotate (1 + (k - 1)) := List.rotate_rotate _ _ _
    _ = u.1.rotate k := by
      congr 1
      omega
    _ = u.1.rotate u.1.length := congrArg u.1.rotate u.length.symm
    _ = u.1 := List.rotate_length _

theorem rotation_injective (hk : 1 ≤ k) :
    Function.Injective (rotation : PermutationVertex k → PermutationVertex k) := by
  intro u v h
  have := congrArg inverseRotation h
  simpa [inverseRotation_rotation hk] using this

theorem rotation_rotation_eq_doubleRotation (hk : 2 ≤ k) (u : PermutationVertex k) :
    rotation (rotation u) = doubleRotation u := by
  apply ext
  calc
    (rotation (rotation u)).1 = (rotation u).1.rotate 1 :=
      rotation_word_eq_rotate (by omega) _
    _ = (u.1.rotate 1).rotate 1 := by rw [rotation_word_eq_rotate (by omega)]
    _ = u.1.rotate (1 + 1) := List.rotate_rotate _ _ _
    _ = (doubleRotation u).1 := (doubleRotation_word_eq_rotate hk _).symm

theorem rotation_ne_self (hk : 2 ≤ k) (u : PermutationVertex k) : rotation u ≠ u := by
  intro h
  have hword : u.1.rotate 1 = u.1 := by
    rw [← rotation_word_eq_rotate (by omega) u]
    exact congrArg Subtype.val h
  rcases (u.nodup.rotate_eq_self_iff.mp hword) with hmod | hnil
  · have hmodone : 1 % u.1.length = 1 := Nat.mod_eq_of_lt (by rw [u.length]; omega)
    omega
  · have hpos : 0 < u.1.length := by simpa [u.length] using (show 0 < k by omega)
    simp [hnil] at hpos

theorem doubleRotation_ne_self (hk : 3 ≤ k) (u : PermutationVertex k) :
    doubleRotation u ≠ u := by
  intro h
  have hword : u.1.rotate 2 = u.1 := by
    rw [← doubleRotation_word_eq_rotate (by omega) u]
    exact congrArg Subtype.val h
  rcases (u.nodup.rotate_eq_self_iff.mp hword) with hmod | hnil
  · have hmodtwo : 2 % u.1.length = 2 := Nat.mod_eq_of_lt (by rw [u.length]; omega)
    omega
  · have hpos : 0 < u.1.length := by simpa [u.length] using (show 0 < k by omega)
    simp [hnil] at hpos

theorem door_ne_self (hk : 3 ≤ k) (u : PermutationVertex k) : door u ≠ u := by
  obtain ⟨a, tail₁, hu₁⟩ := List.exists_cons_of_length_pos
    (l := u.1) (by simpa [u.length] using (show 0 < k by omega))
  have htail₁ : 0 < tail₁.length := by
    have hul := u.length
    rw [hu₁] at hul
    simp only [List.length_cons] at hul
    omega
  obtain ⟨b, tail₂, hu₂⟩ := List.exists_cons_of_length_pos htail₁
  have htail₂ : 0 < tail₂.length := by
    have hul := u.length
    rw [hu₁, hu₂] at hul
    simp only [List.length_cons] at hul
    omega
  obtain ⟨c, rest, hu₃⟩ := List.exists_cons_of_length_pos htail₂
  have hu : u.1 = a :: b :: c :: rest :=
    hu₁.trans (congrArg (List.cons a) (hu₂.trans (congrArg (List.cons b) hu₃)))
  intro h
  have hword := congrArg Subtype.val h
  have hhead := congrArg List.head? hword
  have hca : c = a := by simpa [hu] using hhead
  have hnod := u.nodup
  rw [hu] at hnod
  have hnot : a ∉ b :: c :: rest := (List.nodup_cons.mp hnod).1
  exact hnot (by simp [hca])

theorem doubleRotation_ne_door (hk : 3 ≤ k) (u : PermutationVertex k) :
    doubleRotation u ≠ door u := by
  obtain ⟨a, tail, hu₁⟩ := List.exists_cons_of_length_pos
    (l := u.1) (by simpa [u.length] using (show 0 < k by omega))
  have htail : 0 < tail.length := by
    have hul := u.length
    rw [hu₁] at hul
    simp only [List.length_cons] at hul
    omega
  obtain ⟨b, rest, hu₂⟩ := List.exists_cons_of_length_pos htail
  have hu : u.1 = a :: b :: rest := hu₁.trans (congrArg (List.cons a) hu₂)
  intro h
  have hword := congrArg Subtype.val h
  have hnod := u.nodup
  rw [hu] at hnod
  have hword' : rest ++ [a, b] = rest ++ [b, a] := by
    simpa only [doubleRotation_word, door_word, hu, List.drop, List.take,
      List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      List.append_nil] using hword
  have hpairs : [a, b] = [b, a] := (List.append_right_inj rest).mp hword'
  have hab : a = b := (List.cons.inj hpairs).1
  have hnot : a ∉ b :: rest := (List.nodup_cons.mp hnod).1
  exact hnot (by simp [hab])

end PermutationVertex

end SuperpermutationLowerBound
