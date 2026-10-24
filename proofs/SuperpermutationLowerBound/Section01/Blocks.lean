module

public import SuperpermutationLowerBound.Section01.Paths

@[expose] public section

namespace SuperpermutationLowerBound

/-! Rotation classes and the frozen Section 1 structure of exitless paths.
-/

open PermutationVertex

variable {k : ℕ}

noncomputable instance permutationVertexDecidableEq (k : ℕ) :
    DecidableEq (PermutationVertex k) := Classical.decEq _

namespace PermutationVertex

/-- The `i`th iterate of the left rotation. -/
def rotationPower (i : ℕ) (u : PermutationVertex k) : PermutationVertex k :=
  (rotation^[i]) u

@[simp]
theorem rotationPower_zero (u : PermutationVertex k) : rotationPower 0 u = u := rfl

theorem rotationPower_succ (i : ℕ) (u : PermutationVertex k) :
    rotationPower (i + 1) u = rotationPower i (rotation u) := by
  simp [rotationPower, Function.iterate_succ_apply]

/-- Iterated vertex rotation agrees with list rotation. -/
theorem rotationPower_word (hk : 1 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    (rotationPower i u).1 = u.1.rotate i := by
  induction i generalizing u with
  | zero => simp [rotationPower]
  | succ i ih =>
      calc
        (rotationPower (i + 1) u).1 = (rotationPower i (rotation u)).1 :=
          congrArg Subtype.val (rotationPower_succ i u)
        _ = (rotation u).1.rotate i := ih (rotation u)
        _ = (u.1.rotate 1).rotate i := by rw [rotation_word_eq_rotate hk]
        _ = u.1.rotate (1 + i) := List.rotate_rotate _ _ _
        _ = u.1.rotate (i + 1) := by rw [Nat.add_comm]

/-- Rotation powers compose by addition. -/
theorem rotationPower_add (i j : ℕ) (u : PermutationVertex k) :
    rotationPower i (rotationPower j u) = rotationPower (i + j) u := by
  simp [rotationPower, Function.iterate_add_apply]

/-- Exactly `k` rotations return a permutation word to itself. -/
theorem rotationPower_length (hk : 1 ≤ k) (u : PermutationVertex k) :
    rotationPower k u = u := by
  apply PermutationVertex.ext
  rw [rotationPower_word hk]
  calc
    u.1.rotate k = u.1.rotate u.1.length := congrArg u.1.rotate u.length.symm
    _ = u.1 := List.rotate_length _

/-- Rotation exponents may be reduced modulo `k`. -/
theorem rotationPower_mod (hk : 1 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    rotationPower (i % k) u = rotationPower i u := by
  apply PermutationVertex.ext
  rw [rotationPower_word hk, rotationPower_word hk]
  calc
    u.1.rotate (i % k) = u.1.rotate (i % u.1.length) := by
      exact congrArg u.1.rotate (congrArg (fun n => i % n) u.length.symm)
    _ = u.1.rotate i := List.rotate_mod _ _

/-- Distinct exponents below `k` give distinct rotations of a permutation vertex. -/
theorem rotationPower_injective_on_range (hk : 1 ≤ k) (u : PermutationVertex k) :
    Set.InjOn (fun i : ℕ => rotationPower i u) (Set.Iio k) := by
  intro i hi j hj hij
  have hi' : i < u.1.length := by simpa [u.length] using hi
  have hj' : j < u.1.length := by simpa [u.length] using hj
  have hword := congrArg Subtype.val hij
  rw [rotationPower_word hk, rotationPower_word hk] at hword
  have hhead := congrArg List.head? hword
  rw [List.head?_rotate hi', List.head?_rotate hj',
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj'] at hhead
  have helem : u.1[i] = u.1[j] := Option.some.inj hhead
  exact u.nodup.getElem_inj_iff.mp helem

end PermutationVertex

/-- The rotation class (block) of a permutation vertex. -/
noncomputable def rotationClass (u : PermutationVertex k) :
    Finset (PermutationVertex k) := by
  classical
  exact (Finset.range k).image fun i => rotationPower i u

theorem mem_rotationClass_iff (u v : PermutationVertex k) :
    v ∈ rotationClass u ↔ ∃ i < k, rotationPower i u = v := by
  classical
  simp [rotationClass]

/-- A vertex belongs to its own rotation class. -/
theorem self_mem_rotationClass (hk : 1 ≤ k) (u : PermutationVertex k) :
    u ∈ rotationClass u := by
  exact (mem_rotationClass_iff u u).2 ⟨0, hk, rfl⟩

/-- Every rotation class has exactly `k` vertices. -/
theorem rotationClass_card (hk : 1 ≤ k) (u : PermutationVertex k) :
    (rotationClass u).card = k := by
  classical
  unfold rotationClass
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_range k
  · intro i hi j hj hij
    exact rotationPower_injective_on_range hk u (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hij

/-- Rotating the entry does not change its rotation class. -/
theorem rotationClass_eq_of_mem (hk : 1 ≤ k) {u v : PermutationVertex k}
    (hv : v ∈ rotationClass u) :
    rotationClass v = rotationClass u := by
  classical
  obtain ⟨i, hi, rfl⟩ := (mem_rotationClass_iff u v).1 hv
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_rotationClass_iff (rotationPower i u) x).1 hx
    apply (mem_rotationClass_iff u (rotationPower j (rotationPower i u))).2
    refine ⟨(j + i) % k, Nat.mod_lt _ (by omega), ?_⟩
    rw [rotationPower_mod hk, rotationPower_add]
  · rw [rotationClass_card hk, rotationClass_card hk]

/-- Two rotation classes are equal exactly when one entry belongs to the other class. -/
theorem rotationClass_eq_iff_mem (hk : 1 ≤ k) (u v : PermutationVertex k) :
    rotationClass u = rotationClass v ↔ v ∈ rotationClass u := by
  constructor
  · intro h
    rw [h]
    exact self_mem_rotationClass hk v
  · intro hv
    exact (rotationClass_eq_of_mem hk hv).symm

/-- Rotation classes that meet are equal. -/
theorem rotationClasses_eq_of_intersect (hk : 1 ≤ k)
    {u v : PermutationVertex k}
    (h : (rotationClass u ∩ rotationClass v).Nonempty) :
    rotationClass u = rotationClass v := by
  obtain ⟨x, hx⟩ := h
  have ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
  calc
    rotationClass u = rotationClass x := (rotationClass_eq_of_mem hk hxu).symm
    _ = rotationClass v := rotationClass_eq_of_mem hk hxv

/-- The finite set of all rotation classes. -/
noncomputable def rotationBlocks (k : ℕ) :
    Finset (Finset (PermutationVertex k)) := by
  classical
  exact (Finset.univ : Finset (PermutationVertex k)).image rotationClass

private theorem allVertices_nodup (k : ℕ) : (allVertices k).Nodup := by
  classical
  unfold allVertices
  apply List.Nodup.map
  · intro a b hab
    exact Subtype.ext (congrArg (fun z : PermutationVertex k => z.1) hab)
  · apply List.Nodup.attach
    exact List.nodup_permutations _ (Finset.nodup_toList _)

private theorem mem_allVertices (v : PermutationVertex k) : v ∈ allVertices k := by
  classical
  unfold allVertices
  apply List.mem_map.mpr
  let w : {word // word ∈ (alphabetWord k).permutations} :=
    ⟨v.1, List.mem_permutations.mpr v.2⟩
  exact ⟨w, List.mem_attach _ _, Subtype.ext rfl⟩

/-- The overlap digraph has `k!` permutation vertices. -/
theorem permutationVertex_card (k : ℕ) :
    Fintype.card (PermutationVertex k) = k.factorial := by
  classical
  have huniv : (allVertices k).toFinset =
      (Finset.univ : Finset (PermutationVertex k)) := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    exact List.mem_toFinset.mpr (mem_allVertices v)
  calc
    Fintype.card (PermutationVertex k) =
        (Finset.univ : Finset (PermutationVertex k)).card := by
      rw [Finset.card_univ]
    _ = (allVertices k).toFinset.card := congrArg Finset.card huniv.symm
    _ = (allVertices k).length := List.toFinset_card_of_nodup (allVertices_nodup k)
    _ = k.factorial := by
      calc
        (allVertices k).length = (alphabetWord k).permutations.attach.length :=
          List.length_map (β := PermutationVertex k)
            (fun w : {x // x ∈ (alphabetWord k).permutations} =>
              ⟨w.1, List.mem_permutations.mp w.2⟩)
        _ = (alphabetWord k).permutations.length := List.length_attach
        _ = (alphabetWord k).length.factorial := List.length_permutations _
        _ = k.factorial := by simp [alphabetWord, Alphabet]

private theorem rotationBlocks_pairwiseDisjoint (hk : 1 ≤ k) :
    (↑(rotationBlocks k) : Set (Finset (PermutationVertex k))).PairwiseDisjoint id := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro A hA B hB hinter
  obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨v, _hv, rfl⟩ := Finset.mem_image.mp hB
  exact rotationClasses_eq_of_intersect hk hinter

private theorem rotationBlocks_biUnion (hk : 1 ≤ k) :
    (rotationBlocks k).biUnion id =
      (Finset.univ : Finset (PermutationVertex k)) := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  apply Finset.mem_biUnion.mpr
  refine ⟨rotationClass v, ?_, self_mem_rotationClass hk v⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- The rotation classes partition the vertices into exactly `(k-1)!` blocks. -/
theorem rotationBlocks_card (hk : 1 ≤ k) :
    (rotationBlocks k).card = (k - 1).factorial := by
  classical
  have hcard := Finset.card_biUnion (rotationBlocks_pairwiseDisjoint hk)
  rw [rotationBlocks_biUnion hk] at hcard
  have hsum :
      ∑ B ∈ rotationBlocks k, B.card = (rotationBlocks k).card * k := by
    calc
      ∑ B ∈ rotationBlocks k, B.card = ∑ _B ∈ rotationBlocks k, k := by
        apply Finset.sum_congr rfl
        intro B hB
        obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hB
        exact rotationClass_card hk u
      _ = (rotationBlocks k).card * k := by simp
  have hcard' :
      (Finset.univ : Finset (PermutationVertex k)).card =
        (rotationBlocks k).card * k := by
    calc
      (Finset.univ : Finset (PermutationVertex k)).card =
          ∑ B ∈ rotationBlocks k, (id B).card := hcard
      _ = ∑ B ∈ rotationBlocks k, B.card := by rfl
      _ = (rotationBlocks k).card * k := hsum
  have hfactorial : (rotationBlocks k).card * k = k.factorial := by
    calc
      (rotationBlocks k).card * k =
          (Finset.univ : Finset (PermutationVertex k)).card := hcard'.symm
      _ = Fintype.card (PermutationVertex k) := Finset.card_univ
      _ = k.factorial := permutationVertex_card k
  have hkfactorial : k.factorial = k * (k - 1).factorial := by
    calc
      k.factorial = ((k - 1) + 1).factorial := by congr 1 <;> omega
      _ = ((k - 1) + 1) * (k - 1).factorial := Nat.factorial_succ (k - 1)
      _ = k * (k - 1).factorial := by congr 1 <;> omega
  apply Nat.mul_left_cancel (n := k) (by omega)
  calc
    k * (rotationBlocks k).card = (rotationBlocks k).card * k := Nat.mul_comm _ _
    _ = k.factorial := hfactorial
    _ = k * (k - 1).factorial := hkfactorial

/-- The first `r` vertices obtained by rotating an entry. -/
noncomputable def rotationSegment (r : ℕ) (u : PermutationVertex k) :
    List (PermutationVertex k) :=
  (List.range r).map fun i => rotationPower i u

/-- A complete rotation block, traversed from its entry by weight-one edges. -/
noncomputable def completeRotationBlock (u : PermutationVertex k) :
    List (PermutationVertex k) := rotationSegment k u

@[simp]
theorem rotationSegment_length (r : ℕ) (u : PermutationVertex k) :
    (rotationSegment r u).length = r := by
  simp [rotationSegment]

theorem mem_rotationSegment_iff (r : ℕ) (u v : PermutationVertex k) :
    v ∈ rotationSegment r u ↔ ∃ i < r, rotationPower i u = v := by
  simp [rotationSegment]

theorem rotationSegment_nodup (hk : 1 ≤ k) (u : PermutationVertex k)
    {r : ℕ} (hr : r ≤ k) :
    (rotationSegment r u).Nodup := by
  unfold rotationSegment
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp_of_mem
  intro i j hi hj hij hrot
  have hi' : i < k := (List.mem_range.mp hi).trans_le hr
  have hj' : j < k := (List.mem_range.mp hj).trans_le hr
  exact hij (rotationPower_injective_on_range hk u hi' hj' hrot)

/-- The exit of a block entered at `u`. -/
def blockExit (u : PermutationVertex k) : PermutationVertex k :=
  inverseRotation u

/-- Rotating a block exit returns to its entry. -/
theorem rotation_blockExit (hk : 1 ≤ k) (u : PermutationVertex k) :
    rotation (blockExit u) = u := rotation_inverseRotation hk u

/-- The last vertex of a complete block is its exit. -/
theorem rotationPower_pred_eq_blockExit (hk : 1 ≤ k) (u : PermutationVertex k) :
    rotationPower (k - 1) u = blockExit u := by
  change rotationPower (k - 1) u = inverseRotation u
  apply PermutationVertex.ext
  rw [rotationPower_word hk, inverseRotation_word_eq_rotate]

/-- Rotation commutes with taking a rotation power. -/
theorem rotation_rotationPower (hk : 1 ≤ k) (i : ℕ) (u : PermutationVertex k) :
    rotation (rotationPower i u) = rotationPower (i + 1) u := by
  apply PermutationVertex.ext
  calc
    (rotation (rotationPower i u)).1 = (rotationPower i u).1.rotate 1 :=
      rotation_word_eq_rotate hk _
    _ = (u.1.rotate i).rotate 1 := by rw [rotationPower_word hk]
    _ = u.1.rotate (i + 1) := List.rotate_rotate _ _ _
    _ = (rotationPower (i + 1) u).1 := (rotationPower_word hk _ _).symm

/-- Every rotation power lies in its entry's block. -/
theorem rotationPower_mem_rotationClass (hk : 1 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    rotationPower i u ∈ rotationClass u := by
  apply (mem_rotationClass_iff u _).2
  refine ⟨i % k, Nat.mod_lt _ (by omega), ?_⟩
  exact rotationPower_mod hk i u

/-- Taking a rotation power preserves the rotation class. -/
theorem rotationClass_rotationPower (hk : 1 ≤ k) (i : ℕ)
    (u : PermutationVertex k) :
    rotationClass (rotationPower i u) = rotationClass u :=
  rotationClass_eq_of_mem hk (rotationPower_mem_rotationClass hk i u)

/-- A TeX early exit at zero-based position `i`: a non-weight-one edge is taken while the
rotation successor has not appeared through position `i`. -/
def HasEarlyExit (p : OverlapPath k) : Prop :=
  ∃ i, ∃ hi : i + 1 < p.length,
    1 < overlapWeight
      (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) ∧
    rotation (p.vertex ⟨i, by omega⟩) ∉ p.vertices.take (i + 1)

/-- An exitless path has no early exit. -/
def IsExitless (p : OverlapPath k) : Prop := ¬HasEarlyExit p

/-- A strongly exitless path is exitless and its final rotation successor has already been
visited. -/
def IsStronglyExitless (p : OverlapPath k) : Prop :=
  IsExitless p ∧ rotation (p.vertices.getLast p.nonempty) ∈ p.vertices

/-- Exitlessness in the implication form used in the block-structure proof. -/
theorem exitless_heavy_imp_rotation_visited {p : OverlapPath k} (hp : IsExitless p)
    (i : ℕ) (hi : i + 1 < p.length)
    (hheavy : 1 < overlapWeight
      (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩)) :
    rotation (p.vertex ⟨i, by omega⟩) ∈ p.vertices.take (i + 1) := by
  by_contra hnot
  exact hp ⟨i, hi, hheavy, hnot⟩

/-- The vertex at position `i+1` is absent from the prefix through position `i`. -/
private theorem next_vertex_not_mem_take (p : OverlapPath k)
    (i : ℕ) (hi : i + 1 < p.length) :
    p.vertex ⟨i + 1, hi⟩ ∉ p.vertices.take (i + 1) := by
  intro hmem
  obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp hmem
  have hj' : j < i + 1 := by omega
  have heq := hget
  change p.vertices[j] = p.vertices[i + 1] at heq
  have hji : j = i + 1 := p.nodup.getElem_inj_iff.mp heq
  omega

/-- On an exitless path, an edge has weight one exactly when the current rotation successor
has not yet been visited. -/
theorem exitless_weight_one_iff_rotation_not_visited {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i + 1 < p.length) :
    overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) = 1 ↔
      rotation (p.vertex ⟨i, by omega⟩) ∉ p.vertices.take (i + 1) := by
  let u := p.vertex ⟨i, by omega⟩
  let v := p.vertex ⟨i + 1, hi⟩
  have huv : u ≠ v := p.vertex_ne_of_ne (by simp)
  constructor
  · intro hw hmem
    have hrot : v = rotation u :=
      (unique_weight_one_successor u v hk huv).mp hw
    apply next_vertex_not_mem_take p i hi
    change v ∈ p.vertices.take (i + 1)
    rw [hrot]
    exact hmem
  · intro hnot
    have hpos := (overlapWeight_spec u v).1
    have hnheavy : ¬1 < overlapWeight u v := by
      intro hheavy
      exact hnot (exitless_heavy_imp_rotation_visited hp i hi hheavy)
    exact Nat.le_antisymm (Nat.le_of_not_gt hnheavy) hpos

/-- The corresponding boundary form: a non-weight-one edge occurs exactly when the rotation
successor has already been visited. -/
theorem exitless_boundary_iff_rotation_visited {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i + 1 < p.length) :
    2 ≤ overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) ↔
      rotation (p.vertex ⟨i, by omega⟩) ∈ p.vertices.take (i + 1) := by
  have hpos := (overlapWeight_spec
    (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩)).1
  constructor
  · intro htwo
    by_contra hnot
    have hone := (exitless_weight_one_iff_rotation_not_visited hp hk i hi).2 hnot
    omega
  · intro hmem
    have hne : overlapWeight (p.vertex ⟨i, by omega⟩)
        (p.vertex ⟨i + 1, hi⟩) ≠ 1 := by
      intro hone
      exact (exitless_weight_one_iff_rotation_not_visited hp hk i hi).1 hone hmem
    omega

private def BlockPrefixInvariant (p : OverlapPath k) (hkpos : 0 < k) (N : ℕ) : Prop :=
  (∀ i (hiN : i < N) (hiP : i < p.length),
      p.vertex ⟨i, hiP⟩ =
        rotationPower (i % k)
          (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hiP⟩)) ∧
  (∀ a b (hab : a < b) (hbN : k * b < N) (hbP : k * b < p.length),
      rotationClass
          (p.vertex ⟨k * a, (Nat.mul_lt_mul_of_pos_left hab hkpos).trans hbP⟩) ≠
        rotationClass (p.vertex ⟨k * b, hbP⟩))

private theorem exitless_blockPrefixInvariant (p : OverlapPath k)
    (hp : IsExitless p) (hk : 3 ≤ k) :
    ∀ N, N ≤ p.length → BlockPrefixInvariant p (by omega) N := by
  intro N hN
  induction N with
  | zero =>
      constructor <;> intro <;> omega
  | succ n ih =>
      have hnle : n ≤ p.length := by omega
      have hnP : n < p.length := by omega
      have hprev := ih hnle
      constructor
      · intro i hiN hiP
        by_cases hin : i < n
        · exact hprev.1 i hin hiP
        · have hin' : i = n := by omega
          subst i
          by_cases hnmod : n % k = 0
          · have hnrepr := Nat.div_add_mod n k
            have hstart : k * (n / k) = n := by omega
            simpa [hnmod, hstart]
          · have hnpos : 0 < n := by
              by_contra hnzero
              have : n = 0 := Nat.eq_zero_of_not_pos hnzero
              subst n
              simp at hnmod
            let q := n - 1
            have hqn : q + 1 = n := by dsimp [q]; omega
            have hqP : q < p.length := by omega
            have hnotdvd : ¬k ∣ n := by
              rw [Nat.dvd_iff_mod_eq_zero]
              exact hnmod
            have hdiv : q / k = n / k := by
              have hnotdvdq : ¬k ∣ q + 1 := by simpa [hqn] using hnotdvd
              calc
                q / k = q / k + (if k ∣ q + 1 then 1 else 0) := by
                  rw [if_neg hnotdvdq]
                  simp
                _ = (q + 1) / k := (Nat.succ_div).symm
                _ = n / k := by rw [hqn]
            have hnrepr := Nat.div_add_mod n k
            have hqrepr := Nat.div_add_mod q k
            have hmodsucc : q % k + 1 = n % k := by
              rw [hdiv] at hqrepr
              omega
            have hqform := hprev.1 q (by omega) hqP
            have hentryQN :
                p.vertex ⟨k * (q / k), (Nat.mul_div_le q k).trans_lt hqP⟩ =
                  p.vertex ⟨k * (n / k), (Nat.mul_div_le n k).trans_lt hnP⟩ := by
              apply congrArg p.vertex
              apply Fin.ext
              simp [hdiv]
            have hrotation :
                rotation (p.vertex ⟨q, hqP⟩) =
                  rotationPower (n % k)
                    (p.vertex ⟨k * (n / k), (Nat.mul_div_le n k).trans_lt hnP⟩) := by
              calc
                rotation (p.vertex ⟨q, hqP⟩) =
                    rotation (rotationPower (q % k)
                      (p.vertex ⟨k * (q / k),
                        (Nat.mul_div_le q k).trans_lt hqP⟩)) := congrArg rotation hqform
                _ = rotationPower (q % k + 1)
                    (p.vertex ⟨k * (q / k),
                      (Nat.mul_div_le q k).trans_lt hqP⟩) :=
                  rotation_rotationPower (by omega) _ _
                _ = rotationPower (n % k)
                    (p.vertex ⟨k * (n / k),
                      (Nat.mul_div_le n k).trans_lt hnP⟩) := by
                  rw [hmodsucc, hentryQN]
            have hnotvisited :
                rotation (p.vertex ⟨q, hqP⟩) ∉ p.vertices.take n := by
              intro hmem
              obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp hmem
              have hjn : j < n := by omega
              have hjP : j < p.length := hjn.trans hnP
              have hjform := hprev.1 j hjn hjP
              have hget' := hget
              change p.vertex ⟨j, hjP⟩ = rotation (p.vertex ⟨q, hqP⟩) at hget'
              rw [hrotation, hjform] at hget'
              have hdivle : j / k ≤ n / k := Nat.div_le_div_right (Nat.le_of_lt hjn)
              rcases hdivle.eq_or_lt with hsame | hless
              · have hentryJN :
                    p.vertex ⟨k * (j / k), (Nat.mul_div_le j k).trans_lt hjP⟩ =
                      p.vertex ⟨k * (n / k),
                        (Nat.mul_div_le n k).trans_lt hnP⟩ := by
                  apply congrArg p.vertex
                  apply Fin.ext
                  simp [hsame]
                rw [hentryJN] at hget'
                have hremaineq : j % k = n % k :=
                  rotationPower_injective_on_range (by omega)
                    (p.vertex ⟨k * (n / k), (Nat.mul_div_le n k).trans_lt hnP⟩)
                    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hget'
                have hjrepr := Nat.div_add_mod j k
                rw [hsame] at hjrepr
                omega
              · have hstartP : k * (n / k) < p.length :=
                  (Nat.mul_div_le n k).trans_lt hnP
                have hnmodpos : 0 < n % k := Nat.pos_of_ne_zero hnmod
                have hstartN : k * (n / k) < n := by omega
                have hclasses := hprev.2 (j / k) (n / k) hless hstartN hstartP
                apply hclasses
                calc
                  rotationClass
                      (p.vertex ⟨k * (j / k),
                        (Nat.mul_div_le j k).trans_lt hjP⟩) =
                    rotationClass (rotationPower (j % k)
                      (p.vertex ⟨k * (j / k),
                        (Nat.mul_div_le j k).trans_lt hjP⟩)) :=
                      (rotationClass_rotationPower (by omega) _ _).symm
                  _ = rotationClass (rotationPower (n % k)
                      (p.vertex ⟨k * (n / k),
                        (Nat.mul_div_le n k).trans_lt hnP⟩)) :=
                    congrArg rotationClass hget'
                  _ = rotationClass
                      (p.vertex ⟨k * (n / k),
                        (Nat.mul_div_le n k).trans_lt hnP⟩) :=
                    rotationClass_rotationPower (by omega) _ _
            have hone := (exitless_weight_one_iff_rotation_not_visited hp hk q (by
              simpa [hqn] using hnP)).2 (by simpa [hqn] using hnotvisited)
            have hne : p.vertex ⟨q, hqP⟩ ≠ p.vertex ⟨n, hnP⟩ :=
              p.vertex_ne_of_ne (by
                intro hfin
                have := congrArg Fin.val hfin
                change q = n at this
                omega)
            have hnext : p.vertex ⟨n, hnP⟩ = rotation (p.vertex ⟨q, hqP⟩) := by
              have := (unique_weight_one_successor
                (p.vertex ⟨q, hqP⟩) (p.vertex ⟨n, hnP⟩) hk hne).mp (by
                  simpa [hqn] using hone)
              exact this
            exact hnext.trans hrotation
      · intro a b hab hbN hbP
        by_cases hbn : k * b < n
        · exact hprev.2 a b hab hbn hbP
        · have hbeq : k * b = n := by omega
          intro hclasses
          let va := p.vertex ⟨k * a,
            (Nat.mul_lt_mul_of_pos_left hab (by omega)).trans hbP⟩
          let vb := p.vertex ⟨k * b, hbP⟩
          have hvbmem : vb ∈ rotationClass va :=
            (rotationClass_eq_iff_mem (by omega) va vb).1 hclasses
          obtain ⟨t, ht, htrot⟩ := (mem_rotationClass_iff va vb).1 hvbmem
          let j := k * a + t
          have hab1 : a + 1 ≤ b := by omega
          have hmul := Nat.mul_le_mul_left k hab1
          have hjnext : j < k * (a + 1) := by
            dsimp [j]
            rw [Nat.mul_add]
            omega
          have hjb : j < k * b := hjnext.trans_le hmul
          have hjn : j < n := by rwa [hbeq] at hjb
          have hjP : j < p.length := hjn.trans hnP
          have hjdiv : j / k = a := by
            dsimp [j]
            rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht]
            omega
          have hjmod : j % k = t := by
            dsimp [j]
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
          have hjform := hprev.1 j hjn hjP
          have hentryJA :
              p.vertex ⟨k * (j / k), (Nat.mul_div_le j k).trans_lt hjP⟩ = va := by
            apply congrArg p.vertex
            apply Fin.ext
            simp [va, hjdiv]
          have hjform' : p.vertex ⟨j, hjP⟩ = rotationPower t va := by
            calc
              p.vertex ⟨j, hjP⟩ = rotationPower (j % k)
                  (p.vertex ⟨k * (j / k),
                    (Nat.mul_div_le j k).trans_lt hjP⟩) := hjform
              _ = rotationPower t va := by rw [hjmod, hentryJA]
          have heq : p.vertex ⟨j, hjP⟩ = p.vertex ⟨n, hnP⟩ := by
            calc
              p.vertex ⟨j, hjP⟩ = rotationPower t va := hjform'
              _ = vb := htrot
              _ = p.vertex ⟨n, hnP⟩ := by simp [vb, hbeq]
          have hindex : (⟨j, hjP⟩ : Fin p.length) = ⟨n, hnP⟩ :=
            p.nodup.get_inj_iff.mp heq
          have : j = n := congrArg Fin.val hindex
          omega

/-- Within an exitless path, position `i` is the `(i mod k)`th rotation of the entry at
the beginning of its `i / k` block. This includes a possible partial final block. -/
theorem exitless_vertex_formula {p : OverlapPath k} (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i < p.length) :
    p.vertex ⟨i, hi⟩ =
      rotationPower (i % k)
        (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩) := by
  exact (exitless_blockPrefixInvariant p hp hk p.length le_rfl).1 i hi hi

/-- Entries of distinct blocks in an exitless path lie in distinct rotation classes. -/
theorem exitless_block_entries_distinct {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    {a b : ℕ} (hab : a < b) (hb : k * b < p.length) :
    rotationClass
        (p.vertex ⟨k * a, (Nat.mul_lt_mul_of_pos_left hab (by omega)).trans hb⟩) ≠
      rotationClass (p.vertex ⟨k * b, hb⟩) := by
  exact (exitless_blockPrefixInvariant p hp hk p.length le_rfl).2 a b hab hb hb

/-- The block-local vertex formula with explicit block number and offset. -/
theorem exitless_block_vertex {p : OverlapPath k} (hp : IsExitless p) (hk : 3 ≤ k)
    (b j : ℕ) (hj : j < k) (hpos : k * b + j < p.length) :
    p.vertex ⟨k * b + j, hpos⟩ =
      rotationPower j (p.vertex ⟨k * b, by omega⟩) := by
  have hdiv : (k * b + j) / k = b := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]
    omega
  have hmod : (k * b + j) % k = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hformula := exitless_vertex_formula hp hk (k * b + j) hpos
  have hentry :
      p.vertex ⟨k * ((k * b + j) / k),
        (Nat.mul_div_le (k * b + j) k).trans_lt hpos⟩ =
        p.vertex ⟨k * b, by omega⟩ := by
    apply congrArg p.vertex
    apply Fin.ext
    simp [hdiv]
  rw [hmod, hentry] at hformula
  exact hformula

/-- The exact complete-block/partial-final-block structure. There are `b` complete blocks
and a final block of length `r < k`; the displayed vertex formula covers both the complete
blocks and that partial final block, and different block entries have different classes. -/
theorem exitless_complete_blocks_partial_final {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k) :
    ∃ b r, p.length = k * b + r ∧ r < k ∧
      (∀ i (hi : i < p.length),
        p.vertex ⟨i, hi⟩ = rotationPower (i % k)
          (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩)) ∧
      (∀ a c (hac : a < c) (hc : k * c < p.length),
        rotationClass
            (p.vertex ⟨k * a, (Nat.mul_lt_mul_of_pos_left hac (by omega)).trans hc⟩) ≠
          rotationClass (p.vertex ⟨k * c, hc⟩)) := by
  refine ⟨p.length / k, p.length % k, (Nat.div_add_mod p.length k).symm,
    Nat.mod_lt _ (by omega), ?_, ?_⟩
  · exact fun i hi => exitless_vertex_formula hp hk i hi
  · exact fun a c hac hc => exitless_block_entries_distinct hp hk hac hc

/-- The successor under rotation has appeared through position `i` exactly at a block
boundary. Thus TeX's one-based boundary condition `k ∣ t` becomes `k ∣ i+1` at zero-based
edge index `i`. -/
theorem exitless_rotation_visited_iff_dvd {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i < p.length) :
    rotation (p.vertex ⟨i, hi⟩) ∈ p.vertices.take (i + 1) ↔ k ∣ i + 1 := by
  let n := i + 1
  have hn : n = i + 1 := rfl
  have hnle : n ≤ p.length := by dsimp [n]; omega
  have hiform := exitless_vertex_formula hp hk i hi
  have hirepr := Nat.div_add_mod i k
  constructor
  · intro hvisited
    by_contra hnotdvd
    have hnotmod : n % k ≠ 0 := by
      intro hzero
      exact hnotdvd ((Nat.dvd_iff_mod_eq_zero).2 hzero)
    have hdiv : n / k = i / k := by
      rw [hn, Nat.succ_div, if_neg hnotdvd]
      simp
    have hnrepr := Nat.div_add_mod n k
    have hmodpos : 0 < n % k := Nat.pos_of_ne_zero hnotmod
    have hstartN : k * (n / k) < n := by omega
    have hstartP : k * (n / k) < p.length := hstartN.trans_le hnle
    have hmodsucc : i % k + 1 = n % k := by
      rw [hdiv] at hnrepr
      omega
    have hrotation :
        rotation (p.vertex ⟨i, hi⟩) =
          rotationPower (n % k)
            (p.vertex ⟨k * (n / k), hstartP⟩) := by
      have hentry :
          p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩ =
            p.vertex ⟨k * (n / k), hstartP⟩ := by
        apply congrArg p.vertex
        apply Fin.ext
        simp [hdiv]
      calc
        rotation (p.vertex ⟨i, hi⟩) = rotation
            (rotationPower (i % k)
              (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩)) :=
          congrArg rotation hiform
        _ = rotationPower (i % k + 1)
            (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩) :=
          rotation_rotationPower (by omega) _ _
        _ = rotationPower (n % k)
            (p.vertex ⟨k * (n / k), hstartP⟩) := by
          rw [hmodsucc, hentry]
    obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp hvisited
    have hjn : j < n := hj.trans_le (Nat.min_le_left _ _)
    have hjP : j < p.length := by
      simpa [OverlapPath.length] using hj.trans_le (Nat.min_le_right _ _)
    have hjform := exitless_vertex_formula hp hk j hjP
    have hget' := hget
    change p.vertex ⟨j, hjP⟩ = rotation (p.vertex ⟨i, hi⟩) at hget'
    rw [hrotation, hjform] at hget'
    have hdivle : j / k ≤ n / k := Nat.div_le_div_right (Nat.le_of_lt hjn)
    rcases hdivle.eq_or_lt with hsame | hless
    · have hentry :
          p.vertex ⟨k * (j / k), (Nat.mul_div_le j k).trans_lt hjP⟩ =
            p.vertex ⟨k * (n / k), hstartP⟩ := by
        apply congrArg p.vertex
        apply Fin.ext
        simp [hsame]
      rw [hentry] at hget'
      have hrem : j % k = n % k :=
        rotationPower_injective_on_range (by omega)
          (p.vertex ⟨k * (n / k), hstartP⟩)
          (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hget'
      have hjrepr := Nat.div_add_mod j k
      rw [hsame] at hjrepr
      omega
    ·
      have hclasses := exitless_block_entries_distinct hp hk hless hstartP
      apply hclasses
      calc
        rotationClass
            (p.vertex ⟨k * (j / k), (Nat.mul_div_le j k).trans_lt hjP⟩) =
          rotationClass (rotationPower (j % k)
            (p.vertex ⟨k * (j / k), (Nat.mul_div_le j k).trans_lt hjP⟩)) :=
              (rotationClass_rotationPower (by omega) _ _).symm
        _ = rotationClass (rotationPower (n % k)
            (p.vertex ⟨k * (n / k), hstartP⟩)) :=
          congrArg rotationClass hget'
        _ = rotationClass
            (p.vertex ⟨k * (n / k), hstartP⟩) :=
          rotationClass_rotationPower (by omega) _ _
  · intro hdvd
    have hnmod : n % k = 0 := (Nat.dvd_iff_mod_eq_zero).1 hdvd
    have hdiv : n / k = i / k + 1 := by
      rw [hn, Nat.succ_div, if_pos hdvd]
    have hnrepr := Nat.div_add_mod n k
    have hrem : i % k + 1 = k := by
      rw [hnmod, hdiv] at hnrepr
      rw [Nat.mul_add] at hnrepr
      omega
    have hrotation :
        rotation (p.vertex ⟨i, hi⟩) =
          p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩ := by
      calc
        rotation (p.vertex ⟨i, hi⟩) = rotation
            (rotationPower (i % k)
              (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩)) :=
          congrArg rotation hiform
        _ = rotationPower (i % k + 1)
            (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩) :=
          rotation_rotationPower (by omega) _ _
        _ = rotationPower k
            (p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩) := by rw [hrem]
        _ = p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩ :=
          rotationPower_length (by omega) _
    apply List.mem_take_iff_getElem.mpr
    refine ⟨k * (i / k), ?_, ?_⟩
    · have hstart := Nat.mul_div_le i k
      apply lt_min
      · omega
      · simpa [OverlapPath.length] using hstart.trans_lt hi
    · change p.vertex ⟨k * (i / k), (Nat.mul_div_le i k).trans_lt hi⟩ =
        rotation (p.vertex ⟨i, hi⟩)
      exact hrotation.symm

/-- Exact boundary indexing in the frozen block-structure lemma. -/
theorem exitless_boundary_weight_iff_dvd {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i + 1 < p.length) :
    2 ≤ overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) ↔
      k ∣ i + 1 := by
  exact (exitless_boundary_iff_rotation_visited hp hk i hi).trans
    (exitless_rotation_visited_iff_dvd hp hk i (by omega))

/-- Strong exitlessness eliminates the partial final block. -/
theorem stronglyExitless_length_dvd {p : OverlapPath k}
    (hp : IsStronglyExitless p) (hk : 3 ≤ k) :
    k ∣ p.length := by
  let i := p.length - 1
  have hi : i < p.length := by dsimp [i]; have := p.length_pos; omega
  have hlast : p.vertex ⟨i, hi⟩ = p.vertices.getLast p.nonempty := by
    simpa [i, OverlapPath.vertex, OverlapPath.length] using
      (List.getLast_eq_getElem p.nonempty).symm
  have hvisited : rotation (p.vertex ⟨i, hi⟩) ∈ p.vertices.take (i + 1) := by
    have htake : p.vertices.take (i + 1) = p.vertices := by
      have hilength : i + 1 = p.length := by dsimp [i]; omega
      rw [hilength, OverlapPath.length, List.take_length]
    rw [htake, hlast]
    exact hp.2
  have hdvd := (exitless_rotation_visited_iff_dvd hp.1 hk i hi).1 hvisited
  simpa [i, show p.length - 1 + 1 = p.length by omega] using hdvd

/-- An exitless path is block-aligned when its length is divisible by `k`. -/
def IsBlockAligned (p : OverlapPath k) : Prop :=
  IsExitless p ∧ k ∣ p.length

/-- The number of complete blocks in a block-aligned path (and the number of complete blocks
before the possible partial block for an arbitrary path). -/
def pathBlockCount (p : OverlapPath k) : ℕ := p.length / k

theorem blockAligned_length_eq {p : OverlapPath k} (hp : IsBlockAligned p) :
    p.length = k * pathBlockCount p := by
  exact (Nat.mul_div_cancel' hp.2).symm

theorem blockAligned_blockCount_pos {p : OverlapPath k}
    (hp : IsBlockAligned p) :
    0 < pathBlockCount p := by
  have hlen := blockAligned_length_eq hp
  have hpos := p.length_pos
  by_contra hnot
  have hb : pathBlockCount p = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hb, Nat.mul_zero] at hlen
  omega

/-- The actual weight of the edge at zero-based index `i`, totalized by zero off the path. -/
noncomputable def pathEdgeWeight (p : OverlapPath k) (i : ℕ) : ℕ :=
  if hi : i + 1 < p.length then
    overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩)
  else 0

@[simp]
theorem pathEdgeWeight_of_lt (p : OverlapPath k) (i : ℕ) (hi : i + 1 < p.length) :
    pathEdgeWeight p i =
      overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) := by
  simp [pathEdgeWeight, hi]

private noncomputable def listEdgeWeightAt (l : List (PermutationVertex k)) (i : ℕ) : ℕ :=
  if hi : i + 1 < l.length then
    overlapWeight l[i] l[i + 1]
  else 0

private theorem vertexListWeight_eq_sum_edges (l : List (PermutationVertex k)) :
    vertexListWeight l = ∑ i ∈ Finset.range (l.length - 1), listEdgeWeightAt l i := by
  induction l with
  | nil => simp [vertexListWeight]
  | cons u l ih =>
      rcases l with _ | ⟨v, rest⟩
      · simp [vertexListWeight]
      · rw [show (u :: v :: rest).length - 1 = 1 + rest.length by
          simp [Nat.add_comm]]
        rw [Finset.sum_range_add]
        simp only [Finset.sum_range_one]
        have hshift :
            (∑ x ∈ Finset.range rest.length,
              listEdgeWeightAt (u :: v :: rest) (1 + x)) =
              ∑ x ∈ Finset.range rest.length, listEdgeWeightAt (v :: rest) x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxlt : x < rest.length := Finset.mem_range.mp hx
          unfold listEdgeWeightAt
          rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
          simp [Nat.add_comm]
          congr 1
          simp only [show 1 + (x + 1) = (x + 1) + 1 by omega,
            List.getElem_cons_succ]
        have ih' : vertexListWeight (v :: rest) =
            ∑ x ∈ Finset.range rest.length, listEdgeWeightAt (v :: rest) x := by
          simpa using ih
        rw [hshift, ← ih']
        simp [vertexListWeight, listEdgeWeightAt]

/-- A path's recursive weight is the sum of its indexed edge weights. -/
theorem OverlapPath.weight_eq_sum_edges (p : OverlapPath k) :
    p.weight = ∑ i ∈ Finset.range (p.length - 1), pathEdgeWeight p i := by
  rw [OverlapPath.weight, vertexListWeight_eq_sum_edges]
  apply Finset.sum_congr
  · simp [OverlapPath.length]
  · intro i hi
    have hi' : i + 1 < p.length := by
      have := Finset.mem_range.mp hi
      have hpos := p.length_pos
      omega
    rw [pathEdgeWeight_of_lt p i hi']
    unfold listEdgeWeightAt
    rw [dite_eq_left (show i + 1 < p.vertices.length from hi')]
    rfl

/-- Boundary weights `w₁,...,w_{b-1}` of a block-aligned path. Entry `j` is the jump after
block `j` and before block `j+1`. -/
noncomputable def blockBoundaryWeights (p : OverlapPath k) (hp : IsBlockAligned p) :
    List ℕ :=
  List.ofFn fun j : Fin (pathBlockCount p - 1) =>
    pathEdgeWeight p (k * (j.1 + 1) - 1)

@[simp]
theorem blockBoundaryWeights_length (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockBoundaryWeights p hp).length = pathBlockCount p - 1 := by
  simp [blockBoundaryWeights]

/-- The excess is the sum of `w_i - 2` over block boundaries. -/
noncomputable def pathExcess (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  ((blockBoundaryWeights p hp).map fun w => w - 2).sum

/-- Every recorded boundary weight really is at least two. -/
theorem blockBoundaryWeights_ge_two {p : OverlapPath k}
    (hp : IsBlockAligned p) (hk : 3 ≤ k)
    {w : ℕ} (hw : w ∈ blockBoundaryWeights p hp) : 2 ≤ w := by
  obtain ⟨j, hj⟩ := (List.mem_ofFn.mp hw)
  let t := k * (j.1 + 1)
  have hbpos := blockAligned_blockCount_pos hp
  have htpos : 0 < t := by dsimp [t]; positivity
  have htdvd : k ∣ t := ⟨j.1 + 1, rfl⟩
  have htlt : t < p.length := by
    have hjlt : j.1 + 1 < pathBlockCount p := by omega
    have hmul := Nat.mul_lt_mul_of_pos_left hjlt (by omega : 0 < k)
    rw [blockAligned_length_eq hp]
    exact hmul
  have hedge := (exitless_boundary_weight_iff_dvd hp.1 hk (t - 1) (by omega)).2
    (by simpa [show t - 1 + 1 = t by omega] using htdvd)
  rw [← hj]
  change 2 ≤ pathEdgeWeight p (t - 1)
  rw [pathEdgeWeight_of_lt p (t - 1) (by omega)]
  simpa only [show t - 1 + 1 = t by omega] using hedge

private theorem sum_eq_two_mul_add_sub_two
    (l : List ℕ) (hl : ∀ w ∈ l, 2 ≤ w) :
    l.sum = 2 * l.length + (l.map fun w => w - 2).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
      have hw := hl w (by simp)
      have htail : ∀ x ∈ l, 2 ≤ x := by
        intro x hx
        exact hl x (by simp [hx])
      have hrec := ih htail
      simp only [List.sum_cons, List.length_cons, List.map_cons]
      omega

private theorem pathEdgeWeight_eq_one_of_not_dvd {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (i : ℕ) (hi : i + 1 < p.length) (hnot : ¬k ∣ i + 1) :
    pathEdgeWeight p i = 1 := by
  rw [pathEdgeWeight_of_lt p i hi]
  have hpos := (overlapWeight_spec
    (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩)).1
  have hnTwo : ¬2 ≤ overlapWeight
      (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) := by
    intro htwo
    exact hnot ((exitless_boundary_weight_iff_dvd hp hk i hi).1 htwo)
  omega

private theorem sum_edges_through_blocks {p : OverlapPath k}
    (hp : IsExitless p) (hk : 3 ≤ k)
    (b : ℕ) (hb : k * b ≤ p.length) :
    (∑ i ∈ Finset.range (k * b - 1), pathEdgeWeight p i) =
      (k - 1) * b +
        ∑ j ∈ Finset.range (b - 1), pathEdgeWeight p (k * (j + 1) - 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
      by_cases hbzero : b = 0
      · subst b
        have hklen : k ≤ p.length := by simpa using hb
        have hallone : ∀ i ∈ Finset.range (k - 1), pathEdgeWeight p i = 1 := by
          intro i hiRange
          have hiRange' : i < k - 1 := Finset.mem_range.mp hiRange
          have hi : i + 1 < p.length := by omega
          apply pathEdgeWeight_eq_one_of_not_dvd hp hk i hi
          intro hdvd
          have hle : k ≤ i + 1 := Nat.le_of_dvd (by omega) hdvd
          omega
        calc
          (∑ i ∈ Finset.range (k * (0 + 1) - 1), pathEdgeWeight p i) =
              ∑ _i ∈ Finset.range (k - 1), 1 := by
            apply Finset.sum_congr
            · congr 2 <;> omega
            · intro i hiRange
              exact hallone i (by simpa using hiRange)
          _ = (k - 1) * (0 + 1) +
                ∑ j ∈ Finset.range (0 + 1 - 1),
                  pathEdgeWeight p (k * (j + 1) - 1) := by simp
      · have hbpos : 0 < b := Nat.pos_of_ne_zero hbzero
        have hbrec : k * b ≤ p.length := by
          exact (Nat.mul_le_mul_left k (Nat.le_succ b)).trans hb
        have hrec := ih hbrec
        let A := k * b - 1
        have hA : A + k = k * (b + 1) - 1 := by
          dsimp [A]
          have hkbpos : 0 < k * b := Nat.mul_pos (by omega) hbpos
          rw [Nat.mul_add]
          omega
        have hboundarylt : A + 1 < p.length := by
          dsimp [A]
          have hkbpos : 0 < k * b := Nat.mul_pos (by omega) hbpos
          omega
        have htail :
            (∑ x ∈ Finset.range k, pathEdgeWeight p (A + x)) =
              pathEdgeWeight p A + (k - 1) := by
          have hkdecomp : k = 1 + (k - 1) := by omega
          have hrange : Finset.range k = Finset.range (1 + (k - 1)) := by
            congr 1
          rw [hrange, Finset.sum_range_add]
          simp only [Finset.sum_range_one, Nat.zero_add]
          have hinternal :
              (∑ x ∈ Finset.range (k - 1), pathEdgeWeight p (A + (1 + x))) =
                ∑ _x ∈ Finset.range (k - 1), 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxlt : x < k - 1 := Finset.mem_range.mp hx
            have hindex : A + (1 + x) = k * b + x := by
              dsimp [A]
              have hkbpos : 0 < k * b := Nat.mul_pos (by omega) hbpos
              omega
            rw [hindex]
            have hi : k * b + x + 1 < p.length := by
              have hmul : k * (b + 1) ≤ p.length := by simpa using hb
              rw [Nat.mul_add] at hmul
              omega
            apply pathEdgeWeight_eq_one_of_not_dvd hp hk _ hi
            intro hdvd
            obtain ⟨c, hc⟩ := hdvd
            have hlow : k * b < k * c := by omega
            have hupp : k * c < k * (b + 1) := by
              rw [← hc, Nat.mul_add]
              omega
            have hbc : b < c := (Nat.mul_lt_mul_left (by omega)).mp hlow
            have hcb : c < b + 1 := (Nat.mul_lt_mul_left (by omega)).mp hupp
            omega
          rw [hinternal]
          simp
        have hboundarySum :
            (∑ j ∈ Finset.range b, pathEdgeWeight p (k * (j + 1) - 1)) =
              (∑ j ∈ Finset.range (b - 1),
                pathEdgeWeight p (k * (j + 1) - 1)) + pathEdgeWeight p A := by
          have hbdecomp : b - 1 + 1 = b := by omega
          rw [← hbdecomp, Finset.sum_range_succ]
          congr 1
          simp only [hbdecomp]
          rfl
        rw [← hA, Finset.sum_range_add, htail, hrec]
        rw [show b + 1 - 1 = b by omega, hboundarySum]
        simp only [Nat.mul_add]
        omega

private theorem blockBoundaryWeights_sum_eq_range {p : OverlapPath k}
    (hp : IsBlockAligned p) :
    (blockBoundaryWeights p hp).sum =
      ∑ j ∈ Finset.range (pathBlockCount p - 1),
        pathEdgeWeight p (k * (j + 1) - 1) := by
  rw [blockBoundaryWeights, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range
    (fun j => pathEdgeWeight p (k * (j + 1) - 1)) (pathBlockCount p - 1)

/-- The first equality in frozen equation (1.1): the unit cost of every edge, one extra unit
at each block boundary, and the remaining excess. -/
theorem blockAligned_weight_eq_edge_count {p : OverlapPath k}
    (hp : IsBlockAligned p) (hk : 3 ≤ k) :
    p.weight = (p.length - 1) + (pathBlockCount p - 1) + pathExcess p hp := by
  let b := pathBlockCount p
  have hbpos : 0 < b := blockAligned_blockCount_pos hp
  have hlen : p.length = k * b := blockAligned_length_eq hp
  have hedge := sum_edges_through_blocks hp.1 hk b (by omega)
  have hboundary :
      (∑ j ∈ Finset.range (b - 1), pathEdgeWeight p (k * (j + 1) - 1)) =
        (blockBoundaryWeights p hp).sum := by
    exact (blockBoundaryWeights_sum_eq_range hp).symm
  have hexcess := sum_eq_two_mul_add_sub_two (blockBoundaryWeights p hp)
    (fun w hw => blockBoundaryWeights_ge_two hp hk hw)
  rw [blockBoundaryWeights_length] at hexcess
  have hmul : k * b = (k - 1) * b + b := by
    calc
      k * b = ((k - 1) + 1) * b := by congr 1 <;> omega
      _ = (k - 1) * b + b := by rw [Nat.add_mul, one_mul]
  rw [OverlapPath.weight_eq_sum_edges, hlen, hedge, hboundary, hexcess]
  change (k - 1) * b + (2 * (b - 1) + pathExcess p hp) =
    (k * b - 1) + (b - 1) + pathExcess p hp
  omega

/-- Frozen equation (1.1) in its closed block-count form. -/
theorem blockAligned_weight_eq {p : OverlapPath k}
    (hp : IsBlockAligned p) (hk : 3 ≤ k) :
    p.weight = (k + 1) * pathBlockCount p - 2 + pathExcess p hp := by
  rw [blockAligned_weight_eq_edge_count hp hk, blockAligned_length_eq hp]
  have hbpos := blockAligned_blockCount_pos hp
  have hmul : (k + 1) * pathBlockCount p =
      k * pathBlockCount p + pathBlockCount p := by
    rw [Nat.add_mul, one_mul]
  rw [hmul]
  let b := pathBlockCount p
  let x := k * b
  change (x - 1) + (b - 1) + pathExcess p hp =
    (x + b - 2) + pathExcess p hp
  have hxpos : 0 < x := Nat.mul_pos (by omega) hbpos
  omega

/-- A list of proposed block entries uses pairwise distinct rotation classes. -/
def PairwiseDistinctRotationClasses (entries : List (PermutationVertex k)) : Prop :=
  entries.Pairwise fun u v => rotationClass u ≠ rotationClass v

/-- The vertex list obtained by expanding each entry into its complete rotation block. The
index formula makes block boundaries and zero-based positions explicit. -/
noncomputable def blockSequenceVertices (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) : List (PermutationVertex k) :=
  List.ofFn fun i : Fin (k * entries.length) =>
    rotationPower (i.1 % k)
      (entries.get ⟨i.1 / k, by
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        simpa [Nat.mul_comm] using i.2⟩)

@[simp]
theorem blockSequenceVertices_length (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) :
    (blockSequenceVertices hk entries).length = k * entries.length := by
  simp [blockSequenceVertices]

theorem blockSequenceVertices_getElem (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) (i : ℕ) (hi : i < k * entries.length) :
    (blockSequenceVertices hk entries)[i]'(by simpa using hi) =
      rotationPower (i % k)
        (entries.get ⟨i / k, by
          apply (Nat.div_lt_iff_lt_mul (by omega)).2
          simpa [Nat.mul_comm] using hi⟩) := by
  simp [blockSequenceVertices]

/-- Pairwise distinct entry classes make the expanded complete-block list duplicate-free. -/
theorem blockSequenceVertices_nodup (hk : 1 ≤ k)
    {entries : List (PermutationVertex k)}
    (hclasses : PairwiseDistinctRotationClasses entries) :
    (blockSequenceVertices hk entries).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [blockSequenceVertices_length] at hi hj
  rw [blockSequenceVertices_getElem hk entries i hi,
    blockSequenceVertices_getElem hk entries j hj]
  intro hrot
  have hiq : i / k < entries.length := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    simpa [Nat.mul_comm] using hi
  have hjq : j / k < entries.length := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    simpa [Nat.mul_comm] using hj
  have hqle : i / k ≤ j / k := Nat.div_le_div_right (Nat.le_of_lt hij)
  by_cases hq : i / k = j / k
  · have hentry : entries.get ⟨i / k, hiq⟩ = entries.get ⟨j / k, hjq⟩ := by
      apply congrArg entries.get
      apply Fin.ext
      exact hq
    rw [hentry] at hrot
    have hrem := rotationPower_injective_on_range hk (entries.get ⟨j / k, hjq⟩)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hrot
    have hirepr := Nat.div_add_mod i k
    have hjrepr := Nat.div_add_mod j k
    have hijEq : i = j := by
      calc
        i = k * (i / k) + i % k := hirepr.symm
        _ = k * (j / k) + j % k := by rw [hq, hrem]
        _ = j := hjrepr
    exact (Nat.ne_of_lt hij) hijEq
  · have hqlt : i / k < j / k := lt_of_le_of_ne hqle hq
    have hdistinct := (List.pairwise_iff_getElem.mp hclasses)
      (i / k) (j / k) hiq hjq hqlt
    apply hdistinct
    calc
      rotationClass (entries.get ⟨i / k, hiq⟩) =
          rotationClass (rotationPower (i % k) (entries.get ⟨i / k, hiq⟩)) :=
        (rotationClass_rotationPower hk _ _).symm
      _ = rotationClass (rotationPower (j % k) (entries.get ⟨j / k, hjq⟩)) :=
        congrArg rotationClass hrot
      _ = rotationClass (entries.get ⟨j / k, hjq⟩) :=
        rotationClass_rotationPower hk _ _

/-- Expand a nonempty list of pairwise distinct block entries into an overlap path. -/
noncomputable def blockSequencePath (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries) : OverlapPath k where
  vertices := blockSequenceVertices hk entries
  nodup := blockSequenceVertices_nodup hk hclasses
  nonempty := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [blockSequenceVertices_length, List.length_nil] at hlen
    have hentries : 0 < entries.length := by
      cases entries with
      | nil => exact (hne rfl).elim
      | cons => simp
    have : 0 < k * entries.length := Nat.mul_pos (by omega) hentries
    omega

@[simp]
theorem blockSequencePath_vertices (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries) :
    (blockSequencePath hk entries hne hclasses).vertices =
      blockSequenceVertices hk entries := rfl

@[simp]
theorem blockSequencePath_length (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries) :
    (blockSequencePath hk entries hne hclasses).length = k * entries.length := by
  simp [OverlapPath.length]

/-- An overlap path is exactly a nonempty sequence of complete rotation blocks. -/
def IsCompleteBlockSequence (p : OverlapPath k) (hk : 1 ≤ k) : Prop :=
  ∃ entries : List (PermutationVertex k),
    entries ≠ [] ∧ p.vertices = blockSequenceVertices hk entries

theorem blockSequencePath_isCompleteBlockSequence (hk : 1 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries) :
    IsCompleteBlockSequence (blockSequencePath hk entries hne hclasses) hk :=
  ⟨entries, hne, rfl⟩

private theorem completeBlockSequence_vertex {p : OverlapPath k} (hk : 1 ≤ k)
    {entries : List (PermutationVertex k)}
    (hvertices : p.vertices = blockSequenceVertices hk entries)
    (i : ℕ) (hi : i < p.length) :
    p.vertex ⟨i, hi⟩ = rotationPower (i % k)
      (entries.get ⟨i / k, by
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        have hi' : i < k * entries.length := by
          simpa [OverlapPath.length, hvertices] using hi
        simpa [Nat.mul_comm] using hi'⟩) := by
  have hi' : i < k * entries.length := by
    simpa [OverlapPath.length, hvertices] using hi
  simpa [OverlapPath.vertex, OverlapPath.length, hvertices] using
    blockSequenceVertices_getElem hk entries i hi'

private theorem completeBlockSequence_next_eq_rotation {p : OverlapPath k}
    (hk : 1 ≤ k) {entries : List (PermutationVertex k)}
    (hvertices : p.vertices = blockSequenceVertices hk entries)
    (i : ℕ) (hi : i + 1 < p.length) (hnot : ¬k ∣ i + 1) :
    p.vertex ⟨i + 1, hi⟩ = rotation (p.vertex ⟨i, by omega⟩) := by
  have hdiv : (i + 1) / k = i / k := by
    rw [Nat.succ_div, if_neg hnot]
    simp
  have hirepr := Nat.div_add_mod i k
  have hnrepr := Nat.div_add_mod (i + 1) k
  have hmod : (i + 1) % k = i % k + 1 := by
    rw [hdiv] at hnrepr
    omega
  have hcurrent := completeBlockSequence_vertex hk hvertices i (by omega)
  have hnext := completeBlockSequence_vertex hk hvertices (i + 1) hi
  have hentry :
      entries.get ⟨(i + 1) / k, by
        have hi' : i + 1 < k * entries.length := by
          simpa [OverlapPath.length, hvertices] using hi
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        simpa [Nat.mul_comm] using hi'⟩ =
      entries.get ⟨i / k, by
        have hi' : i < k * entries.length := by
          simpa [OverlapPath.length, hvertices] using (show i < p.length by omega)
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        simpa [Nat.mul_comm] using hi'⟩ := by
    apply congrArg entries.get
    apply Fin.ext
    exact hdiv
  calc
    p.vertex ⟨i + 1, hi⟩ = rotationPower ((i + 1) % k)
        (entries.get ⟨(i + 1) / k, by
          have hi' : i + 1 < k * entries.length := by
            simpa [OverlapPath.length, hvertices] using hi
          apply (Nat.div_lt_iff_lt_mul (by omega)).2
          simpa [Nat.mul_comm] using hi'⟩) := hnext
    _ = rotationPower (i % k + 1)
        (entries.get ⟨i / k, by
          have hi' : i < k * entries.length := by
            simpa [OverlapPath.length, hvertices] using (show i < p.length by omega)
          apply (Nat.div_lt_iff_lt_mul (by omega)).2
          simpa [Nat.mul_comm] using hi'⟩) := by rw [hmod, hentry]
    _ = rotation (p.vertex ⟨i, by omega⟩) := by
      rw [hcurrent, rotation_rotationPower hk]

private theorem completeBlockSequence_rotation_mem_take_of_dvd {p : OverlapPath k}
    (hk : 1 ≤ k) {entries : List (PermutationVertex k)}
    (hvertices : p.vertices = blockSequenceVertices hk entries)
    (i : ℕ) (hi : i < p.length) (hdvd : k ∣ i + 1) :
    rotation (p.vertex ⟨i, hi⟩) ∈ p.vertices.take (i + 1) := by
  have hiK : i < k * entries.length := by
    simpa [OverlapPath.length, hvertices] using hi
  have hiq : i / k < entries.length := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    simpa [Nat.mul_comm] using hiK
  have hcurrent := completeBlockSequence_vertex hk hvertices i hi
  have hnmod : (i + 1) % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hdiv : (i + 1) / k = i / k + 1 := by
    rw [Nat.succ_div, if_pos hdvd]
  have hirepr := Nat.div_add_mod i k
  have hnrepr := Nat.div_add_mod (i + 1) k
  have hrem : i % k + 1 = k := by
    rw [hnmod, hdiv, Nat.mul_add] at hnrepr
    omega
  have hrotation : rotation (p.vertex ⟨i, hi⟩) = entries.get ⟨i / k, hiq⟩ := by
    calc
      rotation (p.vertex ⟨i, hi⟩) =
          rotation (rotationPower (i % k) (entries.get ⟨i / k, hiq⟩)) :=
        congrArg rotation hcurrent
      _ = rotationPower (i % k + 1) (entries.get ⟨i / k, hiq⟩) :=
        rotation_rotationPower hk _ _
      _ = rotationPower k (entries.get ⟨i / k, hiq⟩) := by rw [hrem]
      _ = entries.get ⟨i / k, hiq⟩ := rotationPower_length hk _
  have hstartle : k * (i / k) ≤ i := Nat.mul_div_le i k
  have hstartP : k * (i / k) < p.length := hstartle.trans_lt hi
  have hstart := completeBlockSequence_vertex hk hvertices (k * (i / k)) hstartP
  have hstartEntry :
      entries.get ⟨k * (i / k) / k, by
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        have hsK : k * (i / k) < k * entries.length := by
          simpa [OverlapPath.length, hvertices] using hstartP
        simpa [Nat.mul_comm] using hsK⟩ = entries.get ⟨i / k, hiq⟩ := by
    apply congrArg entries.get
    apply Fin.ext
    exact Nat.mul_div_cancel_left _ (by omega)
  have hstartvertex :
      p.vertex ⟨k * (i / k), hstartP⟩ = entries.get ⟨i / k, hiq⟩ := by
    calc
      p.vertex ⟨k * (i / k), hstartP⟩ = rotationPower (k * (i / k) % k)
          (entries.get ⟨k * (i / k) / k, by
            apply (Nat.div_lt_iff_lt_mul (by omega)).2
            have hsK : k * (i / k) < k * entries.length := by
              simpa [OverlapPath.length, hvertices] using hstartP
            simpa [Nat.mul_comm] using hsK⟩) := hstart
      _ = rotationPower 0
          (entries.get ⟨k * (i / k) / k, by
            apply (Nat.div_lt_iff_lt_mul (by omega)).2
            have hsK : k * (i / k) < k * entries.length := by
              simpa [OverlapPath.length, hvertices] using hstartP
            simpa [Nat.mul_comm] using hsK⟩) := by rw [Nat.mul_mod_right]
      _ = rotationPower 0 (entries.get ⟨i / k, hiq⟩) := congrArg _ hstartEntry
      _ = entries.get ⟨i / k, hiq⟩ := rotationPower_zero _
  apply List.mem_take_iff_getElem.mpr
  refine ⟨k * (i / k), ?_, ?_⟩
  · apply lt_min
    · omega
    · simpa [OverlapPath.length] using hstartP
  · change p.vertex ⟨k * (i / k), hstartP⟩ = rotation (p.vertex ⟨i, hi⟩)
    exact hstartvertex.trans hrotation.symm

/-- Block locality at a single jump: leaving an exit cannot be an early exit once the entry
of that completed block is in the visited prefix. -/
theorem blockExit_jump_not_early (hk : 1 ≤ k) {p : OverlapPath k}
    (i : ℕ) (hi : i + 1 < p.length) {u : PermutationVertex k}
    (hsource : p.vertex ⟨i, by omega⟩ = blockExit u)
    (hentry : u ∈ p.vertices.take (i + 1)) :
    ¬(1 < overlapWeight (p.vertex ⟨i, by omega⟩) (p.vertex ⟨i + 1, hi⟩) ∧
      rotation (p.vertex ⟨i, by omega⟩) ∉ p.vertices.take (i + 1)) := by
  rintro ⟨_hheavy, hnot⟩
  apply hnot
  rw [hsource, rotation_blockExit hk]
  exact hentry

/-- Frozen block locality: every path made from complete blocks is strongly exitless. The
path's built-in vertex distinctness ensures that its block entries lie in pairwise distinct
rotation classes; internal edges follow rotation and each boundary rotates back to the entry
of the block just completed. -/
theorem completeBlockSequence_stronglyExitless {p : OverlapPath k}
    (hk : 3 ≤ k) (hp : IsCompleteBlockSequence p (by omega)) :
    IsStronglyExitless p := by
  obtain ⟨entries, _hne, hvertices⟩ := hp
  have hlen : p.length = k * entries.length := by
    simp [OverlapPath.length, hvertices]
  constructor
  · rintro ⟨i, hi, hheavy, hnotvisited⟩
    by_cases hdvd : k ∣ i + 1
    · exact hnotvisited
        (completeBlockSequence_rotation_mem_take_of_dvd (by omega) hvertices i (by omega) hdvd)
    · have hnext := completeBlockSequence_next_eq_rotation (by omega) hvertices i hi hdvd
      have hne : p.vertex ⟨i, by omega⟩ ≠ p.vertex ⟨i + 1, hi⟩ :=
        p.vertex_ne_of_ne (by simp)
      have hone : overlapWeight (p.vertex ⟨i, by omega⟩)
          (p.vertex ⟨i + 1, hi⟩) = 1 :=
        (unique_weight_one_successor _ _ hk hne).2 hnext
      omega
  · let i := p.length - 1
    have hi : i < p.length := by
      dsimp [i]
      have := p.length_pos
      omega
    have hilength : i + 1 = p.length := by
      dsimp [i]
      omega
    have hdvd : k ∣ i + 1 := by
      rw [hilength, hlen]
      exact ⟨entries.length, rfl⟩
    have hmem := completeBlockSequence_rotation_mem_take_of_dvd
      (by omega) hvertices i hi hdvd
    have htake : p.vertices.take (i + 1) = p.vertices := by
      rw [hilength, OverlapPath.length, List.take_length]
    rw [htake] at hmem
    have hlast : p.vertex ⟨i, hi⟩ = p.vertices.getLast p.nonempty := by
      simpa [i, OverlapPath.vertex, OverlapPath.length] using
        (List.getLast_eq_getElem p.nonempty).symm
    rw [← hlast]
    exact hmem

/-- A sequence of complete blocks in pairwise distinct rotation classes is strongly
exitless. -/
theorem blockSequencePath_stronglyExitless (hk : 3 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries) :
    IsStronglyExitless (blockSequencePath (by omega) entries hne hclasses) := by
  apply completeBlockSequence_stronglyExitless hk
  exact blockSequencePath_isCompleteBlockSequence (by omega) entries hne hclasses

/-- Consecutive complete blocks in the constructed path are joined by genuine boundary
edges, hence by weights at least two. -/
theorem blockSequencePath_boundary_weight_ge_two (hk : 3 ≤ k)
    (entries : List (PermutationVertex k)) (hne : entries ≠ [])
    (hclasses : PairwiseDistinctRotationClasses entries)
    (j : ℕ) (hj : j + 1 < entries.length) :
    2 ≤ pathEdgeWeight (blockSequencePath (by omega) entries hne hclasses)
      (k * (j + 1) - 1) := by
  let p := blockSequencePath (by omega : 1 ≤ k) entries hne hclasses
  let t := k * (j + 1)
  have hpstrong : IsStronglyExitless p := by
    exact blockSequencePath_stronglyExitless hk entries hne hclasses
  have hlen : p.length = k * entries.length := by
    exact blockSequencePath_length (by omega) entries hne hclasses
  have htpos : 0 < t := by dsimp [t]; positivity
  have htlt : t < p.length := by
    dsimp [t]
    rw [hlen]
    exact Nat.mul_lt_mul_of_pos_left hj (by omega)
  have htdiv : k ∣ t := ⟨j + 1, rfl⟩
  have hedge := (exitless_boundary_weight_iff_dvd hpstrong.1 hk (t - 1) (by omega)).2
    (by simpa [show t - 1 + 1 = t by omega] using htdiv)
  change 2 ≤ pathEdgeWeight p (t - 1)
  rw [pathEdgeWeight_of_lt p (t - 1) (by omega)]
  simpa only [show t - 1 + 1 = t by omega] using hedge

/-- Pairwise distinct rotation classes are preserved when taking a contiguous list stretch. -/
theorem pairwiseDistinctRotationClasses_drop_take
    {entries : List (PermutationVertex k)}
    (hclasses : PairwiseDistinctRotationClasses entries) (start count : ℕ) :
    PairwiseDistinctRotationClasses ((entries.drop start).take count) := by
  exact hclasses.drop.take

/-- Every nonempty contiguous stretch of consecutive complete blocks is again a strongly
exitless path, with exactly `k * count` vertices. -/
theorem contiguousBlockStretch_stronglyExitless (hk : 3 ≤ k)
    (entries : List (PermutationVertex k))
    (hclasses : PairwiseDistinctRotationClasses entries)
    (start count : ℕ) (hcount : 0 < count)
    (hfit : start + count ≤ entries.length) :
    ∃ q : OverlapPath k,
      q.vertices = blockSequenceVertices (by omega) ((entries.drop start).take count) ∧
      q.length = k * count ∧ IsStronglyExitless q := by
  let stretch := (entries.drop start).take count
  have hstretchLength : stretch.length = count := by
    dsimp [stretch]
    rw [List.length_take, List.length_drop]
    omega
  have hstretch : stretch ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    rw [hstretchLength] at this
    simp at this
    omega
  have hstretchClasses : PairwiseDistinctRotationClasses stretch := by
    dsimp [stretch]
    exact pairwiseDistinctRotationClasses_drop_take hclasses start count
  let q := blockSequencePath (by omega : 1 ≤ k) stretch hstretch hstretchClasses
  refine ⟨q, rfl, ?_, ?_⟩
  · rw [blockSequencePath_length, hstretchLength]
  · exact blockSequencePath_stronglyExitless hk stretch hstretch hstretchClasses

end SuperpermutationLowerBound
