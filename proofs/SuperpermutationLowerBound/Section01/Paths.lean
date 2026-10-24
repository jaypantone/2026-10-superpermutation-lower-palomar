module

public import SuperpermutationLowerBound.Section01.Overlap
public import Mathlib.Data.Finset.Sort

@[expose] public section

-- Preserve private helpers used by exposed minimum definitions during this port.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Superpermutation words, finite Hamiltonian paths, their attained minima, and the
word/path bridge of frozen Proposition 1.1. -/

open PermutationVertex

variable {k : ℕ}

/-- A word is a `k`-superpermutation when every permutation vertex occurs as a contiguous
factor. -/
def IsSuperpermutation (W : Word k) : Prop :=
  ∀ v : PermutationVertex k, v.1 <:+: W

/-- Concatenating an enumeration of all permutation vertices gives a superpermutation. -/
noncomputable def concatenatedPermutationWord (k : ℕ) : Word k :=
  ((Finset.univ : Finset (PermutationVertex k)).toList.map
    (fun v : PermutationVertex k => v.1)).flatten

private theorem member_infix_flatten_vertices {l : List (PermutationVertex k)}
    {v : PermutationVertex k} (hv : v ∈ l) :
    v.1 <:+: (l.map (fun u : PermutationVertex k => u.1)).flatten := by
  induction l with
  | nil => simp at hv
  | cons u l ih =>
      simp only [List.mem_cons] at hv
      simp only [List.map_cons, List.flatten_cons]
      rcases hv with rfl | hv
      · exact List.infix_append_left
      · exact (ih hv).trans List.infix_append_right

/-- Superpermutation words exist for every alphabet size. -/
theorem superpermutation_exists (k : ℕ) :
    ∃ W : Word k, IsSuperpermutation W := by
  classical
  refine ⟨concatenatedPermutationWord k, ?_⟩
  intro v
  exact member_infix_flatten_vertices (Finset.mem_toList.mpr (Finset.mem_univ v))

private theorem superpermutationLength_exists (k : ℕ) :
    ∃ n : ℕ, ∃ W : Word k, IsSuperpermutation W ∧ W.length = n := by
  obtain ⟨W, hW⟩ := superpermutation_exists k
  exact ⟨W.length, W, hW, rfl⟩

/-- `S(k)`: the least length of a `k`-superpermutation. -/
noncomputable def shortestSuperpermutationLength (k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (superpermutationLength_exists k)

/-- The minimum defining `S(k)` is attained by an actual superpermutation word. -/
theorem shortestSuperpermutationLength_attained (k : ℕ) :
    ∃ W : Word k,
      IsSuperpermutation W ∧ W.length = shortestSuperpermutationLength k := by
  classical
  simpa [shortestSuperpermutationLength] using
    (Nat.find_spec (superpermutationLength_exists k))

/-- The defining minimum `S(k)` is no larger than the length of any superpermutation. -/
theorem shortestSuperpermutationLength_le (W : Word k) (hW : IsSuperpermutation W) :
    shortestSuperpermutationLength k ≤ W.length := by
  classical
  simpa [shortestSuperpermutationLength] using
    (Nat.find_min' (superpermutationLength_exists k) ⟨W, hW, rfl⟩)

/-- Every `k`-superpermutation has length at least `k`. -/
theorem superpermutation_length_ge (W : Word k) (hW : IsSuperpermutation W) :
    k ≤ W.length := by
  let v : PermutationVertex k := ⟨alphabetWord k, List.Perm.refl _⟩
  obtain ⟨before, after, hfactor⟩ := hW v
  have hlen := congrArg List.length hfactor
  simp [PermutationVertex.length] at hlen
  omega

/-- A nonempty path in the loopless overlap digraph, represented by its distinct vertices. -/
structure OverlapPath (k : ℕ) where
  vertices : List (PermutationVertex k)
  nodup : vertices.Nodup
  nonempty : vertices ≠ []

namespace OverlapPath

@[ext]
theorem ext {p q : OverlapPath k} (h : p.vertices = q.vertices) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The number of vertices of a path. -/
def length (p : OverlapPath k) : ℕ := p.vertices.length

/-- The vertex at a zero-based position. -/
def vertex (p : OverlapPath k) (i : Fin p.length) : PermutationVertex k :=
  p.vertices.get i

/-- The vertex set of a path. -/
noncomputable def vertexSet (p : OverlapPath k) : Finset (PermutationVertex k) := by
  classical
  exact p.vertices.toFinset

theorem length_pos (p : OverlapPath k) : 0 < p.length := by
  rcases h : p.vertices with _ | ⟨v, rest⟩
  · exact (p.nonempty h).elim
  · simp [length, h]

theorem vertex_mem (p : OverlapPath k) (i : Fin p.length) :
    p.vertex i ∈ p.vertices := by
  exact List.get_mem _ _

/-- Distinct path positions contain distinct vertices. -/
theorem vertex_ne_of_ne (p : OverlapPath k) {i j : Fin p.length} (hij : i ≠ j) :
    p.vertex i ≠ p.vertex j := by
  exact fun h => hij (p.nodup.get_inj_iff.mp h)

/-- Every pair of consecutive path vertices determines a genuine loopless overlap edge. -/
def edgeAt (p : OverlapPath k) (i : ℕ) (hi : i + 1 < p.length) :
    DirectedOverlapEdge k where
  source := p.vertex ⟨i, by omega⟩
  target := p.vertex ⟨i + 1, hi⟩
  ne := p.vertex_ne_of_ne (by simp)

end OverlapPath

/-- A Hamiltonian path is a duplicate-free list containing every permutation vertex. -/
structure HamiltonianPath (k : ℕ) where
  vertices : List (PermutationVertex k)
  nodup : vertices.Nodup
  complete : ∀ v : PermutationVertex k, v ∈ vertices

namespace HamiltonianPath

@[ext]
theorem ext {P Q : HamiltonianPath k} (h : P.vertices = Q.vertices) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A Hamiltonian path, viewed as a nonempty path in the loopless overlap digraph. -/
noncomputable def toOverlapPath (P : HamiltonianPath k) : OverlapPath k where
  vertices := P.vertices
  nodup := P.nodup
  nonempty := by
    let v : PermutationVertex k := ⟨alphabetWord k, List.Perm.refl _⟩
    exact fun h => by simpa [h] using P.complete v

@[simp]
theorem toOverlapPath_vertices (P : HamiltonianPath k) :
    P.toOverlapPath.vertices = P.vertices := rfl

/-- Every Hamiltonian list is a permutation of the canonical finite vertex list. -/
theorem perm_univ (P : HamiltonianPath k) :
    P.vertices.Perm (Finset.univ : Finset (PermutationVertex k)).toList := by
  classical
  rw [List.perm_ext_iff_of_nodup P.nodup (Finset.nodup_toList _)]
  intro v
  simp [P.complete]

end HamiltonianPath

private noncomputable def allHamiltonianPaths (k : ℕ) : List (HamiltonianPath k) :=
  ((Finset.univ : Finset (PermutationVertex k)).toList.permutations.attach.map fun l =>
    { vertices := l.1
      nodup := (List.Perm.nodup_iff (List.mem_permutations.mp l.2)).mpr
        (Finset.nodup_toList _)
      complete := fun v => by
        have hp := List.mem_permutations.mp l.2
        exact hp.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ v)) })

/-- Hamiltonian paths form a finite type. -/
noncomputable instance (k : ℕ) : Fintype (HamiltonianPath k) := by
  classical
  apply Fintype.ofList (allHamiltonianPaths k)
  intro P
  unfold allHamiltonianPaths
  apply List.mem_map.mpr
  let l : {l // l ∈ (Finset.univ : Finset (PermutationVertex k)).toList.permutations} :=
    ⟨P.vertices, List.mem_permutations.mpr P.perm_univ⟩
  refine ⟨l, List.mem_attach _ _, ?_⟩
  apply HamiltonianPath.ext
  rfl

/-- The canonical finite vertex list is itself a Hamiltonian path. -/
noncomputable def canonicalHamiltonianPath (k : ℕ) : HamiltonianPath k where
  vertices := (Finset.univ : Finset (PermutationVertex k)).toList
  nodup := Finset.nodup_toList _
  complete := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)

/-- Hamiltonian paths are nonempty as a type for every alphabet size. -/
theorem hamiltonianPath_nonempty (k : ℕ) : Nonempty (HamiltonianPath k) :=
  ⟨canonicalHamiltonianPath k⟩

/-- The sum of overlap weights along a vertex list. -/
noncomputable def vertexListWeight : List (PermutationVertex k) → ℕ
  | [] | [_] => 0
  | u :: v :: rest => overlapWeight u v + vertexListWeight (v :: rest)

/-- The weight of an overlap path. -/
noncomputable def OverlapPath.weight (p : OverlapPath k) : ℕ :=
  vertexListWeight p.vertices

/-- The weight of a Hamiltonian path. -/
noncomputable def HamiltonianPath.weight (P : HamiltonianPath k) : ℕ :=
  vertexListWeight P.vertices

private theorem hamiltonianPathWeight_exists (k : ℕ) :
    ∃ n : ℕ, ∃ P : HamiltonianPath k, P.weight = n :=
  ⟨(canonicalHamiltonianPath k).weight, canonicalHamiltonianPath k, rfl⟩

/-- `L(k)`: the least weight of a Hamiltonian path in the loopless overlap digraph. -/
noncomputable def minimumHamiltonianPathWeight (k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (hamiltonianPathWeight_exists k)

/-- The minimum defining `L(k)` is attained by a Hamiltonian path. -/
theorem minimumHamiltonianPathWeight_attained (k : ℕ) :
    ∃ P : HamiltonianPath k, P.weight = minimumHamiltonianPathWeight k := by
  classical
  simpa [minimumHamiltonianPathWeight] using
    (Nat.find_spec (hamiltonianPathWeight_exists k))

/-- The minimum `L(k)` is no larger than the weight of any Hamiltonian path. -/
theorem minimumHamiltonianPathWeight_le (P : HamiltonianPath k) :
    minimumHamiltonianPathWeight k ≤ P.weight := by
  classical
  simpa [minimumHamiltonianPathWeight] using
    (Nat.find_min' (hamiltonianPathWeight_exists k) ⟨P, rfl⟩)

/-- Merge a vertex list using the least suffix-prefix overlap at every step. -/
noncomputable def mergedVertexWord : List (PermutationVertex k) → Word k
  | [] => []
  | [u] => u.1
  | u :: v :: rest =>
      u.1.take (overlapWeight u v) ++ mergedVertexWord (v :: rest)

private theorem head_prefix_mergedVertexWord (hk : 1 ≤ k)
    (u : PermutationVertex k) (rest : List (PermutationVertex k)) :
    u.1 <+: mergedVertexWord (u :: rest) := by
  induction rest generalizing u with
  | nil => exact ⟨[], by simp [mergedVertexWord]⟩
  | cons v rest ih =>
      let t := overlapWeight u v
      have htk : t ≤ k := overlapWeight_le_length hk u v
      have hov : u.1.drop t = v.1.take (k - t) := (overlapWeight_spec u v).2
      obtain ⟨tail, htail⟩ := ih v
      refine ⟨v.1.drop (k - t) ++ tail, ?_⟩
      simp only [mergedVertexWord]
      rw [← htail]
      calc
        u.1 ++ (v.1.drop (k - t) ++ tail) =
            (u.1.take t ++ u.1.drop t) ++ (v.1.drop (k - t) ++ tail) := by
              rw [u.1.take_append_drop]
        _ = u.1.take t ++
            (v.1.take (k - t) ++ v.1.drop (k - t)) ++ tail := by
              rw [hov]
              simp only [List.append_assoc]
        _ = u.1.take t ++ (v.1 ++ tail) := by
          rw [v.1.take_append_drop]
          simp only [List.append_assoc]

private theorem member_infix_mergedVertexWord (hk : 1 ≤ k)
    {l : List (PermutationVertex k)} {v : PermutationVertex k} (hv : v ∈ l) :
    v.1 <:+: mergedVertexWord l := by
  induction l with
  | nil => simp at hv
  | cons u l ih =>
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact (head_prefix_mergedVertexWord hk v l).isInfix
      · rcases l with _ | ⟨w, rest⟩
        · simp at hv
        · have hsuffix : mergedVertexWord (w :: rest) <:+
              mergedVertexWord (u :: w :: rest) := by
            exact ⟨u.1.take (overlapWeight u w), rfl⟩
          exact (ih (by simpa using hv)).trans hsuffix.isInfix

/-- The merged word of a Hamiltonian path is a genuine superpermutation. -/
theorem mergedHamiltonianWord_isSuperpermutation (P : HamiltonianPath k) (hk : 1 ≤ k) :
    IsSuperpermutation (mergedVertexWord P.vertices) := by
  intro v
  exact member_infix_mergedVertexWord hk (P.complete v)

/-- Exact length bookkeeping for the word obtained by merging a nonempty vertex list. -/
theorem mergedVertexWord_length (l : List (PermutationVertex k)) (hk : 1 ≤ k)
    (hl : l ≠ []) :
    (mergedVertexWord l).length = k + vertexListWeight l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons u l ih =>
      rcases l with _ | ⟨v, rest⟩
      · simp [mergedVertexWord, vertexListWeight, PermutationVertex.length]
      · have htail : v :: rest ≠ [] := by simp
        have hi := ih htail
        have htk : overlapWeight u v ≤ k := overlapWeight_le_length hk u v
        simp only [mergedVertexWord, vertexListWeight, List.length_append,
          List.length_take, PermutationVertex.length, Nat.min_eq_left htk]
        omega

/-- The merged word of a Hamiltonian path has length `k + w(P)`. -/
theorem mergedHamiltonianWord_length (P : HamiltonianPath k) (hk : 1 ≤ k) :
    (mergedVertexWord P.vertices).length = k + P.weight := by
  apply mergedVertexWord_length P.vertices hk
  exact P.toOverlapPath.nonempty

private noncomputable def chosenOccurrencePrefix (W : Word k)
    (hW : IsSuperpermutation W) (v : PermutationVertex k) : Word k :=
  Classical.choose (hW v)

private noncomputable def chosenOccurrenceSuffix (W : Word k)
    (hW : IsSuperpermutation W) (v : PermutationVertex k) : Word k :=
  Classical.choose (Classical.choose_spec (hW v))

private theorem chosenOccurrence_eq (W : Word k) (hW : IsSuperpermutation W)
    (v : PermutationVertex k) :
    chosenOccurrencePrefix W hW v ++ v.1 ++ chosenOccurrenceSuffix W hW v = W :=
  Classical.choose_spec (Classical.choose_spec (hW v))

private noncomputable def chosenOccurrenceStart (W : Word k)
    (hW : IsSuperpermutation W) (v : PermutationVertex k) : ℕ :=
  (chosenOccurrencePrefix W hW v).length

private theorem chosenOccurrence_at (W : Word k) (hW : IsSuperpermutation W)
    (v : PermutationVertex k) :
    (W.drop (chosenOccurrenceStart W hW v)).take k = v.1 := by
  let before := chosenOccurrencePrefix W hW v
  let after := chosenOccurrenceSuffix W hW v
  have heq : before ++ v.1 ++ after = W := chosenOccurrence_eq W hW v
  change (W.drop before.length).take k = v.1
  calc
    (W.drop before.length).take k =
        ((before ++ v.1 ++ after).drop before.length).take k :=
      congrArg (fun X => (X.drop before.length).take k) heq.symm
    _ = v.1 := by simp [PermutationVertex.length]

private theorem chosenOccurrenceStart_le (W : Word k) (hW : IsSuperpermutation W)
    (v : PermutationVertex k) :
    chosenOccurrenceStart W hW v ≤ W.length - k := by
  let before := chosenOccurrencePrefix W hW v
  let after := chosenOccurrenceSuffix W hW v
  have heq : before ++ v.1 ++ after = W := chosenOccurrence_eq W hW v
  have hlen : before.length + (k + after.length) = W.length := by
    simpa [PermutationVertex.length] using congrArg List.length heq
  change before.length ≤ W.length - k
  omega

private theorem chosenOccurrenceStart_injective (W : Word k) (hW : IsSuperpermutation W) :
    Function.Injective (chosenOccurrenceStart W hW) := by
  intro u v huv
  apply PermutationVertex.ext
  rw [← chosenOccurrence_at W hW u, ← chosenOccurrence_at W hW v, huv]

private theorem overlapWeight_le_chosenStart_gap (W : Word k)
    (hW : IsSuperpermutation W) (hk : 1 ≤ k) {u v : PermutationVertex k}
    (huv : chosenOccurrenceStart W hW u < chosenOccurrenceStart W hW v) :
    overlapWeight u v ≤ chosenOccurrenceStart W hW v - chosenOccurrenceStart W hW u := by
  let su := chosenOccurrenceStart W hW u
  let sv := chosenOccurrenceStart W hW v
  let d := sv - su
  have hsud : su + d = sv := by dsimp [d]; omega
  have hdpos : 1 ≤ d := by dsimp [d, su, sv]; omega
  by_cases hdk : d < k
  · apply overlapWeight_min u v hdpos
    unfold OverlapsAt
    calc
      u.1.drop d = ((W.drop su).take k).drop d := by
        rw [chosenOccurrence_at W hW u]
      _ = ((W.drop su).drop d).take (k - d) := List.drop_take
      _ = (W.drop (su + d)).take (k - d) := by rw [List.drop_drop]
      _ = (W.drop sv).take (k - d) := by rw [hsud]
      _ = ((W.drop sv).take k).take (k - d) := by
        simp only [List.take_take, Nat.min_eq_left (Nat.sub_le k d)]
      _ = v.1.take (k - d) := by rw [chosenOccurrence_at W hW v]
  · exact (overlapWeight_le_length hk u v).trans (by omega)

private noncomputable def adjacentGaps (f : PermutationVertex k → ℕ) :
    List (PermutationVertex k) → ℕ
  | [] | [_] => 0
  | u :: v :: rest => f v - f u + adjacentGaps f (v :: rest)

private theorem vertexListWeight_le_adjacentGaps (W : Word k)
    (hW : IsSuperpermutation W) (hk : 1 ≤ k)
    (l : List (PermutationVertex k))
    (hsorted : l.Pairwise fun u v =>
      chosenOccurrenceStart W hW u < chosenOccurrenceStart W hW v) :
    vertexListWeight l ≤ adjacentGaps (chosenOccurrenceStart W hW) l := by
  induction l with
  | nil => simp [vertexListWeight, adjacentGaps]
  | cons u l ih =>
      rcases l with _ | ⟨v, rest⟩
      · simp [vertexListWeight, adjacentGaps]
      · have huv := (List.pairwise_cons.mp hsorted).1 v (by simp)
        have htail := (List.pairwise_cons.mp hsorted).2
        have hedge := overlapWeight_le_chosenStart_gap W hW hk huv
        have hrest := ih htail
        simp only [vertexListWeight, adjacentGaps]
        omega

private theorem head_add_adjacentGaps_le (f : PermutationVertex k → ℕ)
    (B : ℕ) (u : PermutationVertex k) (l : List (PermutationVertex k))
    (hsorted : (u :: l).Pairwise fun x y => f x < f y)
    (hbound : ∀ x ∈ u :: l, f x ≤ B) :
    f u + adjacentGaps f (u :: l) ≤ B := by
  induction l generalizing u with
  | nil => simpa [adjacentGaps] using hbound u (by simp)
  | cons v rest ih =>
      have huv := (List.pairwise_cons.mp hsorted).1 v (by simp)
      have htail := (List.pairwise_cons.mp hsorted).2
      have hboundtail : ∀ x ∈ v :: rest, f x ≤ B := by
        intro x hx
        exact hbound x (by simp [hx])
      have hrec := ih v htail hboundtail
      simp only [adjacentGaps]
      omega

/-- Chosen occurrences in a superpermutation, ordered by their strictly increasing starts,
form a Hamiltonian path whose weight is at most the available start-position span. -/
theorem superpermutation_yields_hamiltonianPath (W : Word k)
    (hW : IsSuperpermutation W) (hk : 1 ≤ k) :
    ∃ P : HamiltonianPath k, P.weight ≤ W.length - k := by
  classical
  let start := chosenOccurrenceStart W hW
  let r : PermutationVertex k → PermutationVertex k → Prop :=
    fun u v => start u ≤ start v
  letI : DecidableRel r := Classical.decRel r
  letI : IsTrans (PermutationVertex k) r :=
    ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ hab hba => chosenOccurrenceStart_injective W hW
      (Nat.le_antisymm hab hba)⟩
  letI : Std.Total r := ⟨fun u v => Nat.le_total (start u) (start v)⟩
  let l := (Finset.univ : Finset (PermutationVertex k)).sort r
  have hnodup : l.Nodup := Finset.sort_nodup _ _
  have hcomplete : ∀ v : PermutationVertex k, v ∈ l := by
    intro v
    exact (Finset.mem_sort r).mpr (Finset.mem_univ v)
  have hpairle : l.Pairwise r := Finset.pairwise_sort _ _
  have hpairlt : l.Pairwise fun u v => start u < start v := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hle := (List.pairwise_iff_getElem.mp hpairle) i j hi hj hij
    have hne := (List.pairwise_iff_getElem.mp
      (List.nodup_iff_pairwise_ne.mp hnodup)) i j hi hj hij
    exact Nat.lt_of_le_of_ne hle fun heq =>
      hne (chosenOccurrenceStart_injective W hW heq)
  let P : HamiltonianPath k :=
    { vertices := l, nodup := hnodup, complete := hcomplete }
  refine ⟨P, ?_⟩
  have hweight : vertexListWeight l ≤ adjacentGaps start l := by
    exact vertexListWeight_le_adjacentGaps W hW hk l hpairlt
  have hnonempty : l ≠ [] := by
    let v : PermutationVertex k := ⟨alphabetWord k, List.Perm.refl _⟩
    exact fun hl => by simpa [hl] using hcomplete v
  obtain ⟨u, rest, hl⟩ := List.exists_cons_of_ne_nil hnonempty
  have hpairlt' : (u :: rest).Pairwise fun x y => start x < start y := by
    simpa [hl] using hpairlt
  have hstarts : start u + adjacentGaps start (u :: rest) ≤ W.length - k := by
    apply head_add_adjacentGaps_le start (W.length - k) u rest hpairlt'
    intro v hv
    exact chosenOccurrenceStart_le W hW v
  have hweight' : vertexListWeight (u :: rest) ≤ adjacentGaps start (u :: rest) := by
    simpa [hl] using hweight
  change vertexListWeight l ≤ W.length - k
  rw [hl]
  omega

/-- Frozen Proposition 1.1: shortest superpermutation length equals `k` plus minimum
Hamiltonian path weight. -/
theorem shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight
    (k : ℕ) (hk : 3 ≤ k) :
    shortestSuperpermutationLength k = k + minimumHamiltonianPathWeight k := by
  apply Nat.le_antisymm
  · obtain ⟨P, hP⟩ := minimumHamiltonianPathWeight_attained k
    have hsuper := mergedHamiltonianWord_isSuperpermutation P (by omega)
    have hmin := shortestSuperpermutationLength_le (mergedVertexWord P.vertices) hsuper
    rw [mergedHamiltonianWord_length P (by omega), hP] at hmin
    exact hmin
  · obtain ⟨W, hW, hlen⟩ := shortestSuperpermutationLength_attained k
    obtain ⟨P, hP⟩ := superpermutation_yields_hamiltonianPath W hW (by omega)
    have hL := minimumHamiltonianPathWeight_le P
    have hklen := superpermutation_length_ge W hW
    rw [hlen] at hP hklen
    omega

end SuperpermutationLowerBound
