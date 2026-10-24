module

public import SuperpermutationLowerBound.Section02.PathForest
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace SuperpermutationLowerBound

/-! Frozen Section 3 through Lemma 3.3: reduced minimum paths and the two
Gate C consequences for Step 2 deleted edges.
-/

open PermutationVertex

variable {k : ℕ}

/-- A Hamiltonian path contains one of the forbidden edges `v → σ²(v)`. -/
def HasDoubleRotationEdge (P : HamiltonianPath k) : Prop :=
  ∃ e ∈ P.edgeSet, e.target = doubleRotation e.source

/-- Frozen Definition 3.2. A reduced minimum path has minimum Hamiltonian
weight and contains no edge `v → σ²(v)`. -/
def IsReducedMinimumPath (P : HamiltonianPath k) : Prop :=
  P.weight = minimumHamiltonianPathWeight k ∧ ¬HasDoubleRotationEdge P

/-- The minimum-weight half of the reduced-path interface. -/
theorem IsReducedMinimumPath.minimumWeight {P : HamiltonianPath k}
    (hP : IsReducedMinimumPath P) :
    P.weight = minimumHamiltonianPathWeight k :=
  hP.1

/-- The forbidden-edge half of the reduced-path interface. -/
theorem IsReducedMinimumPath.noDoubleRotationEdge {P : HamiltonianPath k}
    (hP : IsReducedMinimumPath P) : ¬HasDoubleRotationEdge P :=
  hP.2

private noncomputable def vertexListWeightOneCount :
    List (PermutationVertex k) → ℕ
  | [] | [_] => 0
  | u :: v :: rest =>
      (if overlapWeight u v = 1 then 1 else 0) +
        vertexListWeightOneCount (v :: rest)

private noncomputable def HamiltonianPath.weightOneCount
    (P : HamiltonianPath k) : ℕ :=
  vertexListWeightOneCount P.vertices

private theorem cons_append_perm_insert {α : Type*} (x : α)
    (left right : List α) :
    (x :: (left ++ right)).Perm (left ++ x :: right) := by
  induction left with
  | nil => simp
  | cons a left ih =>
      simpa using
        (List.Perm.swap a x (left ++ right)).trans (List.Perm.cons a ih)

private theorem insert_perm_insert {α : Type*} (x : α)
    (left₁ right₁ left₂ right₂ : List α)
    (hbase : left₁ ++ right₁ = left₂ ++ right₂) :
    (left₁ ++ x :: right₁).Perm (left₂ ++ x :: right₂) := by
  exact (cons_append_perm_insert x left₁ right₁).symm |>.trans
    ((List.Perm.refl (x :: (left₁ ++ right₁))).trans
      (hbase ▸ cons_append_perm_insert x left₂ right₂))

private theorem vertexListWeight_delete_le (hk : 2 ≤ k)
    (left right : List (PermutationVertex k)) (x : PermutationVertex k)
    (hnodup : (left ++ x :: right).Nodup) :
    vertexListWeight (left ++ right) ≤ vertexListWeight (left ++ x :: right) := by
  induction left with
  | nil =>
      cases right with
      | nil => simp [vertexListWeight]
      | cons b right =>
          simp [vertexListWeight]
  | cons a left ih =>
      cases left with
      | nil =>
          cases right with
          | nil => simp [vertexListWeight]
          | cons b right =>
              have hn : (a :: x :: b :: right).Nodup := by
                simpa using hnodup
              have hax : a ≠ x := by
                intro h
                exact (List.nodup_cons.mp hn).1 (by simp [h])
              have hxb : x ≠ b := by
                intro h
                exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
              have hab : a ≠ b := by
                intro h
                exact (List.nodup_cons.mp hn).1 (by simp [h])
              have htriangle := directed_triangle_inequality a x b hk hax hxb hab
              simp [vertexListWeight]
              omega
      | cons b left =>
          have htail : ((b :: left) ++ x :: right).Nodup := by
            have hn : (a :: ((b :: left) ++ x :: right)).Nodup := by
              simpa using hnodup
            exact (List.nodup_cons.mp hn).2
          have hrec := ih htail
          simpa [vertexListWeight] using
            Nat.add_le_add_left hrec (overlapWeight a b)

private theorem vertexListWeight_insert_between
    (left right : List (PermutationVertex k))
    (u x v : PermutationVertex k)
    (hweight : overlapWeight u v = overlapWeight u x + overlapWeight x v) :
    vertexListWeight (left ++ u :: x :: v :: right) =
      vertexListWeight (left ++ u :: v :: right) := by
  induction left with
  | nil => simp [vertexListWeight, hweight, Nat.add_assoc]
  | cons a left ih =>
      cases left with
      | nil => simp [vertexListWeight, hweight, Nat.add_assoc]
      | cons b left =>
          simpa [vertexListWeight] using
            congrArg (fun n => overlapWeight a b + n) ih

private theorem vertexListWeightOneCount_delete_le
    (left right : List (PermutationVertex k)) (x : PermutationVertex k)
    (hpred : ∀ a, left.getLast? = some a → overlapWeight a x ≠ 1)
    (hsucc : ∀ b, right.head? = some b → overlapWeight x b ≠ 1) :
    vertexListWeightOneCount (left ++ x :: right) ≤
      vertexListWeightOneCount (left ++ right) := by
  induction left with
  | nil =>
      cases right with
      | nil => simp [vertexListWeightOneCount]
      | cons b right =>
          have hxb := hsucc b (by simp)
          simp [vertexListWeightOneCount, hxb]
  | cons a left ih =>
      cases left with
      | nil =>
          have hax := hpred a (by simp)
          cases right with
          | nil => simp [vertexListWeightOneCount, hax]
          | cons b right =>
              have hxb := hsucc b (by simp)
              simp [vertexListWeightOneCount, hax, hxb]
      | cons b left =>
          have hpred' : ∀ z, (b :: left).getLast? = some z →
              overlapWeight z x ≠ 1 := by
            intro z hz
            apply hpred z
            simpa using hz
          have hrec := ih hpred'
          simpa [vertexListWeightOneCount] using
            Nat.add_le_add_left hrec
              (if overlapWeight a b = 1 then 1 else 0)

private theorem vertexListWeightOneCount_insert_between
    (left right : List (PermutationVertex k))
    (u x v : PermutationVertex k)
    (huv : overlapWeight u v ≠ 1)
    (hux : overlapWeight u x = 1)
    (hxv : overlapWeight x v = 1) :
    vertexListWeightOneCount (left ++ u :: x :: v :: right) =
      vertexListWeightOneCount (left ++ u :: v :: right) + 2 := by
  induction left with
  | nil =>
      simp [vertexListWeightOneCount, huv, hux, hxv]
      omega
  | cons a left ih =>
      cases left with
      | nil =>
          simp [vertexListWeightOneCount, huv, hux, hxv]
          omega
      | cons b left =>
          have hrec := congrArg (fun n =>
            (if overlapWeight a b = 1 then 1 else 0) + n) ih
          simp only [List.cons_append, vertexListWeightOneCount] at hrec ⊢
          omega

private theorem path_edges_eq_of_same_source (P : HamiltonianPath k)
    {e f : DirectedOverlapEdge k} (he : e ∈ P.edgeSet) (hf : f ∈ P.edgeSet)
    (hsource : e.source = f.source) : e = f := by
  classical
  have hle := P.edgeSet_outDegree_rule e.source
  rw [outDegree, Finset.card_le_one] at hle
  exact hle e (mem_outgoingEdgesAt.mpr ⟨he, rfl⟩)
    f (mem_outgoingEdgesAt.mpr ⟨hf, hsource.symm⟩)

private theorem path_edges_eq_of_same_target (P : HamiltonianPath k)
    {e f : DirectedOverlapEdge k} (he : e ∈ P.edgeSet) (hf : f ∈ P.edgeSet)
    (htarget : e.target = f.target) : e = f := by
  classical
  have hle := P.edgeSet_inDegree_rule e.target
  rw [inDegree, Finset.card_le_one] at hle
  exact hle e (mem_incomingEdgesAt.mpr ⟨he, rfl⟩)
    f (mem_incomingEdgesAt.mpr ⟨hf, htarget.symm⟩)

private theorem rotation_ne_doubleRotation (hk : 3 ≤ k)
    (v : PermutationVertex k) : rotation v ≠ doubleRotation v := by
  rw [← rotation_rotation_eq_doubleRotation (by omega) v]
  intro h
  have hv : v = rotation v := rotation_injective (by omega) h
  exact rotation_ne_self (by omega) v hv.symm

private theorem forbidden_rotation_predecessor_not_weight_one (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f e : DirectedOverlapEdge k}
    (hf : f ∈ P.edgeSet) (hftarget : f.target = doubleRotation f.source)
    (he : e ∈ P.edgeSet) (hetarget : e.target = rotation f.source) :
    e.weight ≠ 1 := by
  intro heweight
  have hene : e.source ≠ rotation f.source := by
    intro h
    exact e.ne (h.trans hetarget.symm)
  have hsource : e.source = inverseRotation (rotation f.source) :=
    (unique_weight_one_predecessor (rotation f.source) e.source hk hene).mp (by
      simpa [DirectedOverlapEdge.weight, hetarget] using heweight)
  have hsource' : e.source = f.source := by
    exact hsource.trans (inverseRotation_rotation (by omega) f.source)
  have hef := path_edges_eq_of_same_source P he hf hsource'
  apply rotation_ne_doubleRotation hk f.source
  calc
    rotation f.source = e.target := hetarget.symm
    _ = f.target := congrArg DirectedOverlapEdge.target hef
    _ = doubleRotation f.source := hftarget

private theorem forbidden_rotation_successor_not_weight_one (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f e : DirectedOverlapEdge k}
    (hf : f ∈ P.edgeSet) (hftarget : f.target = doubleRotation f.source)
    (he : e ∈ P.edgeSet) (hesource : e.source = rotation f.source) :
    e.weight ≠ 1 := by
  intro heweight
  have hene : e.source ≠ e.target := e.ne
  have htarget : e.target = rotation e.source :=
    (unique_weight_one_successor e.source e.target hk hene).mp (by
      simpa [DirectedOverlapEdge.weight] using heweight)
  have htarget' : e.target = f.target := by
    calc
      e.target = rotation e.source := htarget
      _ = rotation (rotation f.source) := congrArg rotation hesource
      _ = doubleRotation f.source := rotation_rotation_eq_doubleRotation (by omega) _
      _ = f.target := hftarget.symm
  have hef := path_edges_eq_of_same_target P he hf htarget'
  apply rotation_ne_self (by omega) f.source
  calc
    rotation f.source = e.source := hesource.symm
    _ = f.source := congrArg DirectedOverlapEdge.source hef

set_option backward.isDefEq.respectTransparency false in
private theorem adjacent_edge_mem (P : HamiltonianPath k)
    (left right : List (PermutationVertex k))
    (u v : PermutationVertex k)
    (hvertices : P.vertices = left ++ u :: v :: right) :
    ∃ e ∈ P.edgeSet, e.source = u ∧ e.target = v := by
  classical
  have hn : (left ++ u :: v :: right).Nodup := by
    simpa [hvertices] using P.nodup
  have huv : u ≠ v := by
    have htail : (u :: v :: right).Nodup := (List.nodup_append.mp hn).2.1
    intro h
    exact (List.nodup_cons.mp htail).1 (by simp [h])
  let e : DirectedOverlapEdge k := ⟨u, v, huv⟩
  let i : P.EdgeIndex := ⟨left.length, by simp [hvertices]⟩
  refine ⟨e, HamiltonianPath.mem_edgeSet.mpr ⟨i, ?_⟩, rfl, rfl⟩
  simp [HamiltonianPath.indexedEdge, OverlapPath.edgeAt, OverlapPath.vertex,
    HamiltonianPath.toOverlapPath, i, e, hvertices]

set_option backward.isDefEq.respectTransparency false in
private theorem edge_mem_decomposition (P : HamiltonianPath k)
    {e : DirectedOverlapEdge k} (he : e ∈ P.edgeSet) :
    ∃ left right, P.vertices = left ++ e.source :: e.target :: right := by
  obtain ⟨i, hi⟩ := HamiltonianPath.mem_edgeSet.mp he
  refine ⟨P.vertices.take i.1, P.vertices.drop (i.1 + 2), ?_⟩
  have hi₀ : i.1 < P.vertices.length := by
    have := i.2
    omega
  have hi₁ : i.1 + 1 < P.vertices.length := by
    have := i.2
    omega
  have hsource : P.vertices[i.1] = e.source := by
    have := congrArg DirectedOverlapEdge.source hi
    simpa [HamiltonianPath.indexedEdge, OverlapPath.edgeAt,
      OverlapPath.vertex, HamiltonianPath.toOverlapPath] using this
  have htarget : P.vertices[i.1 + 1] = e.target := by
    have := congrArg DirectedOverlapEdge.target hi
    simpa [HamiltonianPath.indexedEdge, OverlapPath.edgeAt,
      OverlapPath.vertex, HamiltonianPath.toOverlapPath] using this
  calc
    P.vertices = P.vertices.take i.1 ++ P.vertices.drop i.1 :=
      (List.take_append_drop i.1 P.vertices).symm
    _ = P.vertices.take i.1 ++
        P.vertices[i.1] :: P.vertices.drop (i.1 + 1) := by
      rw [List.drop_eq_getElem_cons hi₀]
    _ = P.vertices.take i.1 ++ P.vertices[i.1] ::
        P.vertices[i.1 + 1] :: P.vertices.drop (i.1 + 2) := by
      rw [List.drop_eq_getElem_cons hi₁]
    _ = P.vertices.take i.1 ++ e.source :: e.target ::
        P.vertices.drop (i.1 + 2) := by rw [hsource, htarget]

private theorem forbidden_rotation_delete_count_le (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f : DirectedOverlapEdge k}
    (hf : f ∈ P.edgeSet) (hftarget : f.target = doubleRotation f.source)
    (left right : List (PermutationVertex k))
    (hvertices : P.vertices = left ++ rotation f.source :: right) :
    vertexListWeightOneCount (left ++ rotation f.source :: right) ≤
      vertexListWeightOneCount (left ++ right) := by
  apply vertexListWeightOneCount_delete_le
  · intro a ha
    have haMem : a ∈ left.getLast? := by simp [ha]
    have hleft := List.dropLast_append_getLast? a haMem
    obtain ⟨e, he, hesource, hetarget⟩ := adjacent_edge_mem P
      left.dropLast right a (rotation f.source) (by
        calc
          P.vertices = left ++ rotation f.source :: right := hvertices
          _ = (left.dropLast ++ [a]) ++ rotation f.source :: right := by
            rw [hleft]
          _ = left.dropLast ++ a :: rotation f.source :: right := by simp)
    simpa [DirectedOverlapEdge.weight, hesource, hetarget] using
      forbidden_rotation_predecessor_not_weight_one hk P hf hftarget he hetarget
  · intro b hb
    cases hright : right with
    | nil => simp [hright] at hb
    | cons c rest =>
        have hcb : c = b := by simpa [hright] using hb
        subst c
        obtain ⟨e, he, hesource, hetarget⟩ := adjacent_edge_mem P
          left rest (rotation f.source) b (by simpa [hright] using hvertices)
        simpa [DirectedOverlapEdge.weight, hesource, hetarget] using
          forbidden_rotation_successor_not_weight_one hk P hf hftarget he hesource

private theorem relocate_forbidden_rotation (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f : DirectedOverlapEdge k}
    (hf : f ∈ P.edgeSet) (hftarget : f.target = doubleRotation f.source)
    (left right insertLeft insertRight : List (PermutationVertex k))
    (hvertices : P.vertices = left ++ rotation f.source :: right)
    (hdeleted : left ++ right =
      insertLeft ++ f.source :: f.target :: insertRight) :
    ∃ Q : HamiltonianPath k,
      Q.weight ≤ P.weight ∧ P.weightOneCount + 2 ≤ Q.weightOneCount := by
  let moved := rotation f.source
  let newVertices := insertLeft ++ f.source :: moved :: f.target :: insertRight
  have hdeleted' : left ++ right =
      (insertLeft ++ [f.source]) ++ f.target :: insertRight := by
    simpa [List.append_assoc] using hdeleted
  have hpermInserted := insert_perm_insert moved left right
    (insertLeft ++ [f.source]) (f.target :: insertRight) hdeleted'
  have hperm : P.vertices.Perm newVertices := by
    rw [hvertices]
    simpa [newVertices, moved, List.append_assoc] using hpermInserted
  let Q : HamiltonianPath k :=
    { vertices := newVertices
      nodup := hperm.nodup_iff.mp P.nodup
      complete := fun v => hperm.mem_iff.mp (P.complete v) }
  have hnold : (left ++ moved :: right).Nodup := by
    rw [← hvertices]
    exact P.nodup
  have hdeleteWeight := vertexListWeight_delete_le (by omega : 2 ≤ k)
    left right moved hnold
  have hforbiddenWeight : overlapWeight f.source f.target = 2 := by
    rw [hftarget]
    exact doubleRotation_has_weight_two f.source hk
  have hfirstWeight : overlapWeight f.source moved = 1 :=
    rotation_has_weight_one f.source hk
  have hsecondWeight : overlapWeight moved f.target = 1 := by
    rw [hftarget, ← rotation_rotation_eq_doubleRotation (by omega) f.source]
    exact rotation_has_weight_one (rotation f.source) hk
  have hweightSplit : overlapWeight f.source f.target =
      overlapWeight f.source moved + overlapWeight moved f.target := by
    omega
  have hinsertWeight := vertexListWeight_insert_between insertLeft insertRight
    f.source moved f.target hweightSplit
  have hdeleteCount := forbidden_rotation_delete_count_le hk P hf hftarget
    left right hvertices
  have hinsertCount := vertexListWeightOneCount_insert_between insertLeft insertRight
    f.source moved f.target (by omega) hfirstWeight hsecondWeight
  refine ⟨Q, ?_, ?_⟩
  · change vertexListWeight newVertices ≤ vertexListWeight P.vertices
    calc
      vertexListWeight newVertices =
          vertexListWeight (insertLeft ++ f.source :: f.target :: insertRight) := by
        simpa [newVertices, moved] using hinsertWeight
      _ = vertexListWeight (left ++ right) := congrArg vertexListWeight hdeleted.symm
      _ ≤ vertexListWeight (left ++ moved :: right) := hdeleteWeight
      _ = vertexListWeight P.vertices := congrArg vertexListWeight hvertices.symm
  · change vertexListWeightOneCount P.vertices + 2 ≤
      vertexListWeightOneCount newVertices
    calc
      vertexListWeightOneCount P.vertices + 2 =
          vertexListWeightOneCount (left ++ moved :: right) + 2 := by rw [hvertices]
      _ ≤ vertexListWeightOneCount (left ++ right) + 2 :=
        Nat.add_le_add_right hdeleteCount 2
      _ = vertexListWeightOneCount
          (insertLeft ++ f.source :: f.target :: insertRight) + 2 := by rw [hdeleted]
      _ = vertexListWeightOneCount newVertices := by
        simpa [newVertices, moved] using hinsertCount.symm

private theorem doubleRotation_exchange (hk : 3 ≤ k)
    (P : HamiltonianPath k) {f : DirectedOverlapEdge k}
    (hf : f ∈ P.edgeSet) (hftarget : f.target = doubleRotation f.source) :
    ∃ Q : HamiltonianPath k,
      Q.weight ≤ P.weight ∧ P.weightOneCount + 2 ≤ Q.weightOneCount := by
  obtain ⟨before, after, hvertices⟩ := edge_mem_decomposition P hf
  let moved := rotation f.source
  have hmoved : moved ∈ P.vertices := P.complete moved
  have hmoveSource : moved ≠ f.source := rotation_ne_self (by omega) f.source
  have hmoveTarget : moved ≠ f.target := by
    intro h
    exact rotation_ne_doubleRotation hk f.source (h.trans hftarget)
  rw [hvertices] at hmoved
  simp only [List.mem_append, List.mem_cons] at hmoved
  rcases hmoved with hmovedPrefix | hmovedSource | hmovedTarget | hmovedSuffix
  · obtain ⟨left, right, hprefix⟩ := List.mem_iff_append.mp hmovedPrefix
    apply relocate_forbidden_rotation hk P hf hftarget
      left (right ++ f.source :: f.target :: after) (left ++ right) after
    · calc
        P.vertices = before ++ f.source :: f.target :: after := hvertices
        _ = (left ++ moved :: right) ++ f.source :: f.target :: after := by
          rw [hprefix]
        _ = left ++ moved :: (right ++ f.source :: f.target :: after) := by
          simp [List.append_assoc]
    · simp [List.append_assoc]
  · exact (hmoveSource hmovedSource).elim
  · exact (hmoveTarget hmovedTarget).elim
  · obtain ⟨left, right, hsuffix⟩ := List.mem_iff_append.mp hmovedSuffix
    apply relocate_forbidden_rotation hk P hf hftarget
      (before ++ f.source :: f.target :: left) right before (left ++ right)
    · calc
        P.vertices = before ++ f.source :: f.target :: after := hvertices
        _ = before ++ f.source :: f.target :: (left ++ moved :: right) := by
          rw [hsuffix]
        _ = (before ++ f.source :: f.target :: left) ++ moved :: right := by
          simp [List.append_assoc]
    · simp [List.append_assoc]

/-- Frozen Lemma 3.1. For every `k ≥ 3`, some minimum-weight Hamiltonian
path contains no edge `v → σ²(v)`. The proof chooses a minimum path maximizing
its number of weight-one edges and performs the literal list surgery from the
frozen proof. -/
theorem exists_reducedMinimumPath (hk : 3 ≤ k) :
    ∃ P : HamiltonianPath k, IsReducedMinimumPath P := by
  classical
  obtain ⟨P₀, hP₀⟩ := minimumHamiltonianPathWeight_attained k
  let minimumPaths : Finset (HamiltonianPath k) :=
    Finset.univ.filter fun P => P.weight = minimumHamiltonianPathWeight k
  have hminimumPaths : minimumPaths.Nonempty := by
    refine ⟨P₀, ?_⟩
    simp [minimumPaths, hP₀]
  obtain ⟨P, hPmin, hmax⟩ :=
    Finset.exists_max_image minimumPaths HamiltonianPath.weightOneCount hminimumPaths
  have hminimum : P.weight = minimumHamiltonianPathWeight k := by
    simpa [minimumPaths] using hPmin
  refine ⟨P, hminimum, ?_⟩
  rintro ⟨f, hf, hftarget⟩
  obtain ⟨Q, hQweight, hQcount⟩ := doubleRotation_exchange hk P hf hftarget
  have hQlower := minimumHamiltonianPathWeight_le Q
  have hQminimum : Q.weight = minimumHamiltonianPathWeight k := by
    omega
  have hQmem : Q ∈ minimumPaths := by
    simp [minimumPaths, hQminimum]
  have hmaxQ := hmax Q hQmem
  omega

private theorem directedEdge_eq_of_source_target {e f : DirectedOverlapEdge k}
    (hsource : e.source = f.source) (htarget : e.target = f.target) : e = f := by
  cases e
  cases f
  simp_all

set_option backward.isDefEq.respectTransparency false in
private theorem pathForest_deltaTwo_weight_ge_two (hk : 3 ≤ k)
    (P : HamiltonianPath k) {e : DirectedOverlapEdge k}
    (he : e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P)) :
    2 ≤ e.weight := by
  classical
  let V := residualVertices (by omega : 2 ≤ k) P
  have heInfo :
      e ∈ forestStepOne (by omega) P V ∧
        e ∈ incomingEdges P.edgeSet (doubleIncomingVertices (by omega) P V) := by
    have he' := he
    change e ∈ forestDeltaTwo (by omega) P V at he'
    simp only [forestDeltaTwo, forestStepTwo, forestStepZero,
      Finset.mem_sdiff, mem_incomingEdges] at he'
    refine ⟨he'.1, mem_incomingEdges.mpr ?_⟩
    by_contra hnot
    exact he'.2 ⟨he'.1, hnot⟩
  have heP : e ∈ P.edgeSet := (mem_incomingEdges.mp heInfo.2).1
  have htargetDouble : e.target ∈ doubleIncomingVertices (by omega) P V :=
    (mem_incomingEdges.mp heInfo.2).2
  have hcard :
      (incomingEdgesAt (forestStepOne (by omega) P V) e.target).card = 2 := by
    simpa [doubleIncomingVertices, inDegree] using htargetDouble
  have heIncoming : e ∈ incomingEdgesAt (forestStepOne (by omega) P V) e.target :=
    mem_incomingEdgesAt.mpr ⟨heInfo.1, rfl⟩
  have hcardErase :
      ((incomingEdgesAt (forestStepOne (by omega) P V) e.target).erase e).card = 1 := by
    rw [Finset.card_erase_of_mem heIncoming, hcard]
  obtain ⟨f, hfErase⟩ :
      ((incomingEdgesAt (forestStepOne (by omega) P V) e.target).erase e).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hfIncoming : f ∈ incomingEdgesAt (forestStepOne (by omega) P V) e.target :=
    Finset.mem_of_mem_erase hfErase
  have hfe : f ≠ e := Finset.ne_of_mem_erase hfErase
  have hfStepOne : f ∈ forestStepOne (by omega) P V :=
    (mem_incomingEdgesAt.mp hfIncoming).1
  have hfTarget : f.target = e.target := (mem_incomingEdgesAt.mp hfIncoming).2
  have hfRotation : f ∈ rotationEdges (by omega) V := by
    simp only [forestStepOne, forestStepZero, forestDeltaOne, Finset.mem_union,
      Finset.mem_sdiff, mem_outgoingEdges] at hfStepOne
    rcases hfStepOne with hfOriginal | hfRotation
    · have hle := P.edgeSet_inDegree_rule e.target
      rw [inDegree, Finset.card_le_one] at hle
      have hef := hle f (mem_incomingEdgesAt.mpr ⟨hfOriginal.1, hfTarget⟩)
        e (mem_incomingEdgesAt.mpr ⟨heP, rfl⟩)
      exact (hfe hef).elim
    · exact hfRotation
  obtain ⟨v, hv, hvf⟩ := mem_rotationEdges.mp hfRotation
  have hfSource : f.source = v := by
    calc
      f.source = (rotationEdge (by omega) v).source :=
        congrArg DirectedOverlapEdge.source hvf.symm
      _ = v := rfl
  have hrotationTarget : rotation v = e.target := by
    calc
      rotation v = (rotationEdge (by omega) v).target := rfl
      _ = f.target := congrArg DirectedOverlapEdge.target hvf
      _ = e.target := hfTarget
  have hone : e.weight ≠ 1 := by
    intro heOne
    have heSource : e.source = inverseRotation e.target :=
      (unique_weight_one_predecessor e.target e.source hk e.ne).mp (by
        simpa [DirectedOverlapEdge.weight] using heOne)
    have heSourceV : e.source = v := by
      calc
        e.source = inverseRotation e.target := heSource
        _ = inverseRotation (rotation v) := congrArg inverseRotation hrotationTarget.symm
        _ = v := inverseRotation_rotation (by omega) v
    have hef : e = f := directedEdge_eq_of_source_target
      (heSourceV.trans hfSource.symm) hfTarget.symm
    exact hfe hef.symm
  have hpositive : 1 ≤ e.weight := (overlapWeight_spec e.source e.target).1
  omega

private theorem path_outgoingEdges_card (P : HamiltonianPath k)
    (V : Finset (PermutationVertex k))
    (hV : ∀ v ∈ V, v ∉ graphHeads P.edgeSet) :
    (outgoingEdges P.edgeSet V).card = V.card := by
  classical
  apply Finset.card_bij (fun e _he => e.source)
  · intro e he
    exact (mem_outgoingEdges.mp he).2
  · intro e he f hf hsource
    exact path_edges_eq_of_same_source P
      (mem_outgoingEdges.mp he).1 (mem_outgoingEdges.mp hf).1 hsource
  · intro v hv
    have hnonempty : (outgoingEdgesAt P.edgeSet v).Nonempty := by
      by_contra hnot
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
      exact hV v hv (mem_graphHeads.mpr hempty)
    obtain ⟨e, he⟩ := hnonempty
    have heInfo := mem_outgoingEdgesAt.mp he
    refine ⟨e, mem_outgoingEdges.mpr ⟨heInfo.1, ?_⟩, heInfo.2⟩
    simpa [heInfo.2] using hv

private theorem pathForestComponentHead_mem_vertices (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentHead hk P C ∈ weakComponentVertices C := by
  classical
  rw [← pathForestComponentPath_vertexSet hk P C]
  simp [OverlapPath.vertexSet, pathForestComponentHead, List.getLast_mem]

private theorem weakComponentOutDegree_zero_of_graphHead
    {X : FiniteDirectedSubgraph k} (C : WeakComponent X)
    {v : PermutationVertex k} (_hvC : v ∈ weakComponentVertices C)
    (hvHead : v ∈ graphHeads X) : weakComponentOutDegree C v = 0 := by
  classical
  rw [weakComponentOutDegree, outDegree]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have heInfo := mem_outgoingEdgesAt.mp he
  have heWeak := mem_weakComponentEdges.mp heInfo.1
  have heGlobal : e ∈ outgoingEdgesAt X v :=
    mem_outgoingEdgesAt.mpr ⟨heWeak.1, heInfo.2⟩
  rw [mem_graphHeads.mp hvHead] at heGlobal
  simp at heGlobal

private theorem pathForestComponentHead_mem_graphHeads (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P)) :
    pathForestComponentHead hk P C ∈ graphHeads (pathForest hk P) := by
  classical
  apply mem_graphHeads.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have heInfo := mem_outgoingEdgesAt.mp he
  have hheadC := mem_weakComponentVertices.mp
    (pathForestComponentHead_mem_vertices hk P C)
  have hsourceC : e.source ∈ C.supp := by simpa [heInfo.2] using hheadC
  have htargetC := weakComponent_edge_target_mem C hsourceC heInfo.1
  have heWeak : e ∈ weakComponentEdges C :=
    mem_weakComponentEdges.mpr ⟨heInfo.1, hsourceC, htargetC⟩
  have heWeakOut : e ∈ outgoingEdgesAt (weakComponentEdges C)
      (pathForestComponentHead hk P C) :=
    mem_outgoingEdgesAt.mpr ⟨heWeak, heInfo.2⟩
  have hempty : outgoingEdgesAt (weakComponentEdges C)
      (pathForestComponentHead hk P C) = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [weakComponentOutDegree, outDegree] using
      pathForestComponentHead_outDegree_zero hk P C
  rw [hempty] at heWeakOut
  simp at heWeakOut

private theorem eq_pathForestComponentHead_of_outDegree_zero (hk : 3 ≤ k)
    (P : HamiltonianPath k) (C : WeakComponent (pathForest hk P))
    {v : PermutationVertex k} (hvC : v ∈ weakComponentVertices C)
    (hvZero : weakComponentOutDegree C v = 0) :
    v = pathForestComponentHead hk P C := by
  rcases pathForest_component_isDirectedPath hk P C with
    ⟨tail, htail, head, hhead, _htailZero, _hotherIn,
      hheadZero, hotherOut⟩
  have hvHead : v = head := by
    by_contra hne
    have := hotherOut v hvC hne
    omega
  have hnamedHead : pathForestComponentHead hk P C = head := by
    by_contra hne
    have hnamedOne := hotherOut (pathForestComponentHead hk P C)
      (pathForestComponentHead_mem_vertices hk P C) hne
    have hnamedZero := pathForestComponentHead_outDegree_zero hk P C
    omega
  exact hvHead.trans hnamedHead.symm

private theorem pathForest_graphHeads_card (hk : 3 ≤ k)
    (P : HamiltonianPath k) :
    (graphHeads (pathForest hk P)).card = pathForestComponentCount hk P := by
  classical
  have hcard : (weakComponents (pathForest hk P)).card =
      (graphHeads (pathForest hk P)).card := by
    apply Finset.card_bij (fun C _hC => pathForestComponentHead hk P C)
    · intro C _hC
      exact pathForestComponentHead_mem_graphHeads hk P C
    · intro C _hC D _hD hheads
      apply SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (mem_weakComponentVertices.mp
          (pathForestComponentHead_mem_vertices hk P C))
      have hD := mem_weakComponentVertices.mp
        (pathForestComponentHead_mem_vertices hk P D)
      simpa [hheads] using hD
    · intro v hv
      let C : WeakComponent (pathForest hk P) :=
        (underlyingSimpleGraph (pathForest hk P)).connectedComponentMk v
      have hC : C ∈ weakComponents (pathForest hk P) := by
        simp [weakComponents]
      have hvSupp : v ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hvC : v ∈ weakComponentVertices C :=
        mem_weakComponentVertices.mpr hvSupp
      have hvZero := weakComponentOutDegree_zero_of_graphHead C hvC hv
      refine ⟨C, hC, ?_⟩
      exact (eq_pathForestComponentHead_of_outDegree_zero hk P C hvC hvZero).symm
  rw [← hcard]
  rfl

private theorem pathForest_pathHead_mem_graphHeads_iff (hk : 3 ≤ k)
    (P : HamiltonianPath k) :
    P.head ∈ graphHeads (pathForest hk P) ↔
      P.head ∉ residualVertices (by omega) P := by
  classical
  have hpathHead : P.head ∈ graphHeads P.edgeSet := by
    rw [P.edgeSet_heads]
    simp
  have hrotationNotPath : rotationEdge (by omega) P.head ∉ P.edgeSet := by
    intro hrotation
    have hout : rotationEdge (by omega) P.head ∈ outgoingEdgesAt P.edgeSet P.head :=
      mem_outgoingEdgesAt.mpr ⟨hrotation, rfl⟩
    rw [mem_graphHeads.mp hpathHead] at hout
    simp at hout
  constructor
  · intro hforestHead hresidual
    have hnotPred := (mem_residualVertices_iff (by omega) P P.head).mp hresidual |>.1
    have hout := pathForest_outgoing_of_not_predecessor hk P hnotPred
    have hrotation : rotationEdge (by omega) P.head ∈
        outgoingEdgesAt (pathForest hk P) P.head := by simp [hout]
    rw [mem_graphHeads.mp hforestHead] at hrotation
    simp at hrotation
  · intro hnotResidual
    have hpred : P.head ∈ firstVisitedPredecessors (by omega) P := by
      by_contra hnotPred
      apply hnotResidual
      exact (mem_residualVertices_iff (by omega) P P.head).mpr
        ⟨hnotPred, hrotationNotPath⟩
    apply mem_graphHeads.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨e, heP, hesource, _hetarget, _hout⟩ :=
      pathForest_outgoing_of_predecessor hk P hpred hnonempty
    have heOutP : e ∈ outgoingEdgesAt P.edgeSet P.head :=
      mem_outgoingEdgesAt.mpr ⟨heP, hesource⟩
    rw [mem_graphHeads.mp hpathHead] at heOutP
    simp at heOutP

private theorem pathForestComponentCount_pos (hk : 3 ≤ k)
    (P : HamiltonianPath k) : 0 < pathForestComponentCount hk P := by
  rw [pathForestComponentCount]
  apply Finset.card_pos.mpr
  refine ⟨(underlyingSimpleGraph (pathForest hk P)).connectedComponentMk P.head, ?_⟩
  simp [weakComponents]

private theorem pathForest_newHeads_card (hk : 3 ≤ k)
    (P : HamiltonianPath k) :
    (graphHeads (pathForest hk P) \ graphHeads P.edgeSet).card =
      pathForestComponentCount hk P - 1 +
        forestHeadIndicator P (residualVertices (by omega) P) := by
  classical
  rw [P.edgeSet_heads, Finset.sdiff_singleton_eq_erase]
  by_cases hresidual : P.head ∈ residualVertices (by omega) P
  · have hnotHead : P.head ∉ graphHeads (pathForest hk P) := by
      intro hhead
      exact (pathForest_pathHead_mem_graphHeads_iff hk P).mp hhead hresidual
    rw [Finset.erase_eq_of_notMem hnotHead, pathForest_graphHeads_card hk P,
      forestHeadIndicator, if_pos hresidual]
    have hpos := pathForestComponentCount_pos hk P
    omega
  · have hhead : P.head ∈ graphHeads (pathForest hk P) :=
      (pathForest_pathHead_mem_graphHeads_iff hk P).mpr hresidual
    rw [Finset.card_erase_of_mem hhead, pathForest_graphHeads_card hk P,
      forestHeadIndicator, if_neg hresidual, Nat.add_zero]

private theorem pathForest_deltaTwo_card (hk : 3 ≤ k)
    (P : HamiltonianPath k) :
    (forestDeltaTwo (by omega) P (residualVertices (by omega) P)).card =
      pathForestComponentCount hk P - 1 +
        forestHeadIndicator P (residualVertices (by omega) P) := by
  have hboundary := forestDeltaTwo_eq_outgoing_heads hk P
    (residualVertices (by omega) P)
    (residualVertices_rotationEdgesAdmissible hk P)
  change forestDeltaTwo (by omega) P (residualVertices (by omega) P) =
    outgoingEdges P.edgeSet
      (graphHeads (pathForest hk P) \ graphHeads P.edgeSet) at hboundary
  rw [hboundary, path_outgoingEdges_card P
    (graphHeads (pathForest hk P) \ graphHeads P.edgeSet)]
  · exact pathForest_newHeads_card hk P
  · intro v hv
    exact (Finset.mem_sdiff.mp hv).2

/-- Frozen Lemma 3.3 (`lem:newheadweight`) for `X = F(P)` under the exact
frozen reduced-path hypothesis. Every Step-2 deleted edge has weight at least
two, and the natural-number cardinality is `|Δ₂| = c - 1 + I`. -/
theorem reducedMinimumPath_newHeadWeight (hk : 3 ≤ k)
    (P : HamiltonianPath k) (_hP : IsReducedMinimumPath P) :
    (∀ e ∈ forestDeltaTwo (by omega) P (residualVertices (by omega) P),
        2 ≤ e.weight) ∧
      (forestDeltaTwo (by omega) P (residualVertices (by omega) P)).card =
        pathForestComponentCount hk P - 1 +
          forestHeadIndicator P (residualVertices (by omega) P) := by
  exact ⟨fun _e he => pathForest_deltaTwo_weight_ge_two hk P he,
    pathForest_deltaTwo_card hk P⟩

end SuperpermutationLowerBound
