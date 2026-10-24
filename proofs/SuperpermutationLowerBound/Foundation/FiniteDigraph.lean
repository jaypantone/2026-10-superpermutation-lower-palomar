module

public import SuperpermutationLowerBound.Foundation.Graph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound

/-! Finite directed edge sets on the fixed permutation-vertex type, together with the
weak-component substrate used by frozen Section 2. -/

open PermutationVertex

variable {k : ℕ}

noncomputable instance directedOverlapEdgeDecidableEq (k : ℕ) :
    DecidableEq (DirectedOverlapEdge k) := Classical.decEq _

/-- A finite spanning subgraph of the overlap digraph, represented by its typed edge set. -/
abbrev FiniteDirectedSubgraph (k : ℕ) := Finset (DirectedOverlapEdge k)

/-- Edges of `X` entering a vertex. -/
noncomputable def incomingEdgesAt (X : FiniteDirectedSubgraph k)
    (v : PermutationVertex k) : FiniteDirectedSubgraph k := by
  classical
  exact X.filter fun e => e.target = v

/-- Edges of `X` leaving a vertex. -/
noncomputable def outgoingEdgesAt (X : FiniteDirectedSubgraph k)
    (v : PermutationVertex k) : FiniteDirectedSubgraph k := by
  classical
  exact X.filter fun e => e.source = v

/-- Edges of `X` entering at least one vertex of `A`. -/
noncomputable def incomingEdges (X : FiniteDirectedSubgraph k)
    (A : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k := by
  classical
  exact X.filter fun e => e.target ∈ A

/-- Edges of `X` leaving at least one vertex of `A`. -/
noncomputable def outgoingEdges (X : FiniteDirectedSubgraph k)
    (A : Finset (PermutationVertex k)) : FiniteDirectedSubgraph k := by
  classical
  exact X.filter fun e => e.source ∈ A

@[simp]
theorem mem_incomingEdgesAt {X : FiniteDirectedSubgraph k} {v : PermutationVertex k}
    {e : DirectedOverlapEdge k} :
    e ∈ incomingEdgesAt X v ↔ e ∈ X ∧ e.target = v := by
  simp [incomingEdgesAt]

@[simp]
theorem mem_outgoingEdgesAt {X : FiniteDirectedSubgraph k} {v : PermutationVertex k}
    {e : DirectedOverlapEdge k} :
    e ∈ outgoingEdgesAt X v ↔ e ∈ X ∧ e.source = v := by
  simp [outgoingEdgesAt]

@[simp]
theorem mem_incomingEdges {X : FiniteDirectedSubgraph k}
    {A : Finset (PermutationVertex k)} {e : DirectedOverlapEdge k} :
    e ∈ incomingEdges X A ↔ e ∈ X ∧ e.target ∈ A := by
  simp [incomingEdges]

@[simp]
theorem mem_outgoingEdges {X : FiniteDirectedSubgraph k}
    {A : Finset (PermutationVertex k)} {e : DirectedOverlapEdge k} :
    e ∈ outgoingEdges X A ↔ e ∈ X ∧ e.source ∈ A := by
  simp [outgoingEdges]

/-- In-degree in a finite directed subgraph. -/
noncomputable def inDegree (X : FiniteDirectedSubgraph k)
    (v : PermutationVertex k) : ℕ := (incomingEdgesAt X v).card

/-- Out-degree in a finite directed subgraph. -/
noncomputable def outDegree (X : FiniteDirectedSubgraph k)
    (v : PermutationVertex k) : ℕ := (outgoingEdgesAt X v).card

/-- Total overlap weight of a finite directed subgraph. -/
noncomputable def graphWeight (X : FiniteDirectedSubgraph k) : ℕ :=
  ∑ e ∈ X, e.weight

/-- Vertices with no outgoing edge. -/
noncomputable def graphHeads (X : FiniteDirectedSubgraph k) :
    Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun v => outgoingEdgesAt X v = ∅

/-- Vertices with no incoming edge. -/
noncomputable def graphTails (X : FiniteDirectedSubgraph k) :
    Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun v => incomingEdgesAt X v = ∅

@[simp]
theorem mem_graphHeads {X : FiniteDirectedSubgraph k} {v : PermutationVertex k} :
    v ∈ graphHeads X ↔ outgoingEdgesAt X v = ∅ := by
  simp [graphHeads]

@[simp]
theorem mem_graphTails {X : FiniteDirectedSubgraph k} {v : PermutationVertex k} :
    v ∈ graphTails X ↔ incomingEdgesAt X v = ∅ := by
  simp [graphTails]

/-- The undirected graph obtained by forgetting the orientation of every edge. -/
def underlyingSimpleGraph (X : FiniteDirectedSubgraph k) :
    SimpleGraph (PermutationVertex k) where
  Adj u v := ∃ e ∈ X,
    (e.source = u ∧ e.target = v) ∨ (e.source = v ∧ e.target = u)
  symm := ⟨by
    intro u v
    rintro ⟨e, he, h⟩
    exact ⟨e, he, h.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e, _he, (⟨hsource, htarget⟩ | ⟨hsource, htarget⟩)⟩
    · exact e.ne (hsource.trans htarget.symm)
    · exact e.ne (hsource.trans htarget.symm)⟩

theorem underlyingSimpleGraph_adj_of_edge {X : FiniteDirectedSubgraph k}
    {e : DirectedOverlapEdge k} (he : e ∈ X) :
    (underlyingSimpleGraph X).Adj e.source e.target :=
  ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- A weak component is a connected component after edge orientations are forgotten. -/
abbrev WeakComponent (X : FiniteDirectedSubgraph k) :=
  (underlyingSimpleGraph X).ConnectedComponent

noncomputable instance weakComponentFintype (X : FiniteDirectedSubgraph k) :
    Fintype (WeakComponent X) := Fintype.ofFinite _

noncomputable instance weakComponentVertexFintype {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) : Fintype C := Fintype.ofFinite _

/-- The finite set of weak components of `X`. -/
noncomputable def weakComponents (X : FiniteDirectedSubgraph k) :
    Finset (WeakComponent X) := Finset.univ

/-- The vertices carried by a weak component. -/
noncomputable def weakComponentVertices {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) : Finset (PermutationVertex k) := by
  classical
  exact Finset.univ.filter fun v => v ∈ C.supp

/-- The edges induced by a weak component. -/
noncomputable def weakComponentEdges {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) : FiniteDirectedSubgraph k := by
  classical
  exact X.filter fun e => e.source ∈ C.supp ∧ e.target ∈ C.supp

@[simp]
theorem mem_weakComponentVertices {X : FiniteDirectedSubgraph k}
    {C : WeakComponent X} {v : PermutationVertex k} :
    v ∈ weakComponentVertices C ↔ v ∈ C.supp := by
  simp [weakComponentVertices]

@[simp]
theorem mem_weakComponentEdges {X : FiniteDirectedSubgraph k}
    {C : WeakComponent X} {e : DirectedOverlapEdge k} :
    e ∈ weakComponentEdges C ↔
      e ∈ X ∧ e.source ∈ C.supp ∧ e.target ∈ C.supp := by
  simp [weakComponentEdges]

theorem weakComponent_edge_target_mem {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) {e : DirectedOverlapEdge k}
    (hsource : e.source ∈ C.supp) (he : e ∈ X) : e.target ∈ C.supp := by
  exact C.mem_supp_of_adj_mem_supp hsource (underlyingSimpleGraph_adj_of_edge he)

theorem weakComponent_edge_source_mem {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) {e : DirectedOverlapEdge k}
    (htarget : e.target ∈ C.supp) (he : e ∈ X) : e.source ∈ C.supp := by
  exact C.mem_supp_of_adj_mem_supp htarget (underlyingSimpleGraph_adj_of_edge he).symm

/-- In-degree measured inside a weak component's induced edge set. -/
noncomputable def weakComponentInDegree {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) (v : PermutationVertex k) : ℕ :=
  inDegree (weakComponentEdges C) v

/-- Out-degree measured inside a weak component's induced edge set. -/
noncomputable def weakComponentOutDegree {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) (v : PermutationVertex k) : ℕ :=
  outDegree (weakComponentEdges C) v

/-- A weak component is a directed cycle when every carried vertex has one incoming and one
outgoing edge. Weak connectivity is part of the component type. -/
def IsDirectedCycleComponent {X : FiniteDirectedSubgraph k} (C : WeakComponent X) : Prop :=
  ∀ v ∈ weakComponentVertices C,
    weakComponentInDegree C v = 1 ∧ weakComponentOutDegree C v = 1

/-- A weak component is a directed path when it has a tail of in-degree zero, a head of
out-degree zero, and degree one everywhere else. The one-vertex path has the same tail and
head. Weak connectivity is part of the component type. -/
def IsDirectedPathComponent {X : FiniteDirectedSubgraph k} (C : WeakComponent X) : Prop :=
  ∃ tail ∈ weakComponentVertices C, ∃ head ∈ weakComponentVertices C,
    weakComponentInDegree C tail = 0 ∧
    (∀ v ∈ weakComponentVertices C, v ≠ tail → weakComponentInDegree C v = 1) ∧
    weakComponentOutDegree C head = 0 ∧
    (∀ v ∈ weakComponentVertices C, v ≠ head → weakComponentOutDegree C v = 1)

private theorem weakComponentVertices_nonempty {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) : (weakComponentVertices C).Nonempty := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact ⟨v, mem_weakComponentVertices.mpr hv⟩

private theorem weakComponentVertices_card {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) :
    (weakComponentVertices C).card = Fintype.card C := by
  classical
  let f : C ≃ {v // v ∈ weakComponentVertices C} :=
    { toFun := fun v => ⟨v.1, mem_weakComponentVertices.mpr v.2⟩
      invFun := fun v => ⟨v.1, mem_weakComponentVertices.mp v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (weakComponentVertices C).card = Fintype.card {v // v ∈ weakComponentVertices C} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card C := Fintype.card_congr f.symm

private theorem outgoing_inside_eq {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) {v : PermutationVertex k} (hv : v ∈ C.supp) :
    outgoingEdgesAt (weakComponentEdges C) v = outgoingEdgesAt X v := by
  classical
  ext e
  constructor
  · intro he
    have he' := mem_outgoingEdgesAt.mp he
    exact mem_outgoingEdgesAt.mpr
      ⟨(mem_weakComponentEdges.mp he'.1).1, he'.2⟩
  · intro he
    have heX := (mem_outgoingEdgesAt.mp he).1
    have hsource := (mem_outgoingEdgesAt.mp he).2
    have hsourceC : e.source ∈ C.supp := by rwa [hsource]
    have htargetC := weakComponent_edge_target_mem C hsourceC heX
    exact mem_outgoingEdgesAt.mpr
      ⟨mem_weakComponentEdges.mpr ⟨heX, hsourceC, htargetC⟩, hsource⟩

private theorem incoming_inside_eq {X : FiniteDirectedSubgraph k}
    (C : WeakComponent X) {v : PermutationVertex k} (hv : v ∈ C.supp) :
    incomingEdgesAt (weakComponentEdges C) v = incomingEdgesAt X v := by
  classical
  ext e
  constructor
  · intro he
    have he' := mem_incomingEdgesAt.mp he
    exact mem_incomingEdgesAt.mpr
      ⟨(mem_weakComponentEdges.mp he'.1).1, he'.2⟩
  · intro he
    have heX := (mem_incomingEdgesAt.mp he).1
    have htarget := (mem_incomingEdgesAt.mp he).2
    have htargetC : e.target ∈ C.supp := by rwa [htarget]
    have hsourceC := weakComponent_edge_source_mem C htargetC heX
    exact mem_incomingEdgesAt.mpr
      ⟨mem_weakComponentEdges.mpr ⟨heX, hsourceC, htargetC⟩, htarget⟩

private theorem weakComponentEdges_card_eq_sum_outDegree
    {X : FiniteDirectedSubgraph k} (C : WeakComponent X) :
    (weakComponentEdges C).card =
      ∑ v ∈ weakComponentVertices C, weakComponentOutDegree C v := by
  classical
  have hmaps : (↑(weakComponentEdges C) : Set (DirectedOverlapEdge k)).MapsTo
      DirectedOverlapEdge.source (weakComponentVertices C) := by
    intro e he
    exact mem_weakComponentVertices.mpr (mem_weakComponentEdges.mp he).2.1
  simpa [weakComponentOutDegree, outDegree, outgoingEdgesAt, and_comm] using
    (Finset.card_eq_sum_card_fiberwise hmaps)

private theorem weakComponentEdges_card_eq_sum_inDegree
    {X : FiniteDirectedSubgraph k} (C : WeakComponent X) :
    (weakComponentEdges C).card =
      ∑ v ∈ weakComponentVertices C, weakComponentInDegree C v := by
  classical
  have hmaps : (↑(weakComponentEdges C) : Set (DirectedOverlapEdge k)).MapsTo
      DirectedOverlapEdge.target (weakComponentVertices C) := by
    intro e he
    exact mem_weakComponentVertices.mpr (mem_weakComponentEdges.mp he).2.2
  simpa [weakComponentInDegree, inDegree, incomingEdgesAt, and_comm] using
    (Finset.card_eq_sum_card_fiberwise hmaps)

private abbrev CarriedEdge {X : FiniteDirectedSubgraph k} (C : WeakComponent X) :=
  {e // e ∈ weakComponentEdges C}

private def CarriedEdge.source {X : FiniteDirectedSubgraph k} {C : WeakComponent X}
    (e : CarriedEdge C) : C :=
  ⟨e.1.source, (mem_weakComponentEdges.mp e.2).2.1⟩

private def CarriedEdge.target {X : FiniteDirectedSubgraph k} {C : WeakComponent X}
    (e : CarriedEdge C) : C :=
  ⟨e.1.target, (mem_weakComponentEdges.mp e.2).2.2⟩

private def CarriedEdge.toUnderlyingEdge {X : FiniteDirectedSubgraph k}
    {C : WeakComponent X} (e : CarriedEdge C) : C.toSimpleGraph.edgeSet := by
  refine ⟨s(e.source, e.target), ?_⟩
  rw [SimpleGraph.mem_edgeSet]
  apply (C.toSimpleGraph_adj e.source.2 e.target.2).2
  exact underlyingSimpleGraph_adj_of_edge (mem_weakComponentEdges.mp e.2).1

private theorem carriedEdge_toUnderlyingEdge_surjective
    {X : FiniteDirectedSubgraph k} (C : WeakComponent X) :
    Function.Surjective (CarriedEdge.toUnderlyingEdge (C := C)) := by
  rintro ⟨q, hq⟩
  induction q using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hq
      have hab : (underlyingSimpleGraph X).Adj a.1 b.1 :=
        (C.toSimpleGraph_adj a.2 b.2).1 hq
      obtain ⟨e, heX, hdir⟩ := hab
      rcases hdir with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
      · have heC : e ∈ weakComponentEdges C := by
          exact mem_weakComponentEdges.mpr
            ⟨heX, hsource.symm ▸ a.2, htarget.symm ▸ b.2⟩
        refine ⟨⟨e, heC⟩, Subtype.ext ?_⟩
        simp only [CarriedEdge.toUnderlyingEdge, CarriedEdge.source, CarriedEdge.target]
        congr 1 <;> apply Subtype.ext <;> simp [hsource, htarget]
      · have heC : e ∈ weakComponentEdges C := by
          exact mem_weakComponentEdges.mpr
            ⟨heX, hsource.symm ▸ b.2, htarget.symm ▸ a.2⟩
        refine ⟨⟨e, heC⟩, Subtype.ext ?_⟩
        simp only [CarriedEdge.toUnderlyingEdge, CarriedEdge.source, CarriedEdge.target]
        rw [Sym2.eq_swap]
        congr 1 <;> apply Subtype.ext <;> simp [hsource, htarget]

private theorem weakComponent_card_le_edges_add_one
    {X : FiniteDirectedSubgraph k} (C : WeakComponent X) :
    (weakComponentVertices C).card ≤ (weakComponentEdges C).card + 1 := by
  classical
  have hconnected := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  have hsurj := Fintype.card_le_of_surjective _
    (carriedEdge_toUnderlyingEdge_surjective C)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hconnected
  have hcarried : Fintype.card (CarriedEdge C) = (weakComponentEdges C).card := by simp
  calc
    (weakComponentVertices C).card = Fintype.card C := weakComponentVertices_card C
    _ ≤ Fintype.card C.toSimpleGraph.edgeSet + 1 := hconnected
    _ ≤ Fintype.card (CarriedEdge C) + 1 := Nat.add_le_add_right hsurj 1
    _ = (weakComponentEdges C).card + 1 := by rw [hcarried]

private theorem sum_add_zeroFilter_card
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α → ℕ)
    (hle : ∀ x ∈ s, d x ≤ 1) :
    (∑ x ∈ s, d x) + (s.filter fun x => d x = 0).card = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haLe : d a ≤ 1 := hle a (by simp)
      have hsLe : ∀ x ∈ s, d x ≤ 1 := by
        intro x hx
        exact hle x (by simp [hx])
      have hrec := ih hsLe
      by_cases hzero : d a = 0
      · have hanot : a ∉ s.filter fun x => d x = 0 := by simp [ha]
        have hfilter : (insert a s).filter (fun x => d x = 0) =
            insert a (s.filter fun x => d x = 0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hx, hdx⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hx, hdx⟩
          · rintro (rfl | ⟨hx, hdx⟩)
            · exact ⟨Or.inl rfl, hzero⟩
            · exact ⟨Or.inr hx, hdx⟩
        rw [Finset.sum_insert ha, hfilter, Finset.card_insert_of_notMem hanot,
          Finset.card_insert_of_notMem ha, hzero]
        omega
      · have hone : d a = 1 := by omega
        have hfilter : (insert a s).filter (fun x => d x = 0) =
            s.filter fun x => d x = 0 := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hx, hdx⟩
            · exact (hzero hdx).elim
            · exact ⟨hx, hdx⟩
          · rintro ⟨hx, hdx⟩
            exact ⟨Or.inr hx, hdx⟩
        rw [Finset.sum_insert ha, hfilter, Finset.card_insert_of_notMem ha, hone]
        omega

private theorem all_one_of_sum_eq_card
    {α : Type*} [DecidableEq α] {s : Finset α} {d : α → ℕ}
    (hle : ∀ x ∈ s, d x ≤ 1) (hsum : ∑ x ∈ s, d x = s.card) :
    ∀ x ∈ s, d x = 1 := by
  classical
  have hzero := sum_add_zeroFilter_card s d hle
  rw [hsum] at hzero
  have hfilter : s.filter (fun x => d x = 0) = ∅ := Finset.card_eq_zero.mp (by omega)
  intro x hx
  have hxnot : d x ≠ 0 := by
    intro hdx
    have : x ∈ s.filter fun y => d y = 0 := by simp [hx, hdx]
    rw [hfilter] at this
    simp at this
  have hxle := hle x hx
  omega

private theorem degree_pattern_of_sum_add_one_eq_card
    {α : Type*} [DecidableEq α] {s : Finset α} {d : α → ℕ}
    (hle : ∀ x ∈ s, d x ≤ 1) (hsum : (∑ x ∈ s, d x) + 1 = s.card) :
    ∃ z ∈ s, d z = 0 ∧ ∀ x ∈ s, x ≠ z → d x = 1 := by
  classical
  have hzero := sum_add_zeroFilter_card s d hle
  have hcard : (s.filter fun x => d x = 0).card = 1 := by omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hzmem : z ∈ s := by
    have : z ∈ s.filter fun x => d x = 0 := by simp [hz]
    exact (Finset.mem_filter.mp this).1
  have hzd : d z = 0 := by
    have : z ∈ s.filter fun x => d x = 0 := by simp [hz]
    exact (Finset.mem_filter.mp this).2
  refine ⟨z, hzmem, hzd, ?_⟩
  intro x hx hxz
  have hxnot : d x ≠ 0 := by
    intro hdx
    have hxfilter : x ∈ s.filter fun y => d y = 0 := by simp [hx, hdx]
    rw [hz] at hxfilter
    exact hxz (by simpa using hxfilter)
  have hxle := hle x hx
  omega

/-- Finite weak components with in-degree and out-degree at most one are exactly directed
paths or directed cycles, including isolated one-vertex paths and directed two-cycles. -/
theorem weakComponent_directedPath_or_directedCycle
    (X : FiniteDirectedSubgraph k)
    (hin : ∀ v : PermutationVertex k, inDegree X v ≤ 1)
    (hout : ∀ v : PermutationVertex k, outDegree X v ≤ 1)
    (C : WeakComponent X) :
    IsDirectedPathComponent C ∨ IsDirectedCycleComponent C := by
  classical
  let V := weakComponentVertices C
  let E := weakComponentEdges C
  have hinC : ∀ v ∈ V, weakComponentInDegree C v ≤ 1 := by
    intro v hv
    rw [weakComponentInDegree, inDegree, incoming_inside_eq C
      (mem_weakComponentVertices.mp hv)]
    exact hin v
  have houtC : ∀ v ∈ V, weakComponentOutDegree C v ≤ 1 := by
    intro v hv
    rw [weakComponentOutDegree, outDegree, outgoing_inside_eq C
      (mem_weakComponentVertices.mp hv)]
    exact hout v
  have hsumOut : E.card = ∑ v ∈ V, weakComponentOutDegree C v :=
    weakComponentEdges_card_eq_sum_outDegree C
  have hsumIn : E.card = ∑ v ∈ V, weakComponentInDegree C v :=
    weakComponentEdges_card_eq_sum_inDegree C
  have hupper : E.card ≤ V.card := by
    rw [hsumOut]
    calc
      (∑ v ∈ V, weakComponentOutDegree C v) ≤ ∑ _v ∈ V, 1 := by
        exact Finset.sum_le_sum fun v hv => houtC v hv
      _ = V.card := by simp
  have hlower : V.card ≤ E.card + 1 := weakComponent_card_le_edges_add_one C
  by_cases hcycle : E.card = V.card
  · right
    intro v hv
    constructor
    · exact all_one_of_sum_eq_card hinC (by simpa [← hsumIn] using hcycle) v hv
    · exact all_one_of_sum_eq_card houtC (by simpa [← hsumOut] using hcycle) v hv
  · left
    have hedge : E.card + 1 = V.card := by omega
    have hinPattern := degree_pattern_of_sum_add_one_eq_card hinC (by
      rw [← hsumIn]
      exact hedge)
    have houtPattern := degree_pattern_of_sum_add_one_eq_card houtC (by
      rw [← hsumOut]
      exact hedge)
    obtain ⟨tail, htailV, htailZero, htailOther⟩ := hinPattern
    obtain ⟨head, hheadV, hheadZero, hheadOther⟩ := houtPattern
    exact ⟨tail, htailV, head, hheadV, htailZero, htailOther,
      hheadZero, hheadOther⟩

end SuperpermutationLowerBound
