module

public import SuperpermutationLowerBound.Section06.Witnesses

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! A concrete maximal-positive-cluster decomposition and the charging
argument of Lemma `lem:charging`.  No numerical charging estimate is stored
in the decomposition: all such estimates are derived from R1--R3 below. -/

/-- A nonempty chain of positive clusters separated by zero gaps. -/
inductive PositiveClusterChain where
  | last (cluster : List ℕ)
  | cons (cluster : List ℕ) (gap : ℕ) (tail : PositiveClusterChain)
deriving Repr

namespace PositiveClusterChain

def render : PositiveClusterChain → List ℕ
  | last cluster => cluster
  | cons cluster gap tail =>
      cluster ++ List.replicate gap 0 ++ tail.render

def clusters : PositiveClusterChain → List (List ℕ)
  | last cluster => [cluster]
  | cons cluster _ tail => cluster :: tail.clusters

def gaps : PositiveClusterChain → List ℕ
  | last _ => []
  | cons _ gap tail => gap :: tail.gaps

def firstCluster : PositiveClusterChain → List ℕ
  | last cluster => cluster
  | cons cluster _ _ => cluster

theorem firstCluster_mem_clusters (chain : PositiveClusterChain) :
    chain.firstCluster ∈ chain.clusters := by
  cases chain <;> simp [firstCluster, clusters]

theorem render_head_eq_firstCluster_head (chain : PositiveClusterChain)
    (hfirst : chain.firstCluster ≠ [])
    (hrender : chain.render ≠ []) :
    chain.render.head hrender = chain.firstCluster.head hfirst := by
  cases chain with
  | last K => rfl
  | cons K gap tail =>
      have hKne : K ≠ [] := by simpa [firstCluster] using hfirst
      simpa [render, firstCluster, hKne]

def prependFirst (x : ℕ) : PositiveClusterChain → PositiveClusterChain
  | last cluster => last (x :: cluster)
  | cons cluster gap tail => cons (x :: cluster) gap tail

@[simp] theorem render_prependFirst (x : ℕ) (chain : PositiveClusterChain) :
    (chain.prependFirst x).render = x :: chain.render := by
  cases chain <;> simp [prependFirst, render]

@[simp] theorem clusters_prependFirst (x : ℕ)
    (chain : PositiveClusterChain) :
    (chain.prependFirst x).clusters =
      (x :: chain.clusters.head (by cases chain <;> simp [clusters])) ::
        chain.clusters.tail := by
  cases chain <;> simp [prependFirst, clusters]

@[simp] theorem gaps_prependFirst (x : ℕ) (chain : PositiveClusterChain) :
    (chain.prependFirst x).gaps = chain.gaps := by
  cases chain <;> rfl

theorem cluster_nonempty_prependFirst (x : ℕ) (chain : PositiveClusterChain)
    (h : ∀ K ∈ chain.clusters, K ≠ []) :
    ∀ K ∈ (chain.prependFirst x).clusters, K ≠ [] := by
  intro K hK
  cases chain with
  | last first =>
      simp [prependFirst, clusters] at hK
      subst K
      simp
  | cons first gap rest =>
      simp [prependFirst, clusters] at hK
      rcases hK with rfl | hK
      · simp
      · exact h K (by simp [clusters]; exact Or.inr hK)

theorem cluster_positive_prependFirst (x : ℕ) (hx : 0 < x)
    (chain : PositiveClusterChain)
    (h : ∀ K ∈ chain.clusters, ∀ y ∈ K, 0 < y) :
    ∀ K ∈ (chain.prependFirst x).clusters, ∀ y ∈ K, 0 < y := by
  intro K hK y hy
  cases chain with
  | last first =>
      simp [prependFirst, clusters] at hK
      subst K
      simp at hy
      rcases hy with rfl | hy
      · exact hx
      · exact h first (by simp [clusters]) y hy
  | cons first gap rest =>
      simp [prependFirst, clusters] at hK
      rcases hK with rfl | hK
      · simp at hy
        rcases hy with rfl | hy
        · exact hx
        · exact h first (by simp [clusters]) y hy
      · exact h K (by simp [clusters]; exact Or.inr hK) y hy

theorem clusters_nonempty (chain : PositiveClusterChain) : chain.clusters ≠ [] := by
  cases chain <;> simp [clusters]

theorem render_nonempty (chain : PositiveClusterChain)
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ []) : chain.render ≠ [] := by
  cases chain with
  | last K => simpa [render, clusters] using hclusterNe K (by simp [clusters])
  | cons K gap tail =>
      have hK := hclusterNe K (by simp [clusters])
      simp [render, hK]

theorem render_head_positive (chain : PositiveClusterChain)
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    ∀ x ∈ chain.render.head?, 0 < x := by
  cases chain with
  | last K =>
      intro x hx
      have hKne := hclusterNe K (by simp [clusters])
      have hx' : x ∈ K := by
        exact List.mem_of_mem_head? (by simpa [render] using hx)
      exact hclusterPos K (by simp [clusters]) x hx'
  | cons K gap tail =>
      intro x hx
      have hKne := hclusterNe K (by simp [clusters])
      have hx' : x ∈ K := by
        exact List.mem_of_mem_head? (by simpa [render, hKne] using hx)
      exact hclusterPos K (by simp [clusters]) x hx'

@[simp] theorem gaps_length (chain : PositiveClusterChain) :
    chain.gaps.length + 1 = chain.clusters.length := by
  induction chain with
  | last cluster => simp [gaps, clusters]
  | cons cluster gap tail ih => simp [gaps, clusters, ih]

@[simp] theorem render_length (chain : PositiveClusterChain) :
    chain.render.length = (chain.clusters.map List.length).sum + chain.gaps.sum := by
  induction chain with
  | last cluster => simp [render, clusters, gaps]
  | cons cluster gap tail ih => simp [render, clusters, gaps, ih]; omega

@[simp] theorem render_sum (chain : PositiveClusterChain) :
    chain.render.sum = (chain.clusters.map List.sum).sum := by
  induction chain with
  | last cluster => simp [render, clusters]
  | cons cluster gap tail ih => simp [render, clusters, ih]

@[simp] theorem render_prepend_zero (lead : ℕ) (chain : PositiveClusterChain)
    (trail : ℕ) :
    (List.replicate lead 0 ++ chain.render ++ List.replicate trail 0).sum =
      (chain.clusters.map List.sum).sum := by
  simp

end PositiveClusterChain

/-- A literal decomposition into maximal positive clusters, positive
intervening zero gaps, and the two possibly empty endpoint zero blocks. -/
structure PositiveClusterDecomposition (d : List ℕ) where
  leadingZeros : ℕ
  chain : PositiveClusterChain
  trailingZeros : ℕ
  cluster_nonempty : ∀ K ∈ chain.clusters, K ≠ []
  cluster_positive : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x
  gap_positive : ∀ u ∈ chain.gaps, 0 < u
  rebuild : d = List.replicate leadingZeros 0 ++ chain.render ++
    List.replicate trailingZeros 0

private theorem allZero_eq_replicate_length {d : List ℕ}
    (hall : ∀ x ∈ d, x = 0) : d = List.replicate d.length 0 := by
  apply List.eq_replicate_iff.mpr
  exact ⟨by simp, hall⟩

/-- Every list containing a positive entry has a concrete cluster
decomposition.  This construction is by the entries of the list, not by an
assumed numerical bound. -/
theorem exists_positiveClusterDecomposition {d : List ℕ}
    (hpositive : ∃ x ∈ d, 0 < x) : ∃ dec : PositiveClusterDecomposition d, True := by
  induction d with
  | nil => simp at hpositive
  | cons a tail ih =>
      by_cases htail : ∃ x ∈ tail, 0 < x
      · obtain ⟨dec, _⟩ := ih htail
        by_cases ha0 : a = 0
        · subst a
          refine ⟨{
            leadingZeros := dec.leadingZeros + 1
            chain := dec.chain
            trailingZeros := dec.trailingZeros
            cluster_nonempty := dec.cluster_nonempty
            cluster_positive := dec.cluster_positive
            gap_positive := dec.gap_positive
            rebuild := ?_ }, trivial⟩
          calc
            0 :: tail = 0 :: (List.replicate dec.leadingZeros 0 ++
                dec.chain.render ++ List.replicate dec.trailingZeros 0) :=
              congrArg (fun z => 0 :: z) dec.rebuild
            _ = _ := by
              simp [List.replicate_succ, List.append_assoc, Nat.add_comm]
        · have hapos : 0 < a := by omega
          cases hlead : dec.leadingZeros with
          | zero =>
              refine ⟨{
                leadingZeros := 0
                chain := dec.chain.prependFirst a
                trailingZeros := dec.trailingZeros
                cluster_nonempty := PositiveClusterChain.cluster_nonempty_prependFirst
                  a dec.chain dec.cluster_nonempty
                cluster_positive := PositiveClusterChain.cluster_positive_prependFirst
                  a hapos dec.chain dec.cluster_positive
                gap_positive := by simpa using dec.gap_positive
                rebuild := ?_ }, trivial⟩
              calc
                a :: tail = a :: (List.replicate dec.leadingZeros 0 ++
                    dec.chain.render ++ List.replicate dec.trailingZeros 0) :=
                  congrArg (fun z => a :: z) dec.rebuild
                _ = _ := by
                  simp [hlead, PositiveClusterChain.render_prependFirst]
          | succ lead =>
              refine ⟨{
                leadingZeros := 0
                chain := PositiveClusterChain.cons [a] (lead + 1) dec.chain
                trailingZeros := dec.trailingZeros
                cluster_nonempty := ?_
                cluster_positive := ?_
                gap_positive := ?_
                rebuild := ?_ }, trivial⟩
              · intro K hK
                simp [PositiveClusterChain.clusters] at hK
                rcases hK with rfl | hK
                · simp
                · exact dec.cluster_nonempty K hK
              · intro K hK x hx
                simp [PositiveClusterChain.clusters] at hK
                rcases hK with rfl | hK
                · simp at hx
                  simpa [hx] using hapos
                · exact dec.cluster_positive K hK x hx
              · intro u hu
                simp [PositiveClusterChain.gaps] at hu
                rcases hu with rfl | hu
                · omega
                · exact dec.gap_positive u hu
              · calc
                  a :: tail = a :: (List.replicate dec.leadingZeros 0 ++
                      dec.chain.render ++ List.replicate dec.trailingZeros 0) :=
                    congrArg (fun z => a :: z) dec.rebuild
                  _ = _ := by
                    simp [hlead, PositiveClusterChain.render, List.replicate_succ,
                      List.append_assoc, Nat.add_comm]
      · have hall : ∀ x ∈ tail, x = 0 := by
          intro x hx
          by_contra hx0
          exact htail ⟨x, hx, by omega⟩
        have hapos : 0 < a := by
          rcases hpositive with ⟨x, hx, hxpos⟩
          simp at hx
          rcases hx with rfl | hx
          · exact hxpos
          · exact (htail ⟨x, hx, hxpos⟩).elim
        have htailEq := allZero_eq_replicate_length hall
        refine ⟨{
          leadingZeros := 0
          chain := PositiveClusterChain.last [a]
          trailingZeros := tail.length
          cluster_nonempty := ?_
          cluster_positive := ?_
          gap_positive := ?_
          rebuild := ?_ }, trivial⟩
        · intro K hK
          simp [PositiveClusterChain.clusters] at hK
          subst K
          simp
        · intro K hK x hx
          simp [PositiveClusterChain.clusters] at hK
          subst K
          simp at hx
          simpa [hx] using hapos
        · simp [PositiveClusterChain.gaps]
        · rw [htailEq]
          simp [PositiveClusterChain.render]

private theorem positive_length_le_sum {K : List ℕ}
    (hpositive : ∀ x ∈ K, 0 < x) : K.length ≤ K.sum := by
  induction K with
  | nil => simp
  | cons a K ih =>
      simp only [List.length_cons, List.sum_cons]
      have ha := hpositive a (by simp)
      have htail := ih (by
        intro x hx
        exact hpositive x (List.mem_cons_of_mem a hx))
      omega

private theorem list_member_le_sum {x : ℕ} {K : List ℕ} (hx : x ∈ K) :
    x ≤ K.sum := by
  induction K with
  | nil => simp at hx
  | cons a K ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have := ih hx
        simp
        omega

private theorem shaped_before_deficit {lead : ℕ} (hlead : 0 < lead)
    (K post : List ℕ) :
    deficitAt (List.replicate lead 0 ++ K ++ post) (lead - 1) = 0 := by
  simp [deficitAt, List.getElem?_append, hlead]

private theorem shaped_first_deficit {lead a : ℕ} (tail post : List ℕ) :
    deficitAt (List.replicate lead 0 ++ (a :: tail) ++ post) lead = a := by
  simp [deficitAt, List.getElem?_append]

private theorem shaped_second_deficit {lead a b : ℕ}
    (tail post : List ℕ) :
    deficitAt (List.replicate lead 0 ++ (a :: b :: tail) ++ post) (lead + 1) = b := by
  simp [deficitAt, List.getElem?_append]

private theorem head?_replicate_zero_of_pos {k : ℕ} (hk : 0 < k) :
    (List.replicate k 0).head? = some 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [List.replicate_succ]

/-- The local R2 charge at a cluster preceded by a zero.  The sole
exception is exactly a terminal singleton `[1]`. -/
private theorem precededPositiveCluster_charge {n lead : ℕ}
    {K post : List ℕ}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate lead 0 ++ K ++ post))
    (hlead : 0 < lead) (hKne : K ≠ [])
    (hKpos : ∀ x ∈ K, 0 < x)
    (hpostZero : ∀ z ∈ post.head?, z = 0)
    (hnotTerminalOne : post ≠ [] ∨ K ≠ [1]) :
    K.length + 1 ≤ K.sum := by
  cases K with
  | nil => contradiction
  | cons a tail =>
      have ha : 0 < a := hKpos a (by simp)
      have htailBound : tail.length ≤ tail.sum :=
        positive_length_le_sum (by
          intro x hx
          exact hKpos x (List.mem_cons_of_mem a hx))
      by_cases ha1 : a = 1
      · subst a
        cases tail with
        | nil =>
            have hpost : post ≠ [] := by
              rcases hnotTerminalOne with hpost | hnot
              · exact hpost
              · exact (hnot rfl).elim
            obtain ⟨z, rest, rfl⟩ := List.exists_cons_of_ne_nil hpost
            have hz : z = 0 := hpostZero z (by simp)
            subst z
            have hi : lead - 1 + 2 <
                (List.replicate lead 0 ++ [1] ++ (0 :: rest)).length := by
              simp
              omega
            have hrule := hlegal.rule2 (lead - 1) hi
            exfalso
            apply hrule
            constructor
            · exact shaped_before_deficit hlead [1] (0 :: rest)
            constructor
            · have hindex : lead - 1 + 1 = lead := by omega
              rw [hindex]
              exact shaped_first_deficit (lead := lead) (a := 1) [] (0 :: rest)
            · have hindex : lead - 1 + 2 = lead + 1 := by omega
              rw [hindex]
              simp [deficitAt, List.getElem?_append]
        | cons b rest =>
            have hb : 0 < b := hKpos b (by simp)
            by_contra hsmall
            have hrestBound : rest.length ≤ rest.sum :=
              positive_length_le_sum (by
                intro x hx
                exact hKpos x (by simp; exact Or.inr (Or.inr hx)))
            have hbsmall : b ≤ 1 := by
              simp only [List.length_cons, List.sum_cons] at hsmall
              omega
            have hi : lead - 1 + 2 <
                (List.replicate lead 0 ++ (1 :: b :: rest) ++ post).length := by
              simp
              omega
            have hrule := hlegal.rule2 (lead - 1) hi
            apply hrule
            constructor
            · exact shaped_before_deficit hlead (1 :: b :: rest) post
            constructor
            · have hindex : lead - 1 + 1 = lead := by omega
              rw [hindex]
              exact shaped_first_deficit (lead := lead) (a := 1) (b :: rest) post
            · have hindex : lead - 1 + 2 = lead + 1 := by omega
              rw [hindex]
              rw [shaped_second_deficit (lead := lead)
                (a := 1) (b := b) rest post]
              exact hbsmall
      · have ha2 : 2 ≤ a := by omega
        simp only [List.length_cons, List.sum_cons]
        omega

/-- Legality of a nonempty suffix, stated in append form for the recursive
cluster arguments. -/
theorem IsLegalDeficitSequence.suffix_of_append {n : ℕ} {pref suffix : List ℕ}
    (hlegal : IsLegalDeficitSequence n (pref ++ suffix))
    (hsuffix : suffix ≠ []) : IsLegalDeficitSequence n suffix := by
  have hpos : 0 < suffix.length := by
    cases suffix with
    | nil => contradiction
    | cons a tail => simp
  have hsliced := hlegal.slice (start := pref.length)
    (sliceLength := suffix.length) hpos (by simp)
  simpa [deficitSlice] using hsliced

/-- Indicator for the left endpoint cluster exception. -/
def leftClusterException (leadingZeros : ℕ) : ℕ :=
  if leadingZeros = 0 then 1 else 0

/-- Indicator for the unique possible right endpoint exception. -/
def rightClusterException : PositiveClusterChain → ℕ → ℕ
  | .last K, trailingZeros =>
      if trailingZeros = 0 ∧ K = [1] then 1 else 0
  | .cons _ _ tail, trailingZeros => rightClusterException tail trailingZeros

/-- The total endpoint-exception count `δ`. -/
def clusterExceptionCount (leadingZeros : ℕ) (chain : PositiveClusterChain)
    (trailingZeros : ℕ) : ℕ :=
  leftClusterException leadingZeros + rightClusterException chain trailingZeros

theorem leftClusterException_le_one (leadingZeros : ℕ) :
    leftClusterException leadingZeros ≤ 1 := by
  unfold leftClusterException
  split <;> omega

theorem rightClusterException_le_one (chain : PositiveClusterChain)
    (trailingZeros : ℕ) : rightClusterException chain trailingZeros ≤ 1 := by
  induction chain with
  | last K =>
      unfold rightClusterException
      split <;> omega
  | cons K gap tail ih => simpa [rightClusterException] using ih

theorem clusterExceptionCount_le_two (leadingZeros : ℕ)
    (chain : PositiveClusterChain) (trailingZeros : ℕ) :
    clusterExceptionCount leadingZeros chain trailingZeros ≤ 2 := by
  unfold clusterExceptionCount
  have hl := leftClusterException_le_one leadingZeros
  have hr := rightClusterException_le_one chain trailingZeros
  omega

/-- Sum of the literal cluster charges `m_j+1`, with exactly the two
endpoint exceptions subtracted. -/
theorem cluster_length_charge {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    (chain.clusters.map List.length).sum + chain.clusters.length ≤
      (chain.clusters.map List.sum).sum +
        clusterExceptionCount leading chain trailing := by
  induction chain generalizing leading with
  | last K =>
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKpos : ∀ x ∈ K, 0 < x := hclusterPos K
        (by simp [PositiveClusterChain.clusters])
      have hbase := positive_length_le_sum hKpos
      by_cases hlead : leading = 0
      · simp [PositiveClusterChain.clusters, clusterExceptionCount,
          leftClusterException, hlead]
        omega
      · have hleadPos : 0 < leading := by omega
        by_cases hright : trailing = 0 ∧ K = [1]
        · simp [PositiveClusterChain.clusters, clusterExceptionCount,
            leftClusterException, rightClusterException, hlead, hright]
        · have hextra := precededPositiveCluster_charge
            (hlegal := by simpa [PositiveClusterChain.render] using hlegal)
            hleadPos hKne hKpos (by
              intro z hz
              by_cases htrail0 : trailing = 0
              · subst trailing
                simp at hz
              · have hhead := head?_replicate_zero_of_pos
                    (by omega : 0 < trailing)
                rw [hhead] at hz
                exact (Option.some.inj hz).symm) (by
              rcases not_and_or.mp hright with htrail | hK
              · left
                simp [htrail]
              · exact Or.inr hK)
          simp [PositiveClusterChain.clusters, clusterExceptionCount,
            leftClusterException, rightClusterException, hlead, hright]
          exact hextra
  | cons K gap tail ih =>
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKpos : ∀ x ∈ K, 0 < x := hclusterPos K
        (by simp [PositiveClusterChain.clusters])
      have hgap : 0 < gap := hgapPos gap (by simp [PositiveClusterChain.gaps])
      have hgap0 : gap ≠ 0 := by omega
      have hheadCharge : K.length + 1 ≤ K.sum + leftClusterException leading := by
        by_cases hlead : leading = 0
        · subst leading
          simp [leftClusterException]
          exact positive_length_le_sum hKpos
        · have hleadPos : 0 < leading := by omega
          have hextra := precededPositiveCluster_charge
            (hlegal := by simpa [PositiveClusterChain.render, List.append_assoc] using hlegal)
            hleadPos hKne hKpos (by
              intro z hz
              have hz' : (List.replicate gap 0).head? = some z := by
                simpa [hgap0] using hz
              have hhead := head?_replicate_zero_of_pos hgap
              rw [hhead] at hz'
              exact (Option.some.inj hz').symm) (by
              left
              simp [hgap0])
          simpa [leftClusterException, hlead] using hextra
      let suffix := List.replicate gap 0 ++ tail.render ++ List.replicate trailing 0
      have hlegalAppend : IsLegalDeficitSequence n
          ((List.replicate leading 0 ++ K) ++ suffix) := by
        simpa [suffix, PositiveClusterChain.render, List.append_assoc] using hlegal
      have hsuffixNe : suffix ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp [suffix] at hlen
        omega
      have hlegalTail : IsLegalDeficitSequence n suffix :=
        hlegalAppend.suffix_of_append hsuffixNe
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL
        exact hclusterNe L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL
        exact hclusterPos L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgapPos u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
      have htailCharge := ih (leading := gap)
        (by simpa [suffix] using hlegalTail) htailNe htailPos htailGap
      have hleftGap : leftClusterException gap = 0 := by
        simp [leftClusterException]
        omega
      simp only [PositiveClusterChain.clusters, List.map_cons, List.sum_cons,
        List.length_cons, clusterExceptionCount, rightClusterException]
      simp only [clusterExceptionCount] at htailCharge
      rw [hleftGap] at htailCharge
      omega

private theorem deficitAt_before_cluster_gap {leading gap : ℕ}
    {K rest : List ℕ} (hKne : K ≠ []) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ rest)))
      (leading + K.length - 1) = K.getLast hKne := by
  have hKlen : 0 < K.length := by
    cases K with
    | nil => contradiction
    | cons a tail => simp
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length - 1 - leading = K.length - 1 := by omega
  rw [hindex, ← List.getLast?_eq_getElem?]
  rw [List.getLast?_eq_getLast_of_ne_nil hKne]
  rfl

private theorem deficitAt_after_cluster_gap {leading gap : ℕ}
    {K rest suffix : List ℕ} (hrest : rest ≠ []) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ (rest ++ suffix))))
      (leading + K.length + gap) = rest.head hrest := by
  have hrestLen : 0 < rest.length := by
    cases rest with
    | nil => contradiction
    | cons a tail => simp
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length + gap - leading - K.length - gap = 0 := by omega
  rw [hindex]
  cases rest with
  | nil => contradiction
  | cons a tail => rfl

private theorem deficitAt_inside_cluster_gap {leading gap j : ℕ}
    {K rest : List ℕ} (hj : j < gap) :
    deficitAt (List.replicate leading 0 ++
      (K ++ (List.replicate gap 0 ++ rest))) (leading + K.length + j) = 0 := by
  unfold deficitAt
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_append_left (by simp; omega)]
  simp only [List.length_replicate]
  have hindex : leading + K.length + j - leading - K.length = j := by omega
  rw [hindex]
  rw [List.getElem?_eq_getElem (by simp; exact hj)]
  simp

private theorem internalClusterGap_isMaximal {n leading trailing gap : ℕ}
    {K : List ℕ} {tail : PositiveClusterChain}
    (hKne : K ≠ []) (hKpos : ∀ x ∈ K, 0 < x)
    (htailNe : ∀ L ∈ tail.clusters, L ≠ [])
    (htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x)
    (hgap : 0 < gap) :
    IsMaximalZeroBlock
      (List.replicate leading 0 ++
        (K ++ (List.replicate gap 0 ++
          (tail.render ++ List.replicate trailing 0))))
      (leading + K.length) gap := by
  have htailRender := tail.render_nonempty htailNe
  have hleftValue := deficitAt_before_cluster_gap
    (leading := leading) (gap := gap) (rest := tail.render ++
      List.replicate trailing 0) hKne
  have hrightValue := deficitAt_after_cluster_gap
    (leading := leading) (gap := gap) (K := K) (rest := tail.render)
      (suffix := List.replicate trailing 0) htailRender
  refine ⟨hgap, ?_, ?_, ?_, ?_⟩
  · simp
    omega
  · intro j hj
    exact deficitAt_inside_cluster_gap (leading := leading) (gap := gap)
      (K := K) (rest := tail.render ++ List.replicate trailing 0) hj
  · right
    refine ⟨by
      have hKlen : 0 < K.length := by
        have hKlen0 : K.length ≠ 0 := by
          intro hzero
          exact hKne (List.eq_nil_of_length_eq_zero hzero)
        omega
      omega, ?_⟩
    rw [hleftValue]
    exact hKpos _ (List.getLast_mem hKne)
  · right
    refine ⟨by
      have htailLen : 0 < tail.render.length := by
        have hne : tail.render.length ≠ 0 := by
          intro hzero
          exact htailRender (List.eq_nil_of_length_eq_zero hzero)
        omega
      simp only [List.length_append, List.length_replicate]
      omega, ?_⟩
    rw [hrightValue]
    exact tail.render_head_positive htailNe htailPos _ (List.head_mem_head? _)

/-- The R3 pair inequalities attached to every critical internal gap. -/
def CriticalPairBounds (n mu : ℕ) : PositiveClusterChain → Prop
  | .last _ => True
  | .cons K gap tail =>
      (gap = mu → n ≤ K.sum + tail.firstCluster.sum) ∧
        CriticalPairBounds n mu tail

/-- Rule R3 yields the pair bound for every critical gap in the concrete
cluster decomposition. -/
theorem criticalPairBounds_of_legal {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    CriticalPairBounds n (n - 2) chain := by
  induction chain generalizing leading with
  | last K => trivial
  | cons K gap tail ih =>
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKpos : ∀ x ∈ K, 0 < x := hclusterPos K
        (by simp [PositiveClusterChain.clusters])
      have hgap : 0 < gap := hgapPos gap (by simp [PositiveClusterChain.gaps])
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL
        exact hclusterNe L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL
        exact hclusterPos L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgapPos u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
      constructor
      · intro hcritical
        have hblock := internalClusterGap_isMaximal
          (n := n) (leading := leading) (trailing := trailing)
          hKne hKpos htailNe htailPos hgap
        have hleft : 0 < leading + K.length := by
          have hKlen : 0 < K.length := by cases K <;> simp_all
          omega
        have hright : leading + K.length + (n - 2) <
            (List.replicate leading 0 ++
              (K ++ (List.replicate (n - 2) 0 ++
                (tail.render ++ List.replicate trailing 0)))).length := by
          have htailRender := tail.render_nonempty htailNe
          have htailLen : 0 < tail.render.length := by
            have hne : tail.render.length ≠ 0 := by
              intro hzero
              exact htailRender (List.eq_nil_of_length_eq_zero hzero)
            omega
          simp only [List.length_append, List.length_replicate]
          omega
        have hlegalCritical : IsLegalDeficitSequence n
            (List.replicate leading 0 ++
              (K ++ (List.replicate (n - 2) 0 ++
                (tail.render ++ List.replicate trailing 0)))) := by
          simpa [PositiveClusterChain.render, hcritical, List.append_assoc] using hlegal
        have hrule := hlegalCritical.rule3 (leading + K.length)
          (by simpa [hcritical] using hblock) hleft hright
        have hleftEq := deficitAt_before_cluster_gap
          (leading := leading) (gap := n - 2)
          (rest := tail.render ++ List.replicate trailing 0) hKne
        have htailRender := tail.render_nonempty htailNe
        have hrightEq := deficitAt_after_cluster_gap
          (leading := leading) (gap := n - 2) (K := K)
          (rest := tail.render) (suffix := List.replicate trailing 0) htailRender
        rw [hleftEq, hrightEq] at hrule
        have hleftLe : K.getLast hKne ≤ K.sum :=
          list_member_le_sum (List.getLast_mem hKne)
        have hfirstNe : tail.firstCluster ≠ [] :=
          htailNe _ tail.firstCluster_mem_clusters
        have hheadEq := tail.render_head_eq_firstCluster_head hfirstNe htailRender
        rw [hheadEq] at hrule
        have hrightLe : tail.firstCluster.head hfirstNe ≤
            tail.firstCluster.sum := list_member_le_sum (List.head_mem hfirstNe)
        omega
      · let suffix := List.replicate gap 0 ++ tail.render ++
            List.replicate trailing 0
        have hlegalAppend : IsLegalDeficitSequence n
            ((List.replicate leading 0 ++ K) ++ suffix) := by
          simpa [suffix, PositiveClusterChain.render, List.append_assoc] using hlegal
        have hsuffixNe : suffix ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          simp [suffix] at this
          omega
        have hlegalTail := hlegalAppend.suffix_of_append hsuffixNe
        exact ih (leading := gap) (by simpa [suffix] using hlegalTail)
          htailNe htailPos htailGap

/-- State used to form the maximal runs of critical gaps.  The Boolean says
whether the suffix begins in a critical run; the list stores all run lengths. -/
private def extendCriticalRun : Bool × List ℕ → Bool × List ℕ
  | (false, runs) => (true, 1 :: runs)
  | (true, []) => (true, [1])
  | (true, p :: runs) => (true, (p + 1) :: runs)

private def criticalRunState (mu : ℕ) : List ℕ → Bool × List ℕ
  | [] => (false, [])
  | u :: gaps =>
      if u = mu then extendCriticalRun (criticalRunState mu gaps)
      else (false, (criticalRunState mu gaps).2)

/-- Lengths of the literal maximal runs of critical gaps (`u_j = μ`). -/
def maximalCriticalRunLengths (mu : ℕ) (gaps : List ℕ) : List ℕ :=
  (criticalRunState mu gaps).2

/-- Number `g` of critical gaps. -/
def criticalGapCount (mu : ℕ) (gaps : List ℕ) : ℕ := gaps.count mu

/-- Number `g^{odd}` of maximal critical-gap runs of odd length. -/
def oddCriticalRunCount (mu : ℕ) (gaps : List ℕ) : ℕ :=
  ((maximalCriticalRunLengths mu gaps).filter fun p => p % 2 = 1).length

private theorem criticalRunState_true_nonempty (mu : ℕ) (gaps : List ℕ) :
    (criticalRunState mu gaps).1 = true → (criticalRunState mu gaps).2 ≠ [] := by
  induction gaps with
  | nil => simp [criticalRunState]
  | cons u gaps ih =>
      by_cases hu : u = mu
      · simp only [criticalRunState, if_pos hu]
        cases hstate : criticalRunState mu gaps with
        | mk starts runs =>
            cases starts <;> cases runs <;> simp [extendCriticalRun]
      · simp [criticalRunState, hu]

theorem maximalCriticalRunLengths_sum (mu : ℕ) (gaps : List ℕ) :
    (maximalCriticalRunLengths mu gaps).sum = criticalGapCount mu gaps := by
  induction gaps with
  | nil => simp [maximalCriticalRunLengths, criticalRunState, criticalGapCount]
  | cons u gaps ih =>
      by_cases hu : u = mu
      · subst u
        simp only [criticalRunState, if_pos rfl, maximalCriticalRunLengths,
          criticalGapCount, List.count_cons, beq_self_eq_true, if_true]
        cases hstate : criticalRunState mu gaps with
        | mk starts runs =>
            have ih' : runs.sum = gaps.count mu := by
              simpa [maximalCriticalRunLengths, hstate, criticalGapCount] using ih
            cases starts with
            | false =>
                simp [extendCriticalRun]
                omega
            | true =>
                have hne : runs ≠ [] := by
                  have := criticalRunState_true_nonempty mu gaps
                  simpa [hstate] using this
                cases runs with
                | nil => contradiction
                | cons p runs =>
                    simp only [List.sum_cons] at ih'
                    simp [extendCriticalRun]
                    omega
      · simp only [criticalRunState, if_neg hu, maximalCriticalRunLengths,
          criticalGapCount, List.count_cons]
        simp [hu, maximalCriticalRunLengths, criticalGapCount] at ih ⊢
        exact ih

private theorem odd_sum_has_odd_member {values : List ℕ}
    (hodd : Odd values.sum) : ∃ p ∈ values, Odd p := by
  induction values with
  | nil => simp at hodd
  | cons a values ih =>
      rcases Nat.even_or_odd a with haeven | haodd
      · rcases haeven with ⟨q, hq⟩
        by_cases htail : Odd values.sum
        · obtain ⟨p, hp, hpodd⟩ := ih htail
          exact ⟨p, by simp; exact Or.inr hp, hpodd⟩
        · rcases Nat.even_or_odd values.sum with hteven | htodd
          · rcases hteven with ⟨v, hv⟩
            rcases hodd with ⟨w, hw⟩
            simp at hw
            omega
          · exact (htail htodd).elim
      · exact ⟨a, by simp, haodd⟩

/-- If `g` is odd, at least one maximal critical run has odd length. -/
theorem oddCriticalRunCount_pos_of_odd {mu : ℕ} {gaps : List ℕ}
    (hodd : Odd (criticalGapCount mu gaps)) :
    1 ≤ oddCriticalRunCount mu gaps := by
  have hrunsOdd : Odd (maximalCriticalRunLengths mu gaps).sum := by
    rw [maximalCriticalRunLengths_sum]
    exact hodd
  obtain ⟨p, hp, hpodd⟩ := odd_sum_has_odd_member hrunsOdd
  have hpmod : p % 2 = 1 := by
    rcases hpodd with ⟨q, hq⟩
    omega
  have hmem : p ∈ (maximalCriticalRunLengths mu gaps).filter
      (fun p => p % 2 = 1) := by simp [hp, hpmod]
  unfold oddCriticalRunCount
  have hne : (maximalCriticalRunLengths mu gaps).filter
      (fun p => p % 2 = 1) ≠ [] := List.ne_nil_of_mem hmem
  cases hlist : (maximalCriticalRunLengths mu gaps).filter
      (fun p => p % 2 = 1) with
  | nil => contradiction
  | cons a tail => simp

/-- Greedy number of disjoint adjacent cluster pairs selected across
critical gaps.  A selected edge skips the next edge, so selected pairs are
literally disjoint. -/
def criticalPairCount (mu : ℕ) : List ℕ → ℕ
  | [] => 0
  | [u] => if u = mu then 1 else 0
  | u :: v :: gaps =>
      if u = mu then 1 + criticalPairCount mu gaps
      else criticalPairCount mu (v :: gaps)

theorem criticalPairCount_cons_of_ne {mu u : ℕ} (gaps : List ℕ)
    (hu : u ≠ mu) :
    criticalPairCount mu (u :: gaps) = criticalPairCount mu gaps := by
  cases gaps with
  | nil => simp [criticalPairCount, hu]
  | cons v rest => simp [criticalPairCount, hu]

/-- Pairing the critical gaps run by run selects `(p+1)/2` disjoint pairs
from a run of length `p`; equivalently twice the selected-pair count is
`g + g^{odd}`. -/
theorem criticalPairCount_twice (mu : ℕ) : ∀ gaps : List ℕ,
    2 * criticalPairCount mu gaps =
      criticalGapCount mu gaps + oddCriticalRunCount mu gaps
  | [] => by
      simp [criticalPairCount, criticalGapCount, oddCriticalRunCount,
        maximalCriticalRunLengths, criticalRunState]
  | [u] => by
      by_cases hu : u = mu
      · subst u
        simp [criticalPairCount, criticalGapCount, oddCriticalRunCount,
          maximalCriticalRunLengths, criticalRunState, extendCriticalRun]
      · simp [criticalPairCount, criticalGapCount, oddCriticalRunCount,
          maximalCriticalRunLengths, criticalRunState, extendCriticalRun, hu]
  | u :: v :: rest => by
      by_cases hu : u = mu
      · subst u
        have ihrest := criticalPairCount_twice mu rest
        by_cases hv : v = mu
        · subst v
          cases hstate : criticalRunState mu rest with
          | mk starts runs =>
              cases starts with
              | false =>
                  simp [criticalPairCount, criticalGapCount,
                    oddCriticalRunCount, maximalCriticalRunLengths,
                    criticalRunState, extendCriticalRun, hstate] at ihrest ⊢
                  omega
              | true =>
                  have hne : runs ≠ [] := by
                    have := criticalRunState_true_nonempty mu rest
                    simpa [hstate] using this
                  cases runs with
                  | nil => contradiction
                  | cons p runs =>
                      have hmod : (p + 2) % 2 = p % 2 := by omega
                      have hfilter :
                          (((p + 2) :: runs).filter fun q => q % 2 = 1).length =
                            ((p :: runs).filter fun q => q % 2 = 1).length := by
                        simp only [List.filter_cons]
                        rw [hmod]
                        split <;> simp
                      simp [criticalPairCount, criticalGapCount,
                        oddCriticalRunCount, maximalCriticalRunLengths,
                        criticalRunState, extendCriticalRun, hstate] at ihrest ⊢
                      rw [hfilter]
                      omega
        · simp [criticalPairCount, criticalGapCount, oddCriticalRunCount,
            maximalCriticalRunLengths, criticalRunState,
            extendCriticalRun, hv] at ihrest ⊢
          omega
      · have ihTail := criticalPairCount_twice mu (v :: rest)
        simpa [criticalPairCount, criticalGapCount, oddCriticalRunCount,
          maximalCriticalRunLengths, criticalRunState, hu] using ihTail
termination_by gaps => gaps.length

private theorem legal_tail_of_cluster_cons {n leading trailing gap : ℕ}
    {K : List ℕ} {tail : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++
        (PositiveClusterChain.cons K gap tail).render ++
          List.replicate trailing 0))
    (hgap : 0 < gap) :
    IsLegalDeficitSequence n
      (List.replicate gap 0 ++ tail.render ++ List.replicate trailing 0) := by
  let suffix := List.replicate gap 0 ++ tail.render ++ List.replicate trailing 0
  have happend : IsLegalDeficitSequence n
      ((List.replicate leading 0 ++ K) ++ suffix) := by
    simpa [suffix, PositiveClusterChain.render, List.append_assoc] using hlegal
  have hsuffix : suffix ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [suffix] at this
    omega
  exact happend.suffix_of_append hsuffix

private theorem nonterminal_head_two_charge {n leading trailing gap : ℕ}
    {K : List ℕ} {tail : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++
        (PositiveClusterChain.cons K gap tail).render ++
          List.replicate trailing 0))
    (hKne : K ≠ []) (hKpos : ∀ x ∈ K, 0 < x) (hgap : 0 < gap) :
    2 ≤ K.sum + leftClusterException leading := by
  have hKlen : 1 ≤ K.length := by
    have hne : K.length ≠ 0 := by
      intro hzero
      exact hKne (List.eq_nil_of_length_eq_zero hzero)
    omega
  by_cases hlead : leading = 0
  · subst leading
    have hsum := positive_length_le_sum hKpos
    simp [leftClusterException]
    omega
  · have hleadPos : 0 < leading := by omega
    have hgap0 : gap ≠ 0 := by omega
    have hextra := precededPositiveCluster_charge
      (hlegal := by
        simpa [PositiveClusterChain.render, List.append_assoc] using hlegal)
      hleadPos hKne hKpos (by
        intro z hz
        have hz' : (List.replicate gap 0).head? = some z := by
          simpa [hgap0] using hz
        have hhead := head?_replicate_zero_of_pos hgap
        rw [hhead] at hz'
        exact (Option.some.inj hz').symm) (by
          left
          simp [hgap0])
    simp [leftClusterException, hlead]
    omega

/-- Cluster-charge inequality including the odd-run correction.  The proof
greedily pairs disjoint clusters across critical gaps; a selected pair costs
at least `n ≥ 6`, accounting for the two baseline cluster charges and two
units of critical-gap excess. -/
theorem clusterCriticalCharge {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hn : 6 ≤ n)
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u)
    (hpairs : CriticalPairBounds n (n - 2) chain) :
    2 * chain.clusters.length +
        2 * criticalPairCount (n - 2) chain.gaps ≤
      (chain.clusters.map List.sum).sum +
        clusterExceptionCount leading chain trailing := by
  cases chain with
  | last K =>
      have hcharge := cluster_length_charge hlegal hclusterNe hclusterPos hgapPos
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKlen : 1 ≤ K.length := by
        have hne : K.length ≠ 0 := by
          intro hzero
          exact hKne (List.eq_nil_of_length_eq_zero hzero)
        omega
      simp [PositiveClusterChain.clusters, PositiveClusterChain.gaps,
        criticalPairCount] at hcharge ⊢
      omega
  | cons K gap tail =>
      have hKne : K ≠ [] := hclusterNe K (by simp [PositiveClusterChain.clusters])
      have hKpos : ∀ x ∈ K, 0 < x := hclusterPos K
        (by simp [PositiveClusterChain.clusters])
      have hgap : 0 < gap := hgapPos gap (by simp [PositiveClusterChain.gaps])
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL
        exact hclusterNe L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL
        exact hclusterPos L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgapPos u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
      have hlegalTail := legal_tail_of_cluster_cons hlegal hgap
      by_cases hcritical : gap = n - 2
      · have hpair := hpairs.1 hcritical
        cases tail with
        | last L =>
            simp only [PositiveClusterChain.firstCluster] at hpair
            simp [PositiveClusterChain.clusters, PositiveClusterChain.gaps,
              PositiveClusterChain.firstCluster, criticalPairCount,
              hcritical, clusterExceptionCount, rightClusterException]
            omega
        | cons L nextGap rest =>
            have hnext : 0 < nextGap := htailGap nextGap
              (by simp [PositiveClusterChain.gaps])
            have hrestNe : ∀ A ∈ rest.clusters, A ≠ [] := by
              intro A hA
              exact htailNe A (by simp [PositiveClusterChain.clusters]; exact Or.inr hA)
            have hrestPos : ∀ A ∈ rest.clusters, ∀ x ∈ A, 0 < x := by
              intro A hA
              exact htailPos A (by simp [PositiveClusterChain.clusters]; exact Or.inr hA)
            have hrestGap : ∀ u ∈ rest.gaps, 0 < u := by
              intro u hu
              exact htailGap u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
            have hlegalRest := legal_tail_of_cluster_cons hlegalTail hnext
            have hrestCharge := clusterCriticalCharge (chain := rest)
              (leading := nextGap) (trailing := trailing) hn hlegalRest
              hrestNe hrestPos hrestGap hpairs.2.2
            have hleftNext : leftClusterException nextGap = 0 := by
              simp [leftClusterException]
              omega
            simp only [PositiveClusterChain.firstCluster] at hpair
            simp [PositiveClusterChain.clusters, PositiveClusterChain.gaps,
              List.length_cons, List.map_cons, List.sum_cons,
              PositiveClusterChain.firstCluster, criticalPairCount, hcritical,
              clusterExceptionCount, rightClusterException]
            simp only [clusterExceptionCount] at hrestCharge
            rw [hleftNext] at hrestCharge
            omega
      · have hhead := nonterminal_head_two_charge hlegal hKne hKpos hgap
        have htailCharge := clusterCriticalCharge (chain := tail)
          (leading := gap) (trailing := trailing) hn hlegalTail
          htailNe htailPos htailGap hpairs.2
        have hleftGap : leftClusterException gap = 0 := by
          simp [leftClusterException]
          omega
        have hpairCount := criticalPairCount_cons_of_ne tail.gaps hcritical
        simp only [PositiveClusterChain.clusters, PositiveClusterChain.gaps,
          List.length_cons, List.map_cons, List.sum_cons,
          clusterExceptionCount,
          rightClusterException]
        rw [hpairCount]
        simp only [clusterExceptionCount] at htailCharge
        rw [hleftGap] at htailCharge
        omega
termination_by chain.clusters.length
decreasing_by
  all_goals
    subst chain
    simp_all only [PositiveClusterChain.clusters, List.length_cons]
    omega

/-- The cluster-charge inequality in the literal `g+g^{odd}` form used in
the paper.  Both counts come from the maximal-run construction above. -/
theorem clusterCriticalCharge_with_runs {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hn : 6 ≤ n)
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    2 * chain.clusters.length +
        criticalGapCount (n - 2) chain.gaps +
        oddCriticalRunCount (n - 2) chain.gaps ≤
      (chain.clusters.map List.sum).sum +
        clusterExceptionCount leading chain trailing := by
  have hpairs := criticalPairBounds_of_legal hlegal hclusterNe hclusterPos hgapPos
  have hcharge := clusterCriticalCharge hn hlegal hclusterNe hclusterPos hgapPos hpairs
  have hcount := criticalPairCount_twice (n - 2) chain.gaps
  omega

private theorem shaped_not_all_zero {leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    ¬ ∀ x ∈ List.replicate leading 0 ++ chain.render ++
        List.replicate trailing 0, x = 0 := by
  have hrender : chain.render ≠ [] := chain.render_nonempty hclusterNe
  let x := chain.render.head hrender
  have hxhead : x ∈ chain.render := List.head_mem hrender
  have hxhead? : x ∈ chain.render.head? := by
    exact List.head?_eq_some_head hrender
  have hxpos : 0 < x :=
    chain.render_head_positive hclusterNe hclusterPos x hxhead?
  intro hall
  have hxzero := hall x (by simp [hxhead])
  omega

private theorem shaped_leadingZeros_le {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    leading ≤ n - 2 := by
  by_cases hzero : leading = 0
  · omega
  have hbounds := legal_zeroInterval_bounds hlegal
    (start := 0) (blockLength := leading) (by omega) (by simp) (by
      intro j hj
      simp [deficitAt, List.getElem?_append, hj])
  exact hbounds.2 (shaped_not_all_zero hclusterNe hclusterPos)

private theorem shaped_trailingZeros_le {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    trailing ≤ n - 2 := by
  by_cases hzero : trailing = 0
  · omega
  have hbounds := legal_zeroInterval_bounds hlegal
    (start := leading + chain.render.length) (blockLength := trailing)
    (by omega) (by simp; omega) (by
      intro j hj
      unfold deficitAt
      rw [List.getElem?_append_right (by simp)]
      have hindex : leading + chain.render.length + j -
          (List.replicate leading 0 ++ chain.render).length = j := by
        simp
      rw [hindex, List.getElem?_eq_getElem (by simpa using hj)]
      simp)
  exact hbounds.2 (shaped_not_all_zero hclusterNe hclusterPos)

/-- Every intervening zero block in the concrete decomposition has the R1
bound `u_j ≤ n-2`. -/
theorem internalClusterGaps_le {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    ∀ u ∈ chain.gaps, u ≤ n - 2 := by
  induction chain generalizing leading with
  | last K => simp [PositiveClusterChain.gaps]
  | cons K gap tail ih =>
      have hgap : 0 < gap := hgapPos gap (by simp [PositiveClusterChain.gaps])
      have htailNe : ∀ L ∈ tail.clusters, L ≠ [] := by
        intro L hL
        exact hclusterNe L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailPos : ∀ L ∈ tail.clusters, ∀ x ∈ L, 0 < x := by
        intro L hL
        exact hclusterPos L (by simp [PositiveClusterChain.clusters]; exact Or.inr hL)
      have htailGap : ∀ u ∈ tail.gaps, 0 < u := by
        intro u hu
        exact hgapPos u (by simp [PositiveClusterChain.gaps]; exact Or.inr hu)
      have hlegalTail := legal_tail_of_cluster_cons hlegal hgap
      have hheadBound := shaped_leadingZeros_le hlegalTail htailNe htailPos
      have htailBound := ih (leading := gap) hlegalTail htailNe htailPos htailGap
      intro u hu
      simp [PositiveClusterChain.gaps] at hu
      rcases hu with rfl | hu
      · exact hheadBound
      · exact htailBound u hu

private theorem rightClusterException_eq_one_trailing_zero
    (chain : PositiveClusterChain) (trailing : ℕ)
    (h : rightClusterException chain trailing = 1) : trailing = 0 := by
  induction chain with
  | last K =>
      simp [rightClusterException] at h
      exact h.1
  | cons K gap tail ih =>
      exact ih (by simpa [rightClusterException] using h)

/-- R1 at the two endpoint zero blocks, with the two literal endpoint
exceptions deleting the corresponding allowance. -/
theorem endpointZeroBlocks_bound {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    leading + trailing ≤
      (n - 2) * (2 - clusterExceptionCount leading chain trailing) := by
  have hleading := shaped_leadingZeros_le hlegal hclusterNe hclusterPos
  have htrailing := shaped_trailingZeros_le hlegal hclusterNe hclusterPos
  have hleftLe := leftClusterException_le_one leading
  have hrightLe := rightClusterException_le_one chain trailing
  have hleftZero : leftClusterException leading = 1 → leading = 0 := by
    simp [leftClusterException]
  have hrightZero : rightClusterException chain trailing = 1 → trailing = 0 :=
    rightClusterException_eq_one_trailing_zero chain trailing
  have hleftCases : leftClusterException leading = 0 ∨
      leftClusterException leading = 1 := by omega
  have hrightCases : rightClusterException chain trailing = 0 ∨
      rightClusterException chain trailing = 1 := by omega
  rcases hleftCases with hleft | hleft <;>
    rcases hrightCases with hright | hright
  · rw [clusterExceptionCount, hleft, hright]
    simp
    omega
  · have := hrightZero hright
    rw [clusterExceptionCount, hleft, hright]
    simp
    omega
  · have := hleftZero hleft
    rw [clusterExceptionCount, hleft, hright]
    simp
    omega
  · have hL := hleftZero hleft
    have hR := hrightZero hright
    rw [clusterExceptionCount, hleft, hright]
    simp [hL, hR]

private theorem gapSum_le_pred_mul_add_count (mu : ℕ) :
    ∀ gaps : List ℕ, (∀ u ∈ gaps, u ≤ mu) →
      gaps.sum ≤ gaps.length * (mu - 1) + gaps.count mu
  | [], _ => by simp
  | u :: gaps, hbound => by
      have hu := hbound u (by simp)
      have htail : ∀ v ∈ gaps, v ≤ mu := by
        intro v hv
        exact hbound v (by simp; exact Or.inr hv)
      have ih := gapSum_le_pred_mul_add_count mu gaps htail
      by_cases hcritical : u = mu
      · subst u
        simp [Nat.add_mul]
        omega
      · have hsmall : u ≤ mu - 1 := by omega
        simp [hcritical, Nat.add_mul]
        omega

/-- Among `s-1` internal gaps, only the `g` critical gaps may use the
last unit of the R1 allowance. -/
theorem internalGapSum_bound {n leading trailing : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render ++ List.replicate trailing 0))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x)
    (hgapPos : ∀ u ∈ chain.gaps, 0 < u) :
    chain.gaps.sum ≤
      (chain.clusters.length - 1) * (n - 3) +
        criticalGapCount (n - 2) chain.gaps := by
  have hgapBound := internalClusterGaps_le hlegal hclusterNe hclusterPos hgapPos
  have hraw := gapSum_le_pred_mul_add_count (n - 2) chain.gaps hgapBound
  have hn := hlegal.six_le
  have hlength := chain.gaps_length
  unfold criticalGapCount
  have hpred : n - 2 - 1 = n - 3 := by omega
  rw [hpred] at hraw
  have hgapLength : chain.gaps.length = chain.clusters.length - 1 := by omega
  simpa [hgapLength] using hraw

private theorem clusterLengthSum_le_total {chain : PositiveClusterChain}
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    (chain.clusters.map List.length).sum ≤
      (chain.clusters.map List.sum).sum := by
  apply List.sum_le_sum
  intro K hK
  exact positive_length_le_sum (hclusterPos K hK)

private theorem clusterCount_le_lengthSum {chain : PositiveClusterChain}
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ []) :
    chain.clusters.length ≤ (chain.clusters.map List.length).sum := by
  have hone : (chain.clusters.map fun _ => 1).sum = chain.clusters.length := by simp
  rw [← hone]
  apply List.sum_le_sum
  intro K hK
  have hKne := hclusterNe K hK
  have hlen : K.length ≠ 0 := by
    intro hzero
    exact hKne (List.eq_nil_of_length_eq_zero hzero)
  omega

/-- For total deficit at least two, simultaneous left and right endpoint
exceptions refer to distinct clusters.  In particular the terminal `[1]`
cannot also be the sole initial cluster. -/
theorem endpointExceptions_distinct_of_total_ge_two
    {leading trailing D : ℕ} {chain : PositiveClusterChain}
    (hD : 2 ≤ D)
    (htotal : (chain.clusters.map List.sum).sum = D)
    (_hleft : leftClusterException leading = 1)
    (hright : rightClusterException chain trailing = 1) :
    2 ≤ chain.clusters.length := by
  cases chain with
  | last K =>
      have hshape : trailing = 0 ∧ K = [1] := by
        simpa [rightClusterException] using hright
      rcases hshape with ⟨_, rfl⟩
      simp [PositiveClusterChain.clusters] at htotal
      omega
  | cons K gap tail =>
      cases tail <;> simp [PositiveClusterChain.clusters]

/- The right side here is the integer form of (6.7).  Keeping it in
`ℤ` is essential when `δ=2`: the paper's term `5-n` is negative, whereas
natural subtraction would silently replace it by zero. -/
private theorem six_delta_parity_cases {n D delta r : ℕ}
    (hn : 6 ≤ n) (hD : 2 ≤ D) (hdelta : delta ≤ 2)
    (hbound : (r : ℤ) ≤
      (n : ℤ) - 1 - (delta : ℤ) * ((n : ℤ) - 3) +
        (((n - 4) * ((D + delta) / 2) : ℕ) : ℤ) + (D : ℤ)) :
    r ≤ maxLegalLength n D := by
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have hlarge : ¬ D ≤ 1 := by omega
  have hdeltaCases : delta = 0 ∨ delta = 1 ∨ delta = 2 := by omega
  have hmod := Nat.mod_two_eq_zero_or_one D
  let t := D / 2
  rcases hmod with heven | hodd
  · have hDeq : D = 2 * t := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hdeltaCases with rfl | rfl | rfl
    · -- `δ=0`, `D=2t`.
      have hfloor : (D + 0) / 2 = t := by omega
      have hN : maxLegalLength n D = (n - 1) + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, heven]
        change (n - 1) + (n - 2) * t + 0 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
    · -- `δ=1`, `D=2t`.
      have hfloor : (D + 1) / 2 = t := by omega
      have hN : maxLegalLength n D = (n - 1) + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, heven]
        change (n - 1) + (n - 2) * t + 0 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        nlinarith
      exact_mod_cast hgoal
    · -- `δ=2`, `D=2t`.
      have hfloor : (D + 2) / 2 = t + 1 := by omega
      have hN : maxLegalLength n D = (n - 1) + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, heven]
        change (n - 1) + (n - 2) * t + 0 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
  · have hDeq : D = 2 * t + 1 := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hdeltaCases with rfl | rfl | rfl
    · -- `δ=0`, `D=2t+1`.
      have hfloor : (D + 0) / 2 = t := by omega
      have hN : maxLegalLength n D = n + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, hodd]
        change (n - 1) + (n - 2) * t + 1 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤ ((n + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
    · -- `δ=1`, `D=2t+1`.
      have hfloor : (D + 1) / 2 = t + 1 := by omega
      have hN : maxLegalLength n D = n + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, hodd]
        change (n - 1) + (n - 2) * t + 1 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤ ((n + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
    · -- `δ=2`, `D=2t+1`.
      have hfloor : (D + 2) / 2 = t + 1 := by omega
      have hN : maxLegalLength n D = n + (n - 2) * t := by
        unfold maxLegalLength
        rw [if_neg hlarge, hodd]
        change (n - 1) + (n - 2) * t + 1 = _
        omega
      rw [hfloor] at hbound
      rw [hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤ ((n + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal

/-- **Lemma `lem:charging`.**  Every actual legal deficit sequence has
length at most `N_n(D)` for its actual total `D`.  The proof above constructs
its maximal positive clusters, endpoint zero blocks, critical gaps, and
maximal critical-gap runs; none of their numerical bounds is assumed. -/
theorem legalDeficitSequence_length_le_maxLegalLength {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d) :
    d.length ≤ maxLegalLength n (deficitSequenceTotal d) := by
  let D := deficitSequenceTotal d
  change d.length ≤ maxLegalLength n D
  have hsum : d.sum = D := by rfl
  have hn : 6 ≤ n := hlegal.six_le
  by_cases hDzero : D = 0
  · have hall : ∀ x ∈ d, x = 0 := by
      apply List.sum_eq_zero_iff.mp
      omega
    have hrule := hlegal.rule1
    rw [if_pos hall] at hrule
    simp [maxLegalLength, hDzero]
    exact hrule
  by_cases hDone : D = 1
  · have hpositive : ∃ x ∈ d, 0 < x := by
      by_contra hnot
      have hall : ∀ x ∈ d, x = 0 := by
        intro x hx
        by_contra hxzero
        exact hnot ⟨x, hx, by omega⟩
      have hzeroSum := List.sum_eq_zero hall
      omega
    obtain ⟨dec, _⟩ := exists_positiveClusterDecomposition hpositive
    have hlegalShape : IsLegalDeficitSequence n
        (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
          List.replicate dec.trailingZeros 0) := by
      rw [← dec.rebuild]
      exact hlegal
    have hclusterTotal : (dec.chain.clusters.map List.sum).sum = 1 := by
      have hshapeSum :
          (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
            List.replicate dec.trailingZeros 0).sum = 1 := by
        rw [← dec.rebuild]
        omega
      simpa using hshapeSum
    have hlengthTotal := clusterLengthSum_le_total dec.cluster_positive
    have hcountLength := clusterCount_le_lengthSum dec.cluster_nonempty
    have hcountPos : 1 ≤ dec.chain.clusters.length := by
      cases dec.chain <;> simp [PositiveClusterChain.clusters]
    have hclusterCount : dec.chain.clusters.length = 1 := by omega
    cases hchain : dec.chain with
    | cons K gap tail =>
        have htwo : 2 ≤ dec.chain.clusters.length := by
          rw [hchain]
          cases tail <;> simp [PositiveClusterChain.clusters]
        omega
    | last K =>
        have hKne : K ≠ [] := by
          exact dec.cluster_nonempty K (by
            rw [hchain]
            simp [PositiveClusterChain.clusters])
        have hKpos : ∀ x ∈ K, 0 < x := by
          exact dec.cluster_positive K (by
            rw [hchain]
            simp [PositiveClusterChain.clusters])
        have hKsum : K.sum = 1 := by
          simpa [hchain, PositiveClusterChain.clusters] using hclusterTotal
        have hKlenLe := positive_length_le_sum hKpos
        have hKlenPos : 1 ≤ K.length := by
          have : K.length ≠ 0 := by
            intro hzero
            exact hKne (List.eq_nil_of_length_eq_zero hzero)
          omega
        have hKlen : K.length = 1 := by omega
        obtain ⟨a, hKa⟩ := List.length_eq_one_iff.mp hKlen
        have ha : a = 1 := by simpa [hKa] using hKsum
        subst a
        have hlegalOne : IsLegalDeficitSequence n
            (List.replicate dec.leadingZeros 0 ++ [1] ++
              List.replicate dec.trailingZeros 0) := by
          simpa [hchain, hKa, PositiveClusterChain.render] using hlegalShape
        have hnotBoth : dec.leadingZeros = 0 ∨ dec.trailingZeros = 0 := by
          by_contra hboth
          have hlead : 0 < dec.leadingZeros := by omega
          have htrail : 0 < dec.trailingZeros := by omega
          have hi : dec.leadingZeros - 1 + 2 <
              (List.replicate dec.leadingZeros 0 ++ [1] ++
                List.replicate dec.trailingZeros 0).length := by
            simp
            omega
          have hrule := hlegalOne.rule2 (dec.leadingZeros - 1) hi
          apply hrule
          constructor
          · exact shaped_before_deficit hlead [1]
              (List.replicate dec.trailingZeros 0)
          constructor
          · have hindex : dec.leadingZeros - 1 + 1 = dec.leadingZeros := by omega
            rw [hindex]
            exact shaped_first_deficit (lead := dec.leadingZeros)
              (a := 1) [] (List.replicate dec.trailingZeros 0)
          · have hindex : dec.leadingZeros - 1 + 2 = dec.leadingZeros + 1 := by omega
            rw [hindex]
            simp [deficitAt, List.getElem?_append, htrail]
        have hleadBound := shaped_leadingZeros_le
          (chain := PositiveClusterChain.last [1]) hlegalOne
          (by simp [PositiveClusterChain.clusters])
          (by simp [PositiveClusterChain.clusters])
        have htrailBound := shaped_trailingZeros_le
          (chain := PositiveClusterChain.last [1]) hlegalOne
          (by simp [PositiveClusterChain.clusters])
          (by simp [PositiveClusterChain.clusters])
        have hlength : d.length =
            dec.leadingZeros + 1 + dec.trailingZeros := by
          have hrebuildLength := congrArg List.length dec.rebuild
          rw [hchain, hKa] at hrebuildLength
          simp [PositiveClusterChain.render] at hrebuildLength
          omega
        have hbound : d.length ≤ n - 1 := by
          rcases hnotBoth with hleft | hright
          · omega
          · omega
        simpa [maxLegalLength, hDone] using hbound
  · have hDlarge : 2 ≤ D := by omega
    have hpositive : ∃ x ∈ d, 0 < x := by
      by_contra hnot
      have hall : ∀ x ∈ d, x = 0 := by
        intro x hx
        by_contra hxzero
        exact hnot ⟨x, hx, by omega⟩
      have hzeroSum := List.sum_eq_zero hall
      omega
    obtain ⟨dec, _⟩ := exists_positiveClusterDecomposition hpositive
    have hlegalShape : IsLegalDeficitSequence n
        (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
          List.replicate dec.trailingZeros 0) := by
      rw [← dec.rebuild]
      exact hlegal
    have htotal : (dec.chain.clusters.map List.sum).sum = D := by
      have hshapeSum :
          (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
            List.replicate dec.trailingZeros 0).sum = D := by
        rw [← dec.rebuild]
        exact hsum
      simpa using hshapeSum
    let s := dec.chain.clusters.length
    let M := (dec.chain.clusters.map List.length).sum
    let U := dec.chain.gaps.sum
    let delta := clusterExceptionCount dec.leadingZeros dec.chain dec.trailingZeros
    let g := criticalGapCount (n - 2) dec.chain.gaps
    let gOdd := oddCriticalRunCount (n - 2) dec.chain.gaps
    have hspos : 1 ≤ s := by
      dsimp [s]
      have hne := dec.chain.clusters_nonempty
      cases hclusters : dec.chain.clusters with
      | nil => contradiction
      | cons K rest => simp
    have hdelta : delta ≤ 2 := by
      exact clusterExceptionCount_le_two _ _ _
    have hendpoint := endpointZeroBlocks_bound hlegalShape
      dec.cluster_nonempty dec.cluster_positive
    change dec.leadingZeros + dec.trailingZeros ≤ (n - 2) * (2 - delta) at hendpoint
    have hgapSum := internalGapSum_bound hlegalShape dec.cluster_nonempty
      dec.cluster_positive dec.gap_positive
    change U ≤ (s - 1) * (n - 3) + g at hgapSum
    have hcluster := cluster_length_charge hlegalShape dec.cluster_nonempty
      dec.cluster_positive dec.gap_positive
    change M + s ≤ (dec.chain.clusters.map List.sum).sum + delta at hcluster
    rw [htotal] at hcluster
    have hcritical := clusterCriticalCharge_with_runs hlegalShape.six_le hlegalShape
      dec.cluster_nonempty dec.cluster_positive dec.gap_positive
    change 2 * s + g + gOdd ≤
      (dec.chain.clusters.map List.sum).sum + delta at hcritical
    rw [htotal] at hcritical
    have hdistinct : leftClusterException dec.leadingZeros = 1 →
        rightClusterException dec.chain dec.trailingZeros = 1 →
        2 ≤ dec.chain.clusters.length := by
      intro hleft hright
      exact endpointExceptions_distinct_of_total_ge_two hDlarge htotal hleft hright
    have hlength : d.length = dec.leadingZeros + dec.trailingZeros + M + U := by
      have hrebuildLength := congrArg List.length dec.rebuild
      simp [M, U] at hrebuildLength
      omega
    have hraw : d.length + s ≤
        (n - 2) * (2 - delta) +
          (s - 1) * (n - 3) + g + D + delta := by
      omega
    have hrawInt : (d.length : ℤ) + (s : ℤ) ≤
        (((n - 2) * (2 - delta) +
          (s - 1) * (n - 3) + g + D + delta : ℕ) : ℤ) := by
      exact_mod_cast hraw
    have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
    have htwoDelta : ((2 - delta : ℕ) : ℤ) = 2 - (delta : ℤ) :=
      Int.ofNat_sub hdelta
    have hsPred : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 :=
      Int.ofNat_sub hspos
    simp only [Nat.cast_add, Nat.cast_mul, hn2, hn3, htwoDelta, hsPred] at hrawInt
    have hlengthIntExpanded : (d.length : ℤ) ≤
        (n : ℤ) - 1 - (delta : ℤ) * ((n : ℤ) - 3) +
          ((n : ℤ) - 4) * (s : ℤ) + (g : ℤ) + (D : ℤ) := by
      have htemp : (d.length : ℤ) ≤
          ((n : ℤ) - 2) * (2 - (delta : ℤ)) +
            ((s : ℤ) - 1) * ((n : ℤ) - 3) +
              (g : ℤ) + (D : ℤ) + (delta : ℤ) - (s : ℤ) := by
        omega
      calc
        (d.length : ℤ) ≤ _ := htemp
        _ = _ := by ring
    have hchargeInt : (2 * s : ℤ) ≤
        (D : ℤ) + (delta : ℤ) - (g : ℤ) - (gOdd : ℤ) := by
      have haddInt : ((2 * s + g + gOdd : ℕ) : ℤ) ≤
          ((D + delta : ℕ) : ℤ) := by
        exact_mod_cast hcritical
      simp only [Nat.cast_add, Nat.cast_mul] at haddInt
      omega
    have hodd : Odd g → 1 ≤ gOdd := by
      intro hg
      exact oddCriticalRunCount_pos_of_odd hg
    have hslack := criticalGapSlack hlegalShape.six_le hchargeInt hodd
    have hslackInt :
        (((n - 4) * s + g : ℕ) : ℤ) ≤
          (((n - 4) * ((D + delta) / 2) : ℕ) : ℤ) := by
      exact_mod_cast hslack
    have hlengthInt : (d.length : ℤ) ≤
        (n : ℤ) - 1 - (delta : ℤ) * ((n : ℤ) - 3) +
          (((n - 4) * ((D + delta) / 2) : ℕ) : ℤ) + (D : ℤ) := by
      have hleftCast : (((n - 4) * s + g : ℕ) : ℤ) =
          ((n : ℤ) - 4) * (s : ℤ) + (g : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn4]
      rw [hleftCast] at hslackInt
      omega
    exact six_delta_parity_cases hlegalShape.six_le hDlarge hdelta hlengthInt

end SuperpermutationLowerBound
