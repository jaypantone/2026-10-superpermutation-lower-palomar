module

public import SuperpermutationLowerBound.Section06.DeficitFunction
public import Mathlib.Data.List.SplitBy

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Exact witnesses for `N_n(D)` and the arithmetic critical-gap slack
lemma.
-/

/-- Two entries have the same sign-block status when they are either both
zero or both positive. -/
def sameZeroStatus (a b : ℕ) : Bool := decide ((a = 0) ↔ (b = 0))

/-- The canonical maximal zero/positive block decomposition. -/
def maximalSignBlocks (d : List ℕ) : List (List ℕ) :=
  d.splitBy sameZeroStatus

private theorem getLast?_replicate_succ_zero (q : ℕ) :
    (List.replicate (q + 1) 0).getLast? = some 0 := by
  induction q with
  | zero => rfl
  | succ q ih => simpa [List.replicate_succ] using ih

theorem maximalSignBlocks_flatten (d : List ℕ) :
    (maximalSignBlocks d).flatten = d := by
  simp [maximalSignBlocks]

theorem maximalSignBlocks_no_empty (d : List ℕ) :
    [] ∉ maximalSignBlocks d := by
  exact List.nil_notMem_splitBy sameZeroStatus d

private theorem zeroSlice_eq_replicate {d : List ℕ}
    {start blockLength : ℕ}
    (hwithin : start + blockLength ≤ d.length)
    (hzeros : ∀ j, j < blockLength → deficitAt d (start + j) = 0) :
    deficitSlice d start blockLength = List.replicate blockLength 0 := by
  apply List.eq_replicate_iff.mpr
  constructor
  · exact deficitSlice_length hwithin
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    have hilength : i.1 < blockLength := by
      simpa [deficitSlice_length hwithin] using i.2
    have hvalue := hzeros i.1 hilength
    rw [← deficitAt_deficitSlice hwithin hilength] at hvalue
    rw [deficitAt_eq_get _ i.1 (by
      simpa [deficitSlice_length hwithin] using i.2)] at hvalue
    exact hi.symm.trans hvalue

private theorem take_getLast?_eq {d : List ℕ} {start : ℕ}
    (hstart : 0 < start) (hbound : start ≤ d.length) :
    (d.take start).getLast? = d[start - 1]? := by
  rw [List.getLast?_eq_getElem?]
  simp [List.length_take, hbound, hstart]

private theorem zeroBlock_split_left {d : List ℕ}
    {start blockLength : ℕ} (hpositive : 0 < blockLength)
    (hwithin : start + blockLength ≤ d.length)
    (hzeros : ∀ j, j < blockLength → deficitAt d (start + j) = 0)
    (hleft : start = 0 ∨
      ∃ _hleft : 0 < start, 0 < deficitAt d (start - 1)) :
    maximalSignBlocks
        (d.take start ++ (List.replicate blockLength 0 ++
          d.drop (start + blockLength))) =
      maximalSignBlocks (d.take start) ++
        maximalSignBlocks
          (List.replicate blockLength 0 ++ d.drop (start + blockLength)) := by
  unfold maximalSignBlocks
  apply List.splitBy_append
  intro x hx y hy
  rcases hleft with rfl | ⟨hstart, hvalue⟩
  · simp at hx
  · have hpref : (d.take start).getLast? = some x := by simpa using hx
    have hstartLe : start ≤ d.length := by omega
    have hlast := take_getLast?_eq (d := d) hstart hstartLe
    rw [hlast] at hpref
    have hxvalue : x = deficitAt d (start - 1) := by
      have hindex : start - 1 < d.length := by omega
      rw [List.getElem?_eq_getElem hindex] at hpref
      rw [deficitAt_eq_get _ _ hindex]
      exact (Option.some.inj hpref).symm
    have hyvalue : y = 0 := by
      have hhead :
          (List.replicate blockLength 0 ++ d.drop (start + blockLength)).head? =
            some 0 := by
        have hne : blockLength ≠ 0 := by omega
        obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hne
        subst blockLength
        simp [List.replicate_succ]
      have htmp : 0 = y := by simpa [hhead] using hy
      exact htmp.symm
    simp [sameZeroStatus, hxvalue, hyvalue]
    omega

private theorem zeroBlock_split_right {d : List ℕ}
    {start blockLength : ℕ} (hpositive : 0 < blockLength)
    (hwithin : start + blockLength ≤ d.length)
    (hright : start + blockLength = d.length ∨
      ∃ _hright : start + blockLength < d.length,
        0 < deficitAt d (start + blockLength)) :
    maximalSignBlocks
        (List.replicate blockLength 0 ++ d.drop (start + blockLength)) =
      [List.replicate blockLength 0] ++
        maximalSignBlocks (d.drop (start + blockLength)) := by
  have hchain : (List.replicate blockLength 0).IsChain
      fun x y => sameZeroStatus x y := by
    apply List.isChain_replicate_of_rel
    simp [sameZeroStatus]
  have hsplitZero : maximalSignBlocks (List.replicate blockLength 0) =
      [List.replicate blockLength 0] := by
    apply List.splitBy_of_isChain
    · simp
      omega
    · exact hchain
  rw [← hsplitZero]
  apply List.splitBy_append
  intro x hx y hy
  rcases hright with hend | ⟨hright, hvalue⟩
  · have hsuffix : d.drop (start + blockLength) = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp
      omega
    simp [hsuffix] at hy
  · have hxvalue : x = 0 := by
      have hlast : (List.replicate blockLength 0).getLast? = some 0 := by
        have hne : blockLength ≠ 0 := by omega
        obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hne
        subst blockLength
        exact getLast?_replicate_succ_zero q
      have htmp : 0 = x := by simpa [hlast] using hx
      exact htmp.symm
    have hsuffixHead : (d.drop (start + blockLength)).head? =
        some (d.get ⟨start + blockLength, hright⟩) := by
      rw [List.head?_drop]
      exact List.getElem?_eq_getElem hright
    have hyvalue : y = deficitAt d (start + blockLength) := by
      rw [deficitAt_eq_get _ _ hright]
      have htmp : d.get ⟨start + blockLength, hright⟩ = y := by
        simpa [hsuffixHead] using hy
      exact htmp.symm
    simp [sameZeroStatus, hxvalue, hyvalue]
    omega

/-- Every literal maximal zero block occurs as one of the canonical sign
blocks, with exactly the same length. -/
theorem maximalZeroBlock_mem_maximalSignBlocks {d : List ℕ}
    {start blockLength : ℕ}
    (hblock : IsMaximalZeroBlock d start blockLength) :
    List.replicate blockLength 0 ∈ maximalSignBlocks d := by
  rcases hblock with ⟨hpositive, hwithin, hzeros, hleft, hright⟩
  have hslice := zeroSlice_eq_replicate hwithin hzeros
  have hdecomp : d = d.take start ++ (List.replicate blockLength 0 ++
      d.drop (start + blockLength)) := by
    calc
      d = d.take start ++ d.drop start := (List.take_append_drop start d).symm
      _ = d.take start ++
          (deficitSlice d start blockLength ++
            d.drop (start + blockLength)) := by
            simp [deficitSlice, List.take_append_drop, List.drop_drop,
              Nat.add_comm]
      _ = _ := by rw [hslice]
  rw [hdecomp, zeroBlock_split_left hpositive hwithin hzeros hleft,
    zeroBlock_split_right hpositive hwithin hright]
  simp

/-- A zero block of a canonical sign-block list is bounded by any bound on
the lengths of its zero members. -/
theorem maximalZeroBlock_length_le_of_blocks {d : List ℕ} {bound : ℕ}
    (hblocks : ∀ b ∈ maximalSignBlocks d,
      (∀ x ∈ b, x = 0) → b.length ≤ bound)
    {start blockLength : ℕ}
    (hblock : IsMaximalZeroBlock d start blockLength) :
    blockLength ≤ bound := by
  have hmem := maximalZeroBlock_mem_maximalSignBlocks hblock
  have hall : ∀ x ∈ List.replicate blockLength 0, x = 0 := by simp
  have := hblocks _ hmem hall
  simpa using this

/-- If a maximal zero block has neighbours on both sides, its canonical
sign-block occurrence has both a preceding and a following block.  This is
the endpoint distinction needed for Rule R3. -/
theorem maximalZeroBlock_internal_sign_decomposition {d : List ℕ}
    {start blockLength : ℕ}
    (hblock : IsMaximalZeroBlock d start blockLength)
    (hleft : 0 < start) (hright : start + blockLength < d.length) :
    ∃ pre suf : List (List ℕ),
      pre ≠ [] ∧ suf ≠ [] ∧
        maximalSignBlocks d = pre ++ [List.replicate blockLength 0] ++ suf := by
  rcases hblock with ⟨hpositive, hwithin, hzeros, hmaxLeft, hmaxRight⟩
  have hslice := zeroSlice_eq_replicate hwithin hzeros
  have hdecomp : d = d.take start ++ (List.replicate blockLength 0 ++
      d.drop (start + blockLength)) := by
    calc
      d = d.take start ++ d.drop start := (List.take_append_drop start d).symm
      _ = d.take start ++
          (deficitSlice d start blockLength ++
            d.drop (start + blockLength)) := by
            simp [deficitSlice, List.take_append_drop]
      _ = _ := by rw [hslice]
  let pre := maximalSignBlocks (d.take start)
  let suf := maximalSignBlocks (d.drop (start + blockLength))
  refine ⟨pre, suf, ?_, ?_, ?_⟩
  · unfold pre maximalSignBlocks
    apply (List.splitBy_ne_nil).2
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : start ≠ 0)
    subst start
    cases d with
    | nil =>
        simp at hwithin
    | cons a tail =>
        simp only [List.take_succ_cons]
        exact List.cons_ne_nil _ _
  · unfold suf maximalSignBlocks
    apply (List.splitBy_ne_nil).2
    intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · rw [hdecomp, zeroBlock_split_left hpositive hwithin hzeros hmaxLeft,
      zeroBlock_split_right hpositive hwithin hmaxRight]
    simp only [pre, suf, List.append_assoc]

private def BlockAllZero (b : List ℕ) : Prop := ∀ x ∈ b, x = 0

private def BlockAllPositive (b : List ℕ) : Prop := ∀ x ∈ b, 0 < x

private def SignBlocksSeparated (a b : List ℕ) : Prop :=
  ∃ ha hb, sameZeroStatus (a.getLast ha) (b.head hb) = false

private theorem zero_positive_separated {z p : List ℕ}
    (hz : BlockAllZero z) (hp : BlockAllPositive p)
    (hzne : z ≠ []) (hpne : p ≠ []) : SignBlocksSeparated z p := by
  refine ⟨hzne, hpne, ?_⟩
  have hzlast : z.getLast hzne = 0 := hz _ (List.getLast_mem hzne)
  have hppos : 0 < p.head hpne := hp _ (List.head_mem hpne)
  simp [sameZeroStatus, hzlast]
  omega

private theorem positive_zero_separated {p z : List ℕ}
    (hp : BlockAllPositive p) (hz : BlockAllZero z)
    (hpne : p ≠ []) (hzne : z ≠ []) : SignBlocksSeparated p z := by
  refine ⟨hpne, hzne, ?_⟩
  have hplast : 0 < p.getLast hpne := hp _ (List.getLast_mem hpne)
  have hzhead : z.head hzne = 0 := hz _ (List.head_mem hzne)
  simp [sameZeroStatus, hzhead]
  omega

private theorem sameZeroStatus_chain_of_allZero {b : List ℕ}
    (hb : BlockAllZero b) :
    b.IsChain fun x y => sameZeroStatus x y := by
  induction b with
  | nil => exact List.isChain_nil
  | cons a b ih =>
    apply List.isChain_cons.2
    constructor
    · intro x hx
      have ha0 : a = 0 := hb a (by simp)
      have hx0 : x = 0 := hb x (by
        exact List.mem_cons_of_mem a (List.mem_of_mem_head? hx))
      simp [sameZeroStatus, ha0, hx0]
    · exact ih (by
        intro x hx
        exact hb x (List.mem_cons_of_mem a hx))

private theorem sameZeroStatus_chain_of_allPositive {b : List ℕ}
    (hb : BlockAllPositive b) :
    b.IsChain fun x y => sameZeroStatus x y := by
  induction b with
  | nil => exact List.isChain_nil
  | cons a b ih =>
    apply List.isChain_cons.2
    constructor
    · intro x hx
      have ha : 0 < a := hb a (by simp)
      have hxpos : 0 < x := hb x (by
        exact List.mem_cons_of_mem a (List.mem_of_mem_head? hx))
      simp [sameZeroStatus]
      omega
    · exact ih (by
        intro x hx
        exact hb x (List.mem_cons_of_mem a hx))

/-- A literal alternating zero/positive block decomposition, beginning and
ending in a nonempty zero block. -/
private inductive AlternatingSignBlocks : List (List ℕ) → Prop
  | last {z : List ℕ} (hz : BlockAllZero z) (hzne : z ≠ []) :
      AlternatingSignBlocks [z]
  | step {z p : List ℕ} {rest : List (List ℕ)}
      (hz : BlockAllZero z) (hp : BlockAllPositive p)
      (hzne : z ≠ []) (hpne : p ≠ [])
      (hrest : AlternatingSignBlocks rest) :
      AlternatingSignBlocks (z :: p :: rest)

private theorem AlternatingSignBlocks.head_zero
    {blocks : List (List ℕ)} (h : AlternatingSignBlocks blocks) :
    ∀ b ∈ blocks.head?, b ≠ [] ∧ BlockAllZero b := by
  cases h with
  | last hz hzne => simpa using ⟨hzne, hz⟩
  | step hz hp hzne hpne hrest => simpa using ⟨hzne, hz⟩

private theorem AlternatingSignBlocks.no_empty
    {blocks : List (List ℕ)} (h : AlternatingSignBlocks blocks) :
    [] ∉ blocks := by
  induction h with
  | last hz hzne => simpa
  | step hz hp hzne hpne hrest ih => simp [hzne, hpne, ih]

private theorem AlternatingSignBlocks.blocks_chain
    {blocks : List (List ℕ)} (h : AlternatingSignBlocks blocks) :
    ∀ b ∈ blocks, b.IsChain fun x y => sameZeroStatus x y := by
  induction h with
  | last hz hzne =>
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact sameZeroStatus_chain_of_allZero hz
  | step hz hp hzne hpne hrest ih =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · exact sameZeroStatus_chain_of_allZero hz
      · exact sameZeroStatus_chain_of_allPositive hp
      · exact ih b hb

private theorem AlternatingSignBlocks.separated
    {blocks : List (List ℕ)} (h : AlternatingSignBlocks blocks) :
    blocks.IsChain SignBlocksSeparated := by
  induction h with
  | last hz hzne => simp
  | step hz hp hzne hpne hrest ih =>
      apply List.isChain_cons.2
      constructor
      · simpa using zero_positive_separated hz hp hzne hpne
      · apply List.isChain_cons.2
        constructor
        · intro b hb
          have hhead := hrest.head_zero b hb
          exact positive_zero_separated hp hhead.2 hpne hhead.1
        · exact ih

private theorem maximalSignBlocks_eq_of_alternating
    {blocks : List (List ℕ)} (h : AlternatingSignBlocks blocks) :
    maximalSignBlocks blocks.flatten = blocks := by
  unfold maximalSignBlocks
  apply List.splitBy_flatten h.no_empty h.blocks_chain
  exact h.separated

/-- The terminal part of either exact witness.  It consists of `q`
internal `0^(μ-1),2` pairs followed by the final `0^μ`. -/
private def witnessTailBlocks (mu : ℕ) : ℕ → List (List ℕ)
  | 0 => [List.replicate mu 0]
  | q + 1 => List.replicate (mu - 1) 0 :: [2] ::
      witnessTailBlocks mu q

private theorem witnessTailBlocks_alternating {mu q : ℕ} (hmu : 2 ≤ mu) :
    AlternatingSignBlocks (witnessTailBlocks mu q) := by
  induction q with
  | zero =>
      apply AlternatingSignBlocks.last
      · simp [BlockAllZero]
      · simp
        omega
  | succ q ih =>
      apply AlternatingSignBlocks.step
      · simp [BlockAllZero]
      · simp [BlockAllPositive]
      · simp
        omega
      · simp
      · exact ih

/-- Exact positive-even witness blocks from Lemma `lem:witness`. -/
private def evenWitnessBlocks (n t : ℕ) : List (List ℕ) :=
  List.replicate (n - 2) 0 :: [2] :: witnessTailBlocks (n - 2) (t - 1)

/-- Exact positive-odd witness blocks from Lemma `lem:witness`. -/
private def oddWitnessBlocks (n t : ℕ) : List (List ℕ) :=
  List.replicate (n - 2) 0 :: [1, 2] :: witnessTailBlocks (n - 2) (t - 1)

/-- The exact witness `0^μ 2 (0^(μ-1)2)^(t-1) 0^μ`. -/
def evenDeficitWitness (n t : ℕ) : List ℕ := (evenWitnessBlocks n t).flatten

/-- The exact witness `0^μ 1 2 (0^(μ-1)2)^(t-1) 0^μ`. -/
def oddDeficitWitness (n t : ℕ) : List ℕ := (oddWitnessBlocks n t).flatten

private theorem evenWitnessBlocks_alternating {n t : ℕ}
    (hn : 6 ≤ n) : AlternatingSignBlocks (evenWitnessBlocks n t) := by
  apply AlternatingSignBlocks.step
  · simp [BlockAllZero]
  · simp [BlockAllPositive]
  · simp
    omega
  · simp
  · exact witnessTailBlocks_alternating (by omega)

private theorem oddWitnessBlocks_alternating {n t : ℕ}
    (hn : 6 ≤ n) : AlternatingSignBlocks (oddWitnessBlocks n t) := by
  apply AlternatingSignBlocks.step
  · simp [BlockAllZero]
  · simp [BlockAllPositive]
  · simp
    omega
  · simp
  · exact witnessTailBlocks_alternating (by omega)

/-- The displayed even witness blocks are exactly its maximal sign blocks. -/
theorem evenDeficitWitness_maximalSignBlocks {n t : ℕ} (hn : 6 ≤ n) :
    maximalSignBlocks (evenDeficitWitness n t) = evenWitnessBlocks n t := by
  exact maximalSignBlocks_eq_of_alternating (evenWitnessBlocks_alternating hn)

/-- The displayed odd witness blocks are exactly its maximal sign blocks. -/
theorem oddDeficitWitness_maximalSignBlocks {n t : ℕ} (hn : 6 ≤ n) :
    maximalSignBlocks (oddDeficitWitness n t) = oddWitnessBlocks n t := by
  exact maximalSignBlocks_eq_of_alternating (oddWitnessBlocks_alternating hn)

private theorem witnessTailBlocks_entries {mu q x : ℕ}
    (hx : x ∈ (witnessTailBlocks mu q).flatten) : x = 0 ∨ x = 2 := by
  induction q with
  | zero =>
      simp [witnessTailBlocks] at hx
      exact Or.inl hx.2
  | succ q ih =>
      simp only [witnessTailBlocks, List.flatten_cons, List.mem_append,
        List.mem_replicate, List.mem_singleton] at hx
      rcases hx with ⟨_, rfl⟩ | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ih hx

private theorem evenDeficitWitness_entries {n t x : ℕ}
    (hx : x ∈ evenDeficitWitness n t) : x = 0 ∨ x = 2 := by
  simp only [evenDeficitWitness, evenWitnessBlocks, List.flatten_cons,
    List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  rcases hx with ⟨_, rfl⟩ | rfl | hx
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact witnessTailBlocks_entries hx

private theorem oddDeficitWitness_entries {n t x : ℕ}
    (hx : x ∈ oddDeficitWitness n t) : x = 0 ∨ x = 1 ∨ x = 2 := by
  simp only [oddDeficitWitness, oddWitnessBlocks, List.flatten_cons,
    List.mem_append, List.mem_replicate, List.mem_cons,
    List.mem_singleton] at hx
  rcases hx with ⟨_, rfl⟩ | hx | hx
  · exact Or.inl rfl
  · simp only [List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rcases witnessTailBlocks_entries hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

private theorem witnessTail_zero_block_length_le {mu q : ℕ} {b : List ℕ}
    (hmu : 1 ≤ mu) (hb : b ∈ witnessTailBlocks mu q)
    (hz : BlockAllZero b) : b.length ≤ mu := by
  induction q generalizing b with
  | zero =>
      simp only [witnessTailBlocks, List.mem_singleton] at hb
      subst b
      simp
  | succ q ih =>
      simp only [witnessTailBlocks, List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · simp
      · have htwo := hz 2 (by simp)
        omega
      · exact ih hb hz

private theorem evenWitness_zero_block_length_le {n t : ℕ} {b : List ℕ}
    (hn : 6 ≤ n) (hb : b ∈ evenWitnessBlocks n t)
    (hz : BlockAllZero b) : b.length ≤ n - 2 := by
  simp only [evenWitnessBlocks, List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · simp
  · have htwo := hz 2 (by simp)
    omega
  · exact witnessTail_zero_block_length_le (by omega) hb hz

private theorem oddWitness_zero_block_length_le {n t : ℕ} {b : List ℕ}
    (hn : 6 ≤ n) (hb : b ∈ oddWitnessBlocks n t)
    (hz : BlockAllZero b) : b.length ≤ n - 2 := by
  simp only [oddWitnessBlocks, List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · simp
  · have hone := hz 1 (by simp)
    omega
  · exact witnessTail_zero_block_length_le (by omega) hb hz

private theorem mem_dropLast_of_append_cons_suffix_ne_nil
    {alpha : Type*} {pre suf : List alpha} {x : alpha}
    (hsuf : suf ≠ []) : x ∈ (pre ++ x :: suf).dropLast := by
  induction pre with
  | nil =>
      cases suf with
      | nil => contradiction
      | cons y ys => simp
  | cons a pre ih =>
      have hrest : pre ++ x :: suf ≠ [] := by simp
      cases hrestEq : pre ++ x :: suf with
      | nil => exact (hrest hrestEq).elim
      | cons y ys =>
          rw [List.cons_append, hrestEq, List.dropLast_cons_cons]
          exact List.mem_cons_of_mem a (by simpa [hrestEq] using ih)

private theorem mem_tail_dropLast_of_internal_decomposition
    {alpha : Type*} {l pre suf : List alpha} {x : alpha}
    (hdecomp : l = pre ++ x :: suf) (hpre : pre ≠ []) (hsuf : suf ≠ []) :
    x ∈ l.tail.dropLast := by
  rw [hdecomp]
  cases pre with
  | nil => contradiction
  | cons a pre =>
      simp only [List.cons_append, List.tail_cons]
      exact mem_dropLast_of_append_cons_suffix_ne_nil hsuf

private theorem witnessTailBlocks_dropLast_succ (mu q : ℕ) :
    (witnessTailBlocks mu (q + 1)).dropLast =
      List.replicate (mu - 1) 0 :: [2] ::
        (witnessTailBlocks mu q).dropLast := by
  simp only [witnessTailBlocks, List.dropLast_cons_cons]
  cases htail : witnessTailBlocks mu q with
  | nil =>
      have hne : witnessTailBlocks mu q ≠ [] := by
        cases q <;> simp [witnessTailBlocks]
      exact (hne htail).elim
  | cons b bs => simp

private theorem witnessTail_dropLast_zero_length {mu q : ℕ} {b : List ℕ}
    (hmu : 2 ≤ mu) (hb : b ∈ (witnessTailBlocks mu q).dropLast)
    (hz : BlockAllZero b) : b.length = mu - 1 := by
  induction q generalizing b with
  | zero => simp [witnessTailBlocks] at hb
  | succ q ih =>
      rw [witnessTailBlocks_dropLast_succ] at hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · simp
      · have htwo := hz 2 (by simp)
        omega
      · exact ih hb hz

private theorem dropLast_cons_witnessTail (p : List ℕ) (mu q : ℕ) :
    (p :: witnessTailBlocks mu q).dropLast =
      p :: (witnessTailBlocks mu q).dropLast := by
  cases q <;> simp [witnessTailBlocks]

private theorem evenWitness_internal_zero_length {n t : ℕ}
    {pre suf : List (List ℕ)} {b : List ℕ} (hn : 6 ≤ n)
    (hdecomp : evenWitnessBlocks n t = pre ++ b :: suf)
    (hpre : pre ≠ []) (hsuf : suf ≠ []) (hz : BlockAllZero b) :
    b.length = n - 3 := by
  have hb := mem_tail_dropLast_of_internal_decomposition hdecomp hpre hsuf
  simp only [evenWitnessBlocks, List.tail_cons,
    dropLast_cons_witnessTail, List.mem_cons] at hb
  rcases hb with rfl | hb
  · have htwo := hz 2 (by simp)
    omega
  · have hlen := witnessTail_dropLast_zero_length (mu := n - 2)
      (q := t - 1) (b := b) (by omega) hb hz
    omega

private theorem oddWitness_internal_zero_length {n t : ℕ}
    {pre suf : List (List ℕ)} {b : List ℕ} (hn : 6 ≤ n)
    (hdecomp : oddWitnessBlocks n t = pre ++ b :: suf)
    (hpre : pre ≠ []) (hsuf : suf ≠ []) (hz : BlockAllZero b) :
    b.length = n - 3 := by
  have hb := mem_tail_dropLast_of_internal_decomposition hdecomp hpre hsuf
  simp only [oddWitnessBlocks, List.tail_cons,
    dropLast_cons_witnessTail, List.mem_cons] at hb
  rcases hb with rfl | hb
  · have hone := hz 1 (by simp)
    omega
  · have hlen := witnessTail_dropLast_zero_length (mu := n - 2)
      (q := t - 1) (b := b) (by omega) hb hz
    omega

private theorem witnessTailBlocks_length (mu q : ℕ) (hmu : 1 ≤ mu) :
    (witnessTailBlocks mu q).flatten.length = q * mu + mu := by
  induction q with
  | zero => simp [witnessTailBlocks]
  | succ q ih =>
      simp [witnessTailBlocks, ih]
      have hm : mu - 1 + 1 = mu := by omega
      nlinarith

private theorem witnessTailBlocks_sum (mu q : ℕ) :
    (witnessTailBlocks mu q).flatten.sum = 2 * q := by
  induction q with
  | zero => simp [witnessTailBlocks]
  | succ q ih =>
      simp [witnessTailBlocks, ih]
      omega

theorem evenDeficitWitness_length {n t : ℕ} (hn : 6 ≤ n) (ht : 1 ≤ t) :
    (evenDeficitWitness n t).length = maxLegalLength n (2 * t) := by
  have htEq : t - 1 + 1 = t := by omega
  have hrep := witnessTailBlocks_length (n - 2) (t - 1) (by omega)
  have hlarge : ¬t * 2 ≤ 1 := by omega
  have hmul : (t - 1) * (n - 2) + (n - 2) = t * (n - 2) := by
    calc
      (t - 1) * (n - 2) + (n - 2) =
          ((t - 1) + 1) * (n - 2) := by ring
      _ = _ := by rw [htEq]
  simp [evenDeficitWitness, evenWitnessBlocks, hrep, hmul,
    maxLegalLength, hlarge, Nat.mul_comm]
  omega

theorem evenDeficitWitness_total (n t : ℕ) (ht : 1 ≤ t) :
    deficitSequenceTotal (evenDeficitWitness n t) = 2 * t := by
  have hrep := witnessTailBlocks_sum (n - 2) (t - 1)
  have htEq : t - 1 + 1 = t := by omega
  simp [deficitSequenceTotal, evenDeficitWitness, evenWitnessBlocks, hrep]
  omega

theorem oddDeficitWitness_length {n t : ℕ} (hn : 6 ≤ n) (ht : 1 ≤ t) :
    (oddDeficitWitness n t).length = maxLegalLength n (2 * t + 1) := by
  have htEq : t - 1 + 1 = t := by omega
  have hrep := witnessTailBlocks_length (n - 2) (t - 1) (by omega)
  have hlarge : t ≠ 0 := by omega
  have hdiv : (t * 2 + 1) / 2 = t := by omega
  have hmul : (t - 1) * (n - 2) + (n - 2) = t * (n - 2) := by
    calc
      (t - 1) * (n - 2) + (n - 2) =
          ((t - 1) + 1) * (n - 2) := by ring
      _ = _ := by rw [htEq]
  simp [oddDeficitWitness, oddWitnessBlocks, hrep, hmul,
    maxLegalLength, hlarge, hdiv, Nat.mul_comm]
  omega

theorem oddDeficitWitness_total (n t : ℕ) (ht : 1 ≤ t) :
    deficitSequenceTotal (oddDeficitWitness n t) = 2 * t + 1 := by
  have hrep := witnessTailBlocks_sum (n - 2) (t - 1)
  have htEq : t - 1 + 1 = t := by omega
  simp [deficitSequenceTotal, oddDeficitWitness, oddWitnessBlocks, hrep]
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem oddDeficitWitness_one_index {n t j : ℕ}
    (hj : j < (oddDeficitWitness n t).length)
    (hone : deficitAt (oddDeficitWitness n t) j = 1) : j = n - 2 := by
  by_cases hbefore : j < n - 2
  · have hzero : deficitAt (oddDeficitWitness n t) j = 0 := by
      rw [deficitAt_eq_get _ j hj]
      simp [oddDeficitWitness, oddWitnessBlocks, hbefore]
    omega
  by_cases hat : j = n - 2
  · exact hat
  have hafter : n - 2 + 1 ≤ j := by omega
  by_cases hsecond : j = n - 2 + 1
  · subst j
    have htwo : deficitAt (oddDeficitWitness n t) (n - 2 + 1) = 2 := by
      rw [deficitAt_eq_get _ _ hj]
      simp [oddDeficitWitness, oddWitnessBlocks]
    omega
  have htailIndex : n - 2 + 2 ≤ j := by omega
  let q := j - (n - 2 + 2)
  have hjlen : j < n - 2 +
      (witnessTailBlocks (n - 2) (t - 1)).flatten.length + 2 := by
    simpa [oddDeficitWitness, oddWitnessBlocks, Nat.add_assoc] using hj
  have hget : deficitAt (oddDeficitWitness n t) j =
      (witnessTailBlocks (n - 2) (t - 1)).flatten.get
        ⟨q, by
          dsimp [q]
          omega⟩ := by
    rw [deficitAt_eq_get _ j hj]
    change (List.replicate (n - 2) 0 ++
      ([1, 2] ++ (witnessTailBlocks (n - 2) (t - 1)).flatten))[j] = _
    rw [List.getElem_append_right (by simp; omega)]
    rw [List.getElem_append_right (by simp; omega)]
    congr 1
    dsimp [q]
    simp only [List.length_replicate]
    omega
  have hmem : deficitAt (oddDeficitWitness n t) j ∈
      (witnessTailBlocks (n - 2) (t - 1)).flatten := by
    rw [hget]
    exact List.get_mem _ _
  rcases witnessTailBlocks_entries hmem with hzero | htwo <;> omega

/-- The positive-even displayed witness is legal. -/
theorem evenDeficitWitness_legal {n t : ℕ} (hn : 6 ≤ n) (ht : 1 ≤ t) :
    IsLegalDeficitSequence n (evenDeficitWitness n t) where
  six_le := hn
  nonempty := by
    have hlen := evenDeficitWitness_length hn ht
    apply List.ne_nil_of_length_pos
    rw [hlen]
    unfold maxLegalLength
    split <;> omega
  entries_lt := by
    intro x hx
    rcases evenDeficitWitness_entries hx with rfl | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ evenDeficitWitness n t, x = 0 := by
      intro hall
      have hsumZero : deficitSequenceTotal (evenDeficitWitness n t) = 0 := by
        simp only [deficitSequenceTotal, List.sum_eq_zero_iff]
        exact hall
      rw [evenDeficitWitness_total n t ht] at hsumZero
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    apply maximalZeroBlock_length_le_of_blocks (bound := n - 2) ?_ hblock
    intro b hb hz
    rw [evenDeficitWitness_maximalSignBlocks hn] at hb
    exact evenWitness_zero_block_length_le hn hb hz
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (evenDeficitWitness n t).length := by omega
    have hmem : deficitAt (evenDeficitWitness n t) (i + 1) ∈
        evenDeficitWitness n t := by
      rw [deficitAt_eq_get _ _ hi1]
      exact List.get_mem _ _
    rcases evenDeficitWitness_entries hmem with hzero | htwo
    · omega
    · omega
  rule3 := by
    intro start hblock hleft hright
    obtain ⟨pre, suf, hpre, hsuf, hdecomp⟩ :=
      maximalZeroBlock_internal_sign_decomposition hblock hleft hright
    rw [evenDeficitWitness_maximalSignBlocks hn] at hdecomp
    have hlen := evenWitness_internal_zero_length (b := List.replicate (n - 2) 0)
      hn (by simpa [List.append_assoc] using hdecomp) hpre hsuf
        (by simp [BlockAllZero])
    simp only [List.length_replicate] at hlen
    omega

/-- The positive-odd displayed witness is legal. -/
theorem oddDeficitWitness_legal {n t : ℕ} (hn : 6 ≤ n) (ht : 1 ≤ t) :
    IsLegalDeficitSequence n (oddDeficitWitness n t) where
  six_le := hn
  nonempty := by
    have hlen := oddDeficitWitness_length hn ht
    apply List.ne_nil_of_length_pos
    rw [hlen]
    unfold maxLegalLength
    split <;> omega
  entries_lt := by
    intro x hx
    rcases oddDeficitWitness_entries hx with rfl | rfl | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ oddDeficitWitness n t, x = 0 := by
      intro hall
      have hsumZero : deficitSequenceTotal (oddDeficitWitness n t) = 0 := by
        simp only [deficitSequenceTotal, List.sum_eq_zero_iff]
        exact hall
      rw [oddDeficitWitness_total n t ht] at hsumZero
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    apply maximalZeroBlock_length_le_of_blocks (bound := n - 2) ?_ hblock
    intro b hb hz
    rw [oddDeficitWitness_maximalSignBlocks hn] at hb
    exact oddWitness_zero_block_length_le hn hb hz
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (oddDeficitWitness n t).length := by omega
    have honeIndex := oddDeficitWitness_one_index hi1 hpattern.2.1
    have hi2 : i + 2 < (oddDeficitWitness n t).length := by omega
    have htwo : deficitAt (oddDeficitWitness n t) (i + 2) = 2 := by
      have hindex : i + 2 = n - 2 + 1 := by omega
      rw [hindex]
      have hbound : n - 2 + 1 < (oddDeficitWitness n t).length := by omega
      rw [deficitAt_eq_get _ _ hbound]
      simp [oddDeficitWitness, oddWitnessBlocks]
    omega
  rule3 := by
    intro start hblock hleft hright
    obtain ⟨pre, suf, hpre, hsuf, hdecomp⟩ :=
      maximalZeroBlock_internal_sign_decomposition hblock hleft hright
    rw [oddDeficitWitness_maximalSignBlocks hn] at hdecomp
    have hlen := oddWitness_internal_zero_length (b := List.replicate (n - 2) 0)
      hn (by simpa [List.append_assoc] using hdecomp) hpre hsuf
        (by simp [BlockAllZero])
    simp only [List.length_replicate] at hlen
    omega

/-- The isolated exact witness for `D=0`. -/
def zeroDeficitWitness (n : ℕ) : List ℕ := List.replicate (n - 1) 0

/-- The isolated exact witness for `D=1`. -/
def oneDeficitWitness (n : ℕ) : List ℕ := List.replicate (n - 2) 0 ++ [1]

theorem zeroDeficitWitness_length {n : ℕ} (hn : 6 ≤ n) :
    (zeroDeficitWitness n).length = maxLegalLength n 0 := by
  simp [zeroDeficitWitness, maxLegalLength]

theorem zeroDeficitWitness_total (n : ℕ) :
    deficitSequenceTotal (zeroDeficitWitness n) = 0 := by
  simp [deficitSequenceTotal, zeroDeficitWitness]

theorem zeroDeficitWitness_legal {n : ℕ} (hn : 6 ≤ n) :
    IsLegalDeficitSequence n (zeroDeficitWitness n) where
  six_le := hn
  nonempty := by
    simp [zeroDeficitWitness]
    omega
  entries_lt := by
    intro x hx
    simp [zeroDeficitWitness] at hx
    omega
  rule1 := by
    have hall : ∀ x ∈ zeroDeficitWitness n, x = 0 := by
      simp [zeroDeficitWitness]
    simp [hall, zeroDeficitWitness]
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (zeroDeficitWitness n).length := by omega
    have hzero : deficitAt (zeroDeficitWitness n) (i + 1) = 0 := by
      rw [deficitAt_eq_get _ _ hi1]
      simp [zeroDeficitWitness]
    omega
  rule3 := by
    intro start hblock hleft hright
    simp [zeroDeficitWitness] at hright
    omega

private theorem oneDeficitWitness_one_index {n j : ℕ}
    (hj : j < (oneDeficitWitness n).length)
    (hone : deficitAt (oneDeficitWitness n) j = 1) : j = n - 2 := by
  by_cases hbefore : j < n - 2
  · have hzero : deficitAt (oneDeficitWitness n) j = 0 := by
      rw [deficitAt_eq_get _ _ hj]
      simp [oneDeficitWitness, hbefore]
    omega
  have hlen : (oneDeficitWitness n).length = n - 2 + 1 := by
    simp [oneDeficitWitness]
  omega

theorem oneDeficitWitness_length {n : ℕ} (hn : 6 ≤ n) :
    (oneDeficitWitness n).length = maxLegalLength n 1 := by
  simp [oneDeficitWitness, maxLegalLength]
  omega

theorem oneDeficitWitness_total (n : ℕ) :
    deficitSequenceTotal (oneDeficitWitness n) = 1 := by
  simp [deficitSequenceTotal, oneDeficitWitness]

theorem oneDeficitWitness_legal {n : ℕ} (hn : 6 ≤ n) :
    IsLegalDeficitSequence n (oneDeficitWitness n) where
  six_le := hn
  nonempty := by simp [oneDeficitWitness]
  entries_lt := by
    intro x hx
    simp [oneDeficitWitness] at hx
    rcases hx with ⟨_, rfl⟩ | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ oneDeficitWitness n, x = 0 := by
      intro hall
      have := hall 1 (by simp [oneDeficitWitness])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, _hleft, _hright⟩
    have hstart : start ≤ n - 2 := by
      simp [oneDeficitWitness] at hwithin
      omega
    by_contra hlong
    let j := n - 2 - start
    have hj : j < blockLength := by
      dsimp [j]
      omega
    have hz := hzeros j hj
    have hindex : start + j = n - 2 := by
      dsimp [j]
      omega
    rw [hindex] at hz
    have hlast : deficitAt (oneDeficitWitness n) (n - 2) = 1 := by
      have hbound : n - 2 < (oneDeficitWitness n).length := by
        simp [oneDeficitWitness]
      rw [deficitAt_eq_get _ _ hbound]
      simp [oneDeficitWitness]
    omega
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (oneDeficitWitness n).length := by omega
    have hindex := oneDeficitWitness_one_index hi1 hpattern.2.1
    have hlen : (oneDeficitWitness n).length = n - 1 := by
      simp [oneDeficitWitness]
      omega
    omega
  rule3 := by
    intro start hblock hleft hright
    have hlen : (oneDeficitWitness n).length = n - 1 := by
      simp [oneDeficitWitness]
      omega
    omega

/-- Lemma `lem:witness`, first assertion: exact length and exact total for
every nonnegative `D`, including the isolated values `0` and `1`. -/
theorem exists_exact_legal_deficit_witness {n D : ℕ} (hn : 6 ≤ n) :
    ∃ d : List ℕ, IsLegalDeficitSequence n d ∧
      d.length = maxLegalLength n D ∧ deficitSequenceTotal d = D := by
  by_cases hzero : D = 0
  · subst D
    exact ⟨zeroDeficitWitness n, zeroDeficitWitness_legal hn,
      zeroDeficitWitness_length hn, zeroDeficitWitness_total n⟩
  by_cases hone : D = 1
  · subst D
    exact ⟨oneDeficitWitness n, oneDeficitWitness_legal hn,
      oneDeficitWitness_length hn, oneDeficitWitness_total n⟩
  have hDlarge : 2 ≤ D := by omega
  have hmod := Nat.mod_two_eq_zero_or_one D
  have hdivision := Nat.mod_add_div D 2
  rcases hmod with heven | hodd
  · let t := D / 2
    have hD : D = 2 * t := by
      dsimp [t]
      omega
    have ht : 1 ≤ t := by omega
    refine ⟨evenDeficitWitness n t, evenDeficitWitness_legal hn ht, ?_, ?_⟩
    · rw [hD]
      exact evenDeficitWitness_length hn ht
    · rw [hD]
      exact evenDeficitWitness_total n t ht
  · let t := D / 2
    have hD : D = 2 * t + 1 := by
      dsimp [t]
      omega
    have ht : 1 ≤ t := by omega
    refine ⟨oddDeficitWitness n t, oddDeficitWitness_legal hn ht, ?_, ?_⟩
    · rw [hD]
      exact oddDeficitWitness_length hn ht
    · rw [hD]
      exact oddDeficitWitness_total n t ht

/-- Lemma `lem:witness`, prefix assertion, with the logically necessary
positive-length hypothesis explicit. -/
theorem exists_legal_deficit_witness_of_length_le {n D r : ℕ}
    (hn : 6 ≤ n) (hr : 1 ≤ r) (hrN : r ≤ maxLegalLength n D) :
    ∃ d : List ℕ, d.length = r ∧ IsLegalDeficitSequence n d ∧
      deficitSequenceTotal d ≤ D := by
  obtain ⟨d, hlegal, hlength, htotal⟩ := exists_exact_legal_deficit_witness hn (D := D)
  refine ⟨d.take r, ?_, ?_, ?_⟩
  · simp [hlength, hrN]
  · exact hlegal.take hr (by omega)
  · have hsum := List.sum_take_add_sum_drop d r
    simp only [deficitSequenceTotal] at htotal ⊢
    omega

/-- Lemma `lem:gapslack`, using integer subtraction so the displayed
nonnegative-integer hypothesis is not weakened by natural truncation. -/
theorem criticalGapSlack {n D delta g gOdd s : ℕ} (hn : 6 ≤ n)
    (hcharge : (2 * s : ℤ) ≤ (D : ℤ) + delta - g - gOdd)
    (hodd : Odd g → 1 ≤ gOdd) :
    (n - 4) * s + g ≤ (n - 4) * ((D + delta) / 2) := by
  have hadd : 2 * s + g + gOdd ≤ D + delta := by
    exact_mod_cast (show (2 * s : ℤ) + g + gOdd ≤ D + delta by omega)
  by_cases hgzero : g = 0
  · subst g
    have hs : s ≤ (D + delta) / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      omega
    exact Nat.mul_le_mul_left (n - 4) hs
  rcases Nat.even_or_odd g with hgeven | hgodd
  · obtain ⟨q, hq⟩ := hgeven
    have hs : s + q ≤ (D + delta) / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      omega
    have hmul := Nat.mul_le_mul_left (n - 4) hs
    have ha : 2 ≤ n - 4 := by omega
    have hqbound : 2 * q ≤ (n - 4) * q := by nlinarith
    calc
      (n - 4) * s + g = (n - 4) * s + 2 * q := by omega
      _ ≤ (n - 4) * s + (n - 4) * q := Nat.add_le_add_left hqbound _
      _ = (n - 4) * (s + q) := by ring
      _ ≤ _ := hmul
  · have hgOddPos := hodd hgodd
    obtain ⟨q, hq⟩ := hgodd
    have hs : s + q + 1 ≤ (D + delta) / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      omega
    have hmul := Nat.mul_le_mul_left (n - 4) hs
    have ha : 2 ≤ n - 4 := by omega
    have hqbound : 2 * q + 1 ≤ (n - 4) * (q + 1) := by nlinarith
    calc
      (n - 4) * s + g = (n - 4) * s + (2 * q + 1) := by omega
      _ ≤ (n - 4) * s + (n - 4) * (q + 1) := Nat.add_le_add_left hqbound _
      _ = (n - 4) * (s + q + 1) := by ring
      _ ≤ _ := hmul

/-- Natural-subtraction interface for `criticalGapSlack`; the explicit
nonnegativity premise prevents truncated subtraction from changing the TeX
hypothesis. -/
theorem criticalGapSlack_nat {n D delta g gOdd s : ℕ} (hn : 6 ≤ n)
    (hnonnegative : g + gOdd ≤ D + delta)
    (hcharge : 2 * s ≤ D + delta - g - gOdd)
    (hodd : Odd g → 1 ≤ gOdd) :
    (n - 4) * s + g ≤ (n - 4) * ((D + delta) / 2) := by
  apply criticalGapSlack hn (hodd := hodd)
  omega

end SuperpermutationLowerBound
