module

public import SuperpermutationLowerBound.Refinement.ChainEncoding

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

def zeroRegular (gaps : List ℕ) : List ℕ := 0 :: (regularPath gaps ++ [0])

def zeroCell (a : ℕ) (cells : List Bool) : List ℕ := 0 :: (cellWord a cells ++ [2,0])

def CellFactor (a : ℕ) (cells : List Bool) (d : List ℕ) : Prop :=
  ∃ before after, d = before ++ zeroCell a cells ++ after

theorem cellWord_eq_gapWord (a : ℕ) (cells : List Bool) :
    cellWord a cells = gapWord (cells.map (fun b => if b then a-2 else a-1)) := by
  induction cells with
  | nil => rfl
  | cons b bs ih =>
    simpa [cellWord, gapWord, cellDigits] using (congrArg (fun xs => cellDigits a b ++ xs) ih)

theorem zeroCell_eq_zeroRegular (a : ℕ) (cells : List Bool) :
    zeroCell a cells = zeroRegular (cells.map (fun b => if b then a-2 else a-1)) := by
  simp [zeroCell, zeroRegular, regularPath_eq_gapWord, cellWord_eq_gapWord, List.append_assoc]

theorem zeroRegular_cons (g : ℕ) (hg : 1 ≤ g) (gs : List ℕ) :
    zeroRegular (g :: gs) = ([0,2] ++ List.replicate (g-1) 0) ++
      zeroRegular gs := by
  have hg' : g = (g-1)+1 := by omega
  conv_lhs => unfold zeroRegular; unfold regularPath
  rw [hg', List.replicate_add]
  simp [zeroRegular, List.append_assoc]

theorem zeroRegular_prefix (middle after : List ℕ)
    (ha : ∀ g ∈ after, 1 ≤ g) :
    ∃ post, zeroRegular (middle ++ after) = zeroRegular middle ++ post := by
  cases after with
  | nil => exact ⟨[], by simp⟩
  | cons g gs =>
    have hg : 1 ≤ g := ha g (by simp)
    refine ⟨List.replicate (g-1) 0 ++ regularPath gs ++ [0], ?_⟩
    have hg' : g = 1+(g-1) := by omega
    simp only [zeroRegular, regularPath_eq_gapWord, gapWord_append]
    change 0 :: (gapWord middle ++ gapWord (g::gs) ++ [2] ++ [0]) = _
    simp only [gapWord, List.flatMap_cons]
    rw [hg', List.replicate_add]
    simp [List.append_assoc]

/-- Subpaths retain the two actual bounding zeros, even at a free endpoint. -/
theorem zeroRegular_factor (before middle after : List ℕ)
    (h : ∀ g ∈ before ++ middle ++ after, 1 ≤ g) :
    ∃ pre post, zeroRegular (before ++ middle ++ after) =
      pre ++ zeroRegular middle ++ post := by
  induction before with
  | nil =>
    obtain ⟨post, hp⟩ := zeroRegular_prefix middle after (fun g hg => h g (by simp [hg]))
    exact ⟨[], post, by simpa using hp⟩
  | cons g gs ih =>
    have hg : 1 ≤ g := h g (by simp)
    obtain ⟨pre, post, hf⟩ := ih (fun x hx => h x (by simp only [List.cons_append, List.mem_cons]; exact Or.inr hx))
    refine ⟨([0,2] ++ List.replicate (g-1) 0) ++ pre, post, ?_⟩
    simp only [List.append_assoc] at hf
    simp only [List.cons_append, zeroRegular_cons g hg, List.append_assoc, hf]

theorem CellFactor.trans {a : ℕ} {cells : List Bool} {d factor before after : List ℕ}
    (h : CellFactor a cells factor) (he : d = before ++ factor ++ after) : CellFactor a cells d := by
  obtain ⟨pre, post, hp⟩ := h
  exact ⟨before ++ pre, post ++ after, by simp [he, hp, List.append_assoc]⟩

theorem cellFactor_of_mark_factor {a : ℕ} (ha : 3 ≤ a)
    {cells before middle after : List Bool} (h : cells = before ++ middle ++ after) :
    CellFactor a middle (zeroCell a cells) := by
  rw [zeroCell_eq_zeroRegular, h]
  let f : Bool → ℕ := fun b => if b then a-2 else a-1
  obtain ⟨pre, post, hf⟩ := zeroRegular_factor (before.map f) (middle.map f) (after.map f)
    (by intro g hg
        simp only [← List.map_append, List.mem_map] at hg
        obtain ⟨b, _, rfl⟩ := hg
        dsimp [f]
        split <;> omega)
  exact ⟨pre, post, by simpa [List.map_append, zeroCell_eq_zeroRegular, f] using hf⟩

def chainCells : List ℕ → List Bool
  | [] => []
  | r :: rs => List.replicate (r-1) false ++
      if rs = [] then [] else true :: chainCells rs

theorem chainGaps_eq_chainCells (a : ℕ) (ls : List ℕ) :
    chainGaps a ls = (chainCells ls).map (fun b => if b then a-2 else a-1) := by
  induction ls with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : rs = []
    · simp [chainGaps, chainCells, hr]
    · simp [chainGaps, chainCells, hr, ih]

theorem chainCells_append {xs ys : List ℕ} (hx : xs ≠ []) (hy : ys ≠ []) :
    chainCells (xs ++ ys) = chainCells xs ++ true :: chainCells ys := by
  induction xs with
  | nil => contradiction
  | cons r rs ih =>
    by_cases hr : rs = []
    · simp [chainCells, hr, hy]
    · simp [chainCells, hr, hy, ih hr, List.append_assoc]

theorem zeroRegular_chainGaps (a : ℕ) (ls : List ℕ) :
    zeroRegular (chainGaps a ls) = zeroCell a (chainCells ls) := by
  rw [zeroCell_eq_zeroRegular, chainGaps_eq_chainCells]

end SuperpermutationLowerBound.Refinement
