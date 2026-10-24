module

public import SuperpermutationLowerBound.Section08.ComponentCapacity
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- A uniform rational bound on every contiguous factor; empty factors are
included so that endpoint deletion does not need exceptional conventions. -/
def ListAffineBound (δ β : ℚ) (d : List ℕ) : Prop :=
  ∀ i j : ℕ, δ * (((d.drop i).take j).length : ℚ) - β ≤
    (((d.drop i).take j).sum : ℚ)

/-- The geometric scalar interface, on actual paths and all their factors. -/
def HereditarySegmentBound {k : ℕ} (hk : 7 ≤ k) (δ β : ℚ) : Prop :=
  ∀ (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp), ListAffineBound δ β s.deficitString

def endpointCharge (δ : ℚ) (d : ℕ) : ℚ := max 0 ((d : ℚ) - δ)

theorem ListAffineBound.base {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) : δ * (d.length : ℚ) - β ≤ (d.sum : ℚ) := by
  simpa using h 0 d.length

theorem endpointCharge_nonneg (δ : ℚ) (d : ℕ) : 0 ≤ endpointCharge δ d :=
  le_max_left _ _

theorem ListAffineBound.drop {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) (i : ℕ) : ListAffineBound δ β (d.drop i) := by
  intro j l
  simpa [List.drop_drop, Nat.add_comm] using h (i + j) l

theorem ListAffineBound.first_cons {δ β : ℚ} {x : ℕ} {xs : List ℕ}
    (h : ListAffineBound δ β (x :: xs)) :
    δ * ((x :: xs).length : ℚ) - β + endpointCharge δ x ≤
      ((x :: xs).sum : ℚ) := by
  have hbase := h.base
  have htail : δ * (xs.length : ℚ) - β ≤ (xs.sum : ℚ) := by
    simpa using h 1 xs.length
  simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one] at *
  rcases le_total 0 ((x : ℚ) - δ) with hx | hx
  · rw [endpointCharge, max_eq_right hx]
    linarith
  · rw [endpointCharge, max_eq_left hx]
    linarith

theorem ListAffineBound.last_append {δ β : ℚ} {x : ℕ} {xs : List ℕ}
    (h : ListAffineBound δ β (xs ++ [x])) :
    δ * ((xs ++ [x]).length : ℚ) - β + endpointCharge δ x ≤
      ((xs ++ [x]).sum : ℚ) := by
  have hbase := h.base
  have hinit : δ * (xs.length : ℚ) - β ≤ (xs.sum : ℚ) := by
    simpa using h 0 xs.length
  simp only [List.length_append, List.length_singleton, List.sum_append,
    List.sum_singleton, Nat.cast_add, Nat.cast_one] at *
  rcases le_total 0 ((x : ℚ) - δ) with hx | hx
  · rw [endpointCharge, max_eq_right hx]
    linarith
  · rw [endpointCharge, max_eq_left hx]
    linarith

theorem ListAffineBound.first {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) (hd : d ≠ []) :
    δ * (d.length : ℚ) - β + endpointCharge δ (d.head hd) ≤ (d.sum : ℚ) := by
  cases d with
  | nil => exact (hd rfl).elim
  | cons x xs => exact h.first_cons

theorem ListAffineBound.last {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) (hd : d ≠ []) :
    δ * (d.length : ℚ) - β + endpointCharge δ (d.getLast hd) ≤ (d.sum : ℚ) := by
  have heq := List.dropLast_append_getLast hd
  have h' : ListAffineBound δ β (d.dropLast ++ [d.getLast hd]) := by
    rwa [heq]
  simpa only [heq] using h'.last_append

theorem ListAffineBound.both {δ β : ℚ} {d : List ℕ}
    (h : ListAffineBound δ β d) (hlen : 2 ≤ d.length)
    (hd : d ≠ [] := by intro he; simp [he] at hlen) :
    δ * (d.length : ℚ) - β + endpointCharge δ (d.head hd) +
      endpointCharge δ (d.getLast hd) ≤ (d.sum : ℚ) := by
  cases d with
  | nil => simp at hlen
  | cons x xs =>
      have hxs : xs ≠ [] := by intro he; simp [he] at hlen
      have hbase := h.last hd
      have htail : ListAffineBound δ β xs := by simpa using h.drop 1
      have ht := htail.last hxs
      simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one,
        List.head_cons, List.getLast_cons hxs] at *
      rcases le_total 0 ((x : ℚ) - δ) with hx | hx
      · rw [endpointCharge, max_eq_right hx]
        linarith
      · rw [endpointCharge, max_eq_left hx]
        linarith

end SuperpermutationLowerBound.Refinement
