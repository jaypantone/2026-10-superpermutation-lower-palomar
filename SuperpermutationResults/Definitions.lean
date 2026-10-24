module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
Definitions shared by the independent result statements.

A word over `Fin K` covers the permutations when each list of length K with
no repeated symbol occurs as a contiguous factor. Since the alphabet has K
symbols, these lists are precisely its permutations. The prefix and suffix
in the definition may be empty. No condition is imposed on the other
factors of the word.

This file imports no project proof and makes no assertion that a bound holds.
-/
namespace SuperpermutationResults

def Covers {K : ℕ} (w : List (Fin K)) : Prop :=
  ∀ p : List (Fin K), p.length = K → p.Nodup →
    ∃ u v : List (Fin K), w = u ++ p ++ v

/-- The first three factorial terms, in the rationals. -/
def F3 (K : ℕ) : ℚ :=
  (Nat.factorial K : ℚ) + (Nat.factorial (K - 1) : ℚ) +
    (Nat.factorial (K - 2) : ℚ)

/-- The same three terms, in the natural numbers. -/
def F3Nat (K : ℕ) : ℕ :=
  K.factorial + (K - 1).factorial + (K - 2).factorial

/-- An upper bound means existence of an actual covering word. -/
def HasWord (K bound : ℕ) : Prop :=
  ∃ w : List (Fin K), Covers w ∧ w.length ≤ bound

/-- A lower bound applies to every covering word. -/
def IsLowerBound (K bound : ℕ) : Prop :=
  ∀ w : List (Fin K), Covers w → bound ≤ w.length

end SuperpermutationResults
