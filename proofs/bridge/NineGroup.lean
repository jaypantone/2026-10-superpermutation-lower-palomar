module

public import pairs.CompletedFactors

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

/-! The twelve-element normalization group for the frozen nine-letter case.
Only permutations of nine fixed coordinate labels are evaluated here. These
calculations are ordinary `decide` proofs checked by Lean's kernel. -/
namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.Refinement
open Equiv

private def nineA : Perm (Fin 9) := Equiv.swap 2 8
private def nineB : Perm (Fin 9) := Equiv.swap 8 7
private def nineU : Perm (Fin 9) := Equiv.swap 1 3
private def nineV : Perm (Fin 9) := Equiv.swap 5 6

def nineG0 : Perm (Fin 9) := nineA * nineV
def nineG1 : Perm (Fin 9) := nineA * nineU
def nineG2 : Perm (Fin 9) := nineA * nineB * nineU * nineV

def nineGroup : Finset (Perm (Fin 9)) :=
  {1, nineG0, nineG1, nineG2, nineG0*nineG1, nineG0*nineG2,
    nineG1*nineG2, nineG2*nineG0, nineG2*nineG1, nineG2*nineG2,
    nineG0*nineG1*nineG2, nineG0*nineG2*nineG0}

theorem nineGroup_card : nineGroup.card = 12 := by decide

theorem nineGroup_one : (1 : Perm (Fin 9)) ∈ nineGroup := by decide

theorem nineGroup_mul_generators (g : Perm (Fin 9)) (hg : g ∈ nineGroup) :
    g*nineG0 ∈ nineGroup ∧ g*nineG1 ∈ nineGroup ∧ g*nineG2 ∈ nineGroup := by
  simp only [nineGroup, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def nineChunkCells (chunk : _root_.ChainReturns.Chunk) : List Bool :=
  completedChains chunk.chains

def nineChunkNormalization (chunk : _root_.ChainReturns.Chunk) : Perm (Fin 9) :=
  cellNormalization 8 (by omega) (nineChunkCells chunk)

theorem nine_single_normalization : nineChunkNormalization (.single 12) = nineG0 := by
  change cellNormalization 8 (by omega) (completedChain 12 ++ []) = nineG0
  rw [List.append_nil, completedChain_normalization 8 (by omega) 12 (by omega)]
  decide

theorem nine_pair_first_normalization : nineChunkNormalization (.pair 13 11) = nineG1 := by
  change cellNormalization 8 (by omega) (completedChains [13,11]) = nineG1
  rw [completed_pair_chains, completedPair_normalization 8 (by omega) 13 11 (by omega) (by omega)]
  decide

theorem nine_pair_second_normalization : nineChunkNormalization (.pair 14 10) = nineG2 := by
  change cellNormalization 8 (by omega) (completedChains [14,10]) = nineG2
  rw [completed_pair_chains, completedPair_normalization 8 (by omega) 14 10 (by omega) (by omega)]
  decide

end SuperpermutationLowerBound.ChainReturns
