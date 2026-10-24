module

public import SuperpermutationLowerBound.Refinement.ReturnMaps

@[expose] public section

/-! The two explicit return cycles in each residue class. Only a return at
`period n` is required; no exact-order computation is used. -/
namespace SuperpermutationLowerBound.Refinement

namespace ReturnCycle

/-- Following the edges of a finite walk computes each corresponding power. -/
theorem pow_walk {α : Type*} (g : Equiv.Perm α) (v : ℕ → α) (L : ℕ)
    (step : ∀ i < L, g (v i) = v (i+1)) :
    ∀ i ≤ L, (g^i) (v 0) = v i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), step i (by omega)]

/-- A closed walk fixes all its vertices after any multiple of its length. -/
theorem pow_fix_of_closed_walk {α : Type*} (g : Equiv.Perm α) (v : ℕ → α)
    (L P : ℕ) (step : ∀ i < L, g (v i) = v (i+1))
    (closed : v L = v 0) (hLP : L ∣ P) (j : ℕ) (hj : j ≤ L) :
    (g^P) (v j) = v j := by
  have hL : (g^L) (v 0) = v 0 := (pow_walk g v L step L le_rfl).trans closed
  have hmul : ∀ q : ℕ, (g^(L*q)) (v 0) = v 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hL, ih]
  obtain ⟨q, rfl⟩ := hLP
  rw [← pow_walk g v L step j hj]
  calc
    (g^(L*q)) ((g^j) (v 0)) = (g^j) ((g^(L*q)) (v 0)) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, ← Equiv.Perm.mul_apply, ← pow_add,
        Nat.add_comm]
    _ = (g^j) (v 0) := by rw [hmul]

def a0 (m j : ℕ) : ℕ :=
  if j = 0 then 1 else if j < m then 3*j+2 else if j < 2*m then 3*(j-m+1) else 1

theorem a0_le (m j : ℕ) (hm : 2 ≤ m) : a0 m j ≤ (3*m+0) := by
  unfold a0
  split_ifs <;> omega

theorem a0_closed (m : ℕ) (hm : 2 ≤ m) :
    a0 m (2*m) = a0 m 0 := by
  unfold a0
  split_ifs <;> omega

theorem a0_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2*m) :
    cellGValue (3*m+0) (a0 m j) = a0 m (j+1) := by
  unfold a0
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

def b0 (m j : ℕ) : ℕ :=
  if j = 0 then 2 else if j < m then 3*j+1 else 2

theorem b0_le (m j : ℕ) (hm : 2 ≤ m) : b0 m j ≤ (3*m+0) := by
  unfold b0
  split_ifs <;> omega

theorem b0_closed (m : ℕ) (hm : 2 ≤ m) :
    b0 m (m) = b0 m 0 := by
  unfold b0
  split_ifs <;> omega

theorem b0_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    cellGValue (3*m+0) (b0 m j) = b0 m (j+1) := by
  unfold b0
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

def a1 (m j : ℕ) : ℕ :=
  if j = 0 then 1 else if j < m then 3*j+2 else if j = m then 2 else if j < 2*m+1 then 3*(j-m)+1 else 1

theorem a1_le (m j : ℕ) (hm : 2 ≤ m) : a1 m j ≤ (3*m+1) := by
  unfold a1
  split_ifs <;> omega

theorem a1_closed (m : ℕ) (hm : 2 ≤ m) :
    a1 m (2*m+1) = a1 m 0 := by
  unfold a1
  split_ifs <;> omega

theorem a1_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2*m+1) :
    cellGValue (3*m+1) (a1 m j) = a1 m (j+1) := by
  unfold a1
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

def b1 (m j : ℕ) : ℕ :=
  if j < m then 3*j+3 else 3

theorem b1_le (m j : ℕ) (hm : 2 ≤ m) : b1 m j ≤ (3*m+1) := by
  unfold b1
  split_ifs <;> omega

theorem b1_closed (m : ℕ) (hm : 2 ≤ m) :
    b1 m (m) = b1 m 0 := by
  unfold b1
  split_ifs <;> omega

theorem b1_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    cellGValue (3*m+1) (b1 m j) = b1 m (j+1) := by
  unfold b1
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

def a2 (m j : ℕ) : ℕ :=
  if j = 0 then 1 else if j < m+1 then 3*j+2 else 1

theorem a2_le (m j : ℕ) (hm : 2 ≤ m) : a2 m j ≤ (3*m+2) := by
  unfold a2
  split_ifs <;> omega

theorem a2_closed (m : ℕ) (hm : 2 ≤ m) :
    a2 m (m+1) = a2 m 0 := by
  unfold a2
  split_ifs <;> omega

theorem a2_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < m+1) :
    cellGValue (3*m+2) (a2 m j) = a2 m (j+1) := by
  unfold a2
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

def b2 (m j : ℕ) : ℕ :=
  if j = 0 then 2 else if j < m+1 then 3*j+1 else if j < 2*m+1 then 3*(j-m) else 2

theorem b2_le (m j : ℕ) (hm : 2 ≤ m) : b2 m j ≤ (3*m+2) := by
  unfold b2
  split_ifs <;> omega

theorem b2_closed (m : ℕ) (hm : 2 ≤ m) :
    b2 m (2*m+1) = b2 m 0 := by
  unfold b2
  split_ifs <;> omega

theorem b2_step (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2*m+1) :
    cellGValue (3*m+2) (b2 m j) = b2 m (j+1) := by
  unfold b2
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    (first | contradiction | omega)

theorem cover0 (m i : ℕ) (hm : 2 ≤ m) (hi : i ≤ 3*m+0) :
    i = 0 ∨ (∃ j < 2*m, a0 m j = i) ∨ (∃ j < m, b0 m j = i) := by
  by_cases hzero : i = 0
  · exact Or.inl hzero
  right
  have hdiv := Nat.mod_add_div i 3
  have hmod := Nat.mod_lt i (by omega : 0 < 3)
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · left; refine ⟨m+i/3-1, by omega, ?_⟩
    unfold a0
    split_ifs <;> omega
  · by_cases hone : i = 1
    · left; refine ⟨0, by omega, ?_⟩; simp [a0, hone]
    · right; refine ⟨i/3, by omega, ?_⟩
      unfold b0
      split_ifs <;> omega
  · by_cases htwo : i = 2
    · right; refine ⟨0, by omega, ?_⟩
      unfold b0
      split_ifs <;> omega
    · left; refine ⟨i/3, by omega, ?_⟩
      unfold a0
      split_ifs <;> omega

theorem cover1 (m i : ℕ) (hm : 2 ≤ m) (hi : i ≤ 3*m+1) :
    i = 0 ∨ (∃ j < 2*m+1, a1 m j = i) ∨ (∃ j < m, b1 m j = i) := by
  by_cases hzero : i = 0
  · exact Or.inl hzero
  right
  have hdiv := Nat.mod_add_div i 3
  have hmod := Nat.mod_lt i (by omega : 0 < 3)
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · right; refine ⟨i/3-1, by omega, ?_⟩
    unfold b1
    split_ifs <;> omega
  · by_cases hone : i = 1
    · left; refine ⟨0, by omega, ?_⟩; simp [a1, hone]
    · left; refine ⟨m+i/3, by omega, ?_⟩
      unfold a1
      split_ifs <;> omega
  · by_cases htwo : i = 2
    · left; refine ⟨m, by omega, ?_⟩
      unfold a1
      split_ifs <;> omega
    · left; refine ⟨i/3, by omega, ?_⟩
      unfold a1
      split_ifs <;> omega

theorem cover2 (m i : ℕ) (hm : 2 ≤ m) (hi : i ≤ 3*m+2) :
    i = 0 ∨ (∃ j < m+1, a2 m j = i) ∨ (∃ j < 2*m+1, b2 m j = i) := by
  by_cases hzero : i = 0
  · exact Or.inl hzero
  right
  have hdiv := Nat.mod_add_div i 3
  have hmod := Nat.mod_lt i (by omega : 0 < 3)
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · right; refine ⟨m+i/3, by omega, ?_⟩
    unfold b2
    split_ifs <;> omega
  · by_cases hone : i = 1
    · left; refine ⟨0, by omega, ?_⟩; simp [a2, hone]
    · right; refine ⟨i/3, by omega, ?_⟩
      unfold b2
      split_ifs <;> omega
  · by_cases htwo : i = 2
    · right; refine ⟨0, by omega, ?_⟩
      unfold b2
      split_ifs <;> omega
    · left; refine ⟨i/3, by omega, ?_⟩
      unfold a2
      split_ifs <;> omega

end ReturnCycle

/-- Lift a bounded natural-label closed walk to the literal finite alphabet. -/
theorem cellG_pow_fix_walk (n : ℕ) (hn : 7 ≤ n) (v : ℕ → ℕ)
    (L P : ℕ) (bound : ∀ j, v j ≤ n)
    (step : ∀ j < L, cellGValue n (v j) = v (j+1))
    (closed : v L = v 0) (hLP : L ∣ P) (j : ℕ) (hj : j ≤ L) :
    ((cellG n hn)^P) ⟨v j, by have := bound j; omega⟩ =
      ⟨v j, by have := bound j; omega⟩ := by
  let w : ℕ → Fin (n+1) := fun i => ⟨v i, by have := bound i; omega⟩
  exact ReturnCycle.pow_fix_of_closed_walk (cellG n hn) w L P
    (fun i hi => Fin.ext (step i hi)) (Fin.ext closed) hLP j hj

@[simp] theorem cellG_pow_zero (n : ℕ) (hn : 7 ≤ n) (P : ℕ) :
    ((cellG n hn)^P) 0 = 0 := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    apply Fin.ext
    simp [cellGValue]

/-- Two closed walks covering the nonzero labels establish a global return. -/
theorem cellG_pow_of_two_walks (n : ℕ) (hn : 7 ≤ n) (P LA LB : ℕ)
    (a b : ℕ → ℕ) (boundA : ∀ j, a j ≤ n) (boundB : ∀ j, b j ≤ n)
    (stepA : ∀ j < LA, cellGValue n (a j) = a (j+1))
    (stepB : ∀ j < LB, cellGValue n (b j) = b (j+1))
    (closedA : a LA = a 0) (closedB : b LB = b 0)
    (divA : LA ∣ P) (divB : LB ∣ P)
    (cover : ∀ i ≤ n, i = 0 ∨ (∃ j < LA, a j = i) ∨ (∃ j < LB, b j = i)) :
    (cellG n hn)^P = 1 := by
  apply Equiv.ext
  intro x
  change ((cellG n hn)^P) x = x
  rcases cover x.val (by omega) with hz | ha | hb
  · have hx : x = 0 := Fin.ext hz
    simp [hx]
  · obtain ⟨j, hj, hval⟩ := ha
    have hx : x = ⟨a j, by have := boundA j; omega⟩ := Fin.ext hval.symm
    rw [hx]
    exact cellG_pow_fix_walk n hn a LA P boundA stepA closedA divA j (by omega)
  · obtain ⟨j, hj, hval⟩ := hb
    have hx : x = ⟨b j, by have := boundB j; omega⟩ := Fin.ext hval.symm
    rw [hx]
    exact cellG_pow_fix_walk n hn b LB P boundB stepB closedB divB j (by omega)

theorem cellG_return_residue0 (m : ℕ) (hn : 7 ≤ 3*m+0) :
    (cellG (3*m+0) hn)^(2*m) = 1 := by
  have hm : 2 ≤ m := by omega
  apply cellG_pow_of_two_walks (3*m+0) hn (2*m) (2*m) (m)
    (ReturnCycle.a0 m) (ReturnCycle.b0 m)
    (fun j => ReturnCycle.a0_le m j hm) (fun j => ReturnCycle.b0_le m j hm)
    (fun j hj => ReturnCycle.a0_step m j hm hj)
    (fun j hj => ReturnCycle.b0_step m j hm hj)
    (ReturnCycle.a0_closed m hm) (ReturnCycle.b0_closed m hm)
  · exact dvd_refl _
  · exact dvd_mul_left _ _
  · exact fun i hi => ReturnCycle.cover0 m i hm hi

theorem cellG_return_residue1 (m : ℕ) (hn : 7 ≤ 3*m+1) :
    (cellG (3*m+1) hn)^(m*(2*m+1)) = 1 := by
  have hm : 2 ≤ m := by omega
  apply cellG_pow_of_two_walks (3*m+1) hn (m*(2*m+1)) (2*m+1) (m)
    (ReturnCycle.a1 m) (ReturnCycle.b1 m)
    (fun j => ReturnCycle.a1_le m j hm) (fun j => ReturnCycle.b1_le m j hm)
    (fun j hj => ReturnCycle.a1_step m j hm hj)
    (fun j hj => ReturnCycle.b1_step m j hm hj)
    (ReturnCycle.a1_closed m hm) (ReturnCycle.b1_closed m hm)
  · exact dvd_mul_left _ _
  · exact dvd_mul_right _ _
  · exact fun i hi => ReturnCycle.cover1 m i hm hi

theorem cellG_return_residue2 (m : ℕ) (hn : 7 ≤ 3*m+2) :
    (cellG (3*m+2) hn)^((m+1)*(2*m+1)) = 1 := by
  have hm : 2 ≤ m := by omega
  apply cellG_pow_of_two_walks (3*m+2) hn ((m+1)*(2*m+1)) (m+1) (2*m+1)
    (ReturnCycle.a2 m) (ReturnCycle.b2 m)
    (fun j => ReturnCycle.a2_le m j hm) (fun j => ReturnCycle.b2_le m j hm)
    (fun j hj => ReturnCycle.a2_step m j hm hj)
    (fun j hj => ReturnCycle.b2_step m j hm hj)
    (ReturnCycle.a2_closed m hm) (ReturnCycle.b2_closed m hm)
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _
  · exact fun i hi => ReturnCycle.cover2 m i hm hi

/-- The regular cell returns after the stated residue-dependent period. -/
theorem cellG_pow_period (n : ℕ) (hn : 7 ≤ n) :
    (cellG n hn)^(period n) = 1 := by
  have hmod := Nat.mod_lt n (by omega : 0 < 3)
  have hdiv := Nat.mod_add_div n 3
  generalize hm : n / 3 = m at *
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · have heq : n = 3*m+0 := by omega
    have hp : period n = 2*m := by simp [period, h, hm]
    rw [hp]
    subst n
    exact cellG_return_residue0 m hn
  · have heq : n = 3*m+1 := by omega
    have hp : period n = m*(2*m+1) := by simp [period, h, hm]
    rw [hp]
    subst n
    exact cellG_return_residue1 m hn
  · have heq : n = 3*m+2 := by omega
    have hp : period n = (m+1)*(2*m+1) := by simp [period, h, hm]
    rw [hp]
    subst n
    exact cellG_return_residue2 m hn

end SuperpermutationLowerBound.Refinement
